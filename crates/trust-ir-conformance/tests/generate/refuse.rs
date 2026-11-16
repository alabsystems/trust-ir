// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The must-refuse corpus builders (KIND 4): `trust_ir_conformance::refuse_fixtures`.
//!
//! Included from `src/lib.rs` (feature `all`), NOT from `generate.rs`:
//! `trust-ir-build/tests/builder_doors.rs` includes `generate.rs` without the
//! `binary` feature the byte-string builders need, and the other test targets
//! that include it use none of these. The file sits in a subdirectory so
//! Cargo never auto-discovers it as a test target of its own.

use trust_ir::constant::Constant;
use trust_ir::dialect::DialectInst;
use trust_ir::inst::{AllocOrigin, ICmpOp, Inst, SwitchCase, UnOp};
use trust_ir::node::InstrNode;
use trust_ir::proof::{
    ObligationKind, ProofAnnotation, ProofCertificate, ProofDigest, ProofEvidence, ProofFormula,
    ProofObligation, ProofStatus,
};
use trust_ir::ty::{
    EnumDef, EnumTagRepr, EnumVariant, FatPtrKind, FieldDef, FuncTy, StructDef, Ty, TypeOrigin,
};
use trust_ir::value::{BlockId, EnumId, FuncId, ProofId, StructId, TyId, ValueId};
use trust_ir::{Block, Endianness, Function, Linkage, Module, ParamAttrs, Producer, TargetInfo};
use trust_ir_build::ModuleBuilder;

use crate::fixtures::{FixtureError, OrFixture, fixture_invariant};

// ===========================================================================
// The must-refuse corpus (KIND 4, 2026-09-24) — `tests/fixtures/refuse/`.
//
// Every builder below produces an artifact a conforming consumer must REFUSE,
// paired in `tests/fixtures/refuse/MANIFEST.tsv` with the trust-ir verdict
// that names why. `tests/refuse_corpus.rs` byte-pins each one and runs every
// pinned verdict; `trust_ir_conformance::refuse` hands the checked-in bytes
// to a consumer. Unlike the round-trip corpus in `generate.rs`, these
// modules are NOT required to validate: most are refused by a named entry
// point, and that refusal is the content.
//
// Every builder is a `pub fn` of a library module, so one nobody calls is
// never dead code to the compiler: `refuse_corpus.rs::every_refuse_builder_is_a_rows_line`
// scans this file and refuses a builder that is not a ROWS line.
//
// Naming: `build_refuse_<row>` returns a `Module`; `build_refuse_bytes_<row>`
// returns poisoned wire bytes. Every builder is TOTAL (`Result<_, FixtureError>`,
// r11 item 7): the test that calls it decides. The byte builders read and
// write varints through the codec's own rule (`trust_ir::binary::{
// decode_varint, encode_varint}`) and touch the header only through `get` /
// `get_mut`, so no fixture re-derives the wire grammar or indexes past it. Row ids name the FEATURE, never a wire
// version (`names_not_numbers.rs` walks this directory too).
// ===========================================================================

/// The one target every refuse row that needs one uses: the canonical
/// aarch64-apple-darwin the rest of the corpus is measured on.
fn refuse_target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

/// The license every non-license refuse row wears: OUTSIDE
/// `EVIDENCE_BOUND_GATE_AUTHORITIES` (so the license layer is not what
/// refuses the row) and, by design, in no consumer's default recognized set
/// (so a consumer recognizes it FOR THE RUN, or the control row fails it by
/// name). `refuse_corpus.rs` pins this spelling equal to
/// `trust_ir_conformance::refuse::STRUCTURAL_LICENSE_AUTHORITY`; this file
/// is also compiled standalone (`mod generate;`), so it cannot import it.
pub const REFUSE_STRUCTURAL_LICENSE_AUTHORITY: &str = "trust-direct-lane-structural";

/// `Gated { REFUSE_STRUCTURAL_LICENSE_AUTHORITY }`, so a row whose subject is
/// not the license passes the codegen license layer and exhibits exactly the
/// refusal it is named for.
fn refuse_structural_license() -> trust_ir::BodyGate {
    trust_ir::BodyGate::Gated {
        authority: REFUSE_STRUCTURAL_LICENSE_AUTHORITY.into(),
        evidence: None,
    }
}

/// `fn id(x: i32) -> i32 { x }`, with `gate` on the body.
fn refuse_identity(name: &str, gate: Option<trust_ir::BodyGate>) -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new(name);
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("id", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    if let Some(gate) = gate {
        fb.set_body_gate(gate);
    }
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

// ----- the control row ------------------------------------------------------

/// The CONTROL (carrier `control`): the envelope every module row shares —
/// `fn id(x: i32) -> i32 { x }` under the structural license on the canonical
/// target — with NO subject. A conforming consumer must ACCEPT it; a consumer
/// that refuses it has attributed nothing to any row's subject (the runner is
/// reason-blind: `refuse.rs` module docs).
pub fn build_refuse_control_licensed_identity() -> Result<Module, FixtureError> {
    let mut m = refuse_identity(
        "refuse_control_licensed_identity",
        Some(refuse_structural_license()),
    )?;
    m.target_info = Some(refuse_target());
    Ok(m)
}

// ----- codegen license ------------------------------------------------------

/// `body_gate = Some(Ungated)`: an affirmative "no gate was applied".
pub fn build_refuse_body_gate_ungated() -> Result<Module, FixtureError> {
    refuse_identity(
        "refuse_body_gate_ungated",
        Some(trust_ir::BodyGate::Ungated),
    )
}

/// A bodied function with NO licensing claim in a blob whose header is v41+
/// (the `display_path` forces the contract-surface header): the producer rule
/// the decoded-provenance layer refuses, and the codegen gate's unlicensed
/// refusal under its fail-closed default.
pub fn build_refuse_body_gate_omitted_at_contract_surface() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new("refuse_body_gate_omitted");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("id", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    fb.set_display_path("refuse::id");
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// `Gated { authority: "nobody-ran-this" }`: a gate no consumer recognizes.
pub fn build_refuse_body_gate_unknown_authority() -> Result<Module, FixtureError> {
    refuse_identity(
        "refuse_body_gate_unknown_authority",
        Some(trust_ir::BodyGate::Gated {
            authority: "nobody-ran-this".into(),
            evidence: None,
        }),
    )
}

/// `Gated { "clean-kernel-tv" }` with zero certificates: the evidence-bound
/// authority worn without its evidence.
pub fn build_refuse_body_gate_kernel_tv_without_certificate() -> Result<Module, FixtureError> {
    refuse_identity(
        "refuse_body_gate_kernel_tv_no_cert",
        Some(trust_ir::BodyGate::Gated {
            authority: "clean-kernel-tv".into(),
            evidence: None,
        }),
    )
}

/// `Gated { "clean-kernel-tv" }` beside a FAILED TranslationValidation row
/// scoped to the body: a refuted license.
pub fn build_refuse_body_gate_refuted_by_failed_tv() -> Result<Module, FixtureError> {
    let mut module = refuse_identity(
        "refuse_body_gate_refuted",
        Some(trust_ir::BodyGate::Gated {
            authority: "clean-kernel-tv".into(),
            evidence: None,
        }),
    )?;
    let f = module
        .functions
        .first()
        .or_fixture("the identity function")?
        .id;
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::TranslationValidation,
            ProofStatus::Failed,
            "CleanTV.id.denotes",
        )
        .with_function(f),
    );
    Ok(module)
}

// ----- codegen license evidence (roadmap WS1.12(c) / WS6.7(b)) --------------

/// `f(a, b) = a*b + a` over `u64`, Clean-produced, whose `Certified`
/// TranslationValidation row (#0) is minted by the kernel-replayable identity
/// rung, licensed `clean-kernel-tv` with the `GateEvidence` `evidence` builds
/// from the module and the body (or none). The certificate is genuine, so
/// every lane admits the license on its own; the evidence is the only subject.
fn refuse_certified_tv_body(
    name: &str,
    evidence: impl FnOnce(&Module, FuncId) -> Result<Option<trust_ir::GateEvidence>, FixtureError>,
) -> Result<Module, FixtureError> {
    use trust_ir::proof::{ProofLineageId, ProofTransform, ProofTransformStage};
    let mut mb = ModuleBuilder::new(name);
    mb.set_default_producer(Producer::Clean);
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("f", sig);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::U64);
    let b = fb.add_block_param(e, Ty::U64);
    fb.switch_to_block(e);
    let p = fb.mul(Ty::U64, a, b);
    let r = fb.binop(trust_ir::inst::BinOp::Add, Ty::U64, p, a);
    fb.ret(vec![r]);
    let f = fb.build();
    let mut module = mb.build().or_fixture("ModuleBuilder::build")?;
    let (_, obligation, certificate) = trust_ir_build::certify_identity_lineage_rung(
        &module,
        ProofLineageId::new(0),
        ProofId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "identity",
            "refuse-gate-evidence",
            "1.0.0",
        ),
        f,
    )
    .or_fixture("the body is in the backend-TV fragment")?;
    module.proof_obligations.push(obligation);
    module.proof_certificates.push(certificate);
    let evidence = evidence(&module, f)?;
    module
        .function_by_id_mut(f)
        .or_fixture("built above")?
        .body_gate = Some(trust_ir::BodyGate::Gated {
        authority: "clean-kernel-tv".into(),
        evidence,
    });
    Ok(module)
}

/// A kernel-TV license whose `GateEvidence` cites the body's genuine
/// `Certified` TranslationValidation row but records a body digest that is
/// NOT the body's (one bit off `function_body_digest`): the license names
/// another body — a rewrite after mint, or a transplant — and a present
/// evidence is recomputed, never taken on faith.
pub fn build_refuse_body_gate_evidence_stale_body_digest() -> Result<Module, FixtureError> {
    refuse_certified_tv_body("refuse_body_gate_evidence_stale", |module, f| {
        let mut body_digest = module
            .function_body_digest(f)
            .or_fixture("the body has a digest")?;
        body_digest.bytes[0] ^= 1;
        Ok(Some(trust_ir::GateEvidence {
            obligation: ProofId::new(0),
            body_digest,
        }))
    })
}

/// The same genuinely certified kernel-TV license with NO `GateEvidence`
/// recorded: every default lane admits it (`None` is the pre-evidence
/// meaning), and a consumer that requires the license to name its obligation
/// and body refuses it by name.
pub fn build_refuse_body_gate_kernel_tv_evidence_unrecorded() -> Result<Module, FixtureError> {
    refuse_certified_tv_body("refuse_body_gate_evidence_unrecorded", |_, _| Ok(None))
}

// ----- codegen: what no consumer can lower ---------------------------------

/// A licensed body beside a module-level `global_asm!` block.
pub fn build_refuse_global_asm_block() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new("refuse_global_asm");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    mb.add_global_asm(".globl trust_probe\ntrust_probe:\n  ret\n");
    mb.build().or_fixture("ModuleBuilder::build")
}

/// A licensed body that frees a heap cell with the bare `Dealloc`
/// instruction, which names neither the owning runtime nor the layout.
pub fn build_refuse_dealloc_instruction() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new("refuse_dealloc");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let cell = fb.heap_alloc(Ty::I32, None, None, AllocOrigin::RustHeap);
    fb.dealloc(cell);
    fb.ret(vec![]);
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// A licensed body stamped `Producer::TRust` (the THIR producer's stamp) that
/// spells `&mut x` as the permission instruction `BorrowMut`. A Rust producer
/// spells every reference as the place's address or a `Copy` of it
/// (`docs/SPEC_RATIFICATIONS.md`, "A Rust reference carries no permission
/// instruction"), so plain validation refuses it.
pub fn build_refuse_rust_reference_as_permission_borrow() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new("refuse_rust_reference_permission_borrow");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("bump", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let x = fb.alloca(Ty::I32);
    let five = fb.const_value(Ty::I32, Constant::Int(5));
    fb.store(Ty::I32, x, five);
    let r = fb.borrow_mut(x);
    let six = fb.const_value(Ty::I32, Constant::Int(6));
    fb.store(Ty::I32, r, six);
    let read = fb.load(Ty::I32, x);
    fb.ret(vec![read]);
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// A licensed body indexing a `Ty::Sequence`, which has no machine layout.
pub fn build_refuse_sequence_element_op() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new("refuse_sequence_element");
    let elem = mb.add_type(Ty::I32);
    let seq = Ty::Sequence(elem);
    let ft = mb.add_func_type(vec![seq.clone()], vec![Ty::I32]);
    let mut fb = mb.function("first", ft);
    let entry = fb.create_block();
    let s = fb.add_block_param(entry, seq);
    fb.switch_to_block(entry);
    let zero = fb.uconst(Ty::U64, 0);
    let x = fb.extract_element(Ty::I32, s, zero);
    fb.ret(vec![x]);
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// A licensed body carrying a `DialectOp` in a namespace no in-tree lowering
/// registers (well-formed and opaque; unlowerable).
pub fn build_refuse_dialect_op_foreign_namespace() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new("refuse_dialect_op_foreign");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let _ = fb.dialect_op(DialectInst::new("acme", "noop"));
    fb.ret(vec![]);
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// A `NoOverflow` claim on the very `Assert` that IS the runtime check, with
/// no `ProofRef` binding it to a row about that check.
pub fn build_refuse_unbacked_claim_on_check() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new("refuse_unbacked_claim");
    let ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let mut fb = mb.function("checked", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U32);
    fb.switch_to_block(entry);
    let limit = fb.uconst(Ty::U32, 1000);
    let in_range = fb.icmp(ICmpOp::Ult, Ty::U32, x, limit);
    fb.assert(in_range);
    fb.annotate_last(ProofAnnotation::NoOverflow)
        .or_fixture("the assert was just emitted")?;
    fb.ret(vec![x]);
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// An `Assert` of UNSPECIFIED panic kind (plan item P, wire v52) — what every
/// pre-v52 assert decodes to: well-formed, accepted by the default codegen
/// gate, refused by a consumer that lowers failed checks faithfully. Its
/// subject is the kind alone: the same check under `AssertKind::Overflow`
/// is accepted under the same admission (`refuse_corpus.rs`'s twin test).
pub fn build_refuse_assert_panic_kind_unspecified() -> Result<Module, FixtureError> {
    build_assert_kind_subject(trust_ir::AssertKind::Unspecified)
}

/// The `assert_panic_kind_unspecified` subject with the check's kind as a
/// parameter, so the refusal and its accepted twin differ in that one field.
pub fn build_assert_kind_subject(kind: trust_ir::AssertKind) -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new("refuse_assert_kind");
    let ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let mut fb = mb.function("checked", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U32);
    fb.switch_to_block(entry);
    let limit = fb.uconst(Ty::U32, 1000);
    let in_range = fb.icmp(ICmpOp::Ult, Ty::U32, x, limit);
    fb.assert_kind(in_range, kind);
    fb.ret(vec![x]);
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

// ----- amendment P: the panic site (wire v54) ------------------------------

/// How a `build_panic_site_subject` check spells its site.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PanicSiteSubject {
    /// A well-formed site: `panic_bounds_check(usize, usize, ptr)` at the
    /// immutable `@global.0` — the accepted twin of every row below.
    Faithful,
    /// No site at all (the check of a pre-v54 producer).
    Missing,
    /// The entry takes the location only, not the bounds check's operands.
    EntrySignature,
    /// The location is `Value(global_addr @global.0)`.
    LocationNonCanonical,
    /// The location global is mutable.
    LocationGlobalMutable,
}

/// One licensed function `checked(i: usize, n: usize) -> usize` asserting
/// `i < n` as a bounds check whose site is spelled by `subject` (amendment
/// P). Function 0 is the bodyless entry, global 0 the location record. The
/// rows below and their accepted twin (`Faithful`) differ in the site alone.
pub fn build_panic_site_subject(subject: PanicSiteSubject) -> Result<Module, FixtureError> {
    use trust_ir::{AssertKind, PanicLocation, PanicSite};
    let mut mb = ModuleBuilder::new_with_target_info("refuse_panic_site", refuse_target());
    let entry_params = if subject == PanicSiteSubject::EntrySignature {
        vec![Ty::Ptr]
    } else {
        vec![Ty::Usize, Ty::Usize, Ty::Ptr]
    };
    let entry_ty = mb.add_func_type(entry_params, vec![]);
    let entry = mb.declare_function("panic_bounds_check", entry_ty);
    mb.add_global(trust_ir::Global {
        name: "loc.0".into(),
        ty: Ty::U64,
        mutable: subject == PanicSiteSubject::LocationGlobalMutable,
        initializer: Some(Constant::Int(7)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    let ft = mb.add_func_type(vec![Ty::Usize, Ty::Usize], vec![Ty::Usize]);
    let mut fb = mb.function("checked", ft);
    let bb = fb.create_block();
    let i = fb.add_block_param(bb, Ty::Usize);
    let n = fb.add_block_param(bb, Ty::Usize);
    fb.switch_to_block(bb);
    let location = if subject == PanicSiteSubject::LocationNonCanonical {
        PanicLocation::Value(fb.global_addr(trust_ir::value::GlobalId::new(0)))
    } else {
        PanicLocation::Global(trust_ir::value::GlobalId::new(0))
    };
    let in_range = fb.icmp(ICmpOp::Ult, Ty::Usize, i, n);
    let kind = AssertKind::BoundsCheck { index: i, len: n };
    if subject == PanicSiteSubject::Missing {
        fb.assert_kind(in_range, kind);
    } else {
        fb.assert_sited(in_range, kind, PanicSite { entry, location });
    }
    fb.ret(vec![i]);
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// A bounds check with NO panic site (amendment P): well-formed — every
/// pre-v54 assert is one — and accepted by the default codegen gate, but it
/// names no entry and no location, so a consumer that lowers failed checks
/// faithfully refuses it. Its subject is the site alone: the `Faithful`
/// twin, the same check with a site, is admitted by the same admission
/// (`refuse_corpus.rs`'s twin test).
pub fn build_refuse_assert_panic_site_missing() -> Result<Module, FixtureError> {
    build_panic_site_subject(PanicSiteSubject::Missing)
}

/// A panic site whose entry does not take the bounds check's two `usize`
/// operands before the location (amendment P, V2).
pub fn build_refuse_assert_panic_site_entry_signature() -> Result<Module, FixtureError> {
    build_panic_site_subject(PanicSiteSubject::EntrySignature)
}

/// A run-time panic location that is `global_addr` of a module global: its
/// one spelling is the static `Global` location (amendment P, V5).
pub fn build_refuse_assert_panic_location_non_canonical() -> Result<Module, FixtureError> {
    build_panic_site_subject(PanicSiteSubject::LocationNonCanonical)
}

/// A static panic location naming a MUTABLE global (amendment P, V3).
pub fn build_refuse_assert_panic_location_global_mutable() -> Result<Module, FixtureError> {
    build_panic_site_subject(PanicSiteSubject::LocationGlobalMutable)
}

/// An `AssertInvoke` whose unwind destination does not begin with a landing
/// pad (amendment P, V6: `Invoke`'s rule).
pub fn build_refuse_assert_invoke_unwind_dest_without_landing_pad() -> Result<Module, FixtureError>
{
    use trust_ir::{AssertKind, PanicLocation, PanicSite};
    let mut mb = ModuleBuilder::new_with_target_info("refuse_assert_invoke_pad", refuse_target());
    let entry_ty = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let entry = mb.declare_function("panic_const_div_by_zero", entry_ty);
    mb.add_global(trust_ir::Global {
        name: "loc.0".into(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(Constant::Int(7)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    let ft = mb.add_func_type(vec![Ty::Bool, Ty::Usize], vec![Ty::Usize]);
    let mut fb = mb.function("guarded", ft);
    let bb0 = fb.create_block();
    let bb1 = fb.create_block();
    let bb2 = fb.create_block();
    let c = fb.add_block_param(bb0, Ty::Bool);
    let x = fb.add_block_param(bb0, Ty::Usize);
    let y = fb.add_block_param(bb1, Ty::Usize);
    fb.switch_to_block(bb0);
    fb.assert_invoke(
        c,
        AssertKind::DivByZero,
        PanicSite {
            entry,
            location: PanicLocation::Global(trust_ir::value::GlobalId::new(0)),
        },
        bb1,
        vec![x],
        bb2,
    );
    fb.switch_to_block(bb1);
    fb.ret(vec![y]);
    // The "pad" is an ordinary block: no `LandingPad` heads it.
    fb.switch_to_block(bb2);
    fb.unreachable();
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

// ----- executable drops (amendment D, SPEC_RATIFICATIONS.md §20) -----------

/// Which defect a drop-glue row exhibits (`build_drop_glue_subject`).
#[derive(Clone, Copy)]
enum DropGlueSubject {
    /// `drop Box, %p` with NO drop-glue row: well-formed, never a no-op, and
    /// neither executable nor lowerable.
    Unresolved,
    /// The row's glue is `(i64) -> ()`: glue takes exactly one `ptr`.
    GlueSignature,
    /// A direct `call` of the registered glue.
    GlueCalledDirectly,
    /// A `drop_invoke` whose unwind block is an ordinary block.
    DropInvokeWithoutPad,
}

/// `struct Box { data: ptr }`: a type whose drop glue the format cannot
/// infer (an owning pointer, spelled nominally).
fn refuse_box(mb: &mut ModuleBuilder) -> Ty {
    Ty::Struct(mb.add_struct(StructDef {
        id: StructId::new(0),
        name: "Box".into(),
        fields: vec![FieldDef {
            name: "data".into(),
            ty: Ty::Ptr,
            offset: Some(0),
        }],
        size: Some(8),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    }))
}

/// A licensed module dropping a `Box` through its pointer parameter, with
/// `subject`'s defect: a glue function `drop_box` (unless `Unresolved`) and
/// the caller `f(%p: ptr)`.
fn build_drop_glue_subject(name: &str, subject: DropGlueSubject) -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new_with_target_info(name, refuse_target());
    let boxed = refuse_box(&mut mb);
    let ptr_to_unit = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let glue = if matches!(subject, DropGlueSubject::Unresolved) {
        None
    } else {
        let glue_param = if matches!(subject, DropGlueSubject::GlueSignature) {
            Ty::I64
        } else {
            Ty::Ptr
        };
        let glue_ty = mb.add_func_type(vec![glue_param.clone()], vec![]);
        let mut gb = mb.function("drop_box", glue_ty);
        let entry = gb.create_block();
        gb.add_block_param(entry, glue_param);
        gb.switch_to_block(entry);
        gb.ret(vec![]);
        gb.set_body_gate(refuse_structural_license());
        Some(gb.build())
    };
    let mut fb = mb.function("f", ptr_to_unit);
    let bb0 = fb.create_block();
    let p = fb.add_block_param(bb0, Ty::Ptr);
    fb.switch_to_block(bb0);
    match subject {
        DropGlueSubject::Unresolved | DropGlueSubject::GlueSignature => {
            fb.drop(boxed.clone(), p);
            fb.ret(vec![]);
        }
        DropGlueSubject::GlueCalledDirectly => {
            let glue = glue.or_fixture("the glue of a called-directly row")?;
            fb.call_void(glue, vec![p]);
            fb.ret(vec![]);
        }
        DropGlueSubject::DropInvokeWithoutPad => {
            let bb1 = fb.create_block();
            let bb2 = fb.create_block();
            fb.drop_invoke(boxed.clone(), p, bb1, vec![], bb2);
            fb.switch_to_block(bb1);
            fb.ret(vec![]);
            // The "pad" is an ordinary block: no `LandingPad` heads it.
            fb.switch_to_block(bb2);
            fb.unreachable();
        }
    }
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    if let Some(glue) = glue {
        mb.set_drop_glue(boxed, glue)
            .or_fixture("one drop-glue row for one type")?;
    }
    mb.build().or_fixture("ModuleBuilder::build")
}

/// A `Drop` of a `Struct` with no drop-glue row (amendment D, §20 rule 4).
pub fn build_refuse_drop_unresolved() -> Result<Module, FixtureError> {
    build_drop_glue_subject("refuse_drop_unresolved", DropGlueSubject::Unresolved)
}

/// A drop-glue row whose glue is `(i64) -> ()` (amendment D, §20 rule 1).
pub fn build_refuse_drop_glue_invalid() -> Result<Module, FixtureError> {
    build_drop_glue_subject("refuse_drop_glue_invalid", DropGlueSubject::GlueSignature)
}

/// A direct `call` of a registered drop glue (amendment D, §20 rule 5b).
pub fn build_refuse_drop_glue_called_directly() -> Result<Module, FixtureError> {
    build_drop_glue_subject(
        "refuse_drop_glue_called_directly",
        DropGlueSubject::GlueCalledDirectly,
    )
}

/// A `DropInvoke` whose unwind destination does not begin with a landing
/// pad (amendment D, §20 rule 6: `Invoke`'s rule).
pub fn build_refuse_drop_invoke_unwind_dest_without_landing_pad() -> Result<Module, FixtureError> {
    build_drop_glue_subject(
        "refuse_drop_invoke_pad",
        DropGlueSubject::DropInvokeWithoutPad,
    )
}

/// An `InvokeIndirect` whose unwind destination does not begin with a
/// landing pad (amendment D, Part 2, §21 rule 1: `Invoke`'s rule).
pub fn build_refuse_invoke_indirect_unwind_dest_without_landing_pad() -> Result<Module, FixtureError>
{
    let mut mb = ModuleBuilder::new_with_target_info("refuse_invoke_indirect_pad", refuse_target());
    let thunk_ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut gb = mb.function("seven", thunk_ty);
    let entry = gb.create_block();
    gb.switch_to_block(entry);
    let seven = gb.iconst(Ty::I64, 7);
    gb.ret(vec![seven]);
    gb.set_body_gate(refuse_structural_license());
    let seven_fn = gb.build();
    let mut fb = mb.function("f", thunk_ty);
    let bb0 = fb.create_block();
    let bb1 = fb.create_block();
    let bb2 = fb.create_block();
    fb.switch_to_block(bb0);
    let callee = fb.const_value(Ty::Func(thunk_ty), Constant::FnDef(seven_fn));
    let result = fb.invoke_indirect(callee, thunk_ty, vec![], bb1, vec![], bb2);
    fb.switch_to_block(bb1);
    fb.ret(vec![result]);
    // The "pad" is an ordinary block: no `LandingPad` heads it.
    fb.switch_to_block(bb2);
    fb.unreachable();
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// A drop-glue section whose glue ids are not strictly ascending (amendment
/// D, §20 rule 5c): the writer writes the rows it is given, the reader
/// refuses the order.
pub fn build_refuse_bytes_blob_drop_glue_not_canonical() -> Result<Vec<u8>, FixtureError> {
    let mut module = build_drop_glue_subject(
        "refuse_blob_drop_glue_order",
        DropGlueSubject::DropInvokeWithoutPad,
    )?;
    let first = module
        .drop_glue
        .first()
        .cloned()
        .or_fixture("the glue row")?;
    // A row keyed on a second type, for a glue id ABOVE the first, written
    // BEFORE it: the table descends.
    let above = first
        .glue
        .index()
        .checked_add(1)
        .or_fixture("a glue id above the first row's")?;
    module.drop_glue.insert(
        0,
        trust_ir::DropGlueEntry {
            glue: FuncId::new(above),
            ty: Ty::Tuple(vec![first.ty.clone()]),
        },
    );
    trust_ir::binary::serialize_module(&module).or_fixture("serialize_module")
}

/// A sited assert whose PanicLocation byte is 2: the tag space is closed at
/// 0 `Global` and 1 `Value` (amendment P).
pub fn build_refuse_bytes_blob_panic_location_tag_unknown() -> Result<Vec<u8>, FixtureError> {
    let module = build_panic_site_subject(PanicSiteSubject::Faithful)?;
    let mut bytes = trust_ir::binary::serialize_module(&module).or_fixture("serialize_module")?;
    // The sited assert: tag 66, cond %2, kind presence 1, BoundsCheck 3, %0,
    // %1, entry 0, then the PanicLocation byte (0, Global) and global 0.
    let pattern = [66u8, 2, 1, 3, 0, 1, 0, 0, 0];
    let at = bytes
        .windows(pattern.len())
        .position(|window| window == pattern)
        .or_fixture("the sited assert's bytes")?;
    let location_byte = at
        .checked_add(7)
        .or_fixture("the PanicLocation byte's offset")?;
    *bytes
        .get_mut(location_byte)
        .or_fixture("the PanicLocation byte")? = 2;
    Ok(bytes)
}

// ----- the authority lane --------------------------------------------------

/// A body-less declaration whose `proved` summary is `backed_by` a row of an
/// import: a cross-crate CLAIM the structural pass takes on faith and the
/// authority lane refuses unauthenticated.
pub fn build_refuse_import_backed_summary_unauthenticated() -> Result<Module, FixtureError> {
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
    let mut m = Module::new("refuse_import_backed");
    m.target_info = Some(refuse_target());
    let digest = trust_ir::proof::ProofDigest {
        algorithm: trust_ir::proof::ProofDigestAlgorithm::Sha256,
        bytes: [0x42; 32],
    };
    let dep = m
        .intern_import(
            trust_ir::ModuleImport::new("some_dependency", digest).with_producer(Producer::TRust),
        )
        .or_fixture("Module::intern_import")?;
    let ft = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let mut nonneg = ProofFormula::smtlib2("(>= result 0)", "Bool");
    nonneg.bindings = vec![(
        "result".to_string(),
        ClauseBinding {
            sort: ClauseSort::Int,
            place: ClausePlace::ResultSlot { index: 0 },
        },
    )];
    let mut summary = trust_ir::FunctionSummary::new();
    summary.ensures = vec![nonneg];
    let summary = summary
        .proved()
        .backed_by(trust_ir::ExternRef::new(dep, "f").relying_on(ProofId::new(0)));
    let mut f = Function::declaration(FuncId::new(0), "f", ft, summary);
    f.producer = Some(Producer::TRust);
    m.try_add_function(f)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

// ----- completeness ----------------------------------------------------------

/// A licensed identity with NO completeness claim (`Module.completeness` is
/// `None`): what every hand-built module and every pre-carrier blob reads as.
pub fn build_refuse_completeness_unclaimed() -> Result<Module, FixtureError> {
    refuse_identity(
        "refuse_completeness_unclaimed",
        Some(refuse_structural_license()),
    )
}

// ----- structural canaries: refused by `validate_module` itself ---------------
//
// A consumer that validates never meets these; a consumer LANE that skips
// validation compiles them. Each is one named refusal.

/// A `Tainted` value flowing into a `TrustedSink` in the same block.
pub fn build_refuse_tainted_value_reaches_sink() -> Result<Module, FixtureError> {
    let mut m = Module::new("refuse_taint");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let mut f = Function::new(FuncId::new(0), "probe", ft, BlockId::new(0));
    f.producer = Some(Producer::TRust);
    f.body_gate = Some(refuse_structural_license());
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), Ty::I32));
    b.body.push(
        InstrNode::new(Inst::Copy {
            ty: Ty::I32,
            operand: ValueId::new(0),
        })
        .with_results(vec![ValueId::new(1)])
        .with_proof(ProofAnnotation::Tainted),
    );
    b.body.push(
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        })
        .with_proof(ProofAnnotation::TrustedSink),
    );
    f.blocks.push(b);
    m.try_add_function(f)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

/// An `ObligationKind::Custom` row in a namespace outside
/// `ADMITTED_OBLIGATION_NAMESPACES`.
pub fn build_refuse_custom_obligation_unpinned_namespace() -> Result<Module, FixtureError> {
    let mut module = refuse_identity("refuse_custom_namespace", Some(refuse_structural_license()))?;
    module.proof_obligations.push(ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Custom {
            namespace: "vendor.acme".into(),
            name: "audited".into(),
        },
        ProofStatus::Pending,
        "an authority nobody pinned",
    ));
    Ok(module)
}

/// A contract obligation whose `smtlib2` payload `(>= 0 5)` (false) and whose
/// `smtlib` rendering `(>= 5 0)` (true) are two formulas. The contract
/// grounder read the rendering, so a kernel replay of the true text was
/// admitted for the false payload; one formula is now a validation rule.
pub fn build_refuse_formula_smtlib_rendering_disagrees() -> Result<Module, FixtureError> {
    let mut module = refuse_identity(
        "refuse_formula_two_texts",
        Some(refuse_structural_license()),
    )?;
    let mut formula = ProofFormula::smtlib2("(>= 0 5)", "Bool");
    formula.smtlib = Some("(>= 5 0)".into());
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Pending,
            "states one payload and renders another",
        )
        .with_formula(formula),
    );
    Ok(module)
}

/// The same two texts as a function summary's `requires` clause: a caller, a
/// linker or a minted obligation could each read a different one. One formula
/// holds wherever a module states one (`Module::stated_formulas`).
pub fn build_refuse_summary_clause_smtlib_rendering_disagrees() -> Result<Module, FixtureError> {
    let mut module = refuse_identity(
        "refuse_summary_clause_two_texts",
        Some(refuse_structural_license()),
    )?;
    let mut formula = ProofFormula::smtlib2("(>= 0 5)", "Bool");
    formula.smtlib = Some("(>= 5 0)".into());
    module
        .functions
        .first_mut()
        .or_fixture("the identity function")?
        .summary = Some(
        trust_ir::FunctionSummary::new()
            .with_params(vec!["x".into()])
            .requiring(formula),
    );
    Ok(module)
}

/// Roadmap DG-63 (v62): a `requires` clause binding the entry-state pointee
/// (`ClausePlace::ParamPointeeEntry`) of the by-value `x: i32`. There is no
/// value behind `x` to read: a consumer that resolved the place anyway would
/// read the clause over memory the signature never names (or over `x`
/// itself, the width/type lie of binding `*x` as the parameter).
pub fn build_refuse_summary_clause_param_pointee_of_by_value_param() -> Result<Module, FixtureError>
{
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
    let mut module = refuse_identity(
        "refuse_param_pointee_of_by_value_param",
        Some(refuse_structural_license()),
    )?;
    let mut formula = ProofFormula::smtlib2("(bvsgt x #x00000000)", "Bool");
    formula.bindings = vec![(
        "x".into(),
        ClauseBinding {
            sort: ClauseSort::BitVec(32),
            place: ClausePlace::ParamPointeeEntry { index: 0 },
        },
    )];
    module
        .functions
        .first_mut()
        .or_fixture("the identity function")?
        .summary = Some(
        trust_ir::FunctionSummary::new()
            .with_params(vec!["x".into()])
            .requiring(formula),
    );
    Ok(module)
}

/// The same two texts as a spec machine's typed invariant carrier: the spec
/// linker compared the rendering and never read the payload.
pub fn build_refuse_spec_carrier_smtlib_rendering_disagrees() -> Result<Module, FixtureError> {
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
    let mut module = refuse_identity(
        "refuse_spec_carrier_two_texts",
        Some(refuse_structural_license()),
    )?;
    let mut typed = ProofFormula::smtlib2("(<= seq 8)", "Bool");
    typed.smtlib = Some("(<= seq 7)".into());
    typed.bindings = vec![(
        "seq".into(),
        ClauseBinding {
            sort: ClauseSort::Int,
            place: ClausePlace::SpecVar { index: 0 },
        },
    )];
    let mut spec = trust_ir::SpecModule::design_only("ring");
    spec.vars = vec![trust_ir::SpecVar::new("seq", "Int").with_sort(ClauseSort::Int)];
    spec.invariants = vec![trust_ir::SpecInvariant::new("Bounded", "(<= seq 7)").with_typed(typed)];
    module.spec_modules.push(spec);
    Ok(module)
}

/// A `RefinementType` obligation citing `pred.0` — `(and (<= 1 self) (<= self
/// 8))` in the module's own predicate table — beside the rendering `true`:
/// `trust-ir.Pred@1` is a schema trust-ir owns and reads, so the citation and
/// the rendering are two formulas, and a router indexing the rendering would
/// solve the wrong one. It validated exactly like its honest twin while the
/// one-formula rule covered `smtlib2` alone.
pub fn build_refuse_pred_citation_rendering_disagrees() -> Result<Module, FixtureError> {
    use trust_ir::value::{PredId, UnivId};
    let mut module = refuse_identity(
        "refuse_pred_citation_two_texts",
        Some(refuse_structural_license()),
    )?;
    module.universes = vec![trust_ir::Universe::IntRange { lo: 1, hi: 8 }];
    module.predicates = vec![trust_ir::Pred::InUniverse(
        UnivId::new(0),
        trust_ir::Space::Member,
    )];
    let mut formula = module
        .pred_table()
        .proof_formula(PredId::new(0))
        .or_fixture("pred.0 renders")?;
    formula.smtlib = Some("true".into());
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::RefinementType,
            ProofStatus::Pending,
            "cites one predicate and renders another",
        )
        .with_formula(formula),
    );
    Ok(module)
}

/// The retired-row shape `~/trust`'s Clean-origin join mints: a Rust
/// declaration shadowed by the same-named Clean definition is RENAMED out of
/// the namespace to `<name>::<shadowed-by-clean-origin:FuncId(N)>` instead of
/// being dropped, and keeps the definition's `display_path`. It validated as
/// an ordinary `External` declaration of a symbol no object defines, so a
/// consumer linking it emitted an undefined reference; `validate_module` now
/// refuses the synthetic name (WS4.17, DG-54).
pub fn build_refuse_function_symbol_synthetic_shadowed() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new_with_target_info("refuse_synthetic_symbol", refuse_target());
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut def = mb.function("m::cleanAdd", ft);
    let entry = def.create_block();
    let x = def.add_block_param(entry, Ty::I32);
    def.switch_to_block(entry);
    def.ret(vec![x]);
    def.set_producer(Producer::Clean);
    def.set_display_path("Island.cleanAdd");
    def.set_body_gate(refuse_structural_license());
    let def = def.build();
    let orphan = mb.declare_function(
        format!(
            "m::cleanAdd::<shadowed-by-clean-origin:FuncId({})>",
            def.index()
        ),
        ft,
    );
    let mut m = mb.build().or_fixture("ModuleBuilder::build")?;
    let orphan = m.function_by_id_mut(orphan).or_fixture("orphan")?;
    orphan.producer = Some(Producer::TRust);
    orphan.display_path = Some("Island.cleanAdd".into());
    Ok(m)
}

/// A well-formed `Direct`-tag enum descriptor on a target whose scalar ABI
/// trust-ir does not tabulate (i686).
pub fn build_refuse_enum_tag_lane_off_scalar_table() -> Result<Module, FixtureError> {
    use trust_ir::ty::{EnumLayoutDescriptor, EnumTagEncoding};
    let mut m = refuse_identity("refuse_enum_tag_lane", Some(refuse_structural_license()))?;
    m.target_info = Some(TargetInfo {
        triple: "i686-unknown-linux-gnu".into(),
        pointer_size: 4,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    let variant = |name: &str| EnumVariant {
        name: name.into(),
        fields: Vec::new(),
        field_names: Vec::new(),
    };
    let mut def = EnumDef::new(EnumId::new(0), "E", vec![variant("A"), variant("B")]);
    def.repr = Some(EnumTagRepr::U32);
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 4 },
        size: 8,
        align: 4,
        variant_field_offsets: vec![vec![], vec![]],
    });
    m.add_enum(def);
    Ok(m)
}

/// A table-backed nominal (`Ty::Dialect`) value created by a raw `Load`.
pub fn build_refuse_dialect_type_created_by_load() -> Result<Module, FixtureError> {
    use trust_ir::ty::DialectTy;
    let mut module = Module::new("refuse_nominal_load");
    module
        .types
        .push(Ty::Dialect(Box::new(DialectTy::new("example", "value", 1))));
    let ty = Ty::Array(TyId::new(0), 1);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let mut function = Function::new(FuncId::new(0), "load", sig, BlockId::new(0));
    function.body_gate = Some(refuse_structural_license());
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::Ptr);
    entry.body.push(
        InstrNode::new(Inst::Load {
            ty,
            ptr: ValueId::new(0),
            volatile: false,
            align: None,
        })
        .with_result(ValueId::new(1)),
    );
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    function.blocks.push(entry);
    module
        .try_add_function(function)
        .or_fixture("Module::try_add_function")?;
    Ok(module)
}

/// Exact geometry in an unused signature still cannot be carried by value.
pub fn build_refuse_storage_by_value_signature() -> Result<Module, FixtureError> {
    let mut module = refuse_identity(
        "refuse_storage_by_value_signature",
        Some(refuse_structural_license()),
    )?;
    module.target_info = Some(refuse_target());
    module
        .add_func_type(FuncTy::unrecorded(
            vec![Ty::Storage(trust_ir::StorageLayout::new(80, 8))],
            vec![],
            false,
        ))
        .or_fixture("Module::add_func_type")?;
    Ok(module)
}

/// A `Ty::Handle` naming a runtime absent from the pinned table, in the type
/// table alone.
pub fn build_refuse_handle_runtime_unpinned() -> Result<Module, FixtureError> {
    let mut m = refuse_identity("refuse_handle_unpinned", Some(refuse_structural_license()))?;
    m.target_info = Some(refuse_target());
    m.types.push(Ty::handle("Nat", "evil::Nat"));
    Ok(m)
}

/// A bodyless `ExternalWeak` hook called DIRECTLY (its address is nullable).
pub fn build_refuse_extern_weak_direct_call() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new_with_target_info("refuse_weak_direct_call", refuse_target());
    let hook_ty = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let hook = mb.declare_function("optional_hook", hook_ty);
    let mut f = mb.function("use_hook", hook_ty);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let r = f.call(hook, vec![x]);
    f.ret(vec![r]);
    f.set_body_gate(refuse_structural_license());
    f.build();
    let mut m = mb.build().or_fixture("ModuleBuilder::build")?;
    m.function_by_id_mut(hook).or_fixture("hook")?.linkage = Linkage::ExternalWeak;
    Ok(m)
}

/// The same hook spelled as a `Constant::FnDef` (a non-null function item).
pub fn build_refuse_extern_weak_as_fn_def() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new_with_target_info("refuse_weak_fn_def", refuse_target());
    let hook_ty = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let hook = mb.declare_function("optional_hook", hook_ty);
    let mut f = mb.function("use_hook", hook_ty);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let callee = f.const_value(Ty::Func(hook_ty), Constant::FnDef(hook));
    let r = f.call_indirect(callee, hook_ty, vec![x]);
    f.ret(vec![r]);
    f.set_body_gate(refuse_structural_license());
    f.build();
    let mut m = mb.build().or_fixture("ModuleBuilder::build")?;
    m.function_by_id_mut(hook).or_fixture("hook")?.linkage = Linkage::ExternalWeak;
    Ok(m)
}

/// A `Certified` row whose `CleanCic` certificate has an EMPTY term: the
/// lineage digest matches, there is nothing for a kernel to check.
pub fn build_refuse_certified_with_empty_kernel_term() -> Result<Module, FixtureError> {
    let mut m = refuse_identity(
        "refuse_certified_empty_term",
        Some(refuse_structural_license()),
    )?;
    let oblig = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "claims a kernel-checked proof",
    )
    .with_formula(ProofFormula::new("trust-types.Formula@1", "x > 0"));
    let lineage = trust_ir::proof::clean_cic_lineage_digest(&oblig);
    m.proof_obligations.push(oblig);
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "forger".into(),
        evidence: ProofEvidence::CleanCic {
            term: vec![],
            context: vec![],
            lineage,
            kernel_recheck: None,
        },
        assurance: None,
    });
    Ok(m)
}

/// `fn count(n: u32) -> u32` with one loop, carrying a `SourceProvenance`
/// whose semantic-body digest is NOT the body's (the carrier was minted for
/// another body).
pub fn build_refuse_source_provenance_stale_body_digest() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new("refuse_source_provenance");
    let ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let mut fb = mb.function("count", ft);
    let entry = fb.create_block();
    let header = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    let n = fb.add_block_param(entry, Ty::U32);
    let i = fb.add_block_param(header, Ty::U32);
    fb.switch_to_block(entry);
    let zero = fb.uconst(Ty::U32, 0);
    fb.br(header, vec![zero]);
    fb.switch_to_block(header);
    let more = fb.icmp(ICmpOp::Ult, Ty::U32, i, n);
    fb.condbr(more, body, vec![], exit, vec![]);
    fb.switch_to_block(body);
    let one = fb.uconst(Ty::U32, 1);
    let next = fb.add(Ty::U32, i, one);
    fb.br(header, vec![next]);
    fb.switch_to_block(exit);
    fb.ret(vec![i]);
    fb.set_body_gate(refuse_structural_license());
    let f = fb.build();
    let mut m = mb.build().or_fixture("ModuleBuilder::build")?;
    let stale =
        trust_ir::proof::ProofDigest::sha256_domain("trust_ir.test.refuse", b"another body");
    let source = trust_ir::proof::ProofDigest::sha256_domain("trust_ir.test.refuse", b"compiler");
    m.function_by_id_mut(f)
        .or_fixture("count")?
        .source_provenance = Some(trust_ir::SourceProvenance::new(
        source,
        stale,
        vec![trust_ir::SourceLoopProvenance {
            source_loop_id: 0,
            hir_local_id: 1,
            header,
            bindings: vec![],
        }],
    ));
    Ok(m)
}

/// Two `EnumDef`s with the same id.
pub fn build_refuse_duplicate_enum_id() -> Result<Module, FixtureError> {
    let mut m = refuse_identity(
        "refuse_duplicate_enum_id",
        Some(refuse_structural_license()),
    )?;
    let variant = |name: &str| EnumVariant {
        name: name.into(),
        fields: Vec::new(),
        field_names: Vec::new(),
    };
    m.enums
        .push(EnumDef::new(EnumId::new(0), "A", vec![variant("X")]));
    m.enums
        .push(EnumDef::new(EnumId::new(0), "B", vec![variant("Y")]));
    Ok(m)
}

/// A function whose `ty` names a func-type index the table does not have.
pub fn build_refuse_func_type_out_of_range() -> Result<Module, FixtureError> {
    let mut m = refuse_identity(
        "refuse_func_type_out_of_range",
        Some(refuse_structural_license()),
    )?;
    m.functions
        .first_mut()
        .or_fixture("the identity function")?
        .ty = trust_ir::value::FuncTyId::new(7);
    Ok(m)
}

/// `PtrData` over an `i32`: a pointer op on a type that is not pointer-like.
pub fn build_refuse_ptr_data_of_non_pointer() -> Result<Module, FixtureError> {
    let mut m = Module::new("refuse_ptr_data_non_pointer");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let mut f = Function::new(FuncId::new(0), "data", ft, BlockId::new(0));
    f.body_gate = Some(refuse_structural_license());
    let mut b = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::I32);
    b.body.push(
        InstrNode::new(Inst::PtrData {
            ptr_ty: Ty::I32,
            ptr: ValueId::new(0),
        })
        .with_result(ValueId::new(1)),
    );
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    f.blocks.push(b);
    m.try_add_function(f)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

/// A typed effect summary (v59, WS1.14) that does not cover its body:
/// `fn set(p: *mut u64, q: *mut u64) { *q = 7 }` claims `writes: [*param0]`.
/// A caller that trusted the frame would keep a fact about `*q` across the
/// call that the call destroys.
pub fn build_refuse_effect_summary_uncovered_write() -> Result<Module, FixtureError> {
    let ptr = || Ty::PtrMut(Box::new(Ty::U64));
    let mut m = Module::new("refuse_effect_summary_uncovered_write");
    m.target_info = Some(refuse_target());
    let ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![ptr(), ptr()],
            returns: vec![],
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let mut f = Function::new(FuncId::new(0), "set", ft, BlockId::new(0));
    f.body_gate = Some(refuse_structural_license());
    let mut b = Block::new(BlockId::new(0))
        .with_param(ValueId::new(0), ptr())
        .with_param(ValueId::new(1), ptr());
    b.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(2)),
    );
    b.body.push(InstrNode::new(Inst::Store {
        ty: Ty::U64,
        ptr: ValueId::new(1),
        value: ValueId::new(2),
        volatile: false,
        align: None,
    }));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    f.summary = Some(trust_ir::FunctionSummary::new().with_effects(
        trust_ir::EffectSummary::pure().writing(trust_ir::EffectSet::of([
            trust_ir::EffectPlace::ParamPointee { index: 0 },
        ])),
    ));
    m.try_add_function(f)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

/// A `Trusted` obligation with the justification the structural pass
/// requires: well-formed, and faith-stamped.
pub fn build_refuse_trusted_status_row() -> Result<Module, FixtureError> {
    let mut m = refuse_identity("refuse_trusted_status", Some(refuse_structural_license()))?;
    let f = m.functions.first().or_fixture("the identity function")?.id;
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Trusted,
            "accepted on faith",
        )
        .with_function(f)
        .with_formula(ProofFormula::smtlib2("(= result result)", "Bool")),
    );
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "auditor".into(),
        evidence: ProofEvidence::Trusted("hand-audited by a reviewer".into()),
        assurance: None,
    });
    Ok(m)
}

// ----- consumer-relative: well-formed here, refused by a native backend -----

/// `TargetInfo.struct_passing = Unclassified` beside a by-value struct
/// argument: a backend that passes aggregates needs a classification.
pub fn build_refuse_struct_passing_unclassified_by_value_aggregate() -> Result<Module, FixtureError>
{
    let mut mb = ModuleBuilder::new_with_target_info(
        "refuse_struct_passing_unclassified",
        TargetInfo {
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
            ..refuse_target()
        },
    );
    let point = mb.add_struct(StructDef {
        id: StructId::new(0),
        name: "Point".into(),
        fields: vec![
            FieldDef {
                name: "a".into(),
                ty: Ty::I32,
                offset: Some(0),
            },
            FieldDef {
                name: "b".into(),
                ty: Ty::F64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    });
    let point_ty = Ty::Struct(point);
    let take_ty = mb.add_func_type(vec![point_ty.clone()], vec![Ty::I32]);
    let mut take = mb.function("take", take_ty);
    let entry = take.create_block();
    let p = take.add_block_param(entry, point_ty.clone());
    take.switch_to_block(entry);
    let a = take.extract_field(Ty::I32, p, 0);
    take.ret(vec![a]);
    take.set_body_gate(refuse_structural_license());
    let take = take.build();
    let caller_ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);
    let mut caller = mb.function("caller", caller_ty);
    let entry = caller.create_block();
    let ptr = caller.add_block_param(entry, Ty::Ptr);
    caller.switch_to_block(entry);
    let p = caller.load(point_ty, ptr);
    let r = caller.call(take, vec![p]);
    caller.ret(vec![r]);
    caller.set_body_gate(refuse_structural_license());
    caller.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// `struct Point { a: i32, b: f64 }` (16 bytes, align 8): the by-value
/// aggregate the struct-passing rows share.
fn refuse_point(mb: &mut ModuleBuilder) -> Ty {
    Ty::Struct(mb.add_struct(StructDef {
        id: StructId::new(0),
        name: "Point".into(),
        fields: vec![
            FieldDef {
                name: "a".into(),
                ty: Ty::I32,
                offset: Some(0),
            },
            FieldDef {
                name: "b".into(),
                ty: Ty::F64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    }))
}

/// `fn take(x: <slot>) -> <ret> { <zero> }` plus `fn caller(<carrier>) ->
/// <ret> { take(<arg>) }`, both under the structural license, where the caller
/// obtains the argument by loading it through a pointer (`carrier = Ptr`) or
/// by forwarding its own parameter (`carrier = slot`).
fn refuse_take_and_caller(mb: &mut ModuleBuilder, slot: Ty, ret: Ty, load_through_ptr: bool) {
    let take_ty = mb.add_func_type(vec![slot.clone()], vec![ret.clone()]);
    let mut take = mb.function("take", take_ty);
    let entry = take.create_block();
    take.add_block_param(entry, slot.clone());
    take.switch_to_block(entry);
    let zero = take.iconst(ret.clone(), 0);
    take.ret(vec![zero]);
    take.set_body_gate(refuse_structural_license());
    let take = take.build();
    let carrier = if load_through_ptr {
        Ty::Ptr
    } else {
        slot.clone()
    };
    let caller_ty = mb.add_func_type(vec![carrier.clone()], vec![ret]);
    let mut caller = mb.function("caller", caller_ty);
    let entry = caller.create_block();
    let param = caller.add_block_param(entry, carrier);
    caller.switch_to_block(entry);
    let arg = if load_through_ptr {
        caller.load(slot, param)
    } else {
        param
    };
    let r = caller.call(take, vec![arg]);
    caller.ret(vec![r]);
    caller.set_body_gate(refuse_structural_license());
    caller.build();
}

/// `StructPassingPolicy::AlwaysMemory` beside a by-value struct parameter:
/// `AlwaysMemory` says every aggregate crossing is pre-lowered (`byval` /
/// `sret` pointers), so `validate_module` refuses the by-value slot
/// (`AlwaysMemoryByValueAggregate`, `docs/SPEC_RATIFICATIONS.md` §17).
pub fn build_refuse_struct_passing_always_memory_by_value_aggregate() -> Result<Module, FixtureError>
{
    let mut mb = ModuleBuilder::new_with_target_info(
        "refuse_struct_passing_always_memory",
        TargetInfo {
            struct_passing: trust_ir::StructPassingPolicy::AlwaysMemory,
            ..refuse_target()
        },
    );
    let point = refuse_point(&mut mb);
    refuse_take_and_caller(&mut mb, point, Ty::I32, true);
    mb.build().or_fixture("ModuleBuilder::build")
}

/// `NativeC` on aarch64-apple-darwin with `pass = indirect { on_stack: false }`
/// RECORDED on a C-convention `struct { u64, u64 }` parameter, which AAPCS64
/// passes in two general registers (x0/x1; clang lowers it as `[2 x i64]`).
/// The recorded fact is a second statement of the placement the consumer
/// computes, and here the two disagree: a consumer must refuse rather than
/// prefer either statement.
pub fn build_refuse_struct_passing_native_c_pass_mode_contradicts_target()
-> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new_with_target_info(
        "refuse_struct_passing_native_c_pass_mode",
        refuse_target(),
    );
    let pair = Ty::Struct(mb.add_struct(StructDef {
        id: StructId::new(0),
        name: "TwoWords".into(),
        fields: vec![
            FieldDef {
                name: "a".into(),
                ty: Ty::U64,
                offset: Some(0),
            },
            FieldDef {
                name: "b".into(),
                ty: Ty::U64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: trust_ir::ty::StructRepr::C,
        origin: None,
    }));
    refuse_take_and_caller(&mut mb, pair, Ty::U64, true);
    let mut m = mb.build().or_fixture("ModuleBuilder::build")?;
    for func in &mut m.functions {
        func.calling_conv = trust_ir::CallingConv::C;
    }
    let take = m
        .functions
        .iter_mut()
        .find(|f| f.name == "take")
        .or_fixture("take")?;
    take.attrs.params = vec![trust_ir::ParamAttrs {
        pass: Some(trust_ir::PassMode::Indirect { on_stack: false }),
        ..Default::default()
    }];
    Ok(m)
}

/// `Unclassified` beside a by-value `Refine(Point, Top)` parameter: a
/// refinement has its base's representation, so the slot is a by-value
/// aggregate and a backend needing a classification must refuse it.
pub fn build_refuse_struct_passing_unclassified_refined_aggregate() -> Result<Module, FixtureError>
{
    let mut mb = ModuleBuilder::new_with_target_info(
        "refuse_struct_passing_unclassified_refined",
        TargetInfo {
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
            ..refuse_target()
        },
    );
    let point = refuse_point(&mut mb);
    let top = mb
        .intern_pred(trust_ir::Pred::Top)
        .or_fixture("Top is canonical")?;
    let refined = mb.refine_ty(point, top);
    refuse_take_and_caller(&mut mb, refined, Ty::I32, true);
    mb.build().or_fixture("ModuleBuilder::build")
}

/// `Unclassified` beside a by-value `Vector(I32, 4)` parameter. rustc's Rust
/// ABI passes `int32x4_t` indirectly while `extern "C"` passes it in a vector
/// register (measured on aarch64-apple-darwin), so a producer that classified
/// nothing established neither.
pub fn build_refuse_struct_passing_unclassified_vector_by_value() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new_with_target_info(
        "refuse_struct_passing_unclassified_vector",
        TargetInfo {
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
            ..refuse_target()
        },
    );
    refuse_take_and_caller(&mut mb, Ty::Vector(Box::new(Ty::I32), 4), Ty::I32, true);
    mb.build().or_fixture("ModuleBuilder::build")
}

/// `Unclassified` beside a by-value closure with three `i64` captures
/// (apparent signature `fn(i64) -> i64`): a closure value carries its
/// captures by value, so the slot is a by-value aggregate.
pub fn build_refuse_struct_passing_unclassified_closure_by_value() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new_with_target_info(
        "refuse_struct_passing_unclassified_closure",
        TargetInfo {
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
            ..refuse_target()
        },
    );
    let apparent = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let closure = Ty::Closure(mb.add_closure_type(trust_ir::ClosureTy {
        func: apparent,
        captures: vec![Ty::I64, Ty::I64, Ty::I64],
    }));
    refuse_take_and_caller(&mut mb, closure, Ty::I64, false);
    mb.build().or_fixture("ModuleBuilder::build")
}

/// An FFI declaration `extern "C" fn narrow(i8, u16) -> i32` on
/// aarch64-apple-darwin with a `ParamAttrs` slot RECORDED for each parameter
/// and `ext = None` (`pass = None`) on both, and a caller. The slots are
/// recorded so the row is "`None` on both slots", not "no ABI facts at all":
/// the trigger in `refuse_corpus.rs` requires one slot per parameter. The
/// final empty `#param_attrs N:` text row preserves the complete recorded
/// table as the binary does. This is lossless transport, not ABI authority:
/// the DarwinPCS consumer still refuses each unrecorded extension.
pub fn build_refuse_narrow_arg_ext_unrecorded_darwin() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new_with_target_info("refuse_narrow_ext", refuse_target());
    let narrow_ty = mb.add_func_type(vec![Ty::I8, Ty::U16], vec![Ty::I32]);
    let narrow = mb.declare_function("narrow", narrow_ty);
    let caller_ty = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut caller = mb.function("caller", caller_ty);
    let entry = caller.create_block();
    caller.switch_to_block(entry);
    let a = caller.iconst(Ty::I8, -1);
    let b = caller.uconst(Ty::U16, 65535);
    let r = caller.call(narrow, vec![a, b]);
    caller.ret(vec![r]);
    caller.set_body_gate(refuse_structural_license());
    caller.build();
    let mut m = mb.build().or_fixture("ModuleBuilder::build")?;
    let decl = m.function_by_id_mut(narrow).or_fixture("narrow")?;
    decl.calling_conv = trust_ir::CallingConv::C;
    decl.attrs.params = vec![trust_ir::ParamAttrs::default(); 2];
    Ok(m)
}

/// A DEFINED `extern "C-unwind"` function whose body `Invoke`s a declaration
/// through a cleanup landing pad.
pub fn build_refuse_calling_conv_c_unwind_definition() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new_with_target_info("refuse_c_unwind", refuse_target());
    let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let callee = mb.declare_function("may_throw", ft);
    let mut f = mb.function("unwinding_entry", ft);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let normal = f.create_block();
    let unwind = f.create_block();
    let r = f.invoke(callee, vec![x], normal, vec![], unwind);
    f.switch_to_block(normal);
    f.ret(vec![r]);
    f.switch_to_block(unwind);
    let (exception, _) = f.landingpad(true, vec![]);
    f.resume(exception);
    f.set_calling_conv(trust_ir::CallingConv::CUnwind);
    f.set_body_gate(refuse_structural_license());
    f.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// `target_features = ["avx512f"]` on an aarch64 target.
pub fn build_refuse_target_feature_unknown() -> Result<Module, FixtureError> {
    let mut m = refuse_identity("refuse_target_feature", Some(refuse_structural_license()))?;
    m.target_info = Some(refuse_target());
    m.functions[0].attrs.target_features = vec!["avx512f".into()];
    Ok(m)
}

/// A non-volatile `Store` carrying `RegionHavocStore` (its legal placement).
pub fn build_refuse_region_havoc_store() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new("refuse_region_havoc");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("pick", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let cell = fb.alloca(Ty::U64);
    let five = fb.uconst(Ty::U64, 5);
    fb.store_proven(Ty::U64, cell, five, vec![ProofAnnotation::RegionHavocStore]);
    let v = fb.load(Ty::U64, cell);
    fb.ret(vec![v]);
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// An `Undef` marked `FreshSymbolicHavoc` whose value is NARROWED by an
/// `Assume` before it is returned.
pub fn build_refuse_undef_fresh_havoc_feeds_assume() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new("refuse_undef_assume");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("fresh", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let v = fb.undef_proven(Ty::U64, vec![ProofAnnotation::FreshSymbolicHavoc]);
    let limit = fb.uconst(Ty::U64, 10);
    let small = fb.icmp(ICmpOp::Ult, Ty::U64, v, limit);
    fb.assume(small);
    fb.ret(vec![v]);
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// `ArraySplat` at `i32`: the register uniform array spelled at a type that
/// is not an array. `[v; n]` takes its length from `Array(e, n)`, so there is
/// no `n` to copy `v` into; the validator refuses the shape by name.
pub fn build_refuse_array_splat_non_array_type() -> Result<Module, FixtureError> {
    let mut m = Module::new("refuse_array_splat_non_array");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let mut f = Function::new(FuncId::new(0), "splat", ft, BlockId::new(0));
    f.body_gate = Some(refuse_structural_license());
    let mut b = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::I32);
    b.body.push(
        InstrNode::new(Inst::ArraySplat {
            ty: Ty::I32,
            value: ValueId::new(0),
        })
        .with_result(ValueId::new(1)),
    );
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    f.blocks.push(b);
    m.try_add_function(f)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

/// `const [i32 x 3] array[ 7, 7, 7 ]`: a uniform array spelled as the list.
/// Its one spelling is `splat[ 7; 3 ]` (SPEC_RATIFICATIONS §3.1), so the list
/// is refused as non-canonical, never accepted beside the splat it equals.
pub fn build_refuse_uniform_array_spelled_as_list() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new("refuse_uniform_array_list");
    let i32_id = mb.add_type(Ty::I32);
    let array = Ty::Array(i32_id, 3);
    let ft = mb.add_func_type(vec![], vec![array.clone()]);
    let mut fb = mb.function("sevens", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let sevens = fb.const_value(array, Constant::Array(vec![Constant::Int(7); 3]));
    fb.ret(vec![sevens]);
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// One function, `f(x: selector) = switch x [ case: 1, default: 0 ]`, licensed.
fn refuse_switch_case_module(
    module: &str,
    selector: Ty,
    case: i128,
) -> Result<Module, FixtureError> {
    refuse_switch_case_module_in(ModuleBuilder::new(module), selector, case)
}

/// [`refuse_switch_case_module`] in a builder that already holds what the
/// selector type names (a refinement's predicate).
fn refuse_switch_case_module_in(
    mut mb: ModuleBuilder,
    selector: Ty,
    case: i128,
) -> Result<Module, FixtureError> {
    let ft = mb.add_func_type(vec![selector.clone()], vec![Ty::I32]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let hit = fb.create_block();
    let miss = fb.create_block();
    let x = fb.add_block_param(entry, selector);
    fb.switch_to_block(entry);
    fb.switch(
        x,
        vec![SwitchCase {
            value: Constant::Int(case),
            target: hit,
            args: vec![],
        }],
        miss,
        vec![],
    );
    for (block, value) in [(hit, 1), (miss, 0)] {
        fb.switch_to_block(block);
        let r = fb.iconst(Ty::I32, value);
        fb.ret(vec![r]);
    }
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// `not bool %b`: scalar Bool negation spelled with the BITWISE `not`
/// (WS2.21, F-033). Its one spelling is the Bool connective `bxor %b, true`
/// (SPEC_RATIFICATIONS §3.2), so the validator refuses `not` at scalar `Bool`
/// by name (`UnOpNotOnScalarBool`), never as the generic integer refusal.
pub fn build_refuse_unop_not_scalar_bool() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new("refuse_unop_not_scalar_bool");
    let sig = mb.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
    let mut fb = mb.function("neg", sig);
    let entry = fb.create_block();
    let b = fb.add_block_param(entry, Ty::Bool);
    fb.switch_to_block(entry);
    let negated = fb.unop(trust_ir::inst::UnOp::Not, Ty::Bool, b);
    fb.ret(vec![negated]);
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// `switch u8 %x [ -1: .. ]`. A switch case at an integer selector is a
/// constant OF THE SELECTOR'S TYPE (SPEC_RATIFICATIONS §3.3), so the case is
/// refused exactly as its `Inst::Const` twin `const u8 -1` is, never wrapped
/// into `255`, that value's one spelling. One spelling per row: a consumer
/// runner is reason-blind, so a row holding both spellings would let a
/// missing refusal of one hide behind the refusal of the other.
pub fn build_refuse_switch_case_negative_at_unsigned() -> Result<Module, FixtureError> {
    refuse_switch_case_module("refuse_switch_case_negative_at_unsigned", Ty::U8, -1)
}

/// `switch i8 %x [ 255: .. ]`: refused exactly as `const i8 255` is, never
/// wrapped into `-1` (the twin row of
/// [`build_refuse_switch_case_negative_at_unsigned`]).
pub fn build_refuse_switch_case_above_signed_max() -> Result<Module, FixtureError> {
    refuse_switch_case_module("refuse_switch_case_above_signed_max", Ty::I8, 255)
}

/// `switch refine<u8, [0, 10]> %x [ -1: .. ]`. A refinement selector has
/// exactly its base's representation, so its case is a constant of the BASE
/// (SPEC_RATIFICATIONS §3.3), refused exactly as `const u8 -1` is — never
/// wrapped into `255`, and never admitted because the refinement is not an
/// integer type. Its own row: a consumer that types a case only at a plain
/// integer selector refuses `switch_case_negative_at_unsigned` and admits
/// this one.
pub fn build_refuse_switch_case_negative_at_refined_unsigned() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new("refuse_switch_case_negative_at_refined_unsigned");
    let pred = mb
        .intern_pred(trust_ir::Pred::Interval { lo: 0, hi: 10 })
        .or_fixture("a well-formed interval predicate")?;
    let selector = mb.refine_ty(Ty::U8, pred);
    refuse_switch_case_module_in(mb, selector, -1)
}

/// The 32-bit target the pointer-width rows are measured on: wasm32, the one
/// 32-bit target with a canonical scalar table
/// (`Module::target_has_canonical_scalar_layout`). Every other refuse row uses
/// the 64-bit canonical target, where `isize` / `usize` are 64 bits and none
/// of these spellings exists.
fn refuse_wasm32_target() -> TargetInfo {
    TargetInfo {
        triple: "wasm32-unknown-unknown".into(),
        pointer_size: 4,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

/// `switch usize %x [ 2^32: .. ]` on wasm32. A pointer-width case is a
/// constant of its selector's type ON THE MODULE'S TARGET
/// (SPEC_RATIFICATIONS §3.3): `usize` is 32 bits there, so `2^32` is no
/// `usize` value — it is the 64-bit spelling of `0`, which the interpreter
/// wraps to `0` — and it is refused exactly as `const usize 2^32` is on the
/// same target.
pub fn build_refuse_switch_case_usize_beyond_target_width() -> Result<Module, FixtureError> {
    let mut m = refuse_switch_case_module(
        "refuse_switch_case_usize_beyond_target_width",
        Ty::Usize,
        1 << 32,
    )?;
    m.target_info = Some(refuse_wasm32_target());
    Ok(m)
}

/// `switch isize %x [ 2^31: .. ]` on wasm32: `2^31` is above the 32-bit
/// `isize` maximum (it is the unsigned spelling of `-2^31`), refused exactly
/// as `const isize 2^31` is there (the twin row of
/// [`build_refuse_switch_case_usize_beyond_target_width`]).
pub fn build_refuse_switch_case_isize_beyond_target_width() -> Result<Module, FixtureError> {
    let mut m = refuse_switch_case_module(
        "refuse_switch_case_isize_beyond_target_width",
        Ty::Isize,
        1 << 31,
    )?;
    m.target_info = Some(refuse_wasm32_target());
    Ok(m)
}

/// `const usize 2^32` on wasm32: the constant funnel's own spelling, where
/// the alias began. Every `isize` / `usize` constant is checked at the
/// target's pointer width (`Constant::value_matches_ty` at
/// `Module::pointer_bits`), not at 64 bits.
pub fn build_refuse_const_usize_beyond_target_width() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new("refuse_const_usize_beyond_target_width");
    let ft = mb.add_func_type(vec![], vec![Ty::Usize]);
    let mut fb = mb.function("len", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let len = fb.const_value(Ty::Usize, Constant::Int(1 << 32));
    fb.ret(vec![len]);
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    let mut m = mb.build().or_fixture("ModuleBuilder::build")?;
    m.target_info = Some(refuse_wasm32_target());
    Ok(m)
}

/// One nominal `TypeOrigin` key stamped on TWO definitions of one module: a
/// key names one source entity, which has one image per module, so a
/// consumer resolving the key has nothing to choose by. Refused whatever the
/// two shapes are; here they differ (`{ u32, u32 }` against `{ u64 }`, both
/// 8 bytes), so no structural merge could explain the pair away. Positional
/// fields with no offsets keep the row loss-free in the text format. The two
/// definitions are pushed directly: `Module::add_struct` interns by content.
pub fn build_refuse_type_origin_claimed_twice() -> Result<Module, FixtureError> {
    let mut m = refuse_identity(
        "refuse_type_origin_claimed_twice",
        Some(refuse_structural_license()),
    )?;
    m.target_info = Some(refuse_target());
    let key = TypeOrigin::Rust {
        stable_crate_id: 0x0123_4567_89ab_cdef,
        def_path_hash: [
            0x10, 0x21, 0x32, 0x43, 0x54, 0x65, 0x76, 0x87, 0x98, 0xa9, 0xba, 0xcb, 0xdc, 0xed,
            0xfe, 0x0f,
        ],
        args_digest: ProofDigest::sha256([0x71; 32]),
    };
    let positional = |ty: Ty| FieldDef {
        name: String::new(),
        ty,
        offset: None,
    };
    m.structs.push(
        StructDef {
            id: StructId::new(0),
            name: "Span".into(),
            fields: vec![positional(Ty::U32), positional(Ty::U32)],
            size: Some(8),
            align: Some(4),
            repr: Default::default(),
            origin: None,
        }
        .with_origin(key.clone()),
    );
    m.structs.push(
        StructDef {
            id: StructId::new(1),
            name: "SpanWide".into(),
            fields: vec![positional(Ty::U64)],
            size: Some(8),
            align: Some(8),
            repr: Default::default(),
            origin: None,
        }
        .with_origin(key),
    );
    Ok(m)
}

// ----- poisoned wire: what the binary reader refuses -------------------------

/// The base blob every byte row mutates: a licensed identity, serialized.
fn refuse_bytes_base() -> Result<Vec<u8>, FixtureError> {
    trust_ir::binary::serialize_module(&refuse_identity(
        "refuse_bytes_base",
        Some(refuse_structural_license()),
    )?)
    .or_fixture("serialize_module")
}

/// Bytes `0..8` are the magic, `8..12` the little-endian header version; the
/// string pool's count starts at byte 12.
const HEADER_VERSION: std::ops::Range<usize> = 8..12;
const POOL_COUNT_AT: usize = 12;

/// The header's version word.
fn header_version(bytes: &[u8]) -> Result<u32, FixtureError> {
    let word: [u8; 4] = bytes
        .get(HEADER_VERSION)
        .or_fixture("the blob holds a header version")?
        .try_into()
        .or_fixture("the header version is four bytes")?;
    Ok(u32::from_le_bytes(word))
}

/// Overwrite the header's version word.
fn set_header_version(bytes: &mut [u8], version: u32) -> Result<(), FixtureError> {
    bytes
        .get_mut(HEADER_VERSION)
        .or_fixture("the blob holds a header version")?
        .copy_from_slice(&version.to_le_bytes());
    Ok(())
}

/// Read one varint at `at` by the codec's rule; returns (value, width).
fn refuse_read_varint(bytes: &[u8], at: usize) -> Result<(u64, usize), FixtureError> {
    let tail = bytes
        .get(at..)
        .or_fixture("a varint offset inside the blob")?;
    trust_ir::binary::decode_varint(tail).or_fixture("a canonical varint")
}

/// `at + width`, refused rather than wrapped.
fn refuse_offset(at: usize, width: usize) -> Result<usize, FixtureError> {
    at.checked_add(width)
        .or_fixture("an offset inside the blob")
}

/// Byte offset just past the string pool (header + pool count + strings), and
/// the pool's string count.
fn refuse_pool_end(bytes: &[u8]) -> Result<(usize, u64), FixtureError> {
    let (count, width) = refuse_read_varint(bytes, POOL_COUNT_AT)?;
    let mut at = refuse_offset(POOL_COUNT_AT, width)?;
    for _ in 0..count {
        let (len, width) = refuse_read_varint(bytes, at)?;
        let len = usize::try_from(len).or_fixture("a pool string length")?;
        at = refuse_offset(refuse_offset(at, width)?, len)?;
    }
    Ok((at, count))
}

/// `base` with the varint at `at` replaced by `replacement` bytes.
fn refuse_splice_varint(
    base: &[u8],
    at: usize,
    replacement: &[u8],
) -> Result<Vec<u8>, FixtureError> {
    let (_, width) = refuse_read_varint(base, at)?;
    let mut bytes = base
        .get(..at)
        .or_fixture("the prefix before the varint")?
        .to_vec();
    bytes.extend_from_slice(replacement);
    bytes.extend_from_slice(
        base.get(refuse_offset(at, width)?..)
            .or_fixture("the suffix after the varint")?,
    );
    Ok(bytes)
}

/// The genuine direct boundary tag under a header that has not allocated it.
pub fn build_refuse_bytes_blob_call_boundary_below_its_version() -> Result<Vec<u8>, FixtureError> {
    let module = crate::fixtures::build_call_unwind_boundary()?;
    let mut bytes = trust_ir::binary::serialize_module(&module).or_fixture("serialize_module")?;
    set_header_version(
        &mut bytes,
        trust_ir::binary::CALL_UNWIND_BOUNDARY_FORMAT_VERSION - 1,
    )?;
    Ok(bytes)
}

/// Roadmap DG-63: the `param_pointee_place` golden under the header one
/// version below the place's, which allocates no clause-place tag 10.
pub fn build_refuse_bytes_blob_param_pointee_place_below_its_version()
-> Result<Vec<u8>, FixtureError> {
    let module = crate::fixtures::build_param_pointee_place()?;
    let mut bytes = trust_ir::binary::serialize_module(&module).or_fixture("serialize_module")?;
    set_header_version(
        &mut bytes,
        trust_ir::binary::PARAM_POINTEE_PLACE_FORMAT_VERSION - 1,
    )?;
    Ok(bytes)
}

/// Every direct `CallCannotUnwind` of `body` demoted to a plain `Call`.
fn demote_cannot_unwind_calls(body: &mut [InstrNode]) {
    for node in body {
        if let Inst::CallCannotUnwind { callee, args } = &node.inst {
            node.inst = Inst::Call {
                callee: *callee,
                args: args.clone(),
            };
        }
    }
}

pub fn build_refuse_bytes_blob_indirect_call_boundary_below_its_version()
-> Result<Vec<u8>, FixtureError> {
    let mut module = crate::fixtures::build_call_unwind_boundary()?;
    let caller = module
        .functions
        .get_mut(1)
        .or_fixture("the boundary fixture's caller")?;
    let entry = caller
        .blocks
        .get_mut(0)
        .or_fixture("the boundary fixture caller's entry block")?;
    demote_cannot_unwind_calls(&mut entry.body);
    let mut bytes = trust_ir::binary::serialize_module(&module).or_fixture("serialize_module")?;
    set_header_version(
        &mut bytes,
        trust_ir::binary::CALL_UNWIND_BOUNDARY_FORMAT_VERSION - 1,
    )?;
    Ok(bytes)
}

/// Header version 27: the ambiguous-lineage range, refused forever.
pub fn build_refuse_bytes_blob_ambiguous_lineage_header() -> Result<Vec<u8>, FixtureError> {
    let mut bytes = refuse_bytes_base()?;
    set_header_version(&mut bytes, 27)?;
    Ok(bytes)
}

/// The magic's first byte flipped.
pub fn build_refuse_bytes_blob_bad_magic() -> Result<Vec<u8>, FixtureError> {
    let mut bytes = refuse_bytes_base()?;
    *bytes.first_mut().or_fixture("the blob holds a magic")? ^= 0x01;
    Ok(bytes)
}

/// The blob cut inside its header (the magic and half the version word):
/// the reader runs out of input before it can read a count. (A cut inside
/// the payload trips the declared-count check first, `TooLarge`; a cut this
/// early is the one the reader reports as end of data.)
pub fn build_refuse_bytes_blob_truncated() -> Result<Vec<u8>, FixtureError> {
    let mut bytes = refuse_bytes_base()?;
    bytes.truncate(10);
    Ok(bytes)
}

/// One byte appended after the canonical payload.
pub fn build_refuse_bytes_blob_trailing_bytes() -> Result<Vec<u8>, FixtureError> {
    let mut bytes = refuse_bytes_base()?;
    bytes.push(0x00);
    Ok(bytes)
}

/// A level-S template blob (magic `TRUST_IS`, amendment S) handed to the
/// module reader: a template is never a module.
pub fn build_refuse_bytes_template_blob_is_not_a_module() -> Result<Vec<u8>, FixtureError> {
    trust_ir::binary::serialize_template(
        &crate::template_fixtures::ident_param().or_fixture("the ident_param golden template")?,
    )
    .or_fixture("the ident_param golden template encodes")
}

/// The first byte at which two blobs differ: the tag byte of the one row two
/// otherwise identical modules spell differently.
fn refuse_first_difference(a: &[u8], b: &[u8]) -> Result<usize, FixtureError> {
    a.iter()
        .zip(b)
        .position(|(x, y)| x != y)
        .or_fixture("the two samples differ")
}

/// A module whose ONE type row's tag byte is `Ty` tag 39 (`TyG::Ext`, the
/// template spelling) followed by a well-formed `TemplateRef` (`Param(0)`):
/// a template payload forged under the MODULE magic. The tag is found by
/// difference (a `Unit` row against a `Bool` row), never by offset.
pub fn build_refuse_bytes_ty_ext_tag_under_module_magic() -> Result<Vec<u8>, FixtureError> {
    let type_row = |ty: Ty| -> Result<Vec<u8>, FixtureError> {
        let mut module = refuse_identity("refuse_ty_ext_tag", Some(refuse_structural_license()))?;
        module.types.push(ty);
        trust_ir::binary::serialize_module(&module).or_fixture("serialize_module")
    };
    let (unit, boolean) = (type_row(Ty::Unit)?, type_row(Ty::Bool)?);
    let at = refuse_first_difference(&unit, &boolean)?;
    let mut forged = unit;
    forged.splice(at..=at, [39u8, 0, 0]);
    Ok(forged)
}

/// A module whose one global's initializer tag is `Constant` tag 17
/// (`ConstantG::Ext`) followed by `TemplateRef::Hole(0)`, in place of a
/// `Constant::Int` (whose 16 payload bytes the splice drops, so the blob
/// stays the right length for everything after it).
pub fn build_refuse_bytes_constant_ext_tag_under_module_magic() -> Result<Vec<u8>, FixtureError> {
    let global = |value: Constant| -> Result<Vec<u8>, FixtureError> {
        let mut module =
            refuse_identity("refuse_constant_ext_tag", Some(refuse_structural_license()))?;
        module.globals.push(trust_ir::Global {
            name: "g".into(),
            ty: Ty::I64,
            mutable: false,
            initializer: Some(value),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: trust_ir::Visibility::default(),
            retained: false,
        });
        trust_ir::binary::serialize_module(&module).or_fixture("serialize_module")
    };
    let (zero, yes) = (global(Constant::Int(0))?, global(Constant::Bool(true))?);
    let at = refuse_first_difference(&zero, &yes)?;
    let end = at.checked_add(17).or_fixture("the Int payload's end")?;
    fixture_invariant(
        end <= zero.len(),
        "the Int constant's tag and payload are in the blob",
    )?;
    let mut forged = zero;
    forged.splice(at..end, [17u8, 1, 0]);
    Ok(forged)
}

/// A string-pool count larger than the whole input.
pub fn build_refuse_bytes_blob_pool_count_exceeds_input() -> Result<Vec<u8>, FixtureError> {
    let base = refuse_bytes_base()?;
    refuse_splice_varint(
        &base,
        POOL_COUNT_AT,
        &trust_ir::binary::encode_varint(0x0FFF_FFFF),
    )
}

/// A varint whose continuation bits never end within the width the reader
/// admits.
pub fn build_refuse_bytes_blob_varint_overflow() -> Result<Vec<u8>, FixtureError> {
    let base = refuse_bytes_base()?;
    // Written RAW: no canonical varint spells this, which is the point.
    refuse_splice_varint(&base, POOL_COUNT_AT, &[0xFF; 11])
}

/// The module-name string id points past the pool.
pub fn build_refuse_bytes_blob_string_id_out_of_pool() -> Result<Vec<u8>, FixtureError> {
    let base = refuse_bytes_base()?;
    let (name_at, count) = refuse_pool_end(&base)?;
    let past_pool = count
        .checked_add(7)
        .or_fixture("a string id past the pool")?;
    refuse_splice_varint(&base, name_at, &trust_ir::binary::encode_varint(past_pool))
}

/// The first pool string's first byte is not UTF-8.
pub fn build_refuse_bytes_blob_pool_string_not_utf8() -> Result<Vec<u8>, FixtureError> {
    let mut bytes = refuse_bytes_base()?;
    let (count, width) = refuse_read_varint(&bytes, POOL_COUNT_AT)?;
    fixture_invariant(count > 0, "the base blob interns at least one string")?;
    let first = refuse_offset(POOL_COUNT_AT, width)?;
    let (len, len_width) = refuse_read_varint(&bytes, first)?;
    fixture_invariant(len > 0, "the first pool string is not empty")?;
    *bytes
        .get_mut(refuse_offset(first, len_width)?)
        .or_fixture("the first pool string's first byte")? = 0xFF;
    Ok(bytes)
}

/// A blob carrying a v40 fat-pointer kind (`ContainerVtable`, sub-tag 4)
/// relabelled with a v39 header: the tag is not allocated at that version.
pub fn build_refuse_bytes_blob_feature_tag_below_its_version() -> Result<Vec<u8>, FixtureError> {
    let mut mb = ModuleBuilder::new("refuse_bytes_feature_tag");
    let fat = Ty::FatPtr(FatPtrKind::ContainerVtable);
    let ft = mb.add_func_type(vec![fat.clone()], vec![fat.clone()]);
    let mut fb = mb.function("id", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, fat);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    fb.build();
    let mut bytes =
        trust_ir::binary::serialize_module(&mb.build().or_fixture("ModuleBuilder::build")?)
            .or_fixture("serialize_module")?;
    let version = trust_ir::binary::CONTAINER_VTABLE_FORMAT_VERSION;
    fixture_invariant(
        header_version(&bytes)? == version,
        "the writer selects the container-vtable version for this module",
    )?;
    let below = version
        .checked_sub(1)
        .or_fixture("a version below the container-vtable version")?;
    set_header_version(&mut bytes, below)?;
    Ok(bytes)
}

/// A blob carrying a v45 parameter-extension flag bit (`zeroext`) relabelled
/// with the previous header: the flag bit is not allocated at that version.
pub fn build_refuse_bytes_blob_param_flag_bit_below_its_version() -> Result<Vec<u8>, FixtureError> {
    let mut mb = ModuleBuilder::new("refuse_bytes_param_flag");
    let ft = mb.add_func_type(vec![Ty::I8], vec![Ty::I32]);
    let mut fb = mb.function("widen", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I8);
    fb.switch_to_block(entry);
    let w = fb.sext(Ty::I8, Ty::I32, x);
    fb.ret(vec![w]);
    fb.set_attrs(trust_ir::FuncAttrs {
        params: vec![ParamAttrs {
            ext: trust_ir::ArgExt::ZeroExt,
            ..ParamAttrs::default()
        }],
        ..trust_ir::FuncAttrs::default()
    });
    fb.build();
    let mut bytes =
        trust_ir::binary::serialize_module(&mb.build().or_fixture("ModuleBuilder::build")?)
            .or_fixture("serialize_module")?;
    let version = header_version(&bytes)?;
    fixture_invariant(
        version == trust_ir::binary::ABI_SURFACE_FORMAT_VERSION,
        "the writer selects the ABI-surface version for a recorded extension",
    )?;
    let below = version
        .checked_sub(1)
        .or_fixture("a version below the ABI-surface version")?;
    set_header_version(&mut bytes, below)?;
    Ok(bytes)
}

/// A declared tuple layout whose field offsets OVERLAP, serialized: the
/// binary reader refuses an incoherent table before any validator sees it
/// (`TupleLayoutInconsistent` is therefore reachable only for a hand-built
/// or serde-decoded module, and is allowlisted as such).
pub fn build_refuse_bytes_blob_tuple_layout_incoherent() -> Result<Vec<u8>, FixtureError> {
    let mut m = refuse_identity("refuse_tuple_layout", Some(refuse_structural_license()))?;
    m.target_info = Some(refuse_target());
    let tuple_type = m
        .add_type(Ty::Tuple(vec![Ty::U8, Ty::U64, Ty::U8]))
        .or_fixture("Module::add_type")?;
    m.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
        tuple_type,
        size: 16,
        align: 8,
        field_offsets: vec![0, 0, 9],
    });
    trust_ir::binary::serialize_module(&m).or_fixture("serialize_module")
}

// The one inclusion of `signature_abi.rs` in this crate is `fixtures`'s
// (a second `#[path]` module of the same file is `clippy::duplicate_mod`).
use crate::fixtures::signature_abi_fixture;

fn typed_signature_refusal_base(name: &str) -> Result<Module, FixtureError> {
    let mut module = refuse_identity(name, Some(refuse_structural_license()))?;
    module.target_info = signature_abi_fixture::module()
        .or_fixture("the typed signature fixture module")?
        .target_info;
    module
        .add_func_type(signature_abi_fixture::signature())
        .or_fixture("Module::add_func_type")?;
    Ok(module)
}

/// Whole-signature census: two original scalar-pair pieces claim parameter 2,
/// leaving parameter 3 missing. Equal type lists cannot detect this defect.
pub fn build_refuse_signature_abi_duplicate_binding() -> Result<Module, FixtureError> {
    let mut module = typed_signature_refusal_base("refuse_signature_duplicate")?;
    let abi = module
        .func_types
        .last_mut()
        .and_then(|ty| ty.abi.as_mut())
        .or_fixture("the appended typed signature")?;
    abi.arguments
        .get_mut(2)
        .and_then(|argument| argument.bindings.get_mut(1))
        .or_fixture("the second scalar-pair binding")?
        .place = trust_ir::signature_abi::AbiBindingPlace::Parameter(2);
    Ok(module)
}

pub fn build_refuse_signature_abi_target_disagreement() -> Result<Module, FixtureError> {
    let mut module = typed_signature_refusal_base("refuse_signature_target")?;
    module
        .func_types
        .last_mut()
        .and_then(|ty| ty.abi.as_mut())
        .or_fixture("the appended typed signature")?
        .target
        .pointer_bytes = 4;
    Ok(module)
}

pub fn build_refuse_signature_abi_function_attribute_disagreement() -> Result<Module, FixtureError>
{
    let mut module = typed_signature_refusal_base("refuse_signature_function_attrs")?;
    let index = module
        .func_types
        .len()
        .checked_sub(1)
        .or_fixture("the appended signature index")?;
    let ty = trust_ir::FuncTyId::new(
        u32::try_from(index).or_fixture("the signature index fits its wire identity")?,
    );
    let mut function = Function::new(FuncId::new(1), "typed_callee", ty, BlockId::new(0));
    function.attrs.params = vec![trust_ir::ParamAttrs::default(); 6];
    function
        .attrs
        .params
        .get_mut(1)
        .or_fixture("the narrow argument attribute")?
        .ext = trust_ir::ArgExt::ZeroExt;
    module.functions.push(function);
    Ok(module)
}

/// A same-length unknown field in the canonical payload. The outer lengths
/// and target version remain valid, so the ABI reader itself must reject it.
pub fn build_refuse_bytes_signature_abi_unknown_field() -> Result<Vec<u8>, FixtureError> {
    let module = typed_signature_refusal_base("refuse_signature_unknown_field")?;
    let options = trust_ir::binary::ModuleBinaryOptions {
        body: trust_ir::binary::ModuleBinaryBody::Raw,
        ..Default::default()
    };
    let mut bytes = trust_ir::binary::ProjectedModuleBinaryPlan::try_new(&module, options)
        .or_fixture("encode the complete typed signature")?
        .to_vec()
        .or_fixture("to_vec")?;
    let needle = b"fixed_count=";
    let offset = bytes
        .windows(needle.len())
        .position(|window| window == needle)
        .or_fixture("the fixed_count ABI payload field")?;
    let poisoned = offset
        .checked_add(10)
        .or_fixture("the payload mutation offset")?;
    *bytes
        .get_mut(poisoned)
        .or_fixture("the payload mutation byte")? = b'x';
    Ok(bytes)
}

/// A missing entry cannot seed the frame-generation dataflow.
pub fn build_refuse_binding_frame_analysis_incomplete() -> Result<Module, FixtureError> {
    let mut m = refuse_identity(
        "refuse_binding_frame_analysis_incomplete",
        Some(refuse_structural_license()),
    )?;
    let f = &mut m.functions[0];
    f.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::OpenFrame {
            def: trust_ir::inst::BindingFrameDef::new(
                trust_ir::value::BindingFrameId::new(0),
                "frame",
                vec![],
            ),
        })
        .with_result(ValueId::new(1)),
    );
    f.blocks[0].body.insert(
        1,
        InstrNode::new(Inst::CloseFrame {
            frame: ValueId::new(1),
        }),
    );
    f.entry = BlockId::new(99);
    m.target_info = Some(refuse_target());
    Ok(m)
}

/// The same dynamic lineage stays closed across a CFG edge.
pub fn build_refuse_binding_frame_closed_edge() -> Result<Module, FixtureError> {
    let mut m = refuse_identity(
        "refuse_binding_frame_closed_edge",
        Some(refuse_structural_license()),
    )?;
    let f = &mut m.functions[0];
    let mut target = Block::new(BlockId::new(1));
    target.body.push(InstrNode::new(Inst::CloseFrame {
        frame: ValueId::new(1),
    }));
    target.body.append(&mut f.blocks[0].body);
    f.blocks[0].body = vec![
        InstrNode::new(Inst::OpenFrame {
            def: trust_ir::inst::BindingFrameDef::new(
                trust_ir::value::BindingFrameId::new(0),
                "frame",
                vec![],
            ),
        })
        .with_result(ValueId::new(1)),
        InstrNode::new(Inst::CloseFrame {
            frame: ValueId::new(1),
        }),
        InstrNode::new(Inst::Br {
            target: target.id,
            args: vec![],
        }),
    ];
    f.blocks.push(target);
    m.target_info = Some(refuse_target());
    Ok(m)
}

/// A declared two-capture closure must not accept only one live SSA capture.
pub fn build_refuse_make_closure_capture_count() -> Result<Module, FixtureError> {
    let mut module = crate::fixtures::build_make_closure()?;
    module.name = "refuse_make_closure_capture_count".into();
    for function in &mut module.functions {
        function.body_gate = Some(refuse_structural_license());
    }
    let inst = module
        .functions
        .get_mut(1)
        .and_then(|function| function.blocks.first_mut())
        .and_then(|block| block.body.get_mut(2))
        .or_fixture("the runtime closure constructor")?;
    let Inst::MakeClosure { captures, .. } = &mut inst.inst else {
        return Err(FixtureError {
            context: "runtime closure refusal",
            message: "expected the fixture constructor".into(),
        });
    };
    captures.pop().or_fixture("the second declared capture")?;
    Ok(module)
}

// ----- the tensor region (PKG-U13a) -----------------------------------------

/// `tensor<i32, 2>`, the operand type of every tensor contraction row.
fn refuse_matrix() -> Ty {
    Ty::Tensor(Box::new(Ty::I32), 2)
}

/// The control envelope plus `fn contract(a: tensor<i32, 2>, b: tensor<i32,
/// 2>) -> result`, licensed like the identity, whose one value is
/// `tensor_contract result %a, %b batch [] contract [1:0]`: a matrix multiply
/// when `result` is `tensor<i32, 2>`. The declared return is `result` itself,
/// so a row's only subject is the contraction.
fn refuse_tensor_contract_subject(name: &str, result: Ty) -> Result<Module, FixtureError> {
    let mut m = refuse_identity(name, Some(refuse_structural_license()))?;
    m.target_info = Some(refuse_target());
    let ft = m
        .add_func_type(FuncTy {
            params: vec![refuse_matrix(), refuse_matrix()],
            returns: vec![result.clone()],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let id = u32::try_from(m.functions.len()).or_fixture("the contraction's function id")?;
    let mut f = Function::new(FuncId::new(id), "contract", ft, BlockId::new(0));
    f.body_gate = Some(refuse_structural_license());
    let mut b = Block::new(BlockId::new(0))
        .with_param(ValueId::new(0), refuse_matrix())
        .with_param(ValueId::new(1), refuse_matrix());
    b.body.push(
        InstrNode::new(Inst::TensorContract {
            ty: result,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
            batch: vec![],
            contract: vec![(1, 0)],
        })
        .with_result(ValueId::new(2)),
    );
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    f.blocks.push(b);
    m.try_add_function(f)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

/// A `tensor<f32, 1>` in an otherwise unused signature: a tensor's element
/// must be an integer type, and a float element is refused BY NAME until
/// SemR has a float model (PKG-U15).
pub fn build_refuse_tensor_float_element() -> Result<Module, FixtureError> {
    let mut module = refuse_identity(
        "refuse_tensor_float_element",
        Some(refuse_structural_license()),
    )?;
    module.target_info = Some(refuse_target());
    module
        .add_func_type(FuncTy::unrecorded(
            vec![Ty::Tensor(Box::new(Ty::F32), 1)],
            vec![],
            false,
        ))
        .or_fixture("Module::add_func_type")?;
    Ok(module)
}

/// A matrix multiply of two `tensor<i32, 2>` operands spelled at
/// `tensor<i32, 3>`: the result's rank is the batch axes plus both sides'
/// free axes (here 0 + 1 + 1), so a contraction at any other rank is refused
/// statically. The declared return agrees with the instruction, so the rank
/// rule is the row's only subject.
pub fn build_refuse_tensor_contract_rank_mismatch() -> Result<Module, FixtureError> {
    refuse_tensor_contract_subject(
        "refuse_tensor_contract_rank_mismatch",
        Ty::Tensor(Box::new(Ty::I32), 3),
    )
}

/// A well-formed, licensed integer matrix multiply: the structural pass
/// accepts it, and the default codegen gate refuses it by name, because a
/// tensor contraction has no machine lowering yet (it is outside the
/// lowering-target subset).
pub fn build_refuse_tensor_contract_codegen() -> Result<Module, FixtureError> {
    refuse_tensor_contract_subject("refuse_tensor_contract_codegen", refuse_matrix())
}

/// The `tensor_contract` golden under the header one version below
/// `TENSOR_FORMAT_VERSION`, which allocates neither the tensor type tag nor
/// the contraction's instruction tag.
pub fn build_refuse_bytes_blob_tensor_below_its_version() -> Result<Vec<u8>, FixtureError> {
    let module = crate::fixtures::build_tensor_contract()?;
    let mut bytes = trust_ir::binary::serialize_module(&module).or_fixture("serialize_module")?;
    set_header_version(&mut bytes, trust_ir::binary::TENSOR_FORMAT_VERSION - 1)?;
    Ok(bytes)
}

/// The control envelope plus `fn tensor(params..) -> result`, licensed like
/// the identity, whose body is `body` (its last value `result_value`) then
/// the return of that value: the shared subject of the tensor map, reduce
/// and view rows (PKG-U13c).
fn refuse_tensor_region_subject(
    name: &str,
    params: Vec<Ty>,
    result: Ty,
    body: Vec<InstrNode>,
    result_value: u32,
) -> Result<Module, FixtureError> {
    let mut m = refuse_identity(name, Some(refuse_structural_license()))?;
    m.target_info = Some(refuse_target());
    let ft = m
        .add_func_type(FuncTy {
            params: params.clone(),
            returns: vec![result],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let id = u32::try_from(m.functions.len()).or_fixture("the tensor function's id")?;
    let mut f = Function::new(FuncId::new(id), "tensor", ft, BlockId::new(0));
    f.body_gate = Some(refuse_structural_license());
    let mut b = Block::new(BlockId::new(0));
    for (i, ty) in params.into_iter().enumerate() {
        let i = u32::try_from(i).or_fixture("a parameter index")?;
        b = b.with_param(ValueId::new(i), ty);
    }
    b.body = body;
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(result_value)],
    }));
    f.blocks.push(b);
    m.try_add_function(f)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

/// A tensor map whose one node reads its own lane: `tensor_map tensor<i32,
/// 2> (%a) { neg i32 $1 }`, where lane 1 is the node itself. A node reads
/// only the operands and the nodes before it (rule M3), so the body is
/// refused statically, never evaluated.
pub fn build_refuse_tensor_map_lane_out_of_scope() -> Result<Module, FixtureError> {
    refuse_tensor_region_subject(
        "refuse_tensor_map_lane_out_of_scope",
        vec![refuse_matrix()],
        refuse_matrix(),
        vec![
            InstrNode::new(Inst::TensorMap {
                ty: refuse_matrix(),
                args: vec![ValueId::new(0)],
                body: vec![trust_ir::TensorMapNode::UnOp {
                    op: UnOp::Neg,
                    ty: Ty::I32,
                    operand: 1,
                }],
            })
            .with_result(ValueId::new(1)),
        ],
        1,
    )
}

/// A reduction of a `tensor<i32, 3>` over axes `[2, 0]`: the reduced axes
/// are strictly ascending (rule R2), the one spelling of each axis set, so
/// any other order is refused statically. The result rank (3 - 2) agrees,
/// so the order is the row's only subject.
pub fn build_refuse_tensor_reduce_axes_not_ascending() -> Result<Module, FixtureError> {
    let row = Ty::Tensor(Box::new(Ty::I32), 1);
    refuse_tensor_region_subject(
        "refuse_tensor_reduce_axes_not_ascending",
        vec![Ty::Tensor(Box::new(Ty::I32), 3)],
        row.clone(),
        vec![
            InstrNode::new(Inst::TensorReduce {
                ty: row,
                src: ValueId::new(0),
                op: trust_ir::TensorReduceOp::Add,
                axes: vec![2, 0],
                order: trust_ir::TensorReduceOrder::RowMajor,
            })
            .with_result(ValueId::new(1)),
        ],
        1,
    )
}

/// A view whose result extent reads a result coordinate: `shape [$2]` with
/// `$2 = add($0, $1)` and `$0 = coord(0)`. The extents are fixed before any
/// coordinate exists (rule V6), so the view is refused statically.
pub fn build_refuse_tensor_view_shape_reads_a_coordinate() -> Result<Module, FixtureError> {
    use trust_ir::TensorIndexExpr as E;
    let row = Ty::Tensor(Box::new(Ty::I32), 1);
    refuse_tensor_region_subject(
        "refuse_tensor_view_shape_reads_a_coordinate",
        vec![row.clone()],
        row.clone(),
        vec![
            InstrNode::new(Inst::TensorView {
                ty: row,
                src: ValueId::new(0),
                params: vec![],
                exprs: vec![E::Coord(0), E::Lit(1), E::Add(0, 1)],
                shape: vec![2],
                index: vec![0],
                fill: None,
            })
            .with_result(ValueId::new(1)),
        ],
        1,
    )
}

/// A well-formed, licensed map, reduction and view, chained: `%1 =
/// tensor_map tensor<i32, 2> (%a) { neg i32 $0 }`, `%2 = tensor_reduce add
/// tensor<i32, 1> %1 axes [1] order row_major`, `%3 = tensor_view
/// tensor<i32, 1> %2 params [] exprs [src_extent(0), coord(0)] shape [$0]
/// index [$1]`. The structural pass accepts it, and the default codegen gate
/// refuses each of the three by name: none has a machine lowering yet (they
/// are outside the lowering-target subset).
pub fn build_refuse_tensor_map_reduce_view_codegen() -> Result<Module, FixtureError> {
    use trust_ir::TensorIndexExpr as E;
    let row = Ty::Tensor(Box::new(Ty::I32), 1);
    refuse_tensor_region_subject(
        "refuse_tensor_map_reduce_view_codegen",
        vec![refuse_matrix()],
        row.clone(),
        vec![
            InstrNode::new(Inst::TensorMap {
                ty: refuse_matrix(),
                args: vec![ValueId::new(0)],
                body: vec![trust_ir::TensorMapNode::UnOp {
                    op: UnOp::Neg,
                    ty: Ty::I32,
                    operand: 0,
                }],
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::TensorReduce {
                ty: row.clone(),
                src: ValueId::new(1),
                op: trust_ir::TensorReduceOp::Add,
                axes: vec![1],
                order: trust_ir::TensorReduceOrder::RowMajor,
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::TensorView {
                ty: row,
                src: ValueId::new(2),
                params: vec![],
                exprs: vec![E::SrcExtent(0), E::Coord(0)],
                shape: vec![0],
                index: vec![1],
                fill: None,
            })
            .with_result(ValueId::new(3)),
        ],
        3,
    )
}

/// The `tensor_map_reduce_view` golden under the header one version below
/// `TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION`, which allocates the tensor type
/// but none of the map, reduce and view instruction tags.
pub fn build_refuse_bytes_blob_tensor_map_reduce_view_below_its_version()
-> Result<Vec<u8>, FixtureError> {
    let module = crate::fixtures::build_tensor_map_reduce_view()?;
    let mut bytes = trust_ir::binary::serialize_module(&module).or_fixture("serialize_module")?;
    set_header_version(
        &mut bytes,
        trust_ir::binary::TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION - 1,
    )?;
    Ok(bytes)
}

// ----- the tensor region's gather and scatter (PKG-U13d) --------------------

/// `tensor<T, 1>`.
fn refuse_tensor_row(elem: Ty) -> Ty {
    Ty::Tensor(Box::new(elem), 1)
}

/// A gather of a `tensor<i32, 2>` with ONE coordinate tensor: `tensor_gather
/// tensor<i32, 1> %data coords [%rows]`. The data has two axes and a gather
/// takes exactly one coordinate tensor per data axis (rule G2), so the
/// instruction is refused statically, never run.
pub fn build_refuse_tensor_gather_coordinate_count_is_not_the_data_rank()
-> Result<Module, FixtureError> {
    let row = refuse_tensor_row(Ty::I32);
    refuse_tensor_region_subject(
        "refuse_tensor_gather_coordinate_count_is_not_the_data_rank",
        vec![refuse_matrix(), refuse_tensor_row(Ty::Usize)],
        row.clone(),
        vec![
            InstrNode::new(Inst::TensorGather {
                ty: row,
                data: ValueId::new(0),
                coords: vec![ValueId::new(1)],
            })
            .with_result(ValueId::new(2)),
        ],
        2,
    )
}

/// A scatter whose initial tensor is a `tensor<i64, 1>` under the result type
/// `tensor<i32, 1>`: `tensor_scatter tensor<i32, 1> %init, %src coords
/// [%at]`. The result starts as a copy of `init`, so `init` has the result
/// type (rule S1); any other is refused statically, never run.
pub fn build_refuse_tensor_scatter_init_is_not_the_result_type() -> Result<Module, FixtureError> {
    let row = refuse_tensor_row(Ty::I32);
    refuse_tensor_region_subject(
        "refuse_tensor_scatter_init_is_not_the_result_type",
        vec![
            refuse_tensor_row(Ty::I64),
            row.clone(),
            refuse_tensor_row(Ty::Usize),
        ],
        row.clone(),
        vec![
            InstrNode::new(Inst::TensorScatter {
                ty: row,
                init: ValueId::new(0),
                src: ValueId::new(1),
                coords: vec![ValueId::new(2)],
            })
            .with_result(ValueId::new(3)),
        ],
        3,
    )
}

/// A well-formed, licensed gather and scatter, chained, over `(data:
/// tensor<i32, 2>, rows: tensor<usize, 1>, cols: tensor<usize, 1>)`: `%3 =
/// tensor_gather tensor<i32, 1> %data coords [%rows, %cols]`, then `%4 =
/// tensor_scatter tensor<i32, 1> %3, %3 coords [%rows]` (the gathered row
/// written over itself at `rows`). The structural pass accepts it, and the
/// default codegen gate refuses each of the two by name: neither has a
/// machine lowering yet (both are outside the lowering-target subset).
pub fn build_refuse_tensor_gather_scatter_codegen() -> Result<Module, FixtureError> {
    let row = refuse_tensor_row(Ty::I32);
    let at = refuse_tensor_row(Ty::Usize);
    refuse_tensor_region_subject(
        "refuse_tensor_gather_scatter_codegen",
        vec![refuse_matrix(), at.clone(), at],
        row.clone(),
        vec![
            InstrNode::new(Inst::TensorGather {
                ty: row.clone(),
                data: ValueId::new(0),
                coords: vec![ValueId::new(1), ValueId::new(2)],
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::TensorScatter {
                ty: row,
                init: ValueId::new(3),
                src: ValueId::new(3),
                coords: vec![ValueId::new(1)],
            })
            .with_result(ValueId::new(4)),
        ],
        4,
    )
}

/// The `tensor_gather_scatter` golden under the header one version below
/// `TENSOR_GATHER_SCATTER_FORMAT_VERSION`, which allocates the tensor type
/// but neither the gather nor the scatter instruction tag.
pub fn build_refuse_bytes_blob_tensor_gather_scatter_below_its_version()
-> Result<Vec<u8>, FixtureError> {
    let module = crate::fixtures::build_tensor_gather_scatter()?;
    let mut bytes = trust_ir::binary::serialize_module(&module).or_fixture("serialize_module")?;
    set_header_version(
        &mut bytes,
        trust_ir::binary::TENSOR_GATHER_SCATTER_FORMAT_VERSION - 1,
    )?;
    Ok(bytes)
}

// ----- Box deref validity facts (wire v74) ----------------------------------

/// The `box_deref` golden under the structural license: `fresh` (function 0)
/// premises every conjunct on its own allocation, `checked` (function 1) on
/// its by-value parameter.
fn box_deref_subject(name: &str) -> Result<Module, FixtureError> {
    let mut module = crate::fixtures::build_box_deref()?;
    module.name = name.into();
    for function in &mut module.functions {
        function.body_gate = Some(refuse_structural_license());
    }
    Ok(module)
}

/// The one `BoxDeref` node of `function` in `module`, with its index.
fn box_deref_node(module: &mut Module, function: usize) -> Result<&mut InstrNode, FixtureError> {
    module
        .functions
        .get_mut(function)
        .and_then(|function| function.blocks.first_mut())
        .and_then(|block| {
            block
                .body
                .iter_mut()
                .find(|node| matches!(node.inst, Inst::BoxDeref { .. }))
        })
        .or_fixture("the subject's Box deref")
}

/// The fact of the one `BoxDeref` of `function` in `module`.
fn box_deref_fact(
    module: &mut Module,
    function: usize,
) -> Result<&mut trust_ir::box_validity::BoxValidityFact, FixtureError> {
    match &mut box_deref_node(module, function)?.inst {
        Inst::BoxDeref { fact, .. } => Ok(fact),
        _ => Err(FixtureError {
            context: "Box deref refusal",
            message: "expected the subject's Box deref".into(),
        }),
    }
}

/// The evidence entry of `conjunct` in the fact of `function`.
fn box_deref_entry(
    module: &mut Module,
    function: usize,
    conjunct: trust_ir::box_validity::ValidityConjunct,
) -> Result<&mut trust_ir::box_validity::ValidityEvidence, FixtureError> {
    box_deref_fact(module, function)?
        .evidence
        .iter_mut()
        .find(|entry| entry.conjunct == conjunct)
        .map(|entry| &mut entry.evidence)
        .or_fixture("the subject's conjunct entry")
}

/// The two-verdict row: a well-formed fact whose every conjunct is a named
/// premise. The default gates accept it; a consumer that sets the evidence
/// floor above the premise tier refuses each conjunct.
pub fn build_refuse_box_deref_premise_tier() -> Result<Module, FixtureError> {
    use trust_ir::box_validity::{BoxDerefSite, BoxFactSession, BoxValidityFact, PremiseRoot};
    let mut mb = ModuleBuilder::new("refuse_box_deref_premise_tier");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Ptr]);
    let mut fb = mb.function("unbox", ft);
    let entry = fb.create_block();
    let pointer = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    let boxed = fb.box_deref(
        Ty::I64,
        pointer,
        BoxValidityFact::premise(
            BoxDerefSite {
                item: [0x5a; 16],
                ordinal: 0,
            },
            BoxFactSession::PROOF_SNAPSHOT,
            PremiseRoot::ParamByValue,
        ),
    );
    fb.ret(vec![boxed]);
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    let mut module = mb.build().or_fixture("ModuleBuilder::build")?;
    module.target_info = Some(refuse_target());
    Ok(module)
}

/// The operand is the stored `i64`, not a pointer.
pub fn build_refuse_box_deref_operand_not_ptr() -> Result<Module, FixtureError> {
    let mut module = box_deref_subject("refuse_box_deref_operand_not_ptr")?;
    match &mut box_deref_node(&mut module, 0)?.inst {
        Inst::BoxDeref { operand, .. } => *operand = ValueId::new(1),
        _ => unreachable_box_deref()?,
    }
    Ok(module)
}

fn unreachable_box_deref() -> Result<(), FixtureError> {
    Err(FixtureError {
        context: "Box deref refusal",
        message: "expected the subject's Box deref".into(),
    })
}

/// The pointee is the zero-sized unit type.
pub fn build_refuse_box_deref_pointee_zero_sized() -> Result<Module, FixtureError> {
    let mut module = box_deref_subject("refuse_box_deref_pointee_zero_sized")?;
    match &mut box_deref_node(&mut module, 0)?.inst {
        Inst::BoxDeref { pointee, .. } => *pointee.ty_mut() = Ty::Unit,
        _ => unreachable_box_deref()?,
    }
    Ok(module)
}

/// The pointee is the uninhabited never type.
pub fn build_refuse_box_deref_pointee_uninhabited() -> Result<Module, FixtureError> {
    let mut module = box_deref_subject("refuse_box_deref_pointee_uninhabited")?;
    match &mut box_deref_node(&mut module, 0)?.inst {
        Inst::BoxDeref { pointee, .. } => *pointee.ty_mut() = Ty::Never,
        _ => unreachable_box_deref()?,
    }
    Ok(module)
}

/// The fact carries no evidence for `Dereferenceable`.
pub fn build_refuse_box_deref_conjunct_missing() -> Result<Module, FixtureError> {
    let mut module = box_deref_subject("refuse_box_deref_conjunct_missing")?;
    box_deref_fact(&mut module, 0)?
        .evidence
        .pop()
        .or_fixture("the Dereferenceable entry")?;
    Ok(module)
}

/// `NonNull` carries evidence twice.
pub fn build_refuse_box_deref_conjunct_duplicated() -> Result<Module, FixtureError> {
    let mut module = box_deref_subject("refuse_box_deref_conjunct_duplicated")?;
    let fact = box_deref_fact(&mut module, 0)?;
    let first = fact
        .evidence
        .first()
        .cloned()
        .or_fixture("the NonNull entry")?;
    fact.evidence.insert(0, first);
    Ok(module)
}

/// Every conjunct once, `Aligned` before `NonNull`.
pub fn build_refuse_box_deref_conjunct_misordered() -> Result<Module, FixtureError> {
    let mut module = box_deref_subject("refuse_box_deref_conjunct_misordered")?;
    box_deref_fact(&mut module, 0)?.evidence.swap(0, 1);
    Ok(module)
}

/// A sized pointee's fact carries the wide-only `MetadataValid`.
pub fn build_refuse_box_deref_metadata_valid_on_sized() -> Result<Module, FixtureError> {
    use trust_ir::box_validity::{ConjunctEvidence, ValidityConjunct};
    let mut module = box_deref_subject("refuse_box_deref_metadata_valid_on_sized")?;
    let fact = box_deref_fact(&mut module, 0)?;
    let evidence = fact
        .evidence
        .last()
        .map(|entry| entry.evidence.clone())
        .or_fixture("a premise entry")?;
    fact.evidence.push(ConjunctEvidence {
        conjunct: ValidityConjunct::MetadataValid,
        evidence,
    });
    Ok(module)
}

/// A premise that no longer names `BoxUnique`.
pub fn build_refuse_box_deref_premise_standing_dropped() -> Result<Module, FixtureError> {
    use trust_ir::box_validity::{ValidityConjunct, ValidityEvidence};
    let mut module = box_deref_subject("refuse_box_deref_premise_standing_dropped")?;
    match box_deref_entry(&mut module, 0, ValidityConjunct::Dereferenceable)? {
        ValidityEvidence::Premise { standing, .. } => {
            standing.pop().or_fixture("the BoxUnique assumption")?;
        }
        _ => unreachable_box_deref()?,
    }
    Ok(module)
}

/// The fact was judged on the optimized fallback body.
pub fn build_refuse_box_deref_session_fallback() -> Result<Module, FixtureError> {
    let mut module = box_deref_subject("refuse_box_deref_session_fallback")?;
    box_deref_fact(&mut module, 0)?.session.judged =
        trust_ir::box_validity::JudgedBody::OptimizedFallback;
    Ok(module)
}

/// The fact states a session whose verifier did not run.
pub fn build_refuse_box_deref_session_not_proof() -> Result<Module, FixtureError> {
    let mut module = box_deref_subject("refuse_box_deref_session_not_proof")?;
    box_deref_fact(&mut module, 0)?.session.producing =
        trust_ir::box_validity::ProducingSession::NonProofSession;
    Ok(module)
}

/// The shape an earlier draft of rule 6 accepted, kept as the subject of
/// the dominating-check refusals: `fn checked(p: ptr) -> i64` derefs `p`
/// with `NonNull` and `Aligned` offered as dominating checks, asserts both
/// over the RESULT (`ptrtoint`, compare, `Assert` of kind `NullPtr`; mask,
/// compare, `Assert` of kind `MisalignedPtr`), then loads through the
/// result. `Dereferenceable` is premised on the parameter.
fn box_deref_checked_subject(name: &str) -> Result<Module, FixtureError> {
    use trust_ir::box_validity::{
        BoxDerefSite, BoxFactSession, BoxValidityFact, PremiseRoot, ValidityConjunct,
        ValidityEvidence,
    };
    use trust_ir::inst::{AssertKind, BinOp, CastOp, ICmpOp};
    let mut mb = ModuleBuilder::new(name);
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
    let mut fb = mb.function("checked", ft);
    let entry = fb.create_block();
    let pointer = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    let mut fact = BoxValidityFact::premise(
        BoxDerefSite {
            item: [0xc4; 16],
            ordinal: 0,
        },
        BoxFactSession::PROOF_SNAPSHOT,
        PremiseRoot::ParamByValue,
    );
    for entry in &mut fact.evidence {
        match entry.conjunct {
            ValidityConjunct::NonNull => {
                entry.evidence = ValidityEvidence::DominatingCheck { align: None };
            }
            ValidityConjunct::Aligned => {
                entry.evidence = ValidityEvidence::DominatingCheck { align: Some(8) };
            }
            ValidityConjunct::Dereferenceable | ValidityConjunct::MetadataValid => {}
        }
    }
    let boxed = fb.box_deref(Ty::I64, pointer, fact);
    let address = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::Usize, boxed);
    let zero = fb.const_value(Ty::Usize, Constant::Int(0));
    let nonnull = fb.icmp(ICmpOp::Ne, Ty::Usize, address, zero);
    fb.assert_kind(nonnull, AssertKind::NullPtr);
    let required = fb.const_value(Ty::Usize, Constant::Int(8));
    let mask = fb.const_value(Ty::Usize, Constant::Int(7));
    let low = fb.binop(BinOp::And, Ty::Usize, address, mask);
    let none = fb.const_value(Ty::Usize, Constant::Int(0));
    let aligned = fb.icmp(ICmpOp::Eq, Ty::Usize, low, none);
    fb.assert_kind(
        aligned,
        AssertKind::MisalignedPtr {
            required,
            found: address,
        },
    );
    let read = fb.load(Ty::I64, boxed);
    fb.ret(vec![read]);
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// The checked subject unchanged: both asserts exist over the result and
/// dominate the load through it. Dominating-check evidence is refused in
/// every shape, this one included.
pub fn build_refuse_box_deref_check_pinned_shape() -> Result<Module, FixtureError> {
    box_deref_checked_subject("refuse_box_deref_check_pinned_shape")
}

/// `r = box_deref p [nonnull dominating_check]; a = ptrtoint r;
/// q = inttoptr a; load q;` and only then the null assert over `a`. `r` has
/// no use as a pointer, so a rule that exempts `ptrtoint r` from the uses a
/// check must dominate would be satisfied while the address is dereferenced
/// unchecked.
pub fn build_refuse_box_deref_check_address_round_trip() -> Result<Module, FixtureError> {
    use trust_ir::box_validity::{
        BoxDerefSite, BoxFactSession, BoxValidityFact, PremiseRoot, ValidityConjunct,
        ValidityEvidence,
    };
    use trust_ir::inst::{AssertKind, CastOp, ICmpOp};
    let mut mb = ModuleBuilder::new("refuse_box_deref_check_address_round_trip");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
    let mut fb = mb.function("round_trip", ft);
    let entry = fb.create_block();
    let pointer = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    let mut fact = BoxValidityFact::premise(
        BoxDerefSite {
            item: [0xc5; 16],
            ordinal: 0,
        },
        BoxFactSession::PROOF_SNAPSHOT,
        PremiseRoot::ParamByValue,
    );
    for entry in &mut fact.evidence {
        if entry.conjunct == ValidityConjunct::NonNull {
            entry.evidence = ValidityEvidence::DominatingCheck { align: None };
        }
    }
    let boxed = fb.box_deref(Ty::I64, pointer, fact);
    let address = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::Usize, boxed);
    let again = fb.cast(CastOp::IntToPtr, Ty::Usize, Ty::Ptr, address);
    let read = fb.load(Ty::I64, again);
    let zero = fb.const_value(Ty::Usize, Constant::Int(0));
    let nonnull = fb.icmp(ICmpOp::Ne, Ty::Usize, address, zero);
    fb.assert_kind(nonnull, AssertKind::NullPtr);
    fb.ret(vec![read]);
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// A dominating check offered for `Dereferenceable`.
pub fn build_refuse_box_deref_check_for_dereferenceable() -> Result<Module, FixtureError> {
    use trust_ir::box_validity::{ValidityConjunct, ValidityEvidence};
    let mut module = box_deref_checked_subject("refuse_box_deref_check_for_dereferenceable")?;
    *box_deref_entry(&mut module, 0, ValidityConjunct::Dereferenceable)? =
        ValidityEvidence::DominatingCheck { align: None };
    Ok(module)
}

/// The alignment check claims 4 bytes for an 8-byte-aligned pointee.
pub fn build_refuse_box_deref_check_wrong_alignment() -> Result<Module, FixtureError> {
    use trust_ir::box_validity::{ValidityConjunct, ValidityEvidence};
    let mut module = box_deref_checked_subject("refuse_box_deref_check_wrong_alignment")?;
    *box_deref_entry(&mut module, 0, ValidityConjunct::Aligned)? =
        ValidityEvidence::DominatingCheck { align: Some(4) };
    Ok(module)
}

/// A null check claimed in a function that asserts nothing.
pub fn build_refuse_box_deref_check_absent() -> Result<Module, FixtureError> {
    use trust_ir::box_validity::{ValidityConjunct, ValidityEvidence};
    let mut module = box_deref_subject("refuse_box_deref_check_absent")?;
    *box_deref_entry(&mut module, 0, ValidityConjunct::NonNull)? =
        ValidityEvidence::DominatingCheck { align: None };
    Ok(module)
}

/// The one block of the checked subject with the position of its `BoxDeref`.
fn box_deref_checked_block(
    module: &mut Module,
) -> Result<(&mut Vec<InstrNode>, usize), FixtureError> {
    let body = &mut module
        .functions
        .first_mut()
        .and_then(|function| function.blocks.first_mut())
        .or_fixture("the checked function's block")?
        .body;
    let at = body
        .iter()
        .position(|node| matches!(node.inst, Inst::BoxDeref { .. }))
        .or_fixture("the subject's Box deref")?;
    Ok((body, at))
}

/// Both asserts exist over the result, but the load through the result
/// executes BEFORE them.
pub fn build_refuse_box_deref_check_not_dominating() -> Result<Module, FixtureError> {
    let mut module = box_deref_checked_subject("refuse_box_deref_check_not_dominating")?;
    let (body, at) = box_deref_checked_block(&mut module)?;
    let load = body
        .iter()
        .position(|node| matches!(node.inst, Inst::Load { .. }))
        .or_fixture("the checked function's load through the result")?;
    let node = body.remove(load);
    body.insert(at + 1, node);
    Ok(module)
}

/// Both asserts exist and dominate every use, but they test the cast's
/// OPERAND, not its result.
pub fn build_refuse_box_deref_check_on_operand() -> Result<Module, FixtureError> {
    let mut module = box_deref_checked_subject("refuse_box_deref_check_on_operand")?;
    let (body, at) = box_deref_checked_block(&mut module)?;
    let (Inst::BoxDeref { operand, .. }, [result]) = (&body[at].inst, body[at].results.as_slice())
    else {
        return Err(FixtureError {
            context: "Box deref refusal",
            message: "expected the subject's Box deref with one result".into(),
        });
    };
    let (operand, result) = (*operand, *result);
    let address = body
        .iter_mut()
        .find_map(|node| match &mut node.inst {
            Inst::Cast {
                op: trust_ir::inst::CastOp::PtrToInt,
                operand: checked,
                ..
            } if *checked == result => Some(checked),
            _ => None,
        })
        .or_fixture("the checked function's address of the result")?;
    *address = operand;
    Ok(module)
}

// Rule 9: a premise the function itself contradicts.

/// `fn subject(<params>) -> ptr`: a fresh heap allocation `raw`, the operand
/// `shape` builds from it and the first parameter, the deref of that operand
/// premised on `root`, and the result returned.
fn box_deref_premise_module(
    name: &str,
    with_parameter: bool,
    with_allocation: bool,
    root: trust_ir::box_validity::PremiseRoot,
    shape: fn(
        &mut trust_ir_build::FunctionBuilder<'_>,
        Option<ValueId>,
        Option<ValueId>,
    ) -> ValueId,
) -> Result<Module, FixtureError> {
    use trust_ir::box_validity::{BoxDerefSite, BoxFactSession, BoxValidityFact};
    let mut mb = ModuleBuilder::new(name);
    let params = if with_parameter {
        vec![Ty::Ptr]
    } else {
        vec![]
    };
    let ft = mb.add_func_type(params, vec![Ty::Ptr]);
    let mut fb = mb.function("subject", ft);
    let entry = fb.create_block();
    let parameter = with_parameter.then(|| fb.add_block_param(entry, Ty::Ptr));
    fb.switch_to_block(entry);
    let raw = with_allocation
        .then(|| fb.heap_alloc(Ty::I64, None, None, trust_ir::inst::AllocOrigin::RustHeap));
    let operand = shape(&mut fb, parameter, raw);
    let boxed = fb.box_deref(
        Ty::I64,
        operand,
        BoxValidityFact::premise(
            BoxDerefSite {
                item: [0x9e; 16],
                ordinal: 0,
            },
            BoxFactSession::PROOF_SNAPSHOT,
            root,
        ),
    );
    fb.ret(vec![boxed]);
    fb.set_body_gate(refuse_structural_license());
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// The operand is `null_ptr`, premised non-null on an allocation the body
/// does make.
pub fn build_refuse_box_deref_premise_null_operand() -> Result<Module, FixtureError> {
    box_deref_premise_module(
        "refuse_box_deref_premise_null_operand",
        false,
        true,
        trust_ir::box_validity::PremiseRoot::AllocPostcondition,
        |fb, _, _| fb.null_ptr(),
    )
}

/// The operand is `inttoptr 4096`, premised on the function's parameter.
pub fn build_refuse_box_deref_premise_inttoptr_operand() -> Result<Module, FixtureError> {
    box_deref_premise_module(
        "refuse_box_deref_premise_inttoptr_operand",
        true,
        false,
        trust_ir::box_validity::PremiseRoot::ParamByValue,
        |fb, _, _| {
            let address = fb.const_value(Ty::Usize, Constant::Int(4096));
            fb.cast(
                trust_ir::inst::CastOp::IntToPtr,
                Ty::Usize,
                Ty::Ptr,
                address,
            )
        },
    )
}

/// The root is `param_by_value` in a function that takes no parameter.
pub fn build_refuse_box_deref_premise_param_root_without_parameter() -> Result<Module, FixtureError>
{
    box_deref_premise_module(
        "refuse_box_deref_premise_param_root_without_parameter",
        false,
        true,
        trust_ir::box_validity::PremiseRoot::ParamByValue,
        |_, _, raw| raw.unwrap_or(ValueId::new(u32::MAX)),
    )
}

/// The root is `alloc_postcondition` in a body with no allocation and no
/// call.
pub fn build_refuse_box_deref_premise_alloc_root_without_allocation() -> Result<Module, FixtureError>
{
    box_deref_premise_module(
        "refuse_box_deref_premise_alloc_root_without_allocation",
        true,
        false,
        trust_ir::box_validity::PremiseRoot::AllocPostcondition,
        |_, parameter, _| parameter.unwrap_or(ValueId::new(u32::MAX)),
    )
}

/// The operand's allocation is freed by a `Dealloc` that dominates the deref.
pub fn build_refuse_box_deref_premise_freed_operand() -> Result<Module, FixtureError> {
    box_deref_premise_module(
        "refuse_box_deref_premise_freed_operand",
        false,
        true,
        trust_ir::box_validity::PremiseRoot::AllocPostcondition,
        |fb, _, raw| {
            let raw = raw.unwrap_or(ValueId::new(u32::MAX));
            fb.dealloc(raw);
            raw
        },
    )
}

/// `NonNull` and `Aligned` are premised on `param_by_value`,
/// `Dereferenceable` on `reference_arg_box_valid`: one fact, two roots.
pub fn build_refuse_box_deref_premise_mixed_roots() -> Result<Module, FixtureError> {
    use trust_ir::box_validity::{PremiseRoot, ValidityConjunct, ValidityEvidence};
    let mut module = box_deref_subject("refuse_box_deref_premise_mixed_roots")?;
    match box_deref_entry(&mut module, 1, ValidityConjunct::Dereferenceable)? {
        ValidityEvidence::Premise { root, .. } => *root = PremiseRoot::ReferenceArgBoxValid,
        _ => unreachable_box_deref()?,
    }
    Ok(module)
}

/// The two-verdict row of the lower premise class: a well-formed fact whose
/// every conjunct is premised on `reference_arg_box_valid`, a root that says
/// the producing session verified nothing behind it. The default gates
/// accept it; a consumer whose floor is the named-premise class refuses each
/// conjunct.
pub fn build_refuse_box_deref_assumed_root_tier() -> Result<Module, FixtureError> {
    let mut module = box_deref_premise_module(
        "refuse_box_deref_assumed_root_tier",
        true,
        false,
        trust_ir::box_validity::PremiseRoot::ReferenceArgBoxValid,
        |_, parameter, _| parameter.unwrap_or(ValueId::new(u32::MAX)),
    )?;
    module.target_info = Some(refuse_target());
    Ok(module)
}

/// A `MemorySafety` row owned by and sited on the `BoxDeref` of `fresh`,
/// `Pending`: no certificate exists for it.
fn box_deref_obligation(module: &Module) -> Result<ProofObligation, FixtureError> {
    let function = module.functions.first().or_fixture("the fresh function")?;
    let block = function.blocks.first().or_fixture("its entry block")?;
    let at = block
        .body
        .iter()
        .position(|node| matches!(node.inst, Inst::BoxDeref { .. }))
        .or_fixture("the subject's Box deref")?;
    Ok(ProofObligation::new(
        ProofId::new(0),
        ObligationKind::MemorySafety,
        ProofStatus::Pending,
        "the pointer is dereferenceable for the pointee",
    )
    .with_function(function.id)
    .with_site(trust_ir::proof::ObligationSite::new(
        function.id,
        block.id,
        at as u32,
    )))
}

fn cite_box_deref_obligation(module: &mut Module) -> Result<(), FixtureError> {
    use trust_ir::box_validity::{ValidityConjunct, ValidityEvidence};
    *box_deref_entry(module, 0, ValidityConjunct::Dereferenceable)? =
        ValidityEvidence::Obligation {
            obligation: ProofId::new(0),
        };
    Ok(())
}

/// The fact cites obligation 0 and the module has no obligation rows.
pub fn build_refuse_box_deref_obligation_missing() -> Result<Module, FixtureError> {
    let mut module = box_deref_subject("refuse_box_deref_obligation_missing")?;
    cite_box_deref_obligation(&mut module)?;
    Ok(module)
}

/// The cited row is an `Ownership` obligation.
pub fn build_refuse_box_deref_obligation_wrong_kind() -> Result<Module, FixtureError> {
    let mut module = box_deref_subject("refuse_box_deref_obligation_wrong_kind")?;
    let mut row = box_deref_obligation(&module)?;
    row.kind = ObligationKind::Ownership;
    module.proof_obligations.push(row);
    cite_box_deref_obligation(&mut module)?;
    Ok(module)
}

/// The cited row is a well-formed row of ANOTHER function: owned by
/// `checked` and sited on the deref of `checked`, cited by the fact of
/// `fresh`.
pub fn build_refuse_box_deref_obligation_wrong_function() -> Result<Module, FixtureError> {
    let mut module = box_deref_subject("refuse_box_deref_obligation_wrong_function")?;
    let mut row = box_deref_obligation(&module)?;
    let other = module.functions.get(1).or_fixture("the checked function")?;
    let block = other.blocks.first().or_fixture("its entry block")?;
    let at = block
        .body
        .iter()
        .position(|node| matches!(node.inst, Inst::BoxDeref { .. }))
        .or_fixture("the checked function's Box deref")?;
    row.function = Some(other.id);
    row.site = Some(trust_ir::proof::ObligationSite::new(
        other.id, block.id, at as u32,
    ));
    module.proof_obligations.push(row);
    cite_box_deref_obligation(&mut module)?;
    Ok(module)
}

/// The cited row is sited on the instruction before the deref.
pub fn build_refuse_box_deref_obligation_wrong_site() -> Result<Module, FixtureError> {
    let mut module = box_deref_subject("refuse_box_deref_obligation_wrong_site")?;
    let mut row = box_deref_obligation(&module)?;
    let site = row.site.as_mut().or_fixture("the row's site")?;
    site.inst_index = site
        .inst_index
        .checked_sub(1)
        .or_fixture("an earlier instruction")?;
    module.proof_obligations.push(row);
    cite_box_deref_obligation(&mut module)?;
    Ok(module)
}

/// The cited row binds the instruction and no certificate of it exists.
pub fn build_refuse_box_deref_obligation_not_replayed() -> Result<Module, FixtureError> {
    let mut module = box_deref_subject("refuse_box_deref_obligation_not_replayed")?;
    let row = box_deref_obligation(&module)?;
    module.proof_obligations.push(row);
    cite_box_deref_obligation(&mut module)?;
    Ok(module)
}

/// The fact no longer says it makes no allocator claim.
pub fn build_refuse_box_deref_non_claim_dropped() -> Result<Module, FixtureError> {
    let mut module = box_deref_subject("refuse_box_deref_non_claim_dropped")?;
    box_deref_fact(&mut module, 0)?
        .not_claimed
        .pop()
        .or_fixture("the allocator non-claim")?;
    Ok(module)
}

/// The `box_deref` golden under the header one version below the
/// instruction's, which allocates no Inst tag 77.
pub fn build_refuse_bytes_blob_box_deref_below_its_version() -> Result<Vec<u8>, FixtureError> {
    let module = crate::fixtures::build_box_deref()?;
    let mut bytes = trust_ir::binary::serialize_module(&module).or_fixture("serialize_module")?;
    set_header_version(
        &mut bytes,
        trust_ir::binary::BOX_DEREF_VALIDITY_FORMAT_VERSION - 1,
    )?;
    Ok(bytes)
}

// ---------- content-addressed weight blobs (PKG-U13e) ----------

/// Three `i32` weights, `[1, 2, 3]`, as their twelve little-endian bytes.
const REFUSE_WEIGHTS: [u8; 12] = [1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0];

/// The control envelope plus `fn tensor() -> tensor<i32, 1> { %0 = const
/// tensor<i32, 1> tensor_blob<digest>[dims]; return %0 }` over the blob table
/// `rows`, as written (no row is rehashed or reordered).
fn refuse_tensor_blob_subject(
    name: &str,
    digest: trust_ir::blob::BlobDigest,
    dims: &[u64],
    rows: Vec<trust_ir::blob::Blob>,
) -> Result<Module, FixtureError> {
    let row = refuse_tensor_row(Ty::I32);
    let mut m = refuse_tensor_region_subject(
        name,
        vec![],
        row.clone(),
        vec![
            InstrNode::new(Inst::Const {
                ty: row,
                value: Constant::TensorBlob {
                    digest,
                    dims: dims.to_vec(),
                },
            })
            .with_result(ValueId::new(0)),
        ],
        0,
    )?;
    m.blobs = rows;
    Ok(m)
}

/// The table's one row records the digest of `REFUSE_WEIGHTS` but holds
/// those twelve bytes with the last weight changed (rule B2): the digest the
/// body names is not the bytes it would run on. The constant itself is
/// well-formed (three `i32`, twelve bytes).
pub fn build_refuse_tensor_blob_digest_mismatch() -> Result<Module, FixtureError> {
    let digest = trust_ir::blob::BlobDigest::of(&REFUSE_WEIGHTS);
    let mut forged = REFUSE_WEIGHTS.to_vec();
    let last = forged.get_mut(8).or_fixture("the last weight's low byte")?;
    *last = 4;
    refuse_tensor_blob_subject(
        "refuse_tensor_blob_digest_mismatch",
        digest,
        &[3],
        vec![trust_ir::blob::Blob {
            digest,
            data: forged,
        }],
    )
}

/// A blob constant whose digest names no row: the table is empty, so the
/// tensor it names has no bytes.
pub fn build_refuse_tensor_blob_missing() -> Result<Module, FixtureError> {
    refuse_tensor_blob_subject(
        "refuse_tensor_blob_missing",
        trust_ir::blob::BlobDigest::of(&REFUSE_WEIGHTS),
        &[3],
        Vec::new(),
    )
}

/// A blob constant whose extents `[4]` describe sixteen bytes of `i32` over
/// a row of twelve (rule C4).
pub fn build_refuse_tensor_blob_extents_do_not_fit_its_bytes() -> Result<Module, FixtureError> {
    let row = trust_ir::blob::Blob::new(REFUSE_WEIGHTS.to_vec());
    refuse_tensor_blob_subject(
        "refuse_tensor_blob_extents_do_not_fit_its_bytes",
        row.digest,
        &[4],
        vec![row],
    )
}

/// A well-formed, licensed blob constant: the default codegen gate refuses
/// it by name (a tensor has no machine layout).
pub fn build_refuse_tensor_blob_codegen() -> Result<Module, FixtureError> {
    let row = trust_ir::blob::Blob::new(REFUSE_WEIGHTS.to_vec());
    refuse_tensor_blob_subject("refuse_tensor_blob_codegen", row.digest, &[3], vec![row])
}

/// The `tensor_weight_blob` golden under the header one version below
/// `TENSOR_BLOB_FORMAT_VERSION`, which allocates no Constant tag 18.
pub fn build_refuse_bytes_blob_tensor_blob_below_its_version() -> Result<Vec<u8>, FixtureError> {
    let module = crate::fixtures::build_tensor_weight_blob()?;
    let mut bytes = trust_ir::binary::serialize_module(&module).or_fixture("serialize_module")?;
    set_header_version(&mut bytes, trust_ir::binary::TENSOR_BLOB_FORMAT_VERSION - 1)?;
    Ok(bytes)
}

/// A blob table written in DESCENDING digest order (the writer writes the
/// rows as given; every reader refuses any order but strictly ascending).
pub fn build_refuse_bytes_blob_tensor_blob_table_not_canonical() -> Result<Vec<u8>, FixtureError> {
    let mut module = Module::new("refuse_blob_tensor_blob_order");
    module.intern_blob(REFUSE_WEIGHTS.to_vec());
    module.intern_blob(Vec::new());
    module.blobs.reverse();
    let first = module.blobs.first().or_fixture("the first row")?;
    let second = module.blobs.get(1).or_fixture("the second row")?;
    if first.digest <= second.digest {
        return Err(FixtureError {
            context: "the reversed blob table",
            message: "its rows do not descend".to_string(),
        });
    }
    trust_ir::binary::serialize_module(&module).or_fixture("serialize_module")
}

/// The first premise root byte of the `box_deref` golden set to 9, which
/// names no `PremiseRoot`.
pub fn build_refuse_bytes_blob_box_deref_premise_root_unknown() -> Result<Vec<u8>, FixtureError> {
    let module = crate::fixtures::build_box_deref()?;
    let mut bytes = trust_ir::binary::serialize_module(&module).or_fixture("serialize_module")?;
    // The end of site 0 (item byte 0xf0, ordinal 0), the session (snapshot,
    // proof session), three entries, then `NonNull` (0), `Premise` (0)
    // and its root byte (1, `AllocPostcondition`).
    let pattern = [0xf0u8, 0, 0, 0, 3, 0, 0, 1];
    let at = bytes
        .windows(pattern.len())
        .position(|window| window == pattern)
        .or_fixture("the first premise's bytes")?;
    let root_byte = at.checked_add(7).or_fixture("the root byte's offset")?;
    *bytes.get_mut(root_byte).or_fixture("the root byte")? = 9;
    Ok(bytes)
}
