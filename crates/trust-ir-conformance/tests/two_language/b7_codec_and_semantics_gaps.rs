//! b7 — codecs and semantics gaps.
//!
//! PASS: binary / JSON / MessagePack are lossless for the whole v41–v43
//! contract surface (summary, bindings, imports, body_gate, display_path,
//! tuple layouts, handle, enum layout, struct offsets, global ABI residue,
//! global_asm), the writer selects the MINIMUM lossless wire version, and the
//! read gates refuse a down-labelled blob.
//!
//! GAP ratchets: canonical TEXT silently drops `FunctionSummary`, clause
//! bindings, enum layouts + field names, struct field names + offsets, the
//! v41 global residue and `global_asm`; TEXT cannot parse the names producers
//! mint; there is no typed nondeterministic choice/input instruction; spec
//! invariants are opaque strings.
//!
//! Ported (roadmap WS8.6) from the archived Part B battery
//! `reports/2026-09-17-two-language-proof-program/partb/tests/b7_codec_and_semantics_gaps.rs`, measured there
//! at trust-ir 4efb21bc and re-measured at the port. Every row is checked against
//! `RATCHETS.tsv` (see `harness.rs`). `file:line` citations are relative to
//! `crates/` and date from 4efb21bc: re-locate them by name.
//!
//! Review pass (rows/comments marked `[review]`): the imported dependency now
//! REALLY carries the kernel-certified obligations the surface cites, so the
//! surface (and every production-decoded copy) is validated with
//! `validate_linked_module` under `RejectingModuleProofAuthority`, not only the
//! faith-taking structural tier; v41 evidence tag 8 + function ABI residue were
//! added to the surface; loose "any error" twins were pinned to exact variants.

mod common;

use common::{
    Expect, Outcome, feature_check, feature_gap, feature_ratified, roundtrip_all, run_nullary,
    run_with_args,
};
use trust_ir::binary::{
    BinaryError, BinaryProjectionError, ModuleBinaryOptions, ProjectedModuleBinaryPlan,
    deserialize_module, serialize_module,
};
use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate_in;
use trust_ir::dialect::DialectInst;
use trust_ir::interpret::InterpretValue;
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, ObligationKind, ObligationSite, ProofAnnotation,
    ProofCertificate, ProofEvidence, ProofFormula, ProofObligation, ProofStatus,
    RejectingModuleProofAuthority, SpecObligationRef,
};
use trust_ir::spec::{
    SpecInvariant, SpecLinkViolation, SpecModule, SpecTemporal, SpecVar, TemporalForm,
};
use trust_ir::ty::{
    EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant, FieldDef, StructDef,
    StructRepr, Ty,
};
use trust_ir::value::{BlockId, EnumId, FuncId, ProofId, StructId, ValueId};
use trust_ir::{
    Block, BodyGate, Constant, Endianness, ExternRef, FuncTy, Function, FunctionSummary, Global,
    Inst, InstrNode, Linkage, Module, ModuleImport, Producer, TargetInfo, TupleLayoutDescriptor,
    Visibility,
};
use trust_ir_build::{
    ModuleBuilder, ModuleSet, TRUSTED_HANDLE_RUNTIMES, ValidationError, validate_linked_module,
    validate_module,
};

// ---------------------------------------------------------------------------
// The contract-surface module
// ---------------------------------------------------------------------------

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: Default::default(),
    }
}

fn bound(text: &str, bindings: &[(&str, ClauseSort, ClausePlace)]) -> ProofFormula {
    let mut formula = ProofFormula::smtlib2(text, "Bool");
    formula.bindings = bindings
        .iter()
        .map(|(name, sort, place)| {
            (
                (*name).to_string(),
                ClauseBinding {
                    sort: sort.clone(),
                    place: *place,
                },
            )
        })
        .collect();
    formula
}

/// The contract both far functions carry: `result >= 0` over the `u64` result
/// slot — a BOUND clause (v41 `bindings`) the in-process Clean kernel can
/// certify, so the importer's cross-crate claims are TRUE claims and the
/// surface module survives `validate_linked_module`, not only the structural
/// `validate_module` (which takes every cross-crate row on faith).
fn far_clause() -> ProofFormula {
    bound(
        "(>= result 0)",
        &[(
            "result",
            ClauseSort::Int,
            ClausePlace::ResultSlot { index: 0 },
        )],
    )
}

fn far_contract() -> FunctionSummary {
    FunctionSummary::new()
        .with_params(vec!["x".to_string()])
        .ensuring(far_clause())
}

/// The far module the surface module imports: `far_f(x) = x + k`,
/// `far_g(x) = x + k + 1`, each `proved` by a kernel-CERTIFIED Postcondition
/// (#0 for far_f, #1 for far_g). `k` = 1 in the honest build; any other `k` is
/// "the same crate, one byte different" (the digest twin).
fn build_dep(k: u128) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("b7_dep", target());
    mb.set_default_producer(Producer::TRust);
    let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut ids = Vec::new();
    for (name, add) in [("far_f", k), ("far_g", k + 1)] {
        let mut fb = mb.function(name, ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let c = fb.uconst(Ty::U64, add);
        let r = fb.add(Ty::U64, x, c);
        fb.ret(vec![r]);
        ids.push(fb.build());
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    for (i, f) in ids.into_iter().enumerate() {
        m.function_by_id_mut(f).unwrap().summary = Some(far_contract().proved());
        let obligation = ProofObligation::new(
            ProofId::new(i as u32),
            ObligationKind::Postcondition,
            ProofStatus::Certified,
            "far ensures (>= result 0)",
        )
        .with_function(f)
        .with_formula(far_clause());
        // Module-bound mint (WS1.1, 0aeae341): the free name `result` grounds
        // only once its binding resolves to the u64 result slot of `f`.
        let certificate = contract_clean_cic_certificate_in(&m, &obligation, "b7-contract-prover")
            .expect("`(>= result 0)` over a u64 result slot is kernel-provable");
        m.proof_obligations.push(obligation);
        m.proof_certificates.push(certificate);
    }
    m
}

/// The honest dependency, built (and kernel-certified) once.
fn dep_module() -> &'static Module {
    static DEP: std::sync::OnceLock<Module> = std::sync::OnceLock::new();
    DEP.get_or_init(|| build_dep(1))
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Level {
    /// v41 contract surface only.
    Contract,
    /// + v42 declared tuple layout.
    Tuple,
    /// + v43 handle.
    Handle,
}

struct Surface {
    module: Module,
    bump: FuncId,
    far_f: FuncId,
    far_g: FuncId,
    import: trust_ir::value::ImportId,
    /// Index of the hand-made sited obligation (bound formula + IR site).
    sited: usize,
}

impl Surface {
    /// The surface PLUS the cross-crate inheritance row (v41 evidence tag 8):
    /// a Discharged Postcondition on the `far_g` declaration whose certificate
    /// is `InheritedFromCallee { external: Some(import.0 far_g #1) }`.
    ///
    /// Kept out of the base module on purpose: the STRUCTURAL tier
    /// (`validate_module`) never admits an external inheritance certificate —
    /// it reports `DischargedWithoutCertificate` — so this module validates
    /// ONLY under `validate_linked_module` (measured in
    /// `b7.surface.inheritance_needs_linked_tier`).
    fn with_inheritance(&self) -> Module {
        let mut m = self.module.clone();
        let inherited = ProofId::new(m.proof_obligations.len() as u32);
        m.proof_obligations.push(
            ProofObligation::new(
                inherited,
                ObligationKind::Postcondition,
                ProofStatus::Discharged,
                "inherited: far_g ensures (>= result 0)",
            )
            .with_function(self.far_g)
            .with_formula(far_clause()),
        );
        m.proof_certificates.push(ProofCertificate {
            obligation: inherited,
            prover: "b7-compose".into(),
            evidence: ProofEvidence::InheritedFromCallee {
                callee: self.far_g,
                obligation: inherited,
                external: Some(ExternRef::new(self.import, "far_g").relying_on(ProofId::new(1))),
            },
            assurance: None,
        });
        m
    }
}

/// One module carrying every surface the b7 PASS row names.
///
/// ```text
/// [TRust] bump(x: i64) -> i64 = x + 1          summary{requires,ensures,decreases,params} + bindings
/// [TRust] far_f(x: u64) -> u64   (declaration) summary{ensures, proved, backed_by -> import.0 #0}
/// [TRust] far_g(x: u64) -> u64   (declaration) summary{ensures}; `Surface::with_inheritance`
///                                              adds the Discharged row inheriting import.0 #1
/// [Clean] nat_pred(n: Nat) -> Nat              handle transport (Level::Handle)
/// ```
fn surface(level: Level) -> Surface {
    surface_with(level, ObligationKind::Termination)
}

/// `sited_kind` = the kind of the one obligation that carries a bound formula
/// and an IR site (the design's end state is `Termination`, for `decreases`).
fn surface_with(level: Level, sited_kind: ObligationKind) -> Surface {
    let mut mb = ModuleBuilder::new_with_target_info("b7_surface", target());
    let mut handle_bits = None;
    if level == Level::Handle {
        let pin = TRUSTED_HANDLE_RUNTIMES
            .iter()
            .find(|pin| pin.runtime == "trust_bignum::Nat")
            .expect("the v1 Nat row is pinned");
        let decls = mb
            .declare_handle_runtime(pin)
            .expect("fresh module has no conflicting declaration");
        let h = decls.handle.clone();
        let unop = mb.add_func_type(vec![h.clone()], vec![h.clone()]);
        handle_bits = Some((
            h,
            unop,
            decls.entry("from_u64").unwrap(),
            decls.entry("sub").unwrap(),
            decls.entry("is_zero").unwrap(),
        ));
    }
    let unary = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let far_ty = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);

    // --- bump: body-bearing, contract with bound clauses ---
    let bump = {
        let mut fb = mb.function("bump", unary);
        fb.set_producer(Producer::TRust);
        fb.set_display_path("m::bump::<impl Step for i64>");
        fb.set_body_gate(BodyGate::Gated {
            authority: "trust-verify".into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let one = fb.iconst(Ty::I64, 1);
        let r = fb.add(Ty::I64, x, one);
        fb.ret(vec![r]);
        fb.build()
    };

    // --- nat_pred: the Clean handle transport body ---
    if let Some((h, unop, from_u64, sub, is_zero)) = handle_bits.clone() {
        let mut fb = mb.function("nat_pred", unop);
        fb.set_producer(Producer::Clean);
        fb.set_display_path("Nat.pred");
        fb.set_body_gate(BodyGate::Ungated);
        let entry = fb.create_block();
        let zero = fb.create_block();
        let step = fb.create_block();
        let n = fb.add_block_param(entry, h);
        fb.switch_to_block(entry);
        let z = fb.call(is_zero, vec![n]);
        fb.condbr(z, zero, vec![], step, vec![]);
        fb.switch_to_block(zero);
        fb.ret(vec![n]);
        fb.switch_to_block(step);
        let one = fb.uconst(Ty::U64, 1);
        let one_n = fb.call(from_u64, vec![one]);
        let out = fb.call(sub, vec![n, one_n]);
        fb.ret(vec![out]);
        fb.build();
    }

    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");

    // --- v41 ABI / linkage residue on a function ---
    {
        let f = m.function_by_id_mut(bump).unwrap();
        f.linkage = Linkage::LinkOnceOdr;
        f.attrs.target_features = vec!["+neon".into(), "+crc".into()];
    }

    // --- imports + the two declarations whose proofs live cross-crate ---
    let dep = dep_module();
    // A LEGACY (pre-v44) row: recorded under the V2 identity, so the surface
    // keeps its v41..=v43 ladder, and every linked PASS below also shows a V2
    // row still authenticating its V2 dependency after WS4.10.
    let import = m
        .intern_import(
            ModuleImport::new(
                dep.name.clone(),
                dep.stable_digest_under(trust_ir::IdentityScheme::V2),
            )
            .with_producer(Producer::TRust)
            .with_scheme(trust_ir::IdentityScheme::V2),
        )
        .expect("Module::intern_import: test fixture");
    // far_f: `proved` is BACKED by the far obligation #0 (exact restatement).
    let far_f = FuncId::new(m.functions.len() as u32);
    let mut far = Function::declaration(
        far_f,
        "far_f",
        far_ty,
        far_contract()
            .proved()
            .backed_by(ExternRef::new(import, "far_f").relying_on(ProofId::new(0))),
    );
    far.producer = Some(Producer::TRust);
    m.try_add_function(far)
        .expect("Module::try_add_function: test fixture");
    // far_g: restates the contract, NOT `proved`; a local Discharged row
    // inherits the far obligation #1 (pushed LAST, below).
    let far_g = FuncId::new(m.functions.len() as u32);
    let mut far = Function::declaration(far_g, "far_g", far_ty, far_contract());
    far.producer = Some(Producer::TRust);
    m.try_add_function(far)
        .expect("Module::try_add_function: test fixture");

    // --- bump's summary: requires / ensures / decreases, all bound ---
    let mut summary = FunctionSummary::new()
        .with_params(vec!["x".to_string()])
        .requiring(bound(
            "(bvslt x #x7fffffffffffffff)",
            &[("x", ClauseSort::BitVec(64), ClausePlace::Param { index: 0 })],
        ))
        .ensuring(bound(
            "(and (= r (bvadd x #x0000000000000001)) (not unwound))",
            &[
                ("x", ClauseSort::BitVec(64), ClausePlace::Param { index: 0 }),
                (
                    "r",
                    ClauseSort::BitVec(64),
                    ClausePlace::ResultSlot { index: 0 },
                ),
                ("unwound", ClauseSort::Bool, ClausePlace::Unwind),
            ],
        ));
    summary.decreases.push(bound(
        "x",
        &[("x", ClauseSort::Int, ClausePlace::Param { index: 0 })],
    ));
    m.function_by_id_mut(bump).unwrap().summary = Some(summary);

    // Pending contract obligations for bump (one per clause). Since WS1.9 the
    // minter mints the `decreases` row itself (a Termination row stating the
    // measure `x`, minted last); this fixture sites that row on the `add` and
    // gives it `sited_kind` (the baseline rows re-kind it to a pre-v41 kind).
    // Before WS1.9 the row was hand-built here — same id, same formula.
    let minted =
        trust_ir_build::mint_summary_obligations(&mut m, bump).expect("fresh obligation ids");
    assert_eq!(
        minted.len(),
        3,
        "mint_summary_obligations mints requires, ensures and decreases"
    );
    let sited = minted[2].index() as usize;
    let row = &mut m.proof_obligations[sited];
    assert_eq!(row.id, minted[2]);
    assert_eq!(row.kind, ObligationKind::Termination);
    assert_eq!(
        row.formula,
        Some(bound(
            "x",
            &[("x", ClauseSort::Int, ClausePlace::Param { index: 0 })],
        ))
    );
    row.kind = sited_kind;
    row.site = Some(ObligationSite::new(bump, BlockId::new(0), 1));

    // --- layouts: struct offsets, enum direct + untagged + niche ---
    let vec_like = StructDef {
        id: StructId::new(0),
        name: "Vec".into(),
        fields: (0..3)
            .map(|i| FieldDef {
                name: format!("w{i}"),
                ty: Ty::Usize,
                offset: Some(i * 8),
            })
            .collect(),
        size: Some(24),
        align: Some(8),
        repr: StructRepr::Rust,
        origin: None,
    };
    m.add_struct(vec_like);
    let mut unop = EnumDef::new(
        EnumId::new(0),
        "UnOp",
        vec![EnumVariant {
            name: "Not".into(),
            fields: vec![Ty::Struct(StructId::new(0))],
            field_names: vec!["operand".into()],
        }],
    );
    unop.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Untagged,
        size: 24,
        align: 8,
        variant_field_offsets: vec![vec![0]],
    });
    m.add_enum(unop);
    let mut option = EnumDef::new(
        EnumId::new(1),
        "Option",
        vec![
            EnumVariant {
                name: "None".into(),
                fields: vec![],
                field_names: Vec::new(),
            },
            EnumVariant {
                name: "Some".into(),
                fields: vec![Ty::Enum(EnumId::new(0))],
                field_names: vec!["value".into()],
            },
        ],
    );
    option.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: 1,
            niche_variants_start: 0,
            niche_variants_end: 0,
            niche_start: 0,
            niche_offset: 0,
            niche_ty: EnumTagRepr::U64,
        },
        size: 24,
        align: 8,
        variant_field_offsets: vec![vec![], vec![0]],
    });
    m.add_enum(option);

    // --- v41 global residue + module-level asm ---
    m.globals.push(Global {
        name: "REGISTRY".into(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(Constant::Int(7)),
        linkage: Linkage::Internal,
        tls: None,
        align: Some(16),
        section: Some("__DATA,__b7_registry".into()),
        visibility: Visibility::Hidden,
        retained: true,
    });
    m.global_asm
        .push(".globl _b7_marker\n_b7_marker:\n  ret".into());

    if level != Level::Contract {
        let tuple_type = m
            .add_type(Ty::Tuple(vec![Ty::U8, Ty::U64, Ty::U8]))
            .expect("Module::add_type: test fixture");
        m.tuple_layouts.push(TupleLayoutDescriptor {
            tuple_type,
            size: 16,
            align: 8,
            field_offsets: vec![8, 0, 9],
        });
    }

    Surface {
        module: m,
        bump,
        far_f,
        far_g,
        import,
        sited,
    }
}

fn header_relabel(bytes: &[u8], version: u32) -> Vec<u8> {
    let mut out = bytes.to_vec();
    out[8..12].copy_from_slice(&version.to_le_bytes());
    out
}

// ---------------------------------------------------------------------------
// PASS: the three production transports are lossless for v41..v43
// ---------------------------------------------------------------------------

fn production_codecs_are_lossless_for_the_contract_surface() {
    let s = surface(Level::Handle);

    // 0. the base module is WELL-FORMED at the structural tier.
    let errors = validate_module(&s.module);
    assert!(feature_check(
        "b7.surface.validates",
        errors.is_empty(),
        &format!("validate_module(b7_surface @ handle level) errors={errors:?}"),
    ));

    // 0a. [review] the FULL surface adds the v41 cross-crate inheritance row.
    //     The structural tier never admits an external inheritance certificate
    //     (it cannot authenticate it), so it fails closed with exactly one
    //     error; only the linked tier below can validate this module.
    let full = s.with_inheritance();
    let m = &full;
    let structural = validate_module(m);
    let inherited_row = (m.proof_obligations.len() - 1) as u32;
    assert!(feature_check(
        "b7.surface.inheritance_needs_linked_tier",
        structural.len() == 1
            && matches!(&structural[0], ValidationError::DischargedWithoutCertificate { obligation }
                if *obligation == inherited_row),
        &format!(
            "validate_module(surface + InheritedFromCallee{{external}}) = {structural:?} \
             (fail-closed by design; the linked tier is the only one that admits it)"
        ),
    ));

    // 0b. [review] the STRICTEST applicable entry point. `validate_module` takes
    //     every cross-crate row on faith; `validate_linked_module` re-earns them
    //     against the real dependency under a REJECTING authority (no claim is
    //     faith-accepted): import digest, symbol + signature, exact contract
    //     restatement (bindings included), kernel-grounded far obligation.
    let dep = dep_module();
    let dep_errors = validate_module(dep);
    let set = ModuleSet::new([dep]);
    let report = validate_linked_module(m, &set, &RejectingModuleProofAuthority);
    let backed: Vec<FuncId> = report
        .authenticated()
        .map(|a| a.authenticated_backed_by().collect())
        .unwrap_or_default();
    let inherited = report
        .authenticated_certificate_refs()
        .cloned()
        .unwrap_or_default();
    assert!(feature_check(
        "b7.surface.validates_linked",
        dep_errors.is_empty()
            && report.is_ok()
            && backed == vec![s.far_f]
            && inherited.len() == 1
            && inherited.contains(&m.proof_certificates[0].lineage_ref()),
        &format!(
            "validate_module(dep)={dep_errors:?}; validate_linked_module(b7_surface, {{b7_dep}}, \
             RejectingModuleProofAuthority) errors={:?}; backed_by re-earned for {backed:?}; {} \
             inheritance certificate admitted",
            report.errors(),
            inherited.len()
        ),
    ));
    // twin: the same crate rebuilt one constant different (far_f = x + 2) is a
    // DIFFERENT module; the recorded digest no longer resolves.
    let rebuilt = build_dep(2);
    let wrong_set = ModuleSet::new([&rebuilt]);
    let errors =
        validate_linked_module(m, &wrong_set, &RejectingModuleProofAuthority).into_errors();
    assert!(feature_check(
        "b7.surface.validates_linked.negative_twin.rebuilt_dep",
        // exactly: the import cannot be resolved by digest, and — as its
        // consequence — the inheritance certificate is not admitted.
        errors.len() == 2
            && matches!(&errors[0], ValidationError::ImportUnavailable { import: 0, name } if name == "b7_dep")
            && matches!(&errors[1], ValidationError::DischargedWithoutCertificate { obligation }
                if *obligation == inherited_row),
        &format!("dep rebuilt with far_f = x + 2 => {errors:?}"),
    ));

    // 1. binary / JSON / positional MessagePack: byte-identical re-encode AND
    //    structural equality, writer selects v43.
    let rt = roundtrip_all(m);
    assert!(feature_check(
        "b7.codec.production_lossless",
        rt.lossless_production() && rt.binary_version == 43,
        &rt.summary(),
    ));

    // 2. per-surface: the DECODED module of each production format carries the
    //    exact non-default value (so equality is not vacuous).
    for trip in [&rt.binary, &rt.json, &rt.msgpack] {
        let d = trip.decoded.as_ref().expect("production decode");
        let bump = d.function_by_id(s.bump).unwrap();
        let far = d.function_by_id(s.far_f).unwrap();
        let bs = bump.summary.as_ref();
        let fs = far.summary.as_ref();
        let rows: Vec<(&str, bool)> = vec![
            (
                "summary",
                bs.is_some_and(|x| {
                    x.requires.len() == 1
                        && x.ensures.len() == 1
                        && x.decreases.len() == 1
                        && x.params == ["x"]
                        && !x.proved
                }) && fs.is_some_and(|x| x.proved && x.backed_by.is_some()),
            ),
            (
                "bindings",
                bs.is_some_and(|x| {
                    x.ensures[0].bindings.len() == 3
                        && x.ensures[0].bindings[2].1
                            == ClauseBinding {
                                sort: ClauseSort::Bool,
                                place: ClausePlace::Unwind,
                            }
                        && x.decreases[0].bindings[0].1.sort == ClauseSort::Int
                }) && d.proof_obligations[s.sited]
                    .formula
                    .as_ref()
                    .is_some_and(|f| f.bindings.len() == 1),
            ),
            (
                "imports",
                d.imports.len() == 1
                    && d.imports[0].digest
                        == dep_module().stable_digest_under(trust_ir::IdentityScheme::V2)
                    && d.imports[0].scheme == trust_ir::IdentityScheme::V2
                    && d.imports[0].producer == Some(Producer::TRust)
                    && fs.and_then(|x| x.backed_by.as_ref()).is_some_and(|r| {
                        r.symbol == "far_f" && r.obligation == Some(ProofId::new(0))
                    }),
            ),
            (
                "body_gate",
                bump.body_gate
                    == Some(BodyGate::Gated {
                        authority: "trust-verify".into(),
                        evidence: None,
                    })
                    && d.function_by_name("nat_pred").unwrap().body_gate == Some(BodyGate::Ungated)
                    && far.body_gate.is_none(),
            ),
            (
                "display_path",
                bump.display_path.as_deref() == Some("m::bump::<impl Step for i64>"),
            ),
            (
                "tuple_layouts",
                d.tuple_layouts.len() == 1 && d.tuple_layouts[0].field_offsets == [8, 0, 9],
            ),
            (
                "handle",
                d.function_by_name("nat_pred")
                    .and_then(|f| f.blocks[0].params.first())
                    .is_some_and(|(_, ty)| *ty == Ty::handle("Nat", "trust_bignum::Nat")),
            ),
            (
                "enum_layout",
                d.enums[0].layout.as_ref().map(|l| &l.encoding) == Some(&EnumTagEncoding::Untagged)
                    && matches!(
                        d.enums[1].layout.as_ref().map(|l| &l.encoding),
                        Some(EnumTagEncoding::Niche { .. })
                    )
                    && d.enums[0].variants[0].field_names == ["operand"],
            ),
            (
                "struct_offsets",
                d.structs[0]
                    .fields
                    .iter()
                    .map(|f| f.offset)
                    .collect::<Vec<_>>()
                    == [Some(0), Some(8), Some(16)]
                    && d.structs[0].fields[1].name == "w1",
            ),
            (
                "global_residue",
                d.globals[0].section.as_deref() == Some("__DATA,__b7_registry")
                    && d.globals[0].visibility == Visibility::Hidden
                    && d.globals[0].retained,
            ),
            ("global_asm", d.global_asm.len() == 1),
            (
                "obligation_site",
                d.proof_obligations[s.sited].site
                    == Some(ObligationSite::new(s.bump, BlockId::new(0), 1)),
            ),
            (
                // [review] v41 evidence tag 8: cross-crate inheritance.
                "inherited_external",
                matches!(
                    &d.proof_certificates[0].evidence,
                    ProofEvidence::InheritedFromCallee { callee, external: Some(r), .. }
                        if *callee == s.far_g
                            && r.symbol == "far_g"
                            && r.obligation == Some(ProofId::new(1))
                ),
            ),
            (
                // [review] v41 function-level ABI residue.
                "fn_abi_residue",
                bump.linkage == Linkage::LinkOnceOdr
                    && bump.attrs.target_features == ["+neon", "+crc"],
            ),
        ];
        for (surface, ok) in rows {
            assert!(feature_check(
                &format!("b7.codec.{}.{surface}", trip.format),
                ok && trip.lossless(),
                &format!(
                    "{} carries {surface} (decoded field inspected)",
                    trip.format
                ),
            ));
        }
        // The decoded module is still a VALID module.
        // [review] ... under the LINKED tier, i.e. with every cross-crate claim
        // re-earned from the decoded bytes, not taken on faith.
        let report = validate_linked_module(d, &set, &RejectingModuleProofAuthority);
        assert!(feature_check(
            &format!("b7.codec.{}.decoded_validates", trip.format),
            report.is_ok(),
            &format!(
                "validate_linked_module(decode({}), {{b7_dep}}, Rejecting) errors={:?}",
                trip.format,
                report.errors()
            ),
        ));
    }

    // 3. the identity digest is format-invariant.
    let digest = m.stable_digest();
    let same = [&rt.binary, &rt.json, &rt.msgpack]
        .iter()
        .all(|t| t.decoded.as_ref().unwrap().stable_digest() == digest);
    assert!(feature_check(
        "b7.codec.stable_digest_format_invariant",
        same,
        "stable_digest(decode(bin|json|msgpack)) == stable_digest(original)",
    ));
}

/// Negative twins of the codec PASS row: the writer's version choice is the
/// MINIMUM lossless one, and each read gate / explicit projection refuses the
/// content one version below it, with the specific error.
fn wire_version_selection_and_read_gates() {
    // legacy module (no v39+ surface at all) stays v38.
    let legacy = named_module("f");
    assert!(validate_module(&legacy).is_empty());
    let v =
        common::binary_version(&serialize_module(&legacy).expect("serialize_module: test fixture"));
    assert!(feature_check(
        "b7.wire.legacy_v38",
        v == 38,
        &format!("module with no v39+ surface => v{v}"),
    ));

    let cases = [
        (
            Level::Contract,
            41u32,
            BinaryProjectionError::ContractSurfaceRequiresV41,
        ),
        (
            Level::Tuple,
            42,
            BinaryProjectionError::TupleLayoutRequiresV42,
        ),
        (
            Level::Handle,
            43,
            BinaryProjectionError::HandleTypeRequiresV43,
        ),
    ];
    for (level, want, projection_error) in cases {
        let m = surface(level).module;
        let errors = validate_module(&m);
        assert!(
            errors.is_empty(),
            "surface level v{want} must validate: {errors:?}"
        );
        let rt = roundtrip_all(&m);
        assert!(feature_check(
            &format!("b7.wire.selects_v{want}"),
            rt.binary_version == want && rt.lossless_production(),
            &rt.summary(),
        ));

        // twin 1: an explicit v38 projection is REFUSED with the named error.
        let refused = ProjectedModuleBinaryPlan::try_new(&m, ModuleBinaryOptions::default())
            .map(|_| ())
            .err();
        assert!(feature_check(
            &format!("b7.wire.v{want}.negative_twin.raw_v38_projection"),
            refused.as_ref() == Some(&projection_error),
            &format!("RawV38 projection => {refused:?}, expected {projection_error:?}"),
        ));

        // twin 2: the same bytes labelled one version lower are refused.
        let bytes = rt.binary.encoded.clone();
        let relabelled = deserialize_module(&header_relabel(&bytes, want - 1));
        let ok = match (want, &relabelled) {
            // v43 -> v42: type tag 38 is read-gated on version >= 43.
            (43, Err(BinaryError::InvalidTag(38))) => true,
            (43, _) => false,
            // v42 -> v41: the tuple-layout section is never read, so it is
            // trailing garbage after the v41 imports section.
            (42, Err(BinaryError::InvalidData(why))) => why.contains("trailing bytes"),
            (42, _) => false,
            // v41 -> v40: there is no single "v41 section" to gate — the v41
            // per-record fields are simply not read, so the stream
            // DESYNCHRONISES. Measured on this module: InvalidTag(3). (A
            // refusal by desync, not by a dedicated gate; pinned exactly so a
            // change is seen.)
            (41, Err(BinaryError::InvalidTag(3))) => true,
            _ => false,
        };
        assert!(feature_check(
            &format!("b7.wire.v{want}.negative_twin.header_relabel"),
            ok,
            &format!(
                "v{want} bytes labelled v{} => {:?}{}",
                want - 1,
                relabelled.as_ref().map(|m| m.name.clone()),
                if want == 41 {
                    " (stream desync, no dedicated v41 gate)"
                } else {
                    ""
                }
            ),
        ));

        // twin 3: trailing bytes after the last section are refused.
        let mut trailing = bytes.clone();
        trailing.push(0);
        let refused = deserialize_module(&trailing);
        assert!(feature_check(
            &format!("b7.wire.v{want}.negative_twin.trailing_byte"),
            matches!(&refused, Err(BinaryError::InvalidData(why)) if why.contains("trailing bytes")),
            &format!(
                "bytes + 0x00 => {:?}",
                refused.as_ref().map(|m| m.name.clone())
            ),
        ));
    }
}

/// Validator negative twins: the surface that round-trips is a CHECKED
/// surface — one mutation per carried field, each refused by its own variant.
fn carried_surface_is_validated_negative_twins() {
    // summary binding: Param index past the signature.
    let mut s = surface(Level::Handle);
    let bump = s.bump;
    s.module
        .function_by_id_mut(bump)
        .unwrap()
        .summary
        .as_mut()
        .unwrap()
        .requires[0]
        .bindings[0]
        .1
        .place = ClausePlace::Param { index: 9 };
    let errors = validate_module(&s.module);
    let hit = errors.iter().any(|e| {
        matches!(e, ValidationError::InvalidFunctionSummary { detail, .. }
            if detail.contains("requires clause 0") )
    });
    assert!(feature_check(
        "b7.twin.binding_param_out_of_range",
        hit,
        &format!("{errors:?}"),
    ));

    // backed_by naming an import row that does not exist.
    let mut s = surface(Level::Handle);
    let far_f = s.far_f;
    s.module.imports.clear();
    let errors = validate_module(&s.module);
    let hit = errors
        .iter()
        .any(|e| matches!(e, ValidationError::DanglingExternRef { detail }
            if detail.contains(&format!("function #{}", far_f.index())) && detail.contains("import #0")));
    assert!(feature_check(
        "b7.twin.dangling_extern_ref",
        hit,
        &format!("{errors:?}"),
    ));

    // body_gate: blank authority.
    let mut s = surface(Level::Handle);
    s.module.function_by_id_mut(bump).unwrap().body_gate = Some(BodyGate::Gated {
        authority: "  ".into(),
        evidence: None,
    });
    let errors = validate_module(&s.module);
    let hit = errors
        .iter()
        .any(|e| matches!(e, ValidationError::InvalidBodyGate { .. }));
    assert!(feature_check(
        "b7.twin.blank_gate_authority",
        hit,
        &format!("{errors:?}")
    ));

    // tuple layout: two fields overlap.
    let mut s = surface(Level::Handle);
    s.module.tuple_layouts[0].field_offsets = vec![0, 0, 9];
    let errors = validate_module(&s.module);
    let hit = errors
        .iter()
        .any(|e| matches!(e, ValidationError::TupleLayoutInconsistent { .. }));
    assert!(feature_check(
        "b7.twin.tuple_layout_overlap",
        hit,
        &format!("{errors:?}")
    ));

    // handle: an unpinned (name, runtime) pair.
    let mut s = surface(Level::Handle);
    let forged = Ty::handle("Nat", "evil::Nat");
    let ft = s
        .module
        .add_func_type(FuncTy {
            params: vec![forged.clone()],
            returns: vec![forged.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(s.module.functions.len() as u32);
    let mut f = Function::new(id, "forged_id", ft, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((ValueId::new(0), forged));
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    f.blocks = vec![b];
    s.module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    let errors = validate_module(&s.module);
    let hit = errors
        .iter()
        .any(|e| matches!(e, ValidationError::UntrustedHandleRuntime { .. }));
    assert!(feature_check(
        "b7.twin.untrusted_handle_runtime",
        hit,
        &format!("{errors:?}")
    ));

    // obligation site: instruction index past the block.
    let mut s = surface(Level::Handle);
    let last = s.sited;
    s.module.proof_obligations[last].site = Some(ObligationSite::new(bump, BlockId::new(0), 99));
    let errors = validate_module(&s.module);
    let hit = errors
        .iter()
        .any(|e| matches!(e, ValidationError::ObligationSiteOutOfRange { .. }));
    assert!(feature_check(
        "b7.twin.site_out_of_range",
        hit,
        &format!("{errors:?}")
    ));
}

// ---------------------------------------------------------------------------
// GAP: canonical TEXT is lossy for the contract surface
// ---------------------------------------------------------------------------

fn text_drops_contract_surface() {
    // `Postcondition`, not `Termination`: canonical text cannot even PARSE the
    // v41 obligation kinds (see `text_refuses_v41_obligation_kinds`), and this
    // test is about what a text round trip that SUCCEEDS silently drops.
    let s = surface_with(Level::Handle, ObligationKind::Postcondition);
    let m = &s.module;
    assert!(validate_module(m).is_empty(), "baseline must validate");
    let rt = roundtrip_all(m);
    // WS4.2 made the loss LOUD (`#lossy`, refused by the parser); WS4.4 (the
    // proof surface) and WS4.5 (enum variant field names, `global_asm`) then
    // gave every remaining field a spelling. So the surface module now
    // round-trips through text EXACTLY: no marker, byte-identical re-encode,
    // `parse(canonical(m)) == canonicalize(m)`. `carried()` is therefore the
    // decoded module itself, and each `drops_*` row below is measured on it.
    assert!(
        rt.text.lossy.is_none() && rt.text.lossless(),
        "WS4.5: canonical text of the surface module round-trips exactly: {} (lossy {:?})",
        rt.text.summary(),
        rt.text.lossy
    );
    let lossy = rt.text.lossy.clone().unwrap_or_default();
    let text: String = String::from_utf8(rt.text.encoded.clone())
        .unwrap()
        .lines()
        .filter(|line| !line.starts_with("; #lossy:"))
        .map(|line| format!("{line}\n"))
        .collect();
    let d = rt
        .text
        .carried()
        .expect("the surface text parses once the #lossy marker is deleted");
    let canon = trust_ir::format::canonicalize(m);
    let bump = d.function_by_name("bump").unwrap();
    let far = d.function_by_name("far_f").unwrap();
    let canon_bump = canon.function_by_name("bump").unwrap();

    // --- what text DOES carry (so the GAP rows below are specific) ---
    let carried = d.imports == canon.imports
        && bump.body_gate == canon_bump.body_gate
        && bump.display_path == canon_bump.display_path
        && bump.producer == canon_bump.producer
        && d.tuple_layouts == canon.tuple_layouts
        && d.function_by_name("nat_pred").unwrap().blocks[0].params[0].1
            == Ty::handle("Nat", "trust_bignum::Nat")
        && d.proof_obligations[s.sited].site == canon.proof_obligations[s.sited].site
        && d.proof_obligations[s.sited].site.is_some()
        // [review] also carried: v41 linkage + target_features, and the
        // cross-crate `InheritedFromCallee { external }` evidence.
        && bump.linkage == Linkage::LinkOnceOdr
        && bump.attrs.target_features == ["+neon", "+crc"]
        && {
            let full = s.with_inheritance();
            let back = roundtrip_all(&full)
                .text
                .carried()
                .cloned()
                .expect("full surface text parses once the #lossy marker is deleted");
            matches!(
                &back.proof_certificates[0].evidence,
                ProofEvidence::InheritedFromCallee { external: Some(r), .. }
                    if r.symbol == "far_g" && r.obligation == Some(ProofId::new(1))
            ) && back.proof_certificates[0].evidence == full.proof_certificates[0].evidence
        };
    assert!(feature_check(
        "b7.text.carries_imports_gate_path_tuple_handle_site",
        carried,
        "text round trip preserves imports, body_gate, display_path, producer, tuple_layouts, \
         Ty::Handle, obligation site, v41 linkage (linkonce_odr) + #target_features, \
         InheritedFromCallee{external} (display.rs:128-172,437-452,279-284,575-577,1280-1290); \
         measured on the #lossy text with its marker deleted (WS4.2)",
    ));
    // twin: a body-gate directive the grammar does not know is a parse error,
    // never a silent `None`.
    let forged = text.replacen("#body-gate: gated", "#body-gate: licensed", 1);
    assert_ne!(forged, text, "the text must contain a gated directive");
    let refused = trust_ir::parser::parse_module(&forged);
    assert!(feature_check(
        "b7.text.negative_twin.unknown_body_gate",
        refused
            .as_ref()
            .err()
            .is_some_and(|e| e.to_string().contains("expected body gate")),
        &format!(
            "`#body-gate: licensed` => {:?}",
            refused.as_ref().err().map(|e| e.to_string())
        ),
    ));

    // --- FLIPPED by WS4.4 (F-064): the summary and the clause bindings ---
    // Before WS4.4 there was no FunctionSummary printer or parser arm, and the
    // parser rebuilt every obligation's bindings as `Vec::new()`
    // (UNBINDABLE); WS4.2 then refused the text as `#lossy:
    // function-summary(..), clause-bindings(..)`. Since WS4.5 carried the
    // module's last losses it is no longer refused at all, so the claim is
    // asserted on the decoded module (`d`), and the loss list must not name
    // either field. Each row's mutation control deletes the new spelling from
    // the text and gets exactly the old drop back.
    let lossy_names = |family: &str| lossy.split(", ").any(|loss| loss.starts_with(family));
    let without = |needles: &[&str]| -> Module {
        let stripped: String = text
            .lines()
            .filter(|line| !needles.iter().any(|n| line.contains(n)))
            .map(|line| format!("{line}\n"))
            .collect();
        trust_ir::parser::parse_module(&stripped).expect("the stripped text parses")
    };
    let summary_dropped = without(&[
        "; #summary:",
        "; #requires:",
        "; #ensures:",
        "; #decreases:",
        "; #backed-by:",
    ]);
    assert!(feature_check(
        "b7.text.drops_function_summary",
        canon_bump.summary.is_some()
            && bump.summary == canon_bump.summary
            && far.summary == canon.function_by_name("far_f").unwrap().summary
            && !lossy_names("function-summary(")
            && summary_dropped
                .function_by_name("bump")
                .unwrap()
                .summary
                .is_none(),
        &format!(
            "WS4.4: bump {{requires,ensures,decreases,params}} and declaration far_f \
             {{ensures,proved,backed_by}} come back equal to the canonical module's; the loss \
             list names no function-summary ({lossy}); mutation control: the `#summary` block \
             deleted => bump.summary None"
        ),
    ));

    let o_src = canon.proof_obligations[s.sited].formula.as_ref().unwrap();
    let o_txt = d.proof_obligations[s.sited].formula.as_ref().unwrap();
    let bind_line = text
        .lines()
        .find(|line| line.starts_with(&format!("obligation {} ", s.sited)))
        .expect("the sited obligation is printed")
        .to_owned();
    let unbound = {
        let at = bind_line
            .find(" bind \"")
            .expect("the sited obligation is bound");
        let rest = [" source \"", " site f", " spec \""]
            .iter()
            .filter_map(|keyword| bind_line[at..].find(keyword).map(|k| at + k))
            .min()
            .unwrap_or(bind_line.len());
        let edited = text.replacen(
            &bind_line,
            &format!("{}{}", &bind_line[..at], &bind_line[rest..]),
            1,
        );
        trust_ir::parser::parse_module(&edited).expect("the unbound text parses")
    };
    assert!(feature_check(
        "b7.text.drops_clause_bindings",
        o_src.bindings.len() == 1
            && o_txt == o_src
            && !lossy_names("clause-bindings(")
            && unbound.proof_obligations[s.sited]
                .formula
                .as_ref()
                .is_some_and(|f| f.bindings.is_empty()),
        &format!(
            "WS4.4: ProofFormula.bindings {:?} survive text (`bind \"<name>\" <sort> <place>`) \
             beside schema/payload/smtlib; mutation control: the bind list cut from the line \
             => [] (unbindable), the pre-WS4.4 drop",
            o_txt.bindings
        ),
    ));

    // WS4.5 (enum half) CLOSED THIS ROW: `enum @N { .. } layout(<encoding>
    // size=N align=N offsets=[[..], ..]) id=N`, which carries every field of
    // the `EnumLayoutDescriptor` — the NORMATIVE one, not the legacy
    // payload-offset/size projection of `enum_layout_shape`.
    //
    // The module this fixture builds now round-trips through text EXACTLY
    // (asserted above), so the claim is asserted on the DECODED module (`d`):
    // both descriptors come back byte-identical, where before both came back
    // `None`.
    assert!(feature_check(
        "b7.text.drops_enum_layout",
        canon.enums.iter().all(|e| e.layout.is_some())
            && d.enums.len() == canon.enums.len()
            && d.enums
                .iter()
                .zip(&canon.enums)
                .all(|(got, want)| got.layout == want.layout),
        &format!(
            "WS4.5: text carries both EnumLayoutDescriptors verbatim (untagged + niche) — \
             decoded layouts {:?}; the module carries no text loss at all",
            d.enums.iter().map(|e| &e.layout).collect::<Vec<_>>()
        ),
    ));
    // WS4.5 CLOSED THIS ROW (GAP -> PASS): a variant's field names print as
    // `Name(field: ty, ..)` and parse back verbatim, asserted on the decoded
    // module `d`, like the rows above.
    assert!(feature_check(
        "b7.text.drops_enum_field_names",
        canon.enums[0].variants[0].field_names == ["operand"]
            && d.enums[0].variants[0].field_names == ["operand"]
            && d.enums
                .iter()
                .zip(&canon.enums)
                .all(|(got, want)| got.variants == want.variants)
            && !rt
                .text
                .lossy
                .as_deref()
                .is_some_and(|l| l.contains("enum-field-names")),
        &format!(
            "WS4.5: EnumVariant.field_names {:?} -> {:?} through text; the #lossy summary no \
             longer names enum-field-names ({:?})",
            canon.enums[0].variants[0].field_names,
            d.enums[0].variants[0].field_names,
            rt.text.lossy
        ),
    ));

    // WS4.5 (struct half) CLOSED THIS ROW: `struct @N { name: ty @off, … }`.
    //
    // Asserted on the DECODED module (`d`, an exact round trip since WS4.5):
    // the struct's names and offsets are all present, where before every one
    // came back `""` / `None`.
    let st = &d.structs[0];
    assert!(feature_check(
        "b7.text.drops_struct_offsets_and_field_names",
        st.fields
            .iter()
            .all(|f| !f.name.is_empty() && f.offset.is_some())
            && st.fields[2].offset == Some(16)
            && st.size == Some(24)
            && st.align == Some(8),
        &format!(
            "WS4.5: text carries every struct field name and offset — fields={:?}, size={:?}, \
             align={:?}; the module carries no text loss at all",
            st.fields, st.size, st.align
        ),
    ));

    // The global subset of WS4.5 is lossless. The whole surface fixture
    // still refuses its other losses, so also exercise these exact globals
    // in a module whose text can be accepted without deleting a marker.
    let mut globals = Module::new("global_attrs");
    globals.globals = canon.globals.clone();
    let global_text = trust_ir::format::canonical_checked(&globals).unwrap();
    let global_back = trust_ir::parser::parse_module(&global_text).unwrap();
    let malformed = global_text.replacen(" retained", " retained retained", 1);
    assert_ne!(malformed, global_text);
    assert!(feature_check(
        "b7.text.drops_global_section_visibility_retained",
        d.globals == canon.globals
            && global_back == globals
            && global_back.stable_digest() == globals.stable_digest()
            && trust_ir::parser::parse_module(&malformed).is_err(),
        "exact global section/visibility/retained, linkage and align survive text; duplicate retained is refused",
    ));

    // WS4.5 CLOSED THIS ROW (GAP -> PASS, F-065): `global_asm "<escaped>"`,
    // one line per block. Asserted on the decoded module `d` (an exact round
    // trip) and on a module whose ONLY text-relevant content is the block,
    // which round-trips exactly with no marker.
    let mut asm_only = Module::new("asm_only");
    asm_only.global_asm = canon.global_asm.clone();
    let asm_rt = roundtrip_all(&asm_only).text;
    assert!(feature_check(
        "b7.text.drops_global_asm",
        canon.global_asm.len() == 1
            && d.global_asm == canon.global_asm
            && asm_rt.lossy.is_none()
            && asm_rt.lossless()
            && !rt
                .text
                .lossy
                .as_deref()
                .is_some_and(|l| l.contains("global-asm")),
        &format!(
            "WS4.5: Module.global_asm ({} block) survives text; asm-only module: {}",
            canon.global_asm.len(),
            asm_rt.summary()
        ),
    ));

    // Consequences of the loss. FLIPPED by WS4.2 (F-072's identity half): a
    // text round trip could no longer silently CHANGE a module's identity —
    // the lossy text was refused (`#lossy`). Since WS4.5 the surface module
    // carries no loss at all, so the row now requires the stronger fact: its
    // text round trip is EXACT and keeps the stable digest, and the decoded
    // module validates like the original; the loss-free twin still does too.
    let strict = rt.text.structurally_equal;
    let digest_changed = d.stable_digest() != canon.stable_digest();
    let text_errors = validate_module(d);
    let twin = named_module("f");
    let twin_text = trust_ir::format::canonical_checked(&twin);
    let twin_back = twin_text
        .as_ref()
        .ok()
        .and_then(|t| trust_ir::parser::parse_module(t).ok());
    let twin_exact = twin_back.as_ref().is_some_and(|back| {
        *back == trust_ir::format::canonicalize(&twin)
            && back.stable_digest() == twin.stable_digest()
    });
    assert!(feature_check(
        "b7.text.round_trip_changes_module_identity",
        rt.text.lossy.is_none()
            && rt.text.lossless()
            && strict
            && !digest_changed
            && text_errors.is_empty()
            && twin_exact,
        &format!(
            "WS4.5: surface module text round trip ({}): structurally_equal={strict}, digest \
             changed={digest_changed}, validate(decoded) = {} error(s); loss-free twin: \
             canonical_checked Ok and parse == canonicalize with the same stable_digest = \
             {twin_exact}",
            rt.text.summary(),
            text_errors.len()
        ),
    ));
}

/// Before WS4.2 the losses above were SILENT, so a text round trip did not
/// merely forget metadata — it changed what the validators SAY about the
/// module, in both directions. Each row: well-formed baseline, the single
/// change "serialise as canonical text and parse it back", the verdict that
/// flipped. FLIPPED by WS4.2 (F-065, and the interim guard for F-064 / F-070
/// / F-072): the round trip is now REFUSED at the `#lossy` marker naming the
/// field, so no verdict can flip through text. Each detail still records what
/// the marker-deleted copy would say (the marker is a tripwire, not
/// integrity; carrying the fields is WS4.4 / WS4.5).
fn text_round_trip_flips_validator_verdicts() {
    use trust_ir::proof::{ProofLineageId, ProofTransform, ProofTransformStage};
    use trust_ir_build::{
        certify_identity_lineage_rung, validate_module_for_codegen, validate_module_report,
        validate_module_with_authority,
    };

    // (A) `global_asm` is a codegen REFUSAL (validate.rs:8470
    //     `GlobalAsmNotConsumable`); text drops the blocks, so the refusal is
    //     laundered away.
    let mut gated = named_module("entry");
    gated.functions[0].body_gate = Some(BodyGate::Gated {
        authority: "trust-verify".into(),
        evidence: None,
    });
    let baseline = validate_module_for_codegen(&gated);
    let mut with_asm = gated.clone();
    with_asm.global_asm.push(".globl _x\n_x: ret".into());
    let before = validate_module_for_codegen(&with_asm);
    let refused_before = before
        .iter()
        .any(|e| matches!(e, ValidationError::GlobalAsmNotConsumable { blocks: 1 }));
    assert!(feature_check(
        "b7.text.flip.global_asm.refused_before",
        baseline.is_empty() && refused_before,
        &format!("codegen(no asm)={baseline:?}; codegen(with global_asm)={before:?}"),
    ));
    // WS4.2 closed this flip by REFUSING the text (`#lossy: global-asm`);
    // WS4.5 closes it for good by CARRYING the block, so the round trip is
    // exact and the codegen verdict after it is the verdict before it.
    let trip = roundtrip_all(&with_asm).text;
    let tripped = trip
        .decoded
        .clone()
        .expect("WS4.5: the text parses, no #lossy marker");
    let after = validate_module_for_codegen(&tripped);
    let asm_free = roundtrip_all(&gated).text;
    assert!(feature_check(
        "b7.text.flip.global_asm_refusal_laundered",
        refused_before
            && trip.lossy.is_none()
            && trip.lossless()
            && after == before
            && asm_free.lossless(),
        &format!(
            "validate_module_for_codegen: {before:?}; WS4.5: text round trip is EXACT ({}) and \
             codegen after it = {after:?} — the refusal survives text; asm-free twin \
             round-trips losslessly = {}",
            trip.summary(),
            asm_free.lossless()
        ),
    ));

    // (B) a proof-bearing import (`proved` + `backed_by`) is REFUSED by the
    //     authority tier (`UnauthenticatedImport`, validate.rs:206); text drops
    //     the summary, so the same module then passes the authority tier.
    //     Baseline = the base surface: `backed_by` is its ONLY proof-bearing
    //     import use, so this is a one-cause measurement.
    let s = surface_with(Level::Handle, ObligationKind::Postcondition);
    assert!(
        validate_module(&s.module).is_empty(),
        "flip (B) baseline must validate"
    );
    let before = validate_module_with_authority(&s.module, &RejectingModuleProofAuthority);
    let bearing_before = validate_module_report(&s.module)
        .proof_bearing_imports()
        .len();
    let refused_before = before.len() == 1
        && matches!(&before[0], ValidationError::UnauthenticatedImport { site, .. } if *site == "backed_by");
    assert!(feature_check(
        "b7.text.flip.unauthenticated_import.refused_before",
        refused_before && bearing_before == 1,
        &format!("authority tier on the binary-faithful module: {before:?}"),
    ));
    // FLIPPED by WS4.4 (F-064): the summary is CARRIED, so the refusal
    // SURVIVES text instead of being refused at print time (WS4.2's interim
    // guard). The surface module still carries `global_asm` and enum variant
    // field names, which text refuses for their own reasons (WS4.5), so the
    // measurement is on the same module WITHOUT those two fields: its text is
    // loss-free, round-trips exactly, and the authority tier refuses the text
    // image exactly as it refuses the binary one. Mutation control: the
    // `#backed-by` line deleted from that text removes the cross-crate
    // citation the `UnauthenticatedImport` refusal is ABOUT — the verdict
    // changes to the body-less-declaration rule's refusal of a `proved`
    // summary with `backed_by: None` (NOT RECORDED), so the line is what the
    // measured refusal rides on. (Before that rule landed on main, deleting
    // the line laundered the module to an EMPTY verdict — which is why it
    // must be carried; the declaration rule now closes that laundering too.)
    let mut transportable = s.module.clone();
    transportable.global_asm.clear();
    for e in &mut transportable.enums {
        for v in &mut e.variants {
            v.field_names.clear();
        }
    }
    let trip = roundtrip_all(&transportable).text;
    let tripped = trip.decoded.clone();
    let after = tripped
        .as_ref()
        .map(|m| validate_module_with_authority(m, &RejectingModuleProofAuthority));
    let bearing_after = tripped
        .as_ref()
        .map(|m| validate_module_report(m).proof_bearing_imports().len());
    let printed = String::from_utf8_lossy(&trip.encoded).into_owned();
    let laundered = trust_ir::parser::parse_module(
        &printed
            .lines()
            .filter(|line| !line.contains("; #backed-by:"))
            .map(|line| format!("{line}\n"))
            .collect::<String>(),
    )
    .map(|m| validate_module_with_authority(&m, &RejectingModuleProofAuthority));
    assert!(feature_check(
        "b7.text.flip.unauthenticated_import_laundered",
        refused_before
            && trip.lossless()
            && after.as_ref() == Some(&before)
            && bearing_after == Some(bearing_before)
            && laundered.as_ref().is_ok_and(|errors| {
                matches!(
                    errors.as_slice(),
                    [ValidationError::InvalidFunctionSummary { detail, .. }]
                        if detail.contains("`backed_by: None` is NOT RECORDED")
                )
            }),
        &format!(
            "validate_module_with_authority: UnauthenticatedImport; WS4.4: the text round trip \
             ({}) keeps the summary, so the text image says {after:?} and \
             proof_bearing_imports {bearing_before} -> {bearing_after:?}; mutation control, \
             `#backed-by` deleted => {laundered:?}",
            trip.summary()
        ),
    ));

    // (C) the other direction: a kernel-CERTIFIED module becomes INVALID,
    //     because text drops `CleanCic.kernel_recheck` (display.rs:1305-1308,
    //     parser.rs:3931-3933).
    let mut mb = ModuleBuilder::new("b7_certified");
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
    let mut certified = mb.build().expect("ModuleBuilder::build: test fixture");
    let (_node, obligation, certificate) = certify_identity_lineage_rung(
        &certified,
        ProofLineageId::new(0),
        ProofId::new(0),
        ProofTransform::new(ProofTransformStage::Frontend, "identity", "b7", "1.0.0"),
        f,
    )
    .expect("addmul is in the clean_backend_tv fragment");
    certified.proof_obligations.push(obligation);
    certified.proof_certificates.push(certificate);
    let before = validate_module(&certified);
    let rt = roundtrip_all(&certified);
    assert!(feature_check(
        "b7.text.flip.certified.valid_before",
        before.is_empty() && rt.lossless_production(),
        &format!("validate={before:?} {}", rt.summary()),
    ));
    // FLIPPED by WS4.4 (F-070): text CARRIES the kernel re-check directive,
    // so the Certified module survives text and re-certifies (WS4.2's interim
    // guard refused it at print time instead). Mutation control: cutting ONLY
    // the `recheck` clause from the certificate line turns the text image
    // invalid, exactly as the pre-WS4.4 grammar did.
    let recheck_of = |m: &Module| match &m.proof_certificates[0].evidence {
        ProofEvidence::CleanCic { kernel_recheck, .. } => kernel_recheck.is_some(),
        _ => false,
    };
    let tripped = rt.text.decoded.clone();
    let after = tripped.as_ref().map(validate_module);
    let printed = String::from_utf8_lossy(&rt.text.encoded).into_owned();
    let cut_errors = printed.find(" recheck module ").map(|at| {
        let end = at + printed[at..].find('\n').expect("line end");
        let dropped = format!("{}{}", &printed[..at], &printed[end..]);
        validate_module(&trust_ir::parser::parse_module(&dropped).expect("parses"))
    });
    let cut_refused = cut_errors.as_ref().is_some_and(|errors| {
        matches!(
            errors.as_slice(),
            [ValidationError::CertifiedCleanCicKernelRecheckFailed { reason, .. }]
                if reason.contains("carries no kernel-recheck directive")
        )
    });
    assert!(feature_check(
        "b7.text.flip.certified_becomes_invalid",
        before.is_empty()
            && rt.text.lossless()
            && tripped.as_ref().is_some_and(recheck_of)
            && after.as_ref().is_some_and(Vec::is_empty)
            && cut_refused,
        &format!(
            "validate_module = {before:?}; WS4.4: text round trip {} keeps kernel_recheck \
             ({} -> {:?}) and the text image validates {after:?}; mutation control, recheck \
             clause cut => {cut_errors:?}",
            rt.text.summary(),
            recheck_of(&certified),
            tripped.as_ref().map(recheck_of)
        ),
    ));

    // (D) enum layout loss vs a containing struct: `Wrapper { op: UnOp }` is
    //     24 bytes ONLY because UnOp's descriptor says untagged.
    let mut m = named_module("f");
    m.add_struct(StructDef {
        id: StructId::new(0),
        name: "Vec".into(),
        fields: (0..3)
            .map(|i| FieldDef {
                name: format!("w{i}"),
                ty: Ty::Usize,
                offset: Some(i * 8),
            })
            .collect(),
        size: Some(24),
        align: Some(8),
        repr: StructRepr::Rust,
        origin: None,
    });
    let mut unop = EnumDef::new(
        EnumId::new(0),
        "UnOp",
        vec![EnumVariant {
            name: "Not".into(),
            fields: vec![Ty::Struct(StructId::new(0))],
            field_names: vec!["operand".into()],
        }],
    );
    unop.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Untagged,
        size: 24,
        align: 8,
        variant_field_offsets: vec![vec![0]],
    });
    m.add_enum(unop);
    m.add_struct(StructDef {
        id: StructId::new(1),
        name: "Wrapper".into(),
        fields: vec![FieldDef {
            name: "op".into(),
            ty: Ty::Enum(EnumId::new(0)),
            offset: Some(0),
        }],
        size: Some(24),
        align: Some(8),
        repr: StructRepr::Rust,
        origin: None,
    });
    let before = validate_module(&m);
    let trip = roundtrip_all(&m).text;
    let tripped = trip
        .decoded
        .clone()
        .expect("WS4.5: the text parses, no #lossy marker");
    let after = validate_module(&tripped);
    let enum_bytes = |m: &Module| {
        m.ty_layout_shape(&Ty::Enum(EnumId::new(0)))
            .map(|shape| shape.size_bits / 8)
            .ok()
    };
    let wrapper_bytes = |m: &Module| {
        m.ty_layout_shape(&Ty::Struct(StructId::new(1)))
            .map(|shape| shape.size_bits / 8)
            .map_err(|e| format!("{e:?}"))
    };
    let (e_before, e_after) = (enum_bytes(&m), enum_bytes(&tripped));
    // Measured: the layout does not silently CHANGE, it becomes UNCOMPUTABLE —
    // `shape` needs the struct offsets text dropped (`MissingFieldOffset`) —
    // while `validate_module` still reports nothing, because validate.rs:7975-8086
    // never flags a struct whose offsets are `None` ("deferred to the backend").
    let w_after = wrapper_bytes(&tripped);
    // WS4.5 carried `struct-field-offsets` (struct half), the enum `layout(..)`
    // descriptor (enum half) and the enum variant field names (the
    // remainder), so this module is no longer refused at all: it round-trips
    // through text EXACTLY, and `sizeof(UnOp)` / `sizeof(Wrapper)` stay 24.
    // The archived GAP (the layout silently degraded to uncomputable) and
    // its WS4.2 interim (refused as `#lossy`) are both behind it; the
    // after-values are asserted, so a regression that drops a layout fact
    // again trips this row instead of quietly restoring the 24 -> 32 slide.
    assert!(feature_check(
        "b7.text.flip.layout_becomes_uncomputable",
        before.is_empty()
            && e_before == Some(24)
            && wrapper_bytes(&m) == Ok(24)
            && trip.lossy.is_none()
            && trip.lossless()
            && e_after == Some(24)
            && w_after == Ok(24)
            && after.is_empty(),
        &format!(
            "sizeof(UnOp) = {e_before:?}, sizeof(Wrapper) = {:?}, validate_module = {before:?}; \
             WS4.5: text round trip is EXACT ({}): sizeof(UnOp) {e_after:?}, sizeof(Wrapper) \
             {w_after:?}, validate_module {after:?}",
            wrapper_bytes(&m),
            trip.summary()
        ),
    ));
}

/// display.rs prints every `ObligationKind` (obligations.rs:344-369:
/// `termination`, `ownership`, `custom:<ns>/<name>`), but the text parser's kind
/// table stops at `give_back_refinement` (parser.rs:3643-3656) — so ANY module
/// carrying a v41 obligation kind prints text that the parser refuses.
/// Blocks: `decreases` → Termination routing (spec-surface E5), Ownership,
/// and the pinned-namespace Custom kinds, in the text artifact.
fn text_refuses_v41_obligation_kinds() {
    // Baseline: the same module with a pre-v41 kind on that row parses.
    let base = surface_with(Level::Handle, ObligationKind::Postcondition).module;
    let rt = roundtrip_all(&base);
    // WS4.2 refused this surface module's text as `#lossy` for its OTHER
    // fields; since WS4.4 + WS4.5 carry all of them, the baseline text parses
    // as printed and round-trips EXACTLY (no marker), which is strictly more
    // than the marker-deleted parse this row used to measure.
    let unmarked = rt.text.parse_unmarked();
    assert!(feature_check(
        "b7.text.obligation_kind.baseline_postcondition_parses",
        validate_module(&base).is_empty()
            && rt.text.lossy.is_none()
            && rt.text.lossless()
            && !rt
                .text
                .lossy
                .as_deref()
                .unwrap_or_default()
                .contains("obligation-kind(")
            && unmarked.is_ok(),
        &format!(
            "{}; marker deleted => parses = {}",
            rt.text.summary(),
            unmarked.is_ok()
        ),
    ));

    let kinds = [
        ("termination", ObligationKind::Termination),
        ("ownership", ObligationKind::Ownership),
        (
            "custom",
            ObligationKind::Custom {
                namespace: "trust.contract".into(),
                name: "frame".into(),
            },
        ),
    ];
    // FLIPPED by WS4.4 (F-071): the parser reads `termination`, `ownership`
    // and `custom("<ns>", "<name>")`. The kind is measured on the
    // marker-deleted parse (a no-op since WS4.5 carried the surface module's
    // other losses, so it is the text as printed): it parses, the obligation
    // kind comes back exact, and the loss list names no obligation kind. Twin:
    // a misspelled kind is still an `unknown obligation kind` refusal.
    for (id, kind) in kinds {
        let m = surface_with(Level::Handle, kind.clone()).module;
        let errors = validate_module(&m);
        let rt = roundtrip_all(&m);
        let canon = trust_ir::format::canonicalize(&m);
        let unmarked = rt.text.parse_unmarked();
        let kind_kept = unmarked.as_ref().is_ok_and(|back| {
            back.proof_obligations
                .iter()
                .zip(&canon.proof_obligations)
                .all(|(b, c)| b.kind == c.kind)
        });
        let printed = String::from_utf8_lossy(&rt.text.encoded)
            .lines()
            .filter(|line| !line.starts_with("; #lossy:"))
            .map(|line| format!("{line}\n"))
            .collect::<String>();
        let spelled = match &kind {
            ObligationKind::Custom { namespace, name } => {
                format!(" custom({namespace:?}, {name:?}) ")
            }
            other => format!(" {other} "),
        };
        let misspelled =
            trust_ir::parser::parse_module(&printed.replacen(&spelled, " frobnicate ", 1));
        assert!(feature_check(
            &format!("b7.text.refuses_obligation_kind.{id}"),
            errors.is_empty()
                && rt.lossless_production()
                && printed.contains(&spelled)
                && kind_kept
                && !rt
                    .text
                    .lossy
                    .as_deref()
                    .unwrap_or_default()
                    .contains("obligation-kind(")
                && misspelled.as_ref().is_err_and(|e| e
                    .to_string()
                    .contains("unknown obligation kind: 'frobnicate'")),
            &format!(
                "kind `{kind}` spelled `{}`: validate_module={errors:?}, bin/json/msgpack \
                 lossless; marker-deleted text parses with the kind exact = {kind_kept}; \
                 misspelled => {:?}",
                spelled.trim(),
                misspelled.err().map(|e| e.to_string())
            ),
        ));
    }
}

// ---------------------------------------------------------------------------
// GAP: TEXT cannot parse the names producers mint
// ---------------------------------------------------------------------------

fn named_module(name: &str) -> Module {
    let mut mb = ModuleBuilder::new("b7_names");
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function(name, ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let v = fb.uconst(Ty::U64, 41);
    fb.ret(vec![v]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn text_cannot_parse_minted_names() {
    // Baseline: a name inside the identifier alphabet (alnum _ . $) is
    // lossless in all FOUR formats.
    for ok_name in ["m.f", "_ZN1m1f17h0123456789abcdefE", "opendir$INODE64"] {
        let m = named_module(ok_name);
        let errors = validate_module(&m);
        let rt = roundtrip_all(&m);
        assert!(feature_check(
            &format!("b7.names.baseline.{ok_name}"),
            errors.is_empty() && rt.lossless_all(),
            &format!("validate={errors:?} {}", rt.summary()),
        ));
    }

    // parser.rs:211-231 read_ident admits only alnum/_/./$; display.rs:432
    // prints `fn @{name}` UNQUOTED. Blocks: design 08-27 text artifact must
    // round-trip every minted name.
    let minted = [
        ("rust_def_path", "m::f"),
        ("lean_primed", "step'"),
        ("rust_anon_const", "{constant#0}"),
        ("rust_impl_path", "<impl m::Step for i64>::step"),
        (
            "clean_shadowed",
            "m::cleanAdd::<shadowed-by-clean-origin:FuncId(1)>",
        ),
        ("lean_guillemet", "Nat.«add one»"),
    ];
    for (id, name) in minted {
        let m = named_module(name);
        let errors = validate_module(&m);
        let rt = roundtrip_all(&m);
        let runs = run_nullary(&m, name)
            .ok()
            .and_then(|v| v.first().and_then(common::as_u128));
        let parse_error = rt.text.decode_error.clone().unwrap_or_default();
        // WS4.3 FLIPPED THIS ROW. The printer spells a minted name quoted
        // (`fn @"m::f"`) and `Parser::read_symbol` decodes it, so the text is
        // no longer lossy and round-trips. Before WS4.3 it was refused at the
        // `#lossy` marker and, with the marker deleted, by the bare grammar.
        let _ = &parse_error;
        // WS4.17 (DG-54): the text codec is not the validator. The retired-row
        // spelling still round-trips every transport INCLUDING text (this
        // row's subject), but `validate_module` now refuses it BY NAME as
        // `SyntheticSymbolName`: a row renamed out of the namespace is not a
        // link-time symbol, and the producer must drop the orphan (WS5).
        let expected_errors = if id == "clean_shadowed" {
            vec![ValidationError::SyntheticSymbolName {
                function: m.functions[0].id.index(),
                name: name.to_string(),
            }]
        } else {
            Vec::new()
        };
        assert!(feature_check(
            &format!("b7.names.text_refuses.{id}"),
            rt.text.lossless()
                && errors == expected_errors
                && rt.lossless_production()
                && runs == Some(41),
            &format!(
                "name {name:?}: WS4.3 quotes it — validate_module={errors:?} (expected \
                 {expected_errors:?}), every transport lossless INCLUDING text, interpreter \
                 runs it (= {runs:?}); {}",
                rt.text.summary()
            ),
        ));
    }

    // The same unquoted-identifier grammar governs struct / enum / global
    // names. Rust type names carry `::`, `<`, `>`.
    let mut m = named_module("f");
    m.add_struct(StructDef {
        id: StructId::new(0),
        name: "core::option::Option<u32>".into(),
        fields: vec![FieldDef {
            name: "0".into(),
            ty: Ty::U32,
            offset: Some(0),
        }],
        size: Some(4),
        align: Some(4),
        repr: StructRepr::Rust,
        origin: None,
    });
    let errors = validate_module(&m);
    let rt = roundtrip_all(&m);
    // NOW FULLY CLOSED — by WS4.3 (the NAME) and WS4.5 (the FIELD).
    //
    // WS4.3 carried `core::option::Option<u32>` by quoting it, and this row was
    // RE-AIMED rather than flipped, because the struct's named, offset-bearing
    // FIELD still refused. WS4.5 carries the field, so the module now round-trips
    // and the row is PASS. Refusing to flip it early is what kept the two halves
    // distinguishable.
    assert!(feature_check(
        "b7.names.text_refuses.struct_type_name",
        rt.text.decode_error.is_none() && errors.is_empty() && rt.lossless_all(),
        &format!(
            "struct name \"core::option::Option<u32>\" with a named, offset-bearing field: \
             valid and lossless in ALL FOUR transports including text: {}",
            rt.summary()
        ),
    ));

    let mut m = named_module("f");
    m.globals.push(Global {
        name: "m::COUNTER".into(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(Constant::Int(0)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    let errors = validate_module(&m);
    let rt = roundtrip_all(&m);
    // WS4.3 CLOSED THIS ROW: `@"m::COUNTER"` prints quoted and parses back, so
    // every transport INCLUDING text is now lossless for a def-path global name.
    assert!(feature_check(
        "b7.names.text_refuses.global_name",
        errors.is_empty() && rt.lossless_all(),
        &format!(
            "global name \"m::COUNTER\": WS4.3 quotes it — valid and lossless in all four \
             transports: {}",
            rt.summary()
        ),
    ));

    // NEGATIVE TWIN (the harness requires one for a flipped row): the quoted
    // spelling is only accepted for a name OUTSIDE the bare alphabet. A
    // bare-able global name must be spelled bare, so its quoted form is
    // refused — that is the one-spelling rule (SPEC §3) keeping parse a
    // bijection on printer output.
    let bare_able = trust_ir::format::canonical(&{
        let mut b = named_module("f");
        b.globals.push(Global {
            name: "COUNTER".into(),
            ty: Ty::U64,
            mutable: false,
            initializer: Some(Constant::Int(0)),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Visibility::Default,
            retained: false,
        });
        b
    });
    assert!(
        bare_able.contains("@COUNTER"),
        "a bare-able global name must print bare:\n{bare_able}"
    );
    let forged = bare_able.replace("@COUNTER", "@\"COUNTER\"");
    assert!(
        trust_ir::parser::parse_module(&forged)
            .is_err_and(|e| format!("{e}").contains("must be spelled bare")),
        "the quoted spelling of a bare-able name must be refused:\n{forged}"
    );

    // The quoted slot that DOES work: `display_path` (display.rs:452, `{path:?}`).
    let mut m = named_module("m.f");
    m.functions[0].display_path = Some("m::f::{constant#0}::<impl Foo for Bar>::step'".into());
    let rt = roundtrip_all(&m);
    assert!(feature_check(
        "b7.names.display_path_is_quoted",
        validate_module(&m).is_empty() && rt.lossless_all(),
        &format!(
            "display_path with `::`, `{{`, `#`, `'`, `<` round-trips in all four: {}",
            rt.summary()
        ),
    ));
    // twin: a blank display_path is refused by the validator.
    m.functions[0].display_path = Some(" ".into());
    let errors = validate_module(&m);
    assert!(feature_check(
        "b7.names.display_path.negative_twin.blank",
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::InvalidDisplayPath { .. })),
        &format!("{errors:?}"),
    ));
}

// ---------------------------------------------------------------------------
// PASS: the text parser is total over UTF-8 (roadmap WS4.1, F-066)
//
// Four rows of the 2026-09-17 proof program measured ONE defect: Part A's
// `a.format.text_parser_utf8` (specimen `parta/attrib/text_utf8_comment.trust_ir`,
// `trust-ir validate` exit 101), the Part A reviewer's unexpected finding
// `A.uf09` (a driver file carrying an em dash), and the skeptic claim c09's
// two lenses, `verify.c09.L1` (independent reproduction: every `skip_line`
// shape, the minimal `;é`, the entry points) and `verify.c09.L2` (by design:
// a validator-clean non-ASCII link symbol printed by the crate's own printer
// could not be re-read). Each asserted a PANIC — `Parser::advance(n)` sliced
// `input[pos..pos + n]` as bytes while `skip_line` / `read_ident` stepped one
// byte per character. WS4.1 made the cursor char-safe (`bump`) and `advance`
// fallible; WS4.3 prints a non-bare-able name quoted. Each row is PASS with a
// right-reason negative twin: a non-ASCII character in a TOKEN position is a
// located `ParseError`, never a panic and never the fallible cursor's
// `internal: cursor split` refusal (which only a scanner stepping a byte
// through a multi-byte character can produce).
//
// The mutation control is the `parse_never_panics` leg of
// `module_roundtrip_fuzz` (gate 8): it fails on a panic, on any cursor-split
// refusal, and when an in-comment insertion changes the module. The in-crate
// per-site tests are `module_roundtrip_fuzz`'s `text_parser_utf8` module.
// ---------------------------------------------------------------------------

/// What one parse did, with a panic CAPTURED (a regression must record FAIL
/// on its row, not abort the case).
#[derive(Debug)]
enum Parsed<T> {
    Ok(T),
    Err(trust_ir::parser::ParseError),
    Panicked(String),
}

fn parse_caught_with<T>(
    text: &str,
    parse: impl FnOnce(&str) -> Result<T, trust_ir::parser::ParseError>,
) -> Parsed<T> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| parse(text))) {
        Ok(Ok(value)) => Parsed::Ok(value),
        Ok(Err(err)) => Parsed::Err(err),
        Err(payload) => Parsed::Panicked(
            payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_string()))
                .unwrap_or_else(|| "<non-string panic payload>".to_string()),
        ),
    }
}

fn parse_text(text: &str) -> Parsed<Module> {
    parse_caught_with(text, trust_ir::parser::parse_module)
}

/// The fallible cursor's refusal; the correct parser never produces it.
const CURSOR_SPLIT: &str = "internal: cursor split";

impl<T> Parsed<T> {
    /// `Ok` with exactly `want`.
    fn is_ok_eq(&self, want: &T) -> bool
    where
        T: PartialEq,
    {
        matches!(self, Parsed::Ok(got) if got == want)
    }

    /// A located `ParseError` at `(line, col)` whose message contains
    /// `needle` — never a panic, never a cursor split.
    fn is_located_err(&self, line: usize, col: usize, needle: &str) -> bool {
        matches!(self, Parsed::Err(e)
            if (e.line, e.col) == (line, col)
                && e.message.contains(needle)
                && !e.message.contains(CURSOR_SPLIT))
    }

    /// A clean outcome: `Ok`, or a `ParseError` that is not a cursor split.
    fn is_total(&self) -> bool {
        match self {
            Parsed::Ok(_) => true,
            Parsed::Err(e) => !e.message.contains(CURSOR_SPLIT),
            Parsed::Panicked(_) => false,
        }
    }

    fn render(&self) -> String {
        match self {
            Parsed::Ok(_) => "Ok".to_string(),
            Parsed::Err(e) => format!("Err({e})"),
            Parsed::Panicked(p) => format!("PANICKED({p})"),
        }
    }
}

/// Insert `line` before the first line containing `anchor`.
fn line_before(text: &str, anchor: &str, line: &str) -> String {
    let mut lines: Vec<&str> = text.lines().collect();
    let idx = lines
        .iter()
        .position(|l| l.contains(anchor))
        .unwrap_or_else(|| panic!("no line containing {anchor:?} in:\n{text}"));
    lines.insert(idx, line);
    lines.join("\n") + "\n"
}

/// Append `suffix` to the first line containing `anchor`.
fn line_suffix(text: &str, anchor: &str, suffix: &str) -> String {
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    let idx = lines
        .iter()
        .position(|l| l.contains(anchor))
        .unwrap_or_else(|| panic!("no line containing {anchor:?} in:\n{text}"));
    lines[idx].push_str(suffix);
    lines.join("\n") + "\n"
}

/// The 1-based line of the `fn @` header in `text`.
fn fn_header_line(text: &str) -> usize {
    text.lines()
        .position(|l| l.starts_with("fn @"))
        .expect("a function header")
        + 1
}

fn text_parser_is_total_over_utf8() {
    // 2-, 3- and 4-byte scalars, and a combining mark.
    let chars = ['\u{e9}', '\u{2192}', '\u{2014}', '\u{1f600}', '\u{301}'];

    // --- a.format.text_parser_utf8: Part A's exact specimen. ------------------
    let specimen = "; TrustIr text format v1\n\
                    ; a comment with one multi-byte character: \u{2014}\n\
                    module \"parta-utf8-comment\"\n";
    let parsed = parse_text(specimen);
    let specimen_ok = matches!(&parsed, Parsed::Ok(m)
        if m.name == "parta-utf8-comment" && m.functions.is_empty());
    // Negative twin, one change: the em dash moves out of the comment into
    // the token position where `module` must be. Refused, located at 1:1.
    let twin = parse_text("\u{2014}\nmodule \"parta-utf8-comment\"\n");
    let twin_ok = twin.is_located_err(1, 1, "expected 'module'");
    assert!(feature_check(
        "a.format.text_parser_utf8",
        specimen_ok && twin_ok,
        &format!(
            "Part A specimen (em dash in a `;` comment) => {} (was exit 101, a panic at \
             parser.rs advance); twin (em dash where `module` must be) => {}",
            parsed.render(),
            twin.render()
        ),
    ));

    // --- A.uf09: a real driver-shaped module behind an em-dash comment. ------
    // The reviewer's driver carried an em dash in its comments; the finding is
    // that ANY comment position crashed the parse. The grammar admits a plain
    // `;` comment in three places — the header, between top-level items, and
    // trailing an instruction (`parse_node_comments`); a standalone `;` line
    // inside a function body is not a comment position even in ASCII. Every
    // admitted shape must parse to the ASCII baseline; the ASCII `e` run of
    // the same shapes is the control that each IS an admitted position.
    let module = named_module("m.driver");
    let text = module.to_string();
    let baseline = parse_text(&text);
    let baseline_ok = baseline.is_ok_eq(&module);
    let comment_shapes = |ch: char| {
        [
            format!("; driver {ch} header\n{text}"),
            line_before(&text, "fn @", &format!("; {ch} between top-level items")),
            line_suffix(&text, "= const", &format!(" ; {ch} on an instruction")),
            line_suffix(&text, "ret ", &format!(" ; {ch}")),
            format!("{text}; trailing {ch}\n"),
        ]
    };
    let mut uf09_bad = Vec::new();
    for ch in std::iter::once('e').chain(chars) {
        for shape in comment_shapes(ch) {
            let got = parse_text(&shape);
            if !got.is_ok_eq(&module) {
                uf09_bad.push(format!("{ch:?}: {} for\n{shape}", got.render()));
            }
        }
    }
    // Negative twin: the em dash on a line that is NOT a comment (an unknown
    // top-level line) is refused by name — WS4.2 — never skipped, never a panic.
    let unknown = parse_text(&format!("{text}zzz \u{2014}\n"));
    let unknown_line = text.lines().count() + 1;
    let uf09_twin_ok = unknown.is_located_err(unknown_line, 1, "unknown directive `zzz`");
    assert!(feature_check(
        "A.uf09",
        baseline_ok && uf09_bad.is_empty() && uf09_twin_ok,
        &format!(
            "baseline Display->parse equal={baseline_ok}; {} comment shapes x (ASCII control + \
             {} scalars), mismatches {uf09_bad:?}; twin (unknown top-level `zzz \u{2014}`) => {}",
            comment_shapes('e').len(),
            chars.len(),
            unknown.render()
        ),
    ));

    // --- verify.c09.L1: the independent reproduction's every measurement. ----
    let seven = named_module("seven");
    let seven_text = seven.to_string();
    let mut l1 = Vec::new();
    for ch in chars {
        // Leading comment, the reproduction's single change.
        let leading = parse_text(&format!("; {ch}\n{seven_text}"));
        l1.push((
            format!("leading `; {ch}`"),
            leading.is_ok_eq(&seven),
            leading.render(),
        ));
        // Trailing after the module; between top-level items.
        let trailing = parse_text(&format!("{seven_text}; {ch}\n"));
        l1.push((
            format!("trailing `; {ch}`"),
            trailing.is_ok_eq(&seven),
            trailing.render(),
        ));
        let between = parse_text(&line_before(&seven_text, "fn @", &format!("; caf{ch}")));
        l1.push((
            format!("between items `; caf{ch}`"),
            between.is_ok_eq(&seven),
            between.render(),
        ));
        // Node comments (the reproduction's `parser.rs:1524` site) on both
        // instructions of the body.
        let on_const = parse_text(&line_suffix(&seven_text, "= const", &format!(" ; caf{ch}")));
        l1.push((
            format!("node comment `const ... ; caf{ch}`"),
            on_const.is_ok_eq(&seven),
            on_const.render(),
        ));
        let node = parse_text(&line_suffix(&seven_text, "ret ", &format!(" ; {ch}")));
        l1.push((
            format!("node comment `ret %0 ; {ch}`"),
            node.is_ok_eq(&seven),
            node.render(),
        ));
        // The minimal input `;é` (a comment then EOF): no `module` line.
        let minimal = parse_text(&format!(";{ch}"));
        l1.push((
            format!("minimal `;{ch}`"),
            // `;` + one scalar is two characters: EOF is at 1:3.
            minimal.is_located_err(1, 3, "expected 'module'"),
            minimal.render(),
        ));
        // The single-function entry point: never a panic, never a split.
        let one_fn = parse_caught_with(&format!("; {ch}\n"), trust_ir::parser::parse_function);
        l1.push((
            format!("parse_function(`; {ch}`)"),
            one_fn.is_total(),
            one_fn.render(),
        ));
    }
    // A non-ASCII module name (quoted) and display path round-trip.
    let mut named = named_module("seven");
    named.name = "m\u{e9}".to_string();
    named.functions[0].display_path = Some("crate::caf\u{e9}::\u{2192}".to_string());
    let quoted = parse_text(&named.to_string());
    l1.push((
        "quoted module name + display_path".to_string(),
        quoted.is_ok_eq(&named),
        quoted.render(),
    ));
    let l1_bad: Vec<String> = l1
        .iter()
        .filter(|(_, ok, _)| !ok)
        .map(|(what, _, got)| format!("{what} => {got}"))
        .collect();
    // Negative twin: a bare `é` at the top level (not a comment) is refused.
    let bare = parse_text(&format!("\u{e9}\n{seven_text}"));
    let bare_ok = bare.is_located_err(1, 1, "expected 'module'");
    assert!(feature_check(
        "verify.c09.L1",
        l1_bad.is_empty() && bare_ok,
        &format!(
            "{} reproduction measurements, failures {l1_bad:?}; twin (bare `\u{e9}` before \
             `module`) => {}",
            l1.len(),
            bare.render()
        ),
    ));

    // --- verify.c09.L2: the by-design lens — the crate's OWN output. ---------
    // A validator-clean module whose link symbol is non-ASCII (Lean/Clean
    // names routinely are) must re-parse from Display and from
    // `format::canonical`. WS4.1 made the bare alphabet ASCII (no panic);
    // WS4.3 prints such a name quoted, so it round-trips.
    let mut l2 = Vec::new();
    let mut twins = Vec::new();
    for name in ["caf\u{e9}", "\u{3b1}", "List.map\u{3b1}", "Nat.add\u{271d}"] {
        let m = named_module(name);
        let valid = validate_module(&m).is_empty();
        let shown = m.to_string();
        let via_display = parse_text(&shown);
        let via_canonical = parse_text(&trust_ir::format::canonical(&m));
        l2.push((
            name,
            valid && via_display.is_ok_eq(&m) && via_canonical.is_ok_eq(&m),
            format!(
                "valid={valid} display={} canonical={}",
                via_display.render(),
                via_canonical.render()
            ),
        ));
        // Negative twin: the BARE spelling of the same name (the pre-WS4.3
        // printer output) is a located error AT the first non-ASCII-alphabet
        // character, never a panic and never a different name.
        let quoted_head = format!("fn @{name:?}(");
        let bare_text = shown.replacen(&quoted_head, &format!("fn @{name}("), 1);
        let offending = name
            .chars()
            .position(|c| !(c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '$')))
            .expect("a non-ASCII name");
        let col = "fn @".chars().count() + offending + 1;
        let got = parse_text(&bare_text);
        let located = matches!(&got, Parsed::Err(e)
            if (e.line, e.col) == (fn_header_line(&bare_text), col)
                && !e.message.contains(CURSOR_SPLIT));
        twins.push((name, shown.contains(&quoted_head) && located, got.render()));
    }
    let l2_bad: Vec<String> = l2
        .iter()
        .filter(|(_, ok, _)| !ok)
        .map(|(n, _, got)| format!("{n:?}: {got}"))
        .collect();
    let twin_bad: Vec<String> = twins
        .iter()
        .filter(|(_, ok, _)| !ok)
        .map(|(n, _, got)| format!("{n:?} bare: {got}"))
        .collect();
    assert!(feature_check(
        "verify.c09.L2",
        l2_bad.is_empty() && twin_bad.is_empty(),
        &format!(
            "{} non-ASCII link symbols validate and re-parse from Display and \
             format::canonical (was: a panic at read_ident); failures {l2_bad:?}; \
             bare-spelling twins {twin_bad:?}",
            l2.len()
        ),
    ));
}

// ---------------------------------------------------------------------------
// Harness inputs (F-034). RATIFIED by WS2.11 — docs/SPEC_RATIFICATIONS.md
// "Harness inputs": a verification harness is a function named by the
// verification request, its PARAMETERS are the nondeterministic inputs
// (universally quantified over their `Ty`'s value domain), an unbounded
// stream of `any()` is a `(ptr, len)` tape parameter read through memory, and
// `Assume` on inputs is a vacuity filter (`AssumeViolated`). No new `Inst`,
// no input oracle, no wire change. The rows below that once measured the
// ABSENCE of a choice op / oracle are held in their exact shape as
// RATIFIED-OUT: a choice opcode or an interpreter oracle appearing would trip
// them and force the ratification to be amended first.
// ---------------------------------------------------------------------------

/// `pick() -> u64` whose value comes from `source`.
enum Source {
    Const,
    Undef,
    HavocUndef,
    DialectChoice,
    /// [review] the Kani-style carrier: a call to a body-less `nondet_u64()`.
    ExternCall,
}

fn pick_module(source: Source) -> Module {
    // A body-less external declaration requires target info
    // (`TargetInfoRequired`), so only that variant carries one.
    let mut mb = if matches!(source, Source::ExternCall) {
        ModuleBuilder::new_with_target_info("b7_nondet", target())
    } else {
        ModuleBuilder::new("b7_nondet")
    };
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let nondet =
        matches!(source, Source::ExternCall).then(|| mb.declare_function("nondet_u64", ft));
    let mut fb = mb.function("pick", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let v = match source {
        Source::ExternCall => fb.call(nondet.unwrap(), vec![]),
        Source::Const => fb.uconst(Ty::U64, 5),
        Source::Undef => fb.undef(Ty::U64),
        Source::HavocUndef => fb.undef_proven(Ty::U64, vec![ProofAnnotation::FreshSymbolicHavoc]),
        Source::DialectChoice => {
            let mut op = DialectInst::new("verif", "choose");
            op.result_tys = vec![Ty::U64];
            fb.dialect_op(op)[0]
        }
    };
    let one = fb.uconst(Ty::U64, 1);
    let out = fb.binop(trust_ir::BinOp::And, Ty::U64, v, one);
    fb.ret(vec![out]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn no_typed_nondeterministic_choice() {
    // Baseline: the well-formed deterministic twin validates and runs.
    let base = pick_module(Source::Const);
    let got = run_nullary(&base, "pick");
    assert!(feature_check(
        "b7.nondet.baseline_const",
        validate_module(&base).is_empty()
            && got
                .as_ref()
                .ok()
                .and_then(|v| v.first())
                .and_then(common::as_u128)
                == Some(1),
        &format!("pick() with Const 5 => {got:?}"),
    ));

    // (a) the instruction set has no choice/input/nondet/havoc opcode. Read
    //     from SOURCE (read-only): crates/trust-ir/src/inst.rs `pub enum Inst`.
    //     RATIFIED (entry-parameter model, SPEC "Harness inputs"): inputs are
    //     entry parameters, so there is deliberately no such opcode, and the
    //     Lean MetaTheorems determinism property ("no nondeterminism source")
    //     is preserved. Held exactly: a new choice-like variant trips it.
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../trust-ir/src/inst.rs"
    ))
    .expect("trust-ir source is readable");
    let variants = enum_variants(&src, "pub enum InstG<X> {");
    let suspicious: Vec<&String> = variants
        .iter()
        .filter(|v| {
            let l = v.to_lowercase();
            [
                "choice", "choose", "input", "nondet", "havoc", "any", "fresh", "oracle",
                "symbolic",
            ]
            .iter()
            .any(|k| l.contains(k))
        })
        .collect();
    // The variant COUNT is incidental to this row (it records the enum's
    // size when the row was cut, so an unrelated opcode landing is visible
    // in review): 57 -> 58 at WS3.5 (`MakeAggregate`, an aggregate
    // constructor) and 58 -> 60 at WS3.20 (`MemCopy`/`MemSet`, bulk memory)
    // — none a choice/input opcode — and 60 -> 61 with the crystal lane's
    // `Drop` (a destructor; both engines refuse it). The crystal lane's WEAK
    // `CmpXchg` (D3) adds no opcode: it is a flag on an existing variant, and
    // although a weak compare-exchange is semantically nondeterministic
    // (spurious failure), BOTH engines refuse it (`unsupported.weak_cmpxchg`),
    // so neither executable model gains a nondeterminism source. 61 -> 62 at
    // v50 (`ArraySplat`, `n` copies of one register value — a deterministic
    // constructor). 62 -> 64 at v53 (`CallCannotUnwind` /
    // `CallIndirectCannotUnwind`, a call with a no-crossing unwind boundary
    // — deterministic) and 64 -> 65 at v54 (`AssertInvoke`, amendment P: a sited
    // check with an unwind edge — deterministic; its failure is the terminal
    // panic outcome and its unwind edge is never taken). 65 -> 66 at v55
    // (`DropInvoke`, amendment D: a drop with an unwind edge — deterministic)
    // and 66 -> 67 at v56 (`InvokeIndirect`, amendment D Part 2: an indirect
    // call with an unwind edge — deterministic; under `PanicStrategy::Unwind`
    // the edge is taken exactly when the callee raises, a deterministic
    // consequence of a failed check, never a choice). 67 -> 68 at v63
    // (`MakeClosure`, a runtime closure constructor — deterministic) and
    // 68 -> 69 at the tensor region (`TensorContract`, an integer tensor
    // contraction whose wrapping sum has a pinned fold order — deterministic;
    // mismatched extents are undefined behaviour, never a choice). 69 -> 72 at
    // v68 (`TensorMap` / `TensorReduce` / `TensorView`: an element-wise map
    // through the scalar instructions' own evaluators, a reduction whose fold
    // order is pinned by `TensorReduceOrder::RowMajor`, and an affine view
    // whose out-of-range coordinates read a fill or are undefined behaviour —
    // all deterministic, none a choice). 72 -> 74 at v69 (`TensorGather` /
    // `TensorScatter`: a read at data coordinates, and a write whose repeated
    // coordinates keep the row-major-last source element — deterministic;
    // an out-of-range coordinate is undefined behaviour, never a choice).
    // The absence itself is now RATIFIED (F-034, WS2.11), not a gap.
    assert!(feature_ratified(
        "b7.nondet.no_choice_opcode",
        Expect::measured("74 Inst variants, none a choice/input/nondet/havoc opcode"),
        Outcome::measured(format!(
            "{} Inst variants, {}",
            variants.len(),
            if suspicious.is_empty() {
                "none a choice/input/nondet/havoc opcode".to_string()
            } else {
                format!("suspicious {suspicious:?}")
            }
        )),
        &format!(
            "RATIFIED (entry-parameter model, SPEC \"Harness inputs\"): inst.rs `enum Inst`: {} \
             variants, none named choice/input/nondet/havoc/any/fresh (matches: {suspicious:?}); \
             s3 Kani `any` / E7 harness nondet are entry parameters, not an opcode",
            variants.len()
        ),
    ));

    // (b) the closest spelling, `Inst::Undef`, VALIDATES; since WS2.10 it is
    //     POISON (ub-numerics-policy §4): executing it is not UB, and the `and`
    //     that inspects it is. Flipped GAP -> PASS "Undef is poison; inspection
    //     is UB". It was never an input source and still is not one: the
    //     verdict is UB for the inspection, never a chosen value. Right-reason
    //     negative twin: the baseline `Const` twin above runs to 1, and the UB
    //     here names the inspection, not the retired eager "executing undef".
    let undef = pick_module(Source::Undef);
    let run = run_nullary(&undef, "pick");
    let reason = run.as_ref().err().cloned().unwrap_or_default();
    assert!(feature_check(
        "b7.nondet.undef_executes_as_ub",
        validate_module(&undef).is_empty()
            && reason.contains("UndefinedBehavior")
            && reason.contains("use of an uninitialized value")
            && !reason.contains("executing undef"),
        &format!("Undef is poison; inspection is UB: validate_module=[] ; interpreter => {run:?}"),
    ));

    // (c) `FreshSymbolicHavoc` is INERT: same UB, excluded from the
    //     lowering-target subset (bridge.rs `proof_annotation_excluded`), and
    //     it still round-trips — a marker, not semantics (annotations.rs).
    //     RATIFIED (SPEC "Harness inputs"): the marker grants nothing — it is
    //     not a harness input and admits the node into no subset; since
    //     WS2.11 its PLACEMENT is checked (`HavocMarkerMisplaced`), which is
    //     why "the marked module validates" is part of the held shape.
    let havoc = pick_module(Source::HavocUndef);
    let run = run_nullary(&havoc, "pick");
    let rt = roundtrip_all(&havoc);
    let subset = havoc.check_conformance_subset();
    let subset_reason = subset
        .as_ref()
        .err()
        .map(|v| v.iter().map(|x| x.reason.to_string()).collect::<Vec<_>>())
        .unwrap_or_default();
    assert!(feature_ratified(
        "b7.nondet.fresh_symbolic_havoc_is_inert",
        Expect::refused("UndefinedBehavior"),
        Outcome::of_message(&run).given(&[
            (
                "the marked module validates",
                validate_module(&havoc).is_empty()
            ),
            ("it round-trips in all four formats", rt.lossless_all()),
            (
                "the subset refuses the marker",
                subset_reason
                    .iter()
                    .any(|r| r.contains("FreshSymbolicHavoc is not ratified"))
            ),
        ]),
        &format!(
            "RATIFIED (SPEC \"Harness inputs\": the marker grants nothing): Undef+FreshSymbolicHavoc \
             validates, 4-format lossless, interpreter => {run:?}, conformance subset => \
             {subset_reason:?}"
        ),
    ));
    // Consequence: the UNMARKED `Undef` (poison, WS2.10) is INSIDE the
    // lowering-target subset, the marked havoc is OUTSIDE it. RATIFIED (SPEC
    // "Harness inputs", mutation control): the marker is not ratified into the
    // subset and grants nothing, so the marked node stays outside; the
    // unmarked poison is in-subset on its own (proven) semantics. Held
    // exactly: admitting the marker into the subset trips this row.
    let plain_subset = undef.check_conformance_subset();
    assert!(feature_ratified(
        "b7.nondet.unmarked_undef_is_in_subset_marked_is_not",
        Expect::Accepted,
        Outcome::of_result(&plain_subset)
            .given(&[("the marked havoc is outside the subset", subset.is_err())]),
        &format!(
            "RATIFIED (SPEC \"Harness inputs\", mutation control): check_conformance_subset: plain \
             Undef => {:?}; Undef+FreshSymbolicHavoc => refused",
            plain_subset
                .as_ref()
                .map_err(|v| v.iter().map(|x| x.reason).collect::<Vec<_>>())
        ),
    ));

    // (c') the marker IS placement-checked since WS2.11: on a Const (no Undef
    //      in sight) the validator refuses it by name, `HavocMarkerMisplaced`
    //      naming the marker and the node. Flipped GAP -> PASS. Right-reason
    //      negative twin: the SAME marker on the `Undef` above validates
    //      (`havoc` is the module (c) measured, validate_module=[]), so the
    //      refusal is about the placement, not the marker.
    let mut misplaced = pick_module(Source::Const);
    misplaced.functions[0].blocks[0].body[0]
        .proofs
        .push(ProofAnnotation::FreshSymbolicHavoc);
    let errors = validate_module(&misplaced);
    let misplaced_named = errors.iter().any(|e| {
        matches!(
            e,
            ValidationError::HavocMarkerMisplaced { marker, location }
                if *marker == "FreshSymbolicHavoc" && location.contains("const")
        )
    });
    assert!(feature_check(
        "b7.nondet.havoc_marker_placement_unchecked",
        misplaced_named && errors.len() == 1 && validate_module(&havoc).is_empty(),
        &format!(
            "FreshSymbolicHavoc on a `Const 5`: validate_module={errors:?}; the twin on `Undef` \
             validates (marker legal there, refusal is placement)"
        ),
    ));

    // (d) `b7.nondet.interpreter_has_no_input_oracle` is a compile-time ratchet in
    //     `field_ratchets.rs` (RATIFIED-OUT since WS2.11).

    // (e) an opaque dialect op is the only other carrier: it validates and
    //     round-trips but no consumer executes it. RATIFIED (SPEC "Harness
    //     inputs"): a `DialectOp` is never a harness input; the interpreter's
    //     `UnsupportedDialectOp` is the fail-closed verdict, held exactly.
    let dialect = pick_module(Source::DialectChoice);
    let errors = validate_module(&dialect);
    let run = run_nullary(&dialect, "pick");
    let rt = roundtrip_all(&dialect);
    assert!(feature_ratified(
        "b7.nondet.dialect_op_is_opaque",
        Expect::refused("UnsupportedDialectOp"),
        Outcome::of_message(&run).given(&[
            ("the dialect module validates", errors.is_empty()),
            ("bin/json/msgpack are lossless", rt.lossless_production()),
        ]),
        &format!(
            "RATIFIED (SPEC \"Harness inputs\"): `verif.choose` DialectOp: validate={errors:?}, {} ; \
             interpreter => {run:?}",
            rt.summary()
        ),
    ));

    // (e') [review] the Kani-style carrier — a call to a body-less
    //      `nondet_u64()` declaration — is equally unexecutable. Since WS2.12
    //      the interpreter has a host-call hook (`Interpreter::with_host`), but
    //      no host model is registered for `nondet_u64`, so the call is the
    //      named, fail-closed `UnsupportedCall` (before the hook it entered the
    //      declaration and trapped `MissingBlock` on its absent bb0). RATIFIED
    //      (SPEC "Harness inputs" + §5): a bodyless extern call is not a
    //      harness input — inputs are entry parameters — and executing a
    //      declaration is the named, fail-closed `UnsupportedCall`. Held
    //      exactly: an interpreter that started inventing a value here trips it.
    let ext = pick_module(Source::ExternCall);
    let errors = validate_module(&ext);
    let run = run_nullary(&ext, "pick");
    let rt = roundtrip_all(&ext);
    assert!(feature_ratified(
        "b7.nondet.extern_nondet_call_is_unexecutable",
        Expect::refused_with(
            "UnsupportedCall",
            &["call to bodyless declaration @nondet_u64: no host model"],
        ),
        Outcome::of_message(&run).given(&[
            ("the extern-call module validates", errors.is_empty()),
            ("it round-trips in all four formats", rt.lossless_all()),
        ]),
        &format!(
            "RATIFIED (SPEC \"Harness inputs\"): call to body-less `nondet_u64()`: validate={errors:?}, \
             4-format lossless={}, interpreter => {run:?}",
            rt.lossless_all()
        ),
    ));

    // (f) what DOES work: an explicit input model via entry-block parameters.
    let mut mb = ModuleBuilder::new("b7_input");
    let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("harness", ft);
    let entry = fb.create_block();
    let any = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let one = fb.uconst(Ty::U64, 1);
    let out = fb.binop(trust_ir::BinOp::And, Ty::U64, any, one);
    fb.ret(vec![out]);
    fb.build();
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    let outs: Vec<Option<u128>> = [6i128, 7]
        .iter()
        .map(|v| {
            run_with_args(
                &m,
                "harness",
                vec![InterpretValue::int(Ty::U64, *v).unwrap()],
            )
            .ok()
            .and_then(|r| r.first().and_then(common::as_u128))
        })
        .collect();
    assert!(feature_check(
        "b7.nondet.param_as_input",
        validate_module(&m).is_empty() && outs == [Some(0), Some(1)],
        &format!(
            "harness(any) with any=6,7 => {outs:?} (inputs only at the ENTRY, never mid-body)"
        ),
    ));
    // twin: an input of the wrong type is refused by the interpreter.
    let wrong = run_with_args(&m, "harness", vec![InterpretValue::bool(true)]);
    assert!(feature_check(
        "b7.nondet.param_as_input.negative_twin",
        wrong
            .as_ref()
            .err()
            .is_some_and(|e| e.starts_with("SignatureMismatch")),
        &format!("harness(true: Bool) => {wrong:?}"),
    ));

    // (g) `Assume` on an input is the harness's VACUITY FILTER (WS2.11): an
    //     input outside the assumed domain is `AssumeViolated`, a named code
    //     apart from program UB, so a driver can classify it. `harness(x)`
    //     assumes `x < 10` and returns `x & 1`.
    let mut mb = ModuleBuilder::new("b7_assume");
    let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("harness", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let ten = fb.uconst(Ty::U64, 10);
    let in_domain = fb.icmp(trust_ir::ICmpOp::Ult, Ty::U64, x, ten);
    fb.assume(in_domain);
    let one = fb.uconst(Ty::U64, 1);
    let out = fb.binop(trust_ir::BinOp::And, Ty::U64, x, one);
    fb.ret(vec![out]);
    fb.build();
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    let outside = run_with_args(
        &m,
        "harness",
        vec![InterpretValue::int(Ty::U64, 20).unwrap()],
    );
    assert!(feature_check(
        "b7.nondet.assume_is_a_vacuity_filter",
        validate_module(&m).is_empty()
            && outside.as_ref().err().is_some_and(|e| {
                e.starts_with("AssumeViolated") && !e.starts_with("UndefinedBehavior")
            }),
        &format!(
            "harness(20) with `assume x < 10` => {outside:?} (AssumeViolated, not generic UB)"
        ),
    ));
    // twin: an input inside the domain runs to its value.
    let inside = run_with_args(
        &m,
        "harness",
        vec![InterpretValue::int(Ty::U64, 7).unwrap()],
    )
    .ok()
    .and_then(|r| r.first().and_then(common::as_u128));
    assert!(feature_check(
        "b7.nondet.assume_is_a_vacuity_filter.negative_twin",
        inside == Some(1),
        &format!("harness(7) with `assume x < 10` => {inside:?}"),
    ));
}

/// Top-level variant names of `header` (a `pub enum X {` line) in `src`:
/// lines at exactly four spaces of indentation starting with an uppercase
/// identifier, until the closing `}` at column 0.
fn enum_variants(src: &str, header: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut inside = false;
    for line in src.lines() {
        if !inside {
            inside = line.starts_with(header);
            continue;
        }
        if line.starts_with('}') {
            break;
        }
        if let Some(rest) = line.strip_prefix("    ")
            && rest.chars().next().is_some_and(|c| c.is_ascii_uppercase())
        {
            let name: String = rest
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            out.push(name);
        }
    }
    out
}

// ---------------------------------------------------------------------------
// GAP: SpecModule invariants are opaque strings
// ---------------------------------------------------------------------------

fn spec_module(formula: &str, var_ty: &str) -> Module {
    let mut m = named_module("step");
    let mut spec = SpecModule::design_only("Counter");
    spec.vars.push(SpecVar::new("n", var_ty));
    spec.actions.push("Step".into());
    spec.invariants.push(SpecInvariant::new("Bounded", formula));
    m.spec_modules.push(spec);
    m
}

fn type_name_of<T>(_: &T) -> &'static str {
    std::any::type_name::<T>()
}

fn spec_invariants_are_opaque_strings() {
    // PASS: a TLA-shaped spec module is CARRIED (as text) in all four formats.
    let good = spec_module("[](n >= 0) /\\ <>(n = 7)", "0..7");
    let errors = validate_module(&good);
    let rt = roundtrip_all(&good);
    assert!(feature_check(
        "b7.spec.carried_in_four_formats",
        errors.is_empty() && rt.lossless_all(),
        &format!("validate={errors:?} {}", rt.summary()),
    ));
    // twin: the ONLY check on the formula is non-blankness (spec.rs:853-861).
    let blank = spec_module("   ", "0..7");
    let errors = validate_module(&blank);
    let hit = errors.iter().any(|e| {
        matches!(
            e,
            ValidationError::InvalidSpecStructure {
                violation: SpecLinkViolation::BlankSemanticValue {
                    subject: "invariant",
                    field: "formula",
                    ..
                }
            }
        )
    });
    assert!(feature_check(
        "b7.spec.negative_twin.blank_formula",
        hit,
        &format!("{errors:?}"),
    ));

    // FLIPPED by WS4.14 (F-014, wire v46): the surface strings stay (they are
    // the AUTHORED tags), but beside them the machine now carries a TYPED
    // carrier — `SpecVar.sort: Option<ClauseSort>` and `SpecInvariant.typed:
    // Option<ProofFormula>` (the SAME first-order clause carrier contract
    // clauses use; no second grammar) whose bindings name state variables
    // through `ClausePlace::SpecVar`. Positive: the typed `Counter` validates
    // and round-trips in the three lossless production codecs at v46 (text
    // marks the carrier `#lossy`, WS4.2). Negative twins, each exactly one
    // named S4 refusal: a binding to an undeclared variable index, and a
    // binding whose sort contradicts the variable's declared sort.
    let typed_counter = |sort: ClauseSort, index: u32| {
        let mut m = spec_module("(>= n 0)", "0..7");
        let counter = &mut m.spec_modules[0];
        counter.vars[0].sort = Some(ClauseSort::Int);
        let mut typed = ProofFormula::smtlib2("(>= n 0)", "Bool");
        typed.bindings = vec![(
            "n".to_string(),
            ClauseBinding {
                sort,
                place: ClausePlace::SpecVar { index },
            },
        )];
        counter.invariants[0].typed = Some(typed);
        m
    };
    let typed_ok = typed_counter(ClauseSort::Int, 0);
    let ok_errors = validate_module(&typed_ok);
    let ok_rt = roundtrip_all(&typed_ok);
    let s4_binding = |errors: &[ValidationError], needle: &str| {
        matches!(
            errors,
            [ValidationError::InvalidSpecStructure {
                violation: SpecLinkViolation::SpecTypedBindingInvalid {
                    machine, subject: "invariant", name, binding, detail, ..
                }
            }] if machine == "Counter" && name == "Bounded" && binding == "n"
                && detail.contains(needle)
        )
    };
    let undeclared_index = validate_module(&typed_counter(ClauseSort::Int, 3));
    let sort_contradiction = validate_module(&typed_counter(ClauseSort::BitVec(8), 0));
    let inv = &typed_ok.spec_modules[0].invariants[0];
    let var = &typed_ok.spec_modules[0].vars[0];
    assert!(feature_check(
        "b7.spec.formula_and_var_type_are_strings",
        ok_errors.is_empty()
            && ok_rt.lossless_production()
            && ok_rt.binary_version == 46
            && type_name_of(&inv.typed) == std::any::type_name::<Option<ProofFormula>>()
            && type_name_of(&var.sort) == std::any::type_name::<Option<ClauseSort>>()
            && s4_binding(&undeclared_index, "state variable 3 is out of range")
            && s4_binding(
                &sort_contradiction,
                "at sort BitVec(8), but the variable declares sort Int"
            ),
        &format!(
            "closed by WS4.14 (v46): SpecInvariant.typed: {}, SpecVar.sort: {}; typed \
             Counter validate={ok_errors:?} {}; twins: undeclared index={undeclared_index:?}, \
             sort contradiction={sort_contradiction:?}",
            type_name_of(&inv.typed),
            type_name_of(&var.sort),
            ok_rt.summary()
        ),
    ));

    // … and under `DesignOnly` nothing parses them: syntactic garbage, an
    // undeclared variable and an ill-typed comparison all validate exactly like
    // the good spec. These three rows stay GAP BY DESIGN (roadmap WS1.10): a
    // `DesignOnly` machine is descriptive text, never a certification claim, so
    // its strings stay opaque. Their `Linked` half is the next row.
    for (id, formula, ty) in [
        ("garbage_syntax", ")))( @@ [] <> not a formula", "0..7"),
        ("undeclared_variable", "[](zzz_undeclared >= 0)", "0..7"),
        ("ill_typed", "[](n /\\ 3)", "this is not a type"),
    ] {
        let m = spec_module(formula, ty);
        let errors = validate_module(&m);
        let rt = roundtrip_all(&m);
        assert!(feature_gap(
            &format!("b7.spec.unparsed.{id}"),
            Expect::Accepted,
            Outcome::of(&errors)
                .given(&[("it round-trips in all four formats", rt.lossless_all())]),
            &format!("formula {formula:?} / var type {ty:?}: validate_module={errors:?}"),
        ));
    }

    // FLIPPED by WS1.10 (F-014): the `Linked` enforcement mode is a
    // certification claim, and it now reads its surface
    // (`trust_ir::spec_surface`). The good SMT-LIB2 invariant validates; the
    // three archived shapes — garbage syntax, an undeclared variable, an
    // ill-sorted comparison — are each EXACTLY one named
    // `SpecLinkedFormulaUnparsed` on the one invariant, and a type that is not
    // a type is `SpecLinkedVariableUnparsed`; a blank formula is still the S0
    // `BlankSemanticValue` refusal (right-reason twin: the new rule does not
    // swallow the old one).
    let linked = |formula: &str, ty: &str| {
        let mut m = named_module("step");
        let mut spec = SpecModule::linked("Counter");
        spec.vars.push(SpecVar::new("n", ty));
        spec.vars.push(SpecVar::new("flag", "Bool"));
        spec.actions.push("Step".into());
        spec.invariants.push(SpecInvariant::new("Bounded", formula));
        spec.waivers.push(trust_ir::spec::SpecWaiver {
            machine: "Counter".into(),
            action: "Step".into(),
            reason: "b7: formula typing probe".into(),
        });
        m.spec_modules.push(spec);
        m
    };
    let formula_refused = |errors: &[ValidationError], needle: &str| {
        matches!(
            errors,
            [ValidationError::SpecLinkedFormulaUnparsed { module, invariant, detail }]
                if module == "Counter" && invariant == "Bounded" && detail.contains(needle)
        )
    };
    let good_linked = validate_module(&linked("(>= n 0)", "0..7"));
    let garbage_linked = validate_module(&linked(")))( @@ [] <> not a formula", "0..7"));
    let tla_linked = validate_module(&linked("[](n >= 0)", "0..7"));
    let undeclared_linked = validate_module(&linked("(>= zzz_undeclared 0)", "0..7"));
    let ill_sorted_linked = validate_module(&linked("(>= flag 3)", "0..7"));
    let bad_type_linked = validate_module(&linked("flag", "this is not a type"));
    let blank_linked = validate_module(&linked("  ", "0..7"));
    let design_only_garbage = validate_module(&{
        let mut m = linked(")))( @@ [] <> not a formula", "this is not a type");
        m.spec_modules[0].enforcement = trust_ir::spec::SpecEnforcementMode::DesignOnly;
        m
    });
    assert!(feature_check(
        "b7.spec.unparsed.linked_mode",
        good_linked.is_empty()
            && formula_refused(&garbage_linked, "not one quantifier-free SMT-LIB2 term")
            && formula_refused(&tla_linked, "not one quantifier-free SMT-LIB2 term")
            && formula_refused(&undeclared_linked, "undeclared variable `zzz_undeclared`")
            && formula_refused(&ill_sorted_linked, "ill-sorted")
            && matches!(
                bad_type_linked.as_slice(),
                [ValidationError::SpecLinkedVariableUnparsed { module, variable, .. }]
                    if module == "Counter" && variable == "n"
            )
            && matches!(
                blank_linked.as_slice(),
                [ValidationError::InvalidSpecStructure {
                    violation: SpecLinkViolation::BlankSemanticValue {
                        field: "formula",
                        ..
                    }
                }]
            )
            && design_only_garbage.is_empty(),
        &format!(
            "SpecEnforcementMode::Linked: good={good_linked:?} garbage={garbage_linked:?} \
             tla={tla_linked:?} undeclared={undeclared_linked:?} \
             ill_sorted={ill_sorted_linked:?} bad_type={bad_type_linked:?} \
             blank={blank_linked:?}; DesignOnly control={design_only_garbage:?}"
        ),
    ));

    // FLIPPED by WS4.14 (F-014, wire v46): a `Liveness` / `TemporalSafety`
    // obligation carries a typed first-order formula over the machine's state
    // variables AND a `spec` backref naming the `SpecTemporal` property it
    // discharges. Positive: the backreferenced obligation validates and the
    // module round-trips at v46. Negative twins (one mutation each, one named
    // refusal): a backref to a property the machine does not declare, a
    // backref on a non-temporal kind, and a `SpecVarNext` binding inside the
    // single-state `Eventually` leaf.
    let temporal_module = |property: &str, kind: ObligationKind, leaf: ProofFormula| {
        let mut m = spec_module("(>= n 0)", "0..7");
        let counter = &mut m.spec_modules[0];
        counter.vars[0].sort = Some(ClauseSort::Int);
        counter.temporal.push(SpecTemporal::new(
            "EventuallySeven",
            TemporalForm::Eventually(leaf),
        ));
        let f = m.functions[0].id;
        let mut full = ProofFormula::smtlib2("(= n 7)", "Bool");
        full.bindings = vec![(
            "n".to_string(),
            ClauseBinding {
                sort: ClauseSort::Int,
                place: ClausePlace::SpecVar { index: 0 },
            },
        )];
        let mut obligation = ProofObligation::new(
            ProofId::new(0),
            kind,
            ProofStatus::Pending,
            "eventually n = 7",
        )
        .with_function(f)
        .with_formula(full);
        obligation.spec = Some(SpecObligationRef::new("Counter", property));
        m.proof_obligations.push(obligation);
        m
    };
    let seven = || {
        let mut leaf = ProofFormula::smtlib2("(= n 7)", "Bool");
        leaf.bindings = vec![(
            "n".to_string(),
            ClauseBinding {
                sort: ClauseSort::Int,
                place: ClausePlace::SpecVar { index: 0 },
            },
        )];
        leaf
    };
    let typed_temporal = temporal_module("EventuallySeven", ObligationKind::Liveness, seven());
    let typed_errors = validate_module(&typed_temporal);
    let typed_rt = roundtrip_all(&typed_temporal);
    let dangling = validate_module(&temporal_module(
        "EventuallyEight",
        ObligationKind::Liveness,
        seven(),
    ));
    let wrong_kind = validate_module(&temporal_module(
        "EventuallySeven",
        ObligationKind::Postcondition,
        seven(),
    ));
    let primed_leaf = validate_module(&temporal_module(
        "EventuallySeven",
        ObligationKind::Liveness,
        {
            let mut leaf = seven();
            leaf.bindings[0].1.place = ClausePlace::SpecVarNext { index: 0 };
            leaf
        },
    ));
    assert!(feature_check(
        "b7.spec.temporal_obligation_is_untyped",
        typed_errors.is_empty()
            && typed_rt.lossless_production()
            && typed_rt.binary_version == 46
            // (An unresolved backref also strands the obligation's own
            // `SpecVar` bindings — `InvalidObligationBinding` beside it.)
            && dangling.iter().any(|e| matches!(
                e,
                ValidationError::UnresolvedObligationSpecRef { obligation: 0, machine, temporal, reason }
                    if machine == "Counter" && temporal == "EventuallyEight"
                        && reason.contains("declares no temporal property of that name")
            ))
            && dangling.iter().all(|e| matches!(
                e,
                ValidationError::UnresolvedObligationSpecRef { .. }
                    | ValidationError::InvalidObligationBinding { .. }
            ))
            && wrong_kind.iter().any(|e| matches!(
                e,
                ValidationError::UnresolvedObligationSpecRef { obligation: 0, reason, .. }
                    if reason.contains("only a Liveness or TemporalSafety obligation")
            ))
            && matches!(
                primed_leaf.as_slice(),
                [ValidationError::InvalidSpecStructure {
                    violation: SpecLinkViolation::SpecTypedBindingInvalid {
                        subject: "temporal", name, detail, ..
                    }
                }] if name == "EventuallySeven" && detail.contains("SUCCESSOR state")
            ),
        &format!(
            "closed by WS4.14 (v46): Liveness obligation with typed bindings and spec backref \
             Counter/EventuallySeven: validate={typed_errors:?} {}; twins: dangling={dangling:?} \
             wrong kind={wrong_kind:?} primed leaf={primed_leaf:?}",
            typed_rt.summary()
        ),
    ));
}

// ---------------------------------------------------------------------------
// PASS (WS3.20, F-057): bulk memory and bit intrinsics are CORE ops. The
// archived goal rows `goal-g1-g8/g1-intrinsics-bulk-memory` and
// `goal-g1-g8/g3-no-symbolic-placeholder` measured (format half) that the
// instruction set had no ctlz/bswap/rotate/memcpy-with-dynamic-count and that
// the only spelling for a dynamic bulk write was the `RegionHavocStore`
// marker. Ported here as PASS rows: a `memcpy` with an SSA byte count
// validates, runs, and round-trips through text with no havoc marker; the
// negative twin (a `U32` count under target info) is refused by name.
// ---------------------------------------------------------------------------

/// `copy16(dst, src) -> u32`: 16 bytes copied with a DYNAMIC (`Usize` SSA)
/// count; the caller-visible result is the first u32 of the destination.
fn bulk_copy_module(count_ty: Ty) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("b7_bulk", target());
    let ft = mb.add_func_type(vec![], vec![Ty::U32]);
    let u8_id = mb.add_type(Ty::U8);
    let mut fb = mb.function("copy16", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let src = fb.alloca(Ty::Array(u8_id, 16));
    let dst = fb.alloca(Ty::Array(u8_id, 16));
    let head = fb.uconst(Ty::U32, 0x0102_0304);
    fb.store(Ty::U32, src, head);
    let n = fb.uconst(count_ty, 16);
    fb.memcopy(dst, src, n, false);
    let out = fb.load(Ty::U32, dst);
    fb.ret(vec![out]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn bulk_memory_and_bit_intrinsics_are_core_ops() {
    let module = bulk_copy_module(Ty::Usize);
    let errors = validate_module(&module);
    let ran = run_nullary(&module, "copy16");
    let value = ran
        .as_ref()
        .ok()
        .and_then(|v| v.first())
        .and_then(common::as_u128);
    // No havoc marker, no Undef: the copy is an operation with a checkable result.
    let havoc_free = module.functions.iter().all(|f| {
        f.blocks.iter().flat_map(|b| &b.body).all(|node| {
            !matches!(node.inst, Inst::Undef { .. })
                && !node.proofs.iter().any(|p| {
                    matches!(
                        p,
                        ProofAnnotation::RegionHavocStore | ProofAnnotation::FreshSymbolicHavoc
                    )
                })
        })
    });
    assert!(feature_check(
        "b7.intrinsics.g1_bulk_memory",
        errors.is_empty() && value == Some(0x0102_0304),
        &format!("memcopy with an SSA usize count validates ({errors:?}) and runs => {ran:?}"),
    ));
    assert!(feature_check(
        "b7.intrinsics.g3_no_havoc_for_bulk_copy",
        havoc_free && value == Some(0x0102_0304),
        "a dynamic-count bulk copy needs no RegionHavocStore / FreshSymbolicHavoc / Undef",
    ));
    // Text is lossless for the new spellings. (The binary leg landed with the
    // v51 INST wire batch; its four-format golden is the conformance corpus's
    // `inst_wire_batch`.)
    let text = module.to_string();
    let reparsed = trust_ir::parser::parse_module(&text);
    assert!(feature_check(
        "b7.intrinsics.text_round_trip",
        text.contains("memcopy ptr %")
            && reparsed
                .as_ref()
                .map(|m| m.functions[0].blocks == module.functions[0].blocks)
                .unwrap_or(false),
        &format!(
            "text: {}",
            text.lines().find(|l| l.contains("memcopy")).unwrap_or("")
        ),
    ));
    // Negative twin: the count is EXACTLY `Usize` under target info.
    let twin = validate_module(&bulk_copy_module(Ty::U32));
    assert!(feature_check(
        "b7.intrinsics.g1_bulk_memory.negative_twin",
        twin.iter().any(|e| matches!(
            e,
            ValidationError::OperandTypeMismatch { op, role, expected, .. }
                if op == "memcopy" && role == "bytes" && expected == "usize"
        )),
        &format!("u32 count => {twin:?}"),
    ));
    // Negative twin for g3: the bit intrinsics are typed — `ctlz f32` is
    // refused by name, never silently executed on the float's bits.
    let mut mb = ModuleBuilder::new("b7_bits");
    let ft = mb.add_func_type(vec![Ty::F32], vec![Ty::F32]);
    let mut fb = mb.function("ctlz_f32", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let x = fb.add_block_param(entry, Ty::F32);
    let r = fb.unop(trust_ir::UnOp::CtLz, Ty::F32, x);
    fb.ret(vec![r]);
    fb.build();
    let twin = validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
    assert!(feature_check(
        "b7.intrinsics.g3_no_havoc_for_bulk_copy.negative_twin",
        twin.iter().any(|e| matches!(
            e,
            ValidationError::BinOpRequiresInteger { op, .. } if op == "ctlz"
        )),
        &format!("ctlz f32 => {twin:?}"),
    ));
}

#[test]
fn two_language_b7() {
    common::run_target(
        "b7",
        &[
            (
                "production_codecs_are_lossless_for_the_contract_surface",
                production_codecs_are_lossless_for_the_contract_surface,
            ),
            (
                "wire_version_selection_and_read_gates",
                wire_version_selection_and_read_gates,
            ),
            (
                "carried_surface_is_validated_negative_twins",
                carried_surface_is_validated_negative_twins,
            ),
            ("text_drops_contract_surface", text_drops_contract_surface),
            (
                "text_round_trip_flips_validator_verdicts",
                text_round_trip_flips_validator_verdicts,
            ),
            (
                "text_refuses_v41_obligation_kinds",
                text_refuses_v41_obligation_kinds,
            ),
            (
                "text_cannot_parse_minted_names",
                text_cannot_parse_minted_names,
            ),
            (
                "text_parser_is_total_over_utf8",
                text_parser_is_total_over_utf8,
            ),
            (
                "no_typed_nondeterministic_choice",
                no_typed_nondeterministic_choice,
            ),
            (
                "spec_invariants_are_opaque_strings",
                spec_invariants_are_opaque_strings,
            ),
            (
                "bulk_memory_and_bit_intrinsics_are_core_ops",
                bulk_memory_and_bit_intrinsics_are_core_ops,
            ),
        ],
    );
}
