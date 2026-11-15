// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Roadmap WS4.13 (finding F-073, the remainder after f3c07824 + d71950bf):
//! `trust_ir::diff` sees EVERY identity-bearing field.
//!
//! Three layers, each on one rich fixture that populates every field it
//! mutates with a non-default value:
//!
//! 1. **Per field (positive).** The fields the remainder closes — a clause's
//!    typed `bindings` (summary and obligation), an obligation's IR `site`, a
//!    certificate's coverage `assurance`, a `CleanCic` kernel re-check
//!    directive and its `CertificateBinding`, an `InheritedFromCallee`
//!    retarget, the debug file table's LENGTH, and a node's result arity —
//!    each produce exactly the one named change, hidden by `--ignore-proofs`
//!    exactly when it is proof coverage. WS3.9's v58 surface (declared
//!    closure layouts and the struct / enum nominal `origin` key) is held to
//!    the same mutation control below.
//! 2. **Negative twin.** The same fixture under SSA / block / function / proof
//!    id renumbering, reversed declaration order and a moved checkout (every
//!    `files[i]` string rewritten) diffs EMPTY.
//! 3. **Mutation control.** A single-field mutant generator covers every
//!    field of every carrier the diff reads; an exhaustive destructure below
//!    enumerates those fields (a new field fails to BUILD this file until it
//!    is classified), every mutant must move `Module::stable_digest` (so it is
//!    a real change), and every one then diffs NON-empty — except the debug
//!    fields `diff.rs` documents as ignored, which must diff empty. The
//!    generator is plain data (`MUTANTS`) so WS4.11's merge tests can share
//!    it. The three records a `CleanCic` kernel re-check binding nests
//!    (`CertificateBinding`, `SourceDefinitionRef`, `IslandEnvironment`)
//!    have no binary carrier, so no mutant of theirs can move a digest; they
//!    are held to the same exhaustive inventory by their own diff-only
//!    mutants (`certificate_binding_fields_are_reported`).
//!
//! Plus the in-repo port of audit row `scout-emit.F2`.

use std::collections::BTreeSet;

use trust_ir::blob::{Blob, BlobDigest};
use trust_ir::diff::{
    BlockChange, Diff, DiffOptions, FuncChange, InstrChange, MetaChange, ProofChange,
    ProofStateChange, diff, diff_with,
};
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, CoverageAssurance, CoverageBound, IslandEnvironment,
    ObligationSite, ProofContext, SpecObligationRef,
};
use trust_ir::spec::{
    ProofKind, SpecAnchor, SpecInvariant, SpecModule, SpecProof, SpecTemporal, SpecVar, SpecWaiver,
    TemporalForm,
};
use trust_ir::ty::TypeOrigin;
use trust_ir::{
    ArgExt, BinOp, Block, BlockId, BodyGate, CallingConv, CertificateBinding,
    CleanCicKernelRecheck, ClosureLayoutDescriptor, ClosureTy, ClosureTyId, Constant,
    DiagnosticSeverity, DropGlueEntry, EffectPlace, EffectSet, EffectSummary, Endianness, EnumDef,
    EnumId, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant, ExternRef, FieldDef,
    FuncAttrs, FuncId, FuncTy, FuncTyId, Function, FunctionSummary, Global, ImportId, Inst,
    InstrNode, Linkage, Module, ModuleCompleteness, ModuleImport, ObligationDiagnostic,
    ObligationKind, ParamAttrs, PassMode, Producer, ProofAnnotation, ProofCertificate, ProofDigest,
    ProofEvidence, ProofFormula, ProofId, ProofObligation, ProofObligationSourceIdentity,
    ProofStatus, ScopeData, SourceDefinitionRef, SourceProvenance, SourceSpan, StructDef, StructId,
    StructRepr, TargetInfo, TlsModel, TupleLayoutDescriptor, Ty, ValueId, Visibility,
};

/// One carrier's field names, `"<prefix>.<field>"`, produced by the SAME
/// token list that destructures `$value` EXHAUSTIVELY (no `..`): a field added
/// to the carrier fails to build its line, and once spelled there it is in the
/// inventory — there is no second, hand-kept list to fall behind.
macro_rules! fields {
    ($prefix:literal, $value:expr, $carrier:ident { $($field:ident),* $(,)? }) => {{
        let $carrier { $($field: _),* } = $value;
        [$(concat!($prefix, ".", stringify!($field))),*]
    }};
}

// ---------------------------------------------------------------------------
// The fixture
// ---------------------------------------------------------------------------

const CALLEE: &str = "callee";
const CALLER: &str = "caller";
const MACHINE: &str = "Counter";

/// One build of the fixture: `base` shifts every function / block / value id,
/// `reverse` reverses the declaration order of functions, globals, obligations
/// (renumbering their `ProofId`s) and certificates, and `checkout` is the
/// directory every debug file path starts with.
#[derive(Clone, Copy)]
struct Build {
    base: u32,
    reverse: bool,
    checkout: &'static str,
}

const CANON: Build = Build {
    base: 0,
    reverse: false,
    checkout: "/home/a/app",
};
const TWIN: Build = Build {
    base: 500,
    reverse: true,
    // Assembled, not spelled: publication's forbidden-content baseline
    // refuses a macOS home-directory literal anywhere in the export (owner
    // ruling 2026-09-30, the same rewrite `import_identity.rs` carries). The
    // runtime string is unchanged.
    checkout: concat!("/Us", "ers/b/checkouts/elsewhere"),
};

/// Canonical obligation keys, in canonical order.
const PRE: usize = 0;
const OVF: usize = 1;
const POST: usize = 2;
const LIVE: usize = 3;
const OBLIGATIONS: usize = 4;

impl Build {
    fn callee(self) -> FuncId {
        FuncId::new(self.base + u32::from(self.reverse))
    }
    fn caller(self) -> FuncId {
        FuncId::new(self.base + u32::from(!self.reverse))
    }
    fn callee_entry(self) -> BlockId {
        BlockId::new(self.base + 10)
    }
    fn caller_entry(self) -> BlockId {
        BlockId::new(self.base + 20)
    }
    fn caller_exit(self) -> BlockId {
        BlockId::new(self.base + 30)
    }
    fn v(self, n: u32) -> ValueId {
        ValueId::new(self.base + n)
    }
    /// The `ProofId` of canonical obligation `k` (its table position).
    fn pid(self, k: usize) -> ProofId {
        let position = if self.reverse { OBLIGATIONS - 1 - k } else { k };
        ProofId::new(position as u32)
    }
}

fn digest(byte: u8) -> ProofDigest {
    ProofDigest::sha256([byte; 32])
}

fn bv64(name: &str, place: ClausePlace) -> (String, ClauseBinding) {
    (
        name.to_string(),
        ClauseBinding {
            sort: ClauseSort::BitVec(64),
            place,
        },
    )
}

fn with_bindings(
    mut f: ProofFormula,
    bindings: impl IntoIterator<Item = (String, ClauseBinding)>,
) -> ProofFormula {
    f.bindings = bindings.into_iter().collect();
    f
}

/// `callee(x: u64) -> u64 { x }` under a contract whose clauses are bound.
/// Its signature is interned by [`fixture_with`].
fn callee(b: Build, import: ImportId) -> Function {
    let entry = b.callee_entry();
    let mut f = Function::new(b.callee(), CALLEE, FuncTyId::new(0), entry);
    let mut blk = Block::new(entry);
    blk.params.push((b.v(10), Ty::U64));
    blk.body.push(InstrNode::new(Inst::Return {
        values: vec![b.v(10)],
    }));
    f.blocks.push(blk);
    f.producer = Some(Producer::Clean);
    f.summary = Some(FunctionSummary {
        requires: vec![with_bindings(
            ProofFormula::smtlib2("(bvuge x #x0000000000000000)", "Bool"),
            [bv64("x", ClausePlace::Param { index: 0 })],
        )],
        ensures: vec![with_bindings(
            ProofFormula::smtlib2("(= result x)", "Bool"),
            [
                bv64("result", ClausePlace::ResultSlot { index: 0 }),
                bv64("x", ClausePlace::Param { index: 0 }),
            ],
        )],
        params: vec!["x".into()],
        proved: true,
        decreases: vec![with_bindings(
            ProofFormula::smtlib2("x", "(_ BitVec 64)"),
            [bv64("x", ClausePlace::Param { index: 0 })],
        )],
        backed_by: Some(ExternRef::new(import, "dep_callee")),
        // v59 (WS1.14): every field non-default where a flip is a real
        // change (reads a parameter place; writes nothing; mixed flags).
        effects: Some(EffectSummary {
            reads: EffectSet::of([EffectPlace::ParamPointee { index: 0 }]),
            writes: EffectSet::Nothing,
            allocates: true,
            frees: false,
            may_unwind: true,
            io: false,
        }),
    });
    f
}

/// `caller(p: u64) -> u64 { s = p + 1; callee(s) }`, two blocks, with debug
/// metadata (a scope, a span, a value name) on every node that can carry it.
/// Its signature is interned by [`fixture_with`].
fn caller(b: Build) -> Function {
    let entry = b.caller_entry();
    let exit = b.caller_exit();
    let mut f = Function::new(b.caller(), CALLER, FuncTyId::new(0), entry);

    let mut e = Block::new(entry);
    e.params.push((b.v(20), Ty::U64));
    e.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(1),
        })
        .with_result(b.v(21)),
    );
    let mut add = InstrNode::new(Inst::BinOp {
        op: BinOp::Add,
        ty: Ty::U64,
        lhs: b.v(20),
        rhs: b.v(21),
    })
    .with_result(b.v(22));
    add.span = Some(SourceSpan {
        file: 0,
        line: 3,
        col: 5,
    });
    add.scope = Some(0);
    add.proofs.push(ProofAnnotation::NoOverflow);
    // A proof backref (fast-1) to the obligation that states this check: a
    // `ProofId` the renumbered twin moves, so the diff must resolve it by
    // CLAIM exactly like a certificate's or a proof context's reference.
    add.proofs.push(ProofAnnotation::ProofRef(b.pid(OVF)));
    e.body.push(add);
    let mut call = InstrNode::new(Inst::Call {
        callee: b.callee(),
        args: vec![b.v(22)],
    })
    .with_result(b.v(23));
    call.proof_context = Some(ProofContext {
        assumes: vec![b.pid(POST)],
        establishes: vec![b.pid(PRE)],
    });
    e.body.push(call);
    e.body.push(InstrNode::new(Inst::Br {
        target: exit,
        args: vec![b.v(23)],
    }));

    let mut x = Block::new(exit);
    x.params.push((b.v(30), Ty::U64));
    x.body.push(InstrNode::new(Inst::Return {
        values: vec![b.v(30)],
    }));

    f.blocks.push(e);
    f.blocks.push(x);
    f.producer = Some(Producer::TRust);
    f.proofs.push(ProofAnnotation::Deterministic);
    // A function-level backref as well (a legitimate shape elsewhere; the
    // diff compares it through the function's proof set).
    f.proofs.push(ProofAnnotation::ProofRef(b.pid(POST)));
    f.value_names = Some(vec![(b.v(22), "sum".into())]);
    f.scopes = Some(vec![ScopeData::new(None, None)]);
    f.display_path = Some("app::caller".into());
    f.body_gate = Some(BodyGate::Gated {
        authority: "trust-direct".into(),
        evidence: None,
    });
    f.source_provenance = Some(SourceProvenance {
        schema: 1,
        compiler_source_digest: digest(0x51),
        semantic_body_digest: digest(0x52),
        binding_digest: digest(0x53),
        loops: Vec::new(),
    });
    f
}

fn obligation(b: Build, k: usize) -> ProofObligation {
    let id = b.pid(k);
    match k {
        PRE => ProofObligation::new(
            id,
            ObligationKind::Precondition,
            ProofStatus::Discharged,
            "callee requires x >= 0",
        )
        .with_function(b.callee())
        .with_formula(with_bindings(
            ProofFormula::smtlib2("(bvuge x #x0000000000000000)", "Bool"),
            [bv64("x", ClausePlace::Param { index: 0 })],
        ))
        .with_source(ProofObligationSourceIdentity::new("src/lib.rs", "req.0")),
        OVF => ProofObligation::new(
            id,
            ObligationKind::ArithmeticSafety,
            ProofStatus::Certified,
            "p + 1 does not overflow",
        )
        .with_function(b.caller())
        // The Add node: entry block (visit 0), instruction 1.
        .with_site(ObligationSite::new(b.caller(), b.caller_entry(), 1))
        .with_formula(with_bindings(
            ProofFormula::smtlib2("(bvuge s p)", "Bool"),
            [
                bv64("s", ClausePlace::Value(b.v(22))),
                bv64("p", ClausePlace::Param { index: 0 }),
            ],
        )),
        POST => ProofObligation::new(
            id,
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "caller inherits the callee's precondition",
        )
        .with_function(b.caller()),
        LIVE => {
            let mut o = ProofObligation::new(
                id,
                ObligationKind::Liveness,
                ProofStatus::Pending,
                "the counter eventually moves",
            );
            o.spec = Some(SpecObligationRef {
                machine: MACHINE.into(),
                temporal: "Moves".into(),
            });
            o
        }
        _ => unreachable!(),
    }
}

fn certificates(b: Build) -> Vec<ProofCertificate> {
    vec![
        ProofCertificate {
            obligation: b.pid(PRE),
            prover: "ay".into(),
            evidence: ProofEvidence::SmtProof(vec![1, 2, 3]),
            assurance: Some(CoverageAssurance {
                bound: CoverageBound::UnwindBounded { depth: 1 },
                request_digest: digest(0x61),
            }),
        },
        ProofCertificate {
            obligation: b.pid(OVF),
            prover: "clean".into(),
            evidence: ProofEvidence::CleanCic {
                term: vec![0xaa],
                context: vec![0xbb],
                lineage: digest(0x62),
                kernel_recheck: Some(CleanCicKernelRecheck {
                    module: "App.Overflow".into(),
                    theorems: vec!["App.Overflow.add_le".into()],
                    anchor: "clean_island".into(),
                    allowed_axioms: vec!["propext".into()],
                    binding: None,
                }),
            },
            assurance: None,
        },
        ProofCertificate {
            obligation: b.pid(POST),
            prover: "compose".into(),
            evidence: ProofEvidence::InheritedFromCallee {
                callee: b.callee(),
                obligation: b.pid(PRE),
                external: None,
            },
            assurance: None,
        },
    ]
}

fn spec_module(b: Build) -> SpecModule {
    let mut s = SpecModule::design_only(MACHINE);
    s.vars.push(SpecVar::new("n", "Nat"));
    s.actions.push("Incr".into());
    s.invariants
        .push(SpecInvariant::new("NonNeg", "n \\in Nat"));
    s.anchors.push(SpecAnchor {
        machine: MACHINE.into(),
        action: "Incr".into(),
        rust_symbol: CALLER.into(),
        span: "src/lib.rs:3".into(),
        project: None,
        function: Some(b.caller()),
        projection_target: None,
    });
    s.waivers.push(SpecWaiver {
        machine: MACHINE.into(),
        action: "Reset".into(),
        reason: "not modelled".into(),
    });
    s.proofs.push(SpecProof {
        machine: MACHINE.into(),
        action: "Incr".into(),
        proof_name: "incr_harness".into(),
        kind: ProofKind::Kani,
    });
    s.temporal.push(SpecTemporal::new(
        "Moves",
        TemporalForm::Eventually(ProofFormula::smtlib2("(> n 0)", "Bool")),
    ));
    s
}

/// A v58 `Rust` nominal key; `path` varies the def path hash.
fn rust_origin(path: u8) -> TypeOrigin {
    TypeOrigin::Rust {
        stable_crate_id: 7,
        def_path_hash: [path; 16],
        args_digest: digest(0x74),
    }
}

fn unit_variant(name: &str) -> EnumVariant {
    EnumVariant {
        name: name.into(),
        fields: vec![],
        field_names: vec![],
    }
}

fn fixture_with(b: Build) -> Module {
    let mut m = Module::new("fields");
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("darwinpcs".into()),
        struct_passing: Default::default(),
    });
    m.files = vec![
        format!("{}/src/lib.rs", b.checkout),
        format!("{}/src/other.rs", b.checkout),
    ];
    m.global_asm = vec![".globl app_marker".into()];
    let import = m
        .intern_import(ModuleImport::new("dep", digest(0x71)))
        .expect("Module::intern_import: test fixture");
    // A second dependency nothing cites yet: the `extern.module` mutant
    // re-points the summary's `backed_by` at it (one field, a real referent).
    m.intern_import(ModuleImport::new("dep_b", digest(0x73)))
        .expect("Module::intern_import: test fixture");
    m.structs.push(StructDef {
        id: StructId::new(0),
        name: "Pair".into(),
        fields: vec![
            FieldDef {
                name: "a".into(),
                ty: Ty::U32,
                offset: None,
            },
            FieldDef {
                name: "b".into(),
                ty: Ty::U32,
                offset: None,
            },
        ],
        size: Some(8),
        align: Some(4),
        repr: StructRepr::C,
        // The v58 nominal key (WS3.9): populated, so the `struct.origin`
        // mutant re-keys a real key.
        origin: Some(rust_origin(0xa1)),
    });
    // An enum the `MODE` global uses (a definition is fingerprinted at every
    // use), every field populated with a non-default value.
    let mut mode = EnumDef::new(
        EnumId::new(0),
        "Mode",
        vec![unit_variant("Off"), unit_variant("On")],
    );
    mode.discriminants = vec![Some(1), Some(2)];
    mode.repr = Some(EnumTagRepr::U16);
    mode.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 0 },
        size: 2,
        align: 2,
        variant_field_offsets: vec![vec![], vec![]],
    });
    mode.origin = Some(TypeOrigin::Clean {
        decl: "App.Mode".into(),
        env_digest: digest(0x75),
    });
    m.enums.push(mode);
    // v58 declared closure frames (WS3.9): two closure types with the SAME
    // capture shape and different signatures, declared in reverse order in
    // the twin (so the framed one's `ClosureTyId` differs); the row frames
    // `wide`, and the `closure_layout.closure` mutant re-points it at the
    // other one (one field, a real referent the frame still fits).
    let wide = ClosureTy {
        func: m
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::U32],
                returns: vec![Ty::U32],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture"),
        captures: vec![Ty::U32, Ty::U32],
    };
    let narrow = ClosureTy {
        func: m
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::U16],
                returns: vec![Ty::U16],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture"),
        captures: vec![Ty::U32, Ty::U32],
    };
    let framed = if b.reverse {
        m.add_closure_type(narrow)
            .expect("Module::add_closure_type: test fixture");
        m.add_closure_type(wide)
            .expect("Module::add_closure_type: test fixture")
    } else {
        let framed = m
            .add_closure_type(wide)
            .expect("Module::add_closure_type: test fixture");
        m.add_closure_type(narrow)
            .expect("Module::add_closure_type: test fixture");
        framed
    };
    m.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: framed,
        size: 8,
        align: 4,
        capture_offsets: vec![0, 4],
    });
    let tuple = m
        .add_type(Ty::Tuple(vec![Ty::U32, Ty::U32]))
        .expect("Module::add_type: test fixture");
    // A second tuple type nothing uses yet (an unused table row is invisible
    // by design): the `tuple_layout.tuple_type` mutant re-points the layout
    // at it (one field, a real referent the layout still fits).
    m.add_type(Ty::Tuple(vec![Ty::U32, Ty::U16]))
        .expect("Module::add_type: test fixture");
    m.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: tuple,
        size: 8,
        align: 4,
        field_offsets: vec![0, 4],
    });
    // The v55 drop-glue table (amendment D): one row keyed by the struct,
    // naming the callee by `FuncId` (renumbered in the twin; the diff
    // resolves it to the SYMBOL). The diff does not validate its inputs, so
    // the glue keeps the fixture's shared signature rather than the
    // `(ptr) -> ()` the validator demands; only the row's fields matter here.
    m.drop_glue.push(DropGlueEntry {
        glue: b.callee(),
        ty: Ty::Struct(StructId::new(0)),
    });
    // The v70 blob table (PKG-U13e): one row. A digest names bytes, not an
    // id, so the twin holds the same row.
    m.intern_blob(vec![1, 2, 3, 4]);

    // Functions: their signatures are interned into THIS module.
    let mut functions = vec![callee(b, import), caller(b)];
    for f in &mut functions {
        f.ty = m
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::U64],
                returns: vec![Ty::U64],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
    }
    if b.reverse {
        functions.reverse();
    }
    m.functions = functions;

    let mut globals = vec![
        Global {
            name: "COUNTER".into(),
            ty: Ty::U64,
            mutable: true,
            initializer: Some(Constant::Int(3)),
            linkage: Linkage::External,
            tls: Some(TlsModel::InitialExec),
            align: Some(8),
            section: Some(".data.app".into()),
            visibility: Visibility::Hidden,
            retained: true,
        },
        Global {
            name: "PAIR".into(),
            ty: Ty::Struct(StructId::new(0)),
            mutable: false,
            initializer: None,
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Visibility::Default,
            retained: false,
        },
        Global {
            name: "MODE".into(),
            ty: Ty::Enum(EnumId::new(0)),
            mutable: false,
            initializer: None,
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Visibility::Default,
            retained: false,
        },
    ];
    if b.reverse {
        globals.reverse();
    }
    m.globals = globals;

    let mut obligations: Vec<ProofObligation> =
        (0..OBLIGATIONS).map(|k| obligation(b, k)).collect();
    let mut certs = certificates(b);
    if b.reverse {
        obligations.reverse();
        certs.reverse();
    }
    m.proof_obligations = obligations;
    m.proof_certificates = certs;
    m.obligation_diagnostics.push(ObligationDiagnostic {
        obligation: b.pid(LIVE),
        severity: DiagnosticSeverity::Warning,
        message: "bounded only".into(),
        location: None,
        detail: None,
    });
    m.spec_modules.push(spec_module(b));
    m
}

fn fixture() -> Module {
    fixture_with(CANON)
}

fn func_mut<'m>(m: &'m mut Module, name: &str) -> &'m mut Function {
    m.functions.iter_mut().find(|f| f.name == name).unwrap()
}

fn obligation_mut<'m>(m: &'m mut Module, description_prefix: &str) -> &'m mut ProofObligation {
    m.proof_obligations
        .iter_mut()
        .find(|o| o.description.starts_with(description_prefix))
        .unwrap()
}

fn certificate_mut<'m>(m: &'m mut Module, prover: &str) -> &'m mut ProofCertificate {
    m.proof_certificates
        .iter_mut()
        .find(|c| c.prover == prover)
        .unwrap()
}

fn recheck_mut(m: &mut Module) -> &mut CleanCicKernelRecheck {
    match &mut certificate_mut(m, "clean").evidence {
        ProofEvidence::CleanCic {
            kernel_recheck: Some(r),
            ..
        } => r,
        other => panic!("fixture drifted: {other:?}"),
    }
}

fn summary_mut(m: &mut Module) -> &mut FunctionSummary {
    func_mut(m, CALLEE).summary.as_mut().unwrap()
}

fn effects_mut(m: &mut Module) -> &mut EffectSummary {
    summary_mut(m).effects.as_mut().unwrap()
}

fn node_mut(m: &mut Module, index: usize) -> &mut InstrNode {
    let f = func_mut(m, CALLER);
    let entry = f.entry;
    let blk = f.blocks.iter_mut().find(|b| b.id == entry).unwrap();
    &mut blk.body[index]
}

// ---------------------------------------------------------------------------
// Negative twin
// ---------------------------------------------------------------------------

#[test]
fn fixture_is_isomorphic_to_itself() {
    let a = fixture();
    let d = diff(&a, &a.clone());
    assert!(d.is_empty(), "{}", d.to_text());
}

/// Renumbering every function, block, SSA value and proof id, reversing
/// every declaration order the diff calls cosmetic, and moving the checkout
/// (every `files[i]` string rewritten) is NOT a change. The mutants below
/// change exactly those ids' TARGETS, and are reported.
#[test]
fn renumbered_reordered_and_relocated_twin_diffs_empty() {
    let a = fixture();
    let b = fixture_with(TWIN);
    assert_ne!(a.functions[0].id, b.functions[0].id, "twin must renumber");
    assert_ne!(a.files, b.files, "twin must move the checkout");
    for ignore_proofs in [false, true] {
        let d = diff_with(
            &a,
            &b,
            DiffOptions {
                ignore_proofs,
                include_debug: false,
            },
        );
        assert!(
            d.is_empty(),
            "ignore_proofs={ignore_proofs}: {}",
            d.to_text()
        );
    }
    // A checkout move alone does not move the portable identity either: the
    // `files` row mirrors `IdentityScheme::V3` (WS4.10).
    let mut moved = fixture();
    moved.files = fixture_with(TWIN).files;
    assert_eq!(moved.stable_digest(), a.stable_digest());
    assert!(diff(&a, &moved).is_empty());
}

// ---------------------------------------------------------------------------
// Per field (positive): exactly one change, naming the field
// ---------------------------------------------------------------------------

fn proof_on(d: &Diff, func: &str) -> Vec<ProofChange> {
    assert!(d.module_meta_changes.is_empty(), "{}", d.to_text());
    assert!(d.proof_state_changes.is_empty(), "{}", d.to_text());
    assert_eq!(d.changes.len(), 1, "{}", d.to_text());
    match &d.changes[0] {
        FuncChange::Changed {
            name,
            proof_changes,
            block_changes,
            meta_changes,
        } => {
            assert_eq!(name, func);
            assert!(block_changes.is_empty(), "{}", d.to_text());
            assert!(meta_changes.is_empty(), "{}", d.to_text());
            proof_changes.clone()
        }
        other => panic!("expected a changed @{func}: {other:?}"),
    }
}

fn assert_hidden_by_ignore_proofs(a: &Module, b: &Module) {
    let d = diff_with(
        a,
        b,
        DiffOptions {
            ignore_proofs: true,
            include_debug: false,
        },
    );
    assert!(d.is_empty(), "{}", d.to_text());
}

/// A summary clause re-bound (`x` from parameter 0 to parameter 1) or
/// re-sorted (`BitVec(64)` to `Int`, the width-strip that turns a false
/// clause true) with its TEXT untouched is a contract change.
#[test]
fn summary_clause_bindings_are_reported() {
    let a = fixture();
    for (label, mutate) in [
        (
            "place",
            (|m: &mut Module| {
                summary_mut(m).requires[0].bindings[0].1.place = ClausePlace::Param { index: 1 }
            }) as fn(&mut Module),
        ),
        ("sort", |m: &mut Module| {
            summary_mut(m).requires[0].bindings[0].1.sort = ClauseSort::Int
        }),
        ("dropped", |m: &mut Module| {
            summary_mut(m).requires[0].bindings.clear()
        }),
    ] {
        let mut b = a.clone();
        mutate(&mut b);
        assert_ne!(a.stable_digest(), b.stable_digest(), "{label}");
        let changes = proof_on(&diff(&a, &b), CALLEE);
        assert_eq!(changes.len(), 2, "{label}: {changes:?}");
        match (&changes[0], &changes[1]) {
            (ProofChange::Removed { name: before }, ProofChange::Added { name: after }) => {
                assert!(before.starts_with("summary "), "{before}");
                assert!(
                    before.contains("bindings=[\"x\":BitVec(64)@param0]"),
                    "{label}: {before}"
                );
                assert!(after.starts_with("summary "), "{after}");
            }
            other => panic!("{label}: {other:?}"),
        }
        assert_hidden_by_ignore_proofs(&a, &b);
    }
}

/// The only function-side change an obligation re-key may cause: a
/// `ProofRef` citing the obligation re-keys with it (it names the obligation
/// by CLAIM), on the citing node or in the citing function's proof set —
/// the SAME change, seen from its citation. Anything else is a failure.
fn assert_only_proof_ref_citations(d: &Diff) {
    for change in &d.changes {
        let FuncChange::Changed {
            proof_changes,
            block_changes,
            meta_changes,
            ..
        } = change
        else {
            panic!("unexpected {change:?}");
        };
        assert!(meta_changes.is_empty(), "{}", d.to_text());
        for p in proof_changes {
            let (ProofChange::Added { name } | ProofChange::Removed { name }) = p;
            assert!(name.starts_with("ProofRef("), "{}", d.to_text());
        }
        for b in block_changes {
            let BlockChange::InstrDiff { instr_changes, .. } = b else {
                panic!("unexpected {b:?}");
            };
            for i in instr_changes {
                let InstrChange::Replaced { before, after, .. } = i else {
                    panic!("unexpected {i:?}");
                };
                assert!(
                    before.contains("ProofRef(") && after.contains("ProofRef("),
                    "{}",
                    d.to_text()
                );
            }
        }
    }
}

fn obligation_rows(d: &Diff) -> (String, String) {
    assert_only_proof_ref_citations(d);
    assert!(d.module_meta_changes.is_empty(), "{}", d.to_text());
    let mut removed = None;
    let mut added = None;
    for c in &d.proof_state_changes {
        match c {
            ProofStateChange::ObligationRemoved { obligation, .. } => {
                assert!(
                    removed.replace(obligation.clone()).is_none(),
                    "{}",
                    d.to_text()
                )
            }
            ProofStateChange::ObligationAdded { obligation, .. } => {
                assert!(
                    added.replace(obligation.clone()).is_none(),
                    "{}",
                    d.to_text()
                )
            }
            // A certificate or proof context citing the obligation re-keys
            // with it; that is the SAME change, seen from its citation.
            ProofStateChange::CertificateRemoved { .. }
            | ProofStateChange::CertificateAdded { .. } => {}
            other => panic!("unexpected {other:?}"),
        }
    }
    (removed.expect("removed"), added.expect("added"))
}

/// An obligation's formula bindings are part of its claim; a `Value` place
/// is resolved through the obligation's function body (canonical walk
/// index), so the renumbered twin keeps the key while a re-point moves it.
#[test]
fn obligation_formula_bindings_are_part_of_the_claim() {
    let a = fixture();
    let mut b = a.clone();
    // Re-point `s` from the Add result (%2 in walk order: the entry block's
    // parameter is %0, the constant %1) to the constant.
    let constant = node_mut(&mut b, 0).results[0];
    obligation_mut(&mut b, "p + 1")
        .formula
        .as_mut()
        .unwrap()
        .bindings[0]
        .1
        .place = ClausePlace::Value(constant);
    assert_ne!(a.stable_digest(), b.stable_digest());
    let (before, after) = obligation_rows(&diff(&a, &b));
    assert!(
        before.contains(";bindings=[\"s\":BitVec(64)@%2,"),
        "{before}"
    );
    assert!(after.contains(";bindings=[\"s\":BitVec(64)@%1,"), "{after}");
    assert_hidden_by_ignore_proofs(&a, &b);
}

/// An obligation's IR `site` (v34) is part of its claim, rendered like the
/// body: function by symbol, block by DFS visit index, instruction by
/// position. Moving it to another check is reported; renumbering is not.
#[test]
fn obligation_site_is_part_of_the_claim() {
    let a = fixture();
    for (label, mutate) in [
        (
            "instruction",
            (|m: &mut Module| obligation_mut(m, "p + 1").site.as_mut().unwrap().inst_index = 2)
                as fn(&mut Module),
        ),
        ("block", |m: &mut Module| {
            let exit = func_mut(m, CALLER).blocks[1].id;
            obligation_mut(m, "p + 1").site.as_mut().unwrap().block = exit
        }),
        ("dropped", |m: &mut Module| {
            obligation_mut(m, "p + 1").site = None
        }),
    ] {
        let mut b = a.clone();
        mutate(&mut b);
        assert_ne!(a.stable_digest(), b.stable_digest(), "{label}");
        let (before, after) = obligation_rows(&diff(&a, &b));
        assert!(before.contains(";site=@caller/bb0#1"), "{label}: {before}");
        match label {
            "instruction" => assert!(after.contains(";site=@caller/bb0#2"), "{after}"),
            "block" => assert!(after.contains(";site=@caller/bb1#1"), "{after}"),
            _ => assert!(!after.contains(";site="), "{after}"),
        }
        assert_hidden_by_ignore_proofs(&a, &b);
    }
}

/// Review (WS4.13): an obligation's scope `function` resolves to its symbol;
/// a scope naming NO function used to render as the unscoped `fn=_`, so
/// gaining such a scope moved `stable_digest` and diffed EMPTY (the diff does
/// not validate its inputs). It now keeps its raw index under a distinct
/// spelling, and two dangling scopes stay apart.
#[test]
fn a_dangling_obligation_scope_is_not_unscoped() {
    let a = fixture();
    let scoped = |id: u32| {
        let mut m = a.clone();
        obligation_mut(&mut m, "the counter").function = Some(FuncId::new(id));
        m
    };
    let b = scoped(990);
    assert_ne!(a.stable_digest(), b.stable_digest());
    let (before, after) = obligation_rows(&diff(&a, &b));
    assert!(before.contains("kind=liveness;fn=_;"), "{before}");
    assert!(after.contains("kind=liveness;fn=#dangling 990;"), "{after}");
    assert!(!diff(&scoped(990), &scoped(991)).is_empty());
    // A resolved scope keeps its symbol spelling (the twin relies on it).
    assert!(diff(&scoped(990), &scoped(990)).is_empty());
}

fn certificate_rows(d: &Diff) -> (String, String) {
    assert!(d.changes.is_empty(), "{}", d.to_text());
    assert!(d.module_meta_changes.is_empty(), "{}", d.to_text());
    match d.proof_state_changes.as_slice() {
        [
            ProofStateChange::CertificateRemoved {
                certificate: before,
            },
            ProofStateChange::CertificateAdded { certificate: after },
        ] => (before.clone(), after.clone()),
        other => panic!("expected one certificate swap: {other:?}"),
    }
}

/// A certificate's v41 coverage projection is carried content: claiming
/// `Unbounded` where it said `UnwindBounded { depth: 1 }`, citing another
/// bundle, or dropping the row is reported.
#[test]
fn certificate_assurance_is_reported() {
    let a = fixture();
    for (label, mutate) in [
        (
            "bound",
            (|m: &mut Module| {
                certificate_mut(m, "ay").assurance.as_mut().unwrap().bound =
                    CoverageBound::Unbounded
            }) as fn(&mut Module),
        ),
        ("digest", |m: &mut Module| {
            certificate_mut(m, "ay")
                .assurance
                .as_mut()
                .unwrap()
                .request_digest = digest(0x99)
        }),
        ("dropped", |m: &mut Module| {
            certificate_mut(m, "ay").assurance = None
        }),
    ] {
        let mut b = a.clone();
        mutate(&mut b);
        assert_ne!(a.stable_digest(), b.stable_digest(), "{label}");
        let (before, after) = certificate_rows(&diff(&a, &b));
        assert!(
            before.contains(";assurance=UnwindBounded { depth: 1 }@sha256:6161"),
            "{label}: {before}"
        );
        assert_ne!(before, after, "{label}");
        assert_hidden_by_ignore_proofs(&a, &b);
    }
}

/// The kernel re-check directive is what makes a `CleanCic` certificate
/// re-checkable at all; it used to be skipped by the fingerprint, so dropping
/// or re-anchoring it diffed empty.
#[test]
fn kernel_recheck_directive_is_reported() {
    let a = fixture();
    for (label, mutate) in [
        (
            "anchor",
            (|m: &mut Module| recheck_mut(m).anchor = "clean_backend_tv".into()) as fn(&mut Module),
        ),
        ("module", |m: &mut Module| {
            recheck_mut(m).module = "App.Other".into()
        }),
        ("theorems", |m: &mut Module| {
            recheck_mut(m).theorems.push("App.Overflow.extra".into())
        }),
        ("axioms", |m: &mut Module| {
            recheck_mut(m).allowed_axioms.clear()
        }),
        ("dropped", |m: &mut Module| {
            match &mut certificate_mut(m, "clean").evidence {
                ProofEvidence::CleanCic { kernel_recheck, .. } => *kernel_recheck = None,
                _ => unreachable!(),
            }
        }),
    ] {
        let mut b = a.clone();
        mutate(&mut b);
        assert_ne!(a.stable_digest(), b.stable_digest(), "{label}");
        let (before, after) = certificate_rows(&diff(&a, &b));
        assert!(
            before.contains(":recheck{module=\"App.Overflow\";anchor=\"clean_island\""),
            "{label}: {before}"
        );
        assert_ne!(before, after, "{label}");
        assert_hidden_by_ignore_proofs(&a, &b);
    }
}

fn bound(m: &Module) -> Module {
    let mut m = m.clone();
    recheck_mut(&mut m).binding = Some(Box::new(CertificateBinding {
        environment_digest: digest(0x81),
        statement_digest: digest(0x82),
        origin_module: None,
        source: Some(SourceDefinitionRef {
            decl: "App.add".into(),
            closure_digest: digest(0x83),
        }),
        callees: vec!["callee".into()],
        environment: Some(IslandEnvironment::new(vec![1, 2, 3])),
    }));
    m
}

/// One named single-field mutation of a fixture module.
type Mutation = fn(&mut Module);

fn binding_mut(m: &mut Module) -> &mut CertificateBinding {
    recheck_mut(m).binding.as_deref_mut().unwrap()
}

/// Every field of a `CertificateBinding` (WS1.12a / WS1.13) and of the two
/// records it nests, `SourceDefinitionRef` and `IslandEnvironment`. Since
/// binary v61 (`CERTIFICATE_BINDING_FORMAT_VERSION`, WS6.7(b)) the binding
/// has a binary carrier, so every mutant must also move `stable_digest`, like
/// every other field this file covers (it was diff-only while the writer
/// refused a bound module); the island's bytes are fingerprinted by their
/// RECOMPUTED digest, so a stale stored digest cannot hide a changed island.
///
/// Review (WS4.13): the mutant labels are held EQUAL to an exhaustive
/// destructure of the three records ([`fields!`]), exactly like the module
/// harness's inventory — `fp_kernel_recheck` destructures them without `..`,
/// and a hand-kept label list could fall behind it (it had: the two
/// `SourceDefinitionRef` fields and the island's stored digest had no
/// mutant, only "drop the whole record").
#[test]
fn certificate_binding_fields_are_reported() {
    let a = bound(&fixture());
    assert!(diff(&a, &a.clone()).is_empty());
    // Gaining a binding is a change.
    let (_, after) = certificate_rows(&diff(&fixture(), &a));
    assert!(
        after.contains(";binding{environment=sha256:8181"),
        "{after}"
    );
    let binding = binding_mut(&mut a.clone()).clone();
    let mut inventory: BTreeSet<&str> = BTreeSet::new();
    inventory.extend(fields!(
        "cert_binding",
        &binding,
        CertificateBinding {
            environment_digest,
            statement_digest,
            origin_module,
            source,
            callees,
            environment,
        }
    ));
    inventory.extend(fields!(
        "source_ref",
        binding.source.as_ref().unwrap(),
        SourceDefinitionRef {
            decl,
            closure_digest,
        }
    ));
    inventory.extend(fields!(
        "island",
        binding.environment.as_ref().unwrap(),
        IslandEnvironment {
            declarations,
            digest,
        }
    ));
    let mutants: [(&str, Mutation); 10] = [
        ("cert_binding.environment_digest", |m| {
            binding_mut(m).environment_digest = digest(0x91)
        }),
        ("cert_binding.statement_digest", |m| {
            binding_mut(m).statement_digest = digest(0x92)
        }),
        ("cert_binding.origin_module", |m| {
            binding_mut(m).origin_module = Some(digest(0x93))
        }),
        ("cert_binding.source", |m| binding_mut(m).source = None),
        ("cert_binding.callees", |m| {
            binding_mut(m).callees.push("other".into())
        }),
        ("cert_binding.environment", |m| {
            binding_mut(m).environment = None
        }),
        // The source definition re-pointed at another declaration, or at the
        // same declaration under another dependency closure.
        ("source_ref.decl", |m| {
            binding_mut(m).source.as_mut().unwrap().decl = "App.sub".into()
        }),
        ("source_ref.closure_digest", |m| {
            binding_mut(m).source.as_mut().unwrap().closure_digest = digest(0x94)
        }),
        // The island's bytes change while its STORED digest is left stale.
        ("island.declarations", |m| {
            binding_mut(m)
                .environment
                .as_mut()
                .unwrap()
                .declarations
                .push(4)
        }),
        // The stored digest changes over UNCHANGED bytes (the other half of
        // a stale island: both digests are rendered).
        ("island.digest", |m| {
            binding_mut(m).environment.as_mut().unwrap().digest = digest(0x95)
        }),
    ];
    assert_eq!(
        mutants
            .iter()
            .map(|(label, _)| *label)
            .collect::<BTreeSet<_>>(),
        inventory,
        "every CertificateBinding / SourceDefinitionRef / IslandEnvironment \
         field needs exactly one mutant here"
    );
    for (label, mutate) in mutants {
        let mut b = a.clone();
        mutate(&mut b);
        assert_ne!(a, b, "{label}: the mutant is a no-op (fixture drift)");
        let (before, after) = certificate_rows(&diff(&a, &b));
        assert_ne!(before, after, "{label}");
        assert_ne!(a.stable_digest(), b.stable_digest(), "{label}");
        assert_hidden_by_ignore_proofs(&a, &b);
    }
}

/// `InheritedFromCallee` names its callee by SYMBOL and its obligation by
/// CLAIM: the renumbered twin keeps the key (see the negative twin), a
/// retarget onto another obligation moves it.
#[test]
fn inherited_from_callee_is_resolved_by_meaning() {
    let a = fixture();
    let mut b = a.clone();
    let live = b
        .proof_obligations
        .iter()
        .find(|o| o.description.starts_with("the counter"))
        .unwrap()
        .id;
    match &mut certificate_mut(&mut b, "compose").evidence {
        ProofEvidence::InheritedFromCallee { obligation, .. } => *obligation = live,
        _ => unreachable!(),
    }
    let (before, after) = certificate_rows(&diff(&a, &b));
    assert!(
        before.contains("ev=inherited:@callee:kind=precondition;fn=callee"),
        "{before}"
    );
    assert!(
        after.contains("ev=inherited:@callee:kind=liveness;fn=_"),
        "{after}"
    );

    // The CALLEE half: re-pointed at another function, or left dangling,
    // is a different claim; neither may collapse onto the original key.
    let caller = func_mut(&mut b, CALLER).id;
    for (label, callee) in [("retarget", caller), ("dangling", FuncId::new(999))] {
        let mut c = a.clone();
        match &mut certificate_mut(&mut c, "compose").evidence {
            ProofEvidence::InheritedFromCallee { callee: slot, .. } => *slot = callee,
            _ => unreachable!(),
        }
        assert_ne!(a.stable_digest(), c.stable_digest(), "{label}");
        let (before, after) = certificate_rows(&diff(&a, &c));
        assert!(
            before.contains("ev=inherited:@callee:"),
            "{label}: {before}"
        );
        match label {
            "retarget" => assert!(after.contains("ev=inherited:@caller:"), "{after}"),
            _ => assert!(after.contains("ev=inherited:#dangling 999:"), "{after}"),
        }
        assert_hidden_by_ignore_proofs(&a, &c);
    }
}

/// Review (WS4.13): a `ProofRef` (fast-1 proof backref) names a module
/// obligation by `ProofId`, exactly like a certificate or a proof context —
/// but the diff rendered it as its RAW index. So the renumbered twin was a
/// spurious change, and, worse, re-pointing the backref by renumbering the
/// obligation table under it (the `ProofRef` keeps its index, the obligation
/// that index names changes) moved `stable_digest` and diffed EMPTY. It is
/// now resolved to the obligation's CLAIM, on a node and on a function.
#[test]
fn proof_ref_is_resolved_by_claim() {
    // Isolate the backref: strip every OTHER citation of an obligation id
    // (certificates, the call's proof context), so nothing but the
    // `ProofRef`s can see the obligation table re-pointed under them.
    let isolated = |m: &Module| {
        let mut m = m.clone();
        m.proof_certificates.clear();
        node_mut(&mut m, 2).proof_context = None;
        m
    };
    let a = isolated(&fixture());
    // The renumbered twin, isolated the same way, still diffs empty.
    assert!(
        diff(&a, &isolated(&fixture_with(TWIN))).is_empty(),
        "{}",
        diff(&a, &isolated(&fixture_with(TWIN))).to_text()
    );

    // Swap the ids of two obligations: every claim is unchanged, so the
    // proof table itself is the same SET, but the node's `ProofRef` (to
    // "p + 1 does not overflow") and the function's (to "caller inherits")
    // now name the OTHER obligation.
    let swap = |m: &mut Module, x: &str, y: &str| {
        let ix = obligation_mut(m, x).id;
        let iy = obligation_mut(m, y).id;
        obligation_mut(m, x).id = iy;
        obligation_mut(m, y).id = ix;
    };
    let mut node = a.clone();
    swap(&mut node, "p + 1", "the counter");
    assert_ne!(a.stable_digest(), node.stable_digest());
    let d = diff(&a, &node);
    assert!(d.proof_state_changes.is_empty(), "{}", d.to_text());
    let text = d.to_text();
    assert!(
        text.contains("ProofRef(kind=arithmetic_safety;fn=caller;desc=p + 1 does not overflow"),
        "{text}"
    );
    assert!(
        text.contains("ProofRef(kind=liveness;fn=_;desc=the counter eventually moves"),
        "{text}"
    );
    match &d.changes[..] {
        [FuncChange::Changed { block_changes, .. }] => assert!(
            matches!(
                &block_changes[..],
                [BlockChange::InstrDiff { visit: 0, instr_changes }]
                    if matches!(&instr_changes[..], [InstrChange::Replaced { index: 1, .. }])
            ),
            "{}",
            d.to_text()
        ),
        other => panic!("{other:?}"),
    }
    assert_hidden_by_ignore_proofs(&a, &node);

    let mut function = a.clone();
    swap(&mut function, "caller inherits", "callee requires");
    assert_ne!(a.stable_digest(), function.stable_digest());
    let changes = proof_on(&diff(&a, &function), CALLER);
    assert!(
        changes.iter().any(|c| matches!(
            c,
            ProofChange::Added { name } if name.starts_with("ProofRef(kind=precondition;fn=callee")
        )),
        "{changes:?}"
    );
    assert_hidden_by_ignore_proofs(&a, &function);

    // A dangling backref keeps a distinct, index-bearing spelling: never a
    // match for a resolved claim, and two dangling ids stay apart.
    let dangle = |id: u32| {
        let mut m = a.clone();
        node_mut(&mut m, 1).proofs[1] = ProofAnnotation::ProofRef(ProofId::new(id));
        m
    };
    let text = diff(&a, &dangle(90)).to_text();
    assert!(text.contains("ProofRef(obl#90)"), "{text}");
    assert!(!diff(&dangle(90), &dangle(91)).is_empty());
}

/// The debug file table's LENGTH is compared (WS4.10 / DG-16: the V3
/// identity blanks the strings and keeps the length); its strings are not.
#[test]
fn files_count_is_reported_and_strings_are_not() {
    let a = fixture();
    let mut b = a.clone();
    b.files.push("/home/a/app/src/third.rs".into());
    assert_ne!(a.stable_digest(), b.stable_digest());
    let d = diff(&a, &b);
    assert!(d.changes.is_empty() && d.proof_state_changes.is_empty());
    assert_eq!(
        d.module_meta_changes,
        vec![MetaChange {
            field: "files".into(),
            before: "2".into(),
            after: "3".into(),
        }]
    );
    assert!(d.to_text().contains("files: 2 -> 3"), "{}", d.to_text());
    // Metadata, never proof coverage: it survives --ignore-proofs.
    let d = diff_with(
        &a,
        &b,
        DiffOptions {
            ignore_proofs: true,
            include_debug: false,
        },
    );
    assert_eq!(d.module_meta_changes.len(), 1);

    // Renaming one entry is the checkout-move case: no digest move, no row.
    let mut c = a.clone();
    c.files[1] = "/elsewhere/src/other.rs".into();
    assert_eq!(a.stable_digest(), c.stable_digest());
    assert!(diff(&a, &c).is_empty());
    // Nor is swapping two entries (same length, strings only).
    let mut c = a.clone();
    c.files.swap(0, 1);
    assert!(diff(&a, &c).is_empty());

    // Review (WS4.13): the table SHRINKING is a change too, down to empty —
    // a length compared only on growth would pass the push above.
    for (keep, after) in [(1, "1"), (0, "0")] {
        let mut c = a.clone();
        c.files.truncate(keep);
        assert_ne!(a.stable_digest(), c.stable_digest(), "keep {keep}");
        assert_eq!(
            diff(&a, &c).module_meta_changes,
            vec![MetaChange {
                field: "files".into(),
                before: "2".into(),
                after: after.into(),
            }],
            "keep {keep}"
        );
    }
}

/// A node's result ARITY: its result ids are renumbering, their COUNT is
/// not. Mutated on the LAST node in walk order (the exit block's `Return`),
/// so no later value's canonical index shifts and the change is exactly one
/// replaced instruction.
#[test]
fn result_arity_is_reported() {
    let a = fixture();
    let mut b = a.clone();
    func_mut(&mut b, CALLER).blocks[1].body[0]
        .results
        .push(ValueId::new(900));
    assert_ne!(a.stable_digest(), b.stable_digest());
    let d = diff(&a, &b);
    let text = d.to_text();
    assert!(
        text.contains("[results=0]") && text.contains("[results=1]"),
        "{text}"
    );
    assert!(d.module_meta_changes.is_empty() && d.proof_state_changes.is_empty());
    match &d.changes[..] {
        [FuncChange::Changed { block_changes, .. }] => match &block_changes[..] {
            [
                BlockChange::InstrDiff {
                    visit: 1,
                    instr_changes,
                },
            ] => {
                assert!(matches!(
                    &instr_changes[..],
                    [InstrChange::Replaced { index: 0, .. }]
                ));
            }
            other => panic!("{other:?}"),
        },
        other => panic!("{other:?}"),
    }
    // Ignoring proofs does not hide it: arity is program shape.
    let d = diff_with(
        &a,
        &b,
        DiffOptions {
            ignore_proofs: true,
            include_debug: false,
        },
    );
    assert!(!d.is_empty());

    // Review (WS4.13): a node that ALREADY binds a result gaining a second
    // (1 -> 2), and one dropping its only result (1 -> 0), are reported too;
    // the arity row is not special to a result-free terminator.
    for (label, arity) in [("grows", 2), ("drops", 0)] {
        let mut c = a.clone();
        let results = &mut func_mut(&mut c, CALLER).blocks[0].body[0].results;
        results.resize(arity, ValueId::new(901));
        assert_ne!(a.stable_digest(), c.stable_digest(), "{label}");
        let text = diff(&a, &c).to_text();
        assert!(
            text.contains("[results=1]") && text.contains(&format!("[results={arity}]")),
            "{label}: {text}"
        );
    }
}

/// The v55 drop-glue table (amendment D) is compared as a sorted multiset of
/// `key type => glue SYMBOL`: declaration order is cosmetic, while a
/// duplicated row, a dangling glue id and a re-pointed glue are each reported
/// as the one `drop_glue` module row.
#[test]
fn drop_glue_rows_are_a_multiset_by_symbol() {
    let a = fixture();
    let glue_rows = |m: &Module| {
        diff(&a, m)
            .module_meta_changes
            .iter()
            .filter(|mc| mc.field == "drop_glue")
            .count()
    };

    // Reordering two rows is cosmetic (the digest moves, the diff does not).
    let mut two = a.clone();
    let caller = func_mut(&mut two, CALLER).id;
    two.drop_glue.push(DropGlueEntry {
        glue: caller,
        ty: Ty::Tuple(vec![Ty::U32, Ty::U32]),
    });
    let mut swapped = two.clone();
    swapped.drop_glue.reverse();
    assert_ne!(two.stable_digest(), swapped.stable_digest());
    assert!(diff(&two, &swapped).is_empty());

    // A duplicated row is not absorbed by the comparison.
    let mut dup = a.clone();
    let row = dup.drop_glue[0].clone();
    dup.drop_glue.push(row);
    assert_eq!(glue_rows(&dup), 1);

    // A dangling glue id has its own spelling, never a function's symbol.
    let mut dangling = a.clone();
    dangling.drop_glue[0].glue = FuncId::new(4242);
    assert_eq!(glue_rows(&dangling), 1);
}

// ---------------------------------------------------------------------------
// Mutation control: every stable_digest-moving single-field mutant is seen
// ---------------------------------------------------------------------------

/// What a mutant must produce.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Expect {
    /// A non-empty default diff.
    Reported,
    /// An EMPTY default diff: a debug field `diff.rs` documents as ignored.
    /// The mutant must still move `stable_digest` (so the exclusion is a
    /// decision, not an accident of the fixture).
    Ignored,
}

/// One single-field mutant. `field` is `carrier.field`, exactly as the
/// inventory below spells it; `digest` is false only for carriers the binary
/// writer cannot encode yet (their mutants cannot move a digest).
struct Mutant {
    field: &'static str,
    expect: Expect,
    digest: bool,
    apply: fn(&mut Module),
}

const fn reported(field: &'static str, apply: fn(&mut Module)) -> Mutant {
    Mutant {
        field,
        expect: Expect::Reported,
        digest: true,
        apply,
    }
}

const fn ignored(field: &'static str, apply: fn(&mut Module)) -> Mutant {
    Mutant {
        field,
        expect: Expect::Ignored,
        digest: true,
        apply,
    }
}

const fn reported_unencodable(field: &'static str, apply: fn(&mut Module)) -> Mutant {
    Mutant {
        field,
        expect: Expect::Reported,
        digest: false,
        apply,
    }
}

fn clause_mut(m: &mut Module) -> &mut ProofFormula {
    &mut summary_mut(m).requires[0]
}

fn global_mut<'m>(m: &'m mut Module, name: &str) -> &'m mut Global {
    m.globals.iter_mut().find(|g| g.name == name).unwrap()
}

/// The single-field mutant generator (shared data; WS4.11's merge tests can
/// iterate it too).
const MUTANTS: &[Mutant] = &[
    // --- Module ------------------------------------------------------------
    ignored("module.name", |m| m.name = "renamed".into()),
    reported("module.functions", |m| {
        let mut f = m.functions[0].clone();
        f.name = "copy".into();
        f.id = FuncId::new(77);
        m.functions.push(f)
    }),
    reported("module.structs", |m| m.structs[0].fields[0].ty = Ty::U64),
    reported("module.globals", |m| m.globals.pop().map(drop).unwrap()),
    reported("module.proof_obligations", |m| {
        m.proof_obligations.push(ProofObligation::new(
            ProofId::new(40),
            ObligationKind::PanicFreedom,
            ProofStatus::Pending,
            "extra",
        ))
    }),
    reported("module.proof_certificates", |m| {
        m.proof_certificates.pop().map(drop).unwrap()
    }),
    reported("module.target_info", |m| m.target_info = None),
    reported("module.files", |m| m.files.push("x.rs".into())),
    ignored("module.obligation_diagnostics", |m| {
        m.obligation_diagnostics[0].message = "changed".into()
    }),
    reported("module.spec_modules", |m| {
        m.spec_modules.push(SpecModule::design_only("Other"))
    }),
    reported("module.global_asm", |m| m.global_asm.clear()),
    reported("module.imports", |m| {
        m.imports.push(ModuleImport::new("dep2", digest(0x72)))
    }),
    reported("module.tuple_layouts", |m| m.tuple_layouts.clear()),
    reported_unencodable("module.completeness", |m| {
        m.completeness = Some(ModuleCompleteness::Complete)
    }),
    reported("module.closure_layouts", |m| m.closure_layouts.clear()),
    reported("module.blobs", |m| m.blobs.clear()),
    // --- Function ------------------------------------------------------------
    reported("function.name", |m| {
        func_mut(m, CALLER).name = "caller2".into()
    }),
    reported("function.ty", |m| {
        let ft = m
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::U64],
                returns: vec![Ty::U32],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        func_mut(m, CALLER).ty = ft
    }),
    reported("function.entry", |m| {
        let f = func_mut(m, CALLER);
        f.entry = f.blocks[1].id
    }),
    reported("function.blocks", |m| {
        func_mut(m, CALLER).blocks.pop().map(drop).unwrap()
    }),
    reported("function.proofs", |m| {
        func_mut(m, CALLER).proofs.push(ProofAnnotation::Pure)
    }),
    // The fixture keeps the default `C`; `Fast` is a pre-v45 tag, so the
    // mutant stays encodable at the fixture's wire version.
    reported("function.calling_conv", |m| {
        func_mut(m, CALLER).calling_conv = CallingConv::Fast
    }),
    reported("function.linkage", |m| {
        func_mut(m, CALLER).linkage = Linkage::Internal
    }),
    reported("function.attrs", |m| {
        func_mut(m, CALLER).attrs = FuncAttrs {
            cold: true,
            naked: true,
            ..FuncAttrs::default()
        }
    }),
    // --- FuncAttrs -------------------------------------------------------------
    reported("attrs.readonly", |m| {
        func_mut(m, CALLER).attrs.readonly = true
    }),
    reported("attrs.readnone", |m| {
        func_mut(m, CALLER).attrs.readnone = true
    }),
    reported("attrs.inlinehint", |m| {
        func_mut(m, CALLER).attrs.inlinehint = true
    }),
    reported("attrs.cold", |m| func_mut(m, CALLER).attrs.cold = true),
    reported("attrs.params", |m| {
        func_mut(m, CALLER).attrs.params.push(ParamAttrs {
            noalias: true,
            ..ParamAttrs::default()
        })
    }),
    reported("attrs.naked", |m| func_mut(m, CALLER).attrs.naked = true),
    reported("attrs.target_features", |m| {
        func_mut(m, CALLER)
            .attrs
            .target_features
            .push("neon".into())
    }),
    reported("attrs.ret", |m| {
        func_mut(m, CALLER).attrs.ret.nonnull = true
    }),
    // --- ParamAttrs: every field of one slot (the return slot), one at a time.
    // `attrs.params` / `attrs.ret` above only prove a slot is compared at all;
    // these prove no field of the slot's record is dropped from its
    // fingerprint (review, WS4.13: `slot_attrs_fp` is destructured
    // exhaustively, so the harness enumerates the same record).
    reported("param.dereferenceable", |m| {
        func_mut(m, CALLER).attrs.ret.dereferenceable = Some(8)
    }),
    reported("param.nonnull", |m| {
        func_mut(m, CALLER).attrs.ret.nonnull = true
    }),
    reported("param.align", |m| {
        func_mut(m, CALLER).attrs.ret.align = Some(16)
    }),
    reported("param.noalias", |m| {
        func_mut(m, CALLER).attrs.ret.noalias = true
    }),
    reported("param.readonly", |m| {
        func_mut(m, CALLER).attrs.ret.readonly = true
    }),
    reported("param.byval", |m| {
        func_mut(m, CALLER).attrs.ret.byval = true
    }),
    reported("param.sret", |m| func_mut(m, CALLER).attrs.ret.sret = true),
    reported("param.ext", |m| {
        func_mut(m, CALLER).attrs.ret.ext = ArgExt::ZeroExt
    }),
    reported("param.pass", |m| {
        func_mut(m, CALLER).attrs.ret.pass = Some(PassMode::Direct)
    }),
    reported("function.summary", |m| func_mut(m, CALLEE).summary = None),
    reported("function.producer", |m| func_mut(m, CALLER).producer = None),
    ignored("function.value_names", |m| {
        func_mut(m, CALLER).value_names = Some(vec![])
    }),
    ignored("function.scopes", |m| {
        func_mut(m, CALLER)
            .scopes
            .as_mut()
            .unwrap()
            .push(ScopeData::new(Some(0), None))
    }),
    reported("function.source_provenance", |m| {
        func_mut(m, CALLER)
            .source_provenance
            .as_mut()
            .unwrap()
            .binding_digest = digest(0x5f)
    }),
    reported("function.body_gate", |m| {
        func_mut(m, CALLER).body_gate = Some(BodyGate::Ungated)
    }),
    reported("function.display_path", |m| {
        func_mut(m, CALLER).display_path = None
    }),
    reported("function.section", |m| {
        func_mut(m, CALLER).section = Some(".text.hot".into())
    }),
    reported("function.visibility", |m| {
        func_mut(m, CALLER).visibility = Visibility::Protected
    }),
    reported("function.retained", |m| func_mut(m, CALLER).retained = true),
    // --- Block ---------------------------------------------------------------
    reported("block.params", |m| {
        func_mut(m, CALLER).blocks[1].params[0].1 = Ty::I64
    }),
    reported("block.body", |m| {
        func_mut(m, CALLER).blocks[1].body.insert(
            0,
            InstrNode::new(Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(901)),
        )
    }),
    // --- InstrNode -----------------------------------------------------------
    reported("node.inst", |m| {
        node_mut(m, 0).inst = Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(2),
        }
    }),
    reported("node.results", |m| {
        node_mut(m, 3).results.push(ValueId::new(902))
    }),
    reported("node.proofs", |m| node_mut(m, 1).proofs.clear()),
    ignored("node.span", |m| {
        node_mut(m, 1).span = Some(SourceSpan {
            file: 1,
            line: 9,
            col: 9,
        })
    }),
    reported("node.proof_context", |m| {
        node_mut(m, 2).proof_context = None
    }),
    // --- ProofContext ----------------------------------------------------------
    reported("context.assumes", |m| {
        node_mut(m, 2)
            .proof_context
            .as_mut()
            .unwrap()
            .assumes
            .clear()
    }),
    reported("context.establishes", |m| {
        node_mut(m, 2)
            .proof_context
            .as_mut()
            .unwrap()
            .establishes
            .clear()
    }),
    ignored("node.scope", |m| node_mut(m, 1).scope = None),
    // --- FunctionSummary -----------------------------------------------------
    reported("summary.requires", |m| summary_mut(m).requires.clear()),
    reported("summary.ensures", |m| summary_mut(m).ensures.clear()),
    reported("summary.params", |m| {
        summary_mut(m).params = vec!["y".into()]
    }),
    reported("summary.proved", |m| summary_mut(m).proved = false),
    reported("summary.decreases", |m| summary_mut(m).decreases.clear()),
    reported("summary.backed_by", |m| summary_mut(m).backed_by = None),
    reported("summary.effects", |m| summary_mut(m).effects = None),
    // --- EffectSummary (the summary's `effects`, v59) ---------------------------
    reported("effects.reads", |m| {
        effects_mut(m).reads = EffectSet::Everything
    }),
    reported("effects.writes", |m| {
        effects_mut(m).writes = EffectSet::of([EffectPlace::ParamPointee { index: 0 }])
    }),
    reported("effects.allocates", |m| effects_mut(m).allocates = false),
    reported("effects.frees", |m| effects_mut(m).frees = true),
    reported("effects.may_unwind", |m| effects_mut(m).may_unwind = false),
    reported("effects.io", |m| effects_mut(m).io = true),
    // --- ExternRef (the summary's `backed_by`) ---------------------------------
    reported("extern.module", |m| {
        let other = m
            .imports
            .iter()
            .position(|i| i.name == "dep_b")
            .map(|i| ImportId::new(i as u32))
            .unwrap();
        summary_mut(m).backed_by.as_mut().unwrap().module = other
    }),
    reported("extern.symbol", |m| {
        summary_mut(m).backed_by.as_mut().unwrap().symbol = "dep_other".into()
    }),
    reported("extern.obligation", |m| {
        summary_mut(m).backed_by.as_mut().unwrap().obligation = Some(ProofId::new(3))
    }),
    // --- ProofFormula (a summary clause) -------------------------------------
    reported("formula.schema", |m| {
        clause_mut(m).schema = "trust-types.Formula@1".into()
    }),
    reported("formula.payload", |m| {
        let text = "(bvugt x #x0000000000000000)".to_string();
        clause_mut(m).payload = text.clone();
        clause_mut(m).smtlib = Some(text)
    }),
    reported("formula.smtlib", |m| clause_mut(m).smtlib = None),
    reported("formula.sort", |m| clause_mut(m).sort = None),
    reported("formula.bindings", |m| clause_mut(m).bindings.clear()),
    // --- ClauseBinding (a summary clause's) ------------------------------------
    reported("binding.sort", |m| {
        clause_mut(m).bindings[0].1.sort = ClauseSort::Int
    }),
    reported("binding.place", |m| {
        clause_mut(m).bindings[0].1.place = ClausePlace::Param { index: 1 }
    }),
    // --- ProofObligation -----------------------------------------------------
    reported("obligation.kind", |m| {
        obligation_mut(m, "caller inherits").kind = ObligationKind::Termination
    }),
    reported("obligation.status", |m| {
        obligation_mut(m, "caller inherits").status = ProofStatus::Failed
    }),
    reported("obligation.description", |m| {
        obligation_mut(m, "caller inherits").description = "caller inherits it".into()
    }),
    reported("obligation.formula", |m| {
        obligation_mut(m, "p + 1")
            .formula
            .as_mut()
            .unwrap()
            .bindings[1]
            .1
            .place = ClausePlace::Param { index: 1 }
    }),
    reported("obligation.function", |m| {
        let callee = func_mut(m, CALLEE).id;
        obligation_mut(m, "caller inherits").function = Some(callee)
    }),
    reported("obligation.source", |m| {
        obligation_mut(m, "callee requires").source =
            Some(ProofObligationSourceIdentity::new("src/lib.rs", "req.1"))
    }),
    reported("obligation.site", |m| {
        obligation_mut(m, "p + 1").site = None
    }),
    reported("obligation.spec", |m| {
        obligation_mut(m, "the counter").spec = None
    }),
    // --- SpecObligationRef -----------------------------------------------------
    reported("spec_ref.machine", |m| {
        obligation_mut(m, "the counter")
            .spec
            .as_mut()
            .unwrap()
            .machine = "Counter2".into()
    }),
    reported("spec_ref.temporal", |m| {
        obligation_mut(m, "the counter")
            .spec
            .as_mut()
            .unwrap()
            .temporal = "Stays".into()
    }),
    // --- ObligationSite --------------------------------------------------------
    reported("site.function", |m| {
        let callee = func_mut(m, CALLEE).id;
        obligation_mut(m, "p + 1").site.as_mut().unwrap().function = callee
    }),
    reported("site.block", |m| {
        let exit = func_mut(m, CALLER).blocks[1].id;
        obligation_mut(m, "p + 1").site.as_mut().unwrap().block = exit
    }),
    reported("site.inst_index", |m| {
        obligation_mut(m, "p + 1").site.as_mut().unwrap().inst_index = 0
    }),
    // --- ProofCertificate ----------------------------------------------------
    reported("certificate.obligation", |m| {
        let live = obligation_mut(m, "the counter").id;
        certificate_mut(m, "ay").obligation = live
    }),
    reported("certificate.prover", |m| {
        certificate_mut(m, "ay").prover = "z3".into()
    }),
    reported("certificate.evidence", |m| {
        certificate_mut(m, "ay").evidence = ProofEvidence::SmtProof(vec![9])
    }),
    reported("certificate.assurance", |m| {
        certificate_mut(m, "ay").assurance = None
    }),
    // --- CoverageAssurance -----------------------------------------------------
    reported("assurance.bound", |m| {
        certificate_mut(m, "ay").assurance.as_mut().unwrap().bound = CoverageBound::Unbounded
    }),
    reported("assurance.request_digest", |m| {
        certificate_mut(m, "ay")
            .assurance
            .as_mut()
            .unwrap()
            .request_digest = digest(0x99)
    }),
    // --- CleanCicKernelRecheck -----------------------------------------------
    reported("recheck.module", |m| recheck_mut(m).module = "M2".into()),
    reported("recheck.theorems", |m| recheck_mut(m).theorems.clear()),
    reported("recheck.anchor", |m| recheck_mut(m).anchor = "other".into()),
    reported("recheck.allowed_axioms", |m| {
        recheck_mut(m).allowed_axioms.clear()
    }),
    reported_unencodable("recheck.binding", |m| {
        *m = bound(m);
    }),
    // --- Global ----------------------------------------------------------------
    reported("global.name", |m| {
        global_mut(m, "PAIR").name = "PAIR2".into()
    }),
    reported("global.ty", |m| global_mut(m, "COUNTER").ty = Ty::I64),
    reported("global.mutable", |m| {
        global_mut(m, "COUNTER").mutable = false
    }),
    reported("global.initializer", |m| {
        global_mut(m, "COUNTER").initializer = Some(Constant::Int(4))
    }),
    reported("global.linkage", |m| {
        global_mut(m, "COUNTER").linkage = Linkage::Internal
    }),
    reported("global.tls", |m| global_mut(m, "COUNTER").tls = None),
    reported("global.align", |m| {
        global_mut(m, "COUNTER").align = Some(16)
    }),
    reported("global.section", |m| {
        global_mut(m, "COUNTER").section = None
    }),
    reported("global.visibility", |m| {
        global_mut(m, "COUNTER").visibility = Visibility::Default
    }),
    reported("global.retained", |m| {
        global_mut(m, "COUNTER").retained = false
    }),
    // --- TargetInfo ------------------------------------------------------------
    reported("target.triple", |m| {
        m.target_info.as_mut().unwrap().triple = "x86_64-unknown-linux-gnu".into()
    }),
    reported("target.pointer_size", |m| {
        m.target_info.as_mut().unwrap().pointer_size = 4
    }),
    reported("target.endianness", |m| {
        m.target_info.as_mut().unwrap().endianness = Endianness::Big
    }),
    reported("target.abi", |m| m.target_info.as_mut().unwrap().abi = None),
    reported("target.struct_passing", |m| {
        m.target_info.as_mut().unwrap().struct_passing = trust_ir::StructPassingPolicy::Unclassified
    }),
    // --- ModuleImport ----------------------------------------------------------
    reported("import.name", |m| m.imports[0].name = "dep_renamed".into()),
    reported("import.digest", |m| m.imports[0].digest = digest(0x7f)),
    reported("import.producer", |m| {
        m.imports[0].producer = Some(Producer::Clean)
    }),
    // `ModuleImport::new` records `IdentityScheme::CURRENT` (V3); the mutant
    // re-labels the row as a legacy V2 digest.
    reported("import.scheme", |m| {
        m.imports[0].scheme = trust_ir::IdentityScheme::V2
    }),
    // --- TupleLayoutDescriptor -------------------------------------------------
    reported("tuple_layout.tuple_type", |m| {
        let other = m
            .types
            .iter()
            .position(|t| *t == Ty::Tuple(vec![Ty::U32, Ty::U16]))
            .map(|i| trust_ir::TyId::new(i as u32))
            .unwrap();
        m.tuple_layouts[0].tuple_type = other
    }),
    reported("tuple_layout.size", |m| m.tuple_layouts[0].size = 16),
    reported("tuple_layout.align", |m| m.tuple_layouts[0].align = 8),
    reported("tuple_layout.field_offsets", |m| {
        m.tuple_layouts[0].field_offsets = vec![4, 0]
    }),
    // --- DropGlueEntry (v55, amendment D) --------------------------------------
    reported("module.drop_glue", |m| m.drop_glue.clear()),
    reported("drop_glue.glue", |m| {
        let other = func_mut(m, CALLER).id;
        m.drop_glue[0].glue = other
    }),
    reported("drop_glue.ty", |m| {
        m.drop_glue[0].ty = Ty::Tuple(vec![Ty::U32, Ty::U32])
    }),
    // --- ClosureLayoutDescriptor (v58, WS3.9) ------------------------------------
    reported("closure_layout.closure", |m| {
        let framed = m.closure_layouts[0].closure;
        let other = (0..m.closure_types.len())
            .map(|i| ClosureTyId::new(i as u32))
            .find(|id| *id != framed)
            .unwrap();
        m.closure_layouts[0].closure = other
    }),
    reported("closure_layout.origin", |m| {
        m.closure_layouts[0].origin = Some(TypeOrigin::Clean {
            decl: "Changed.Closure".into(),
            env_digest: ProofDigest::sha256([7; 32]),
        });
    }),
    reported("closure_layout.size", |m| m.closure_layouts[0].size = 16),
    reported("closure_layout.align", |m| m.closure_layouts[0].align = 8),
    reported("closure_layout.capture_offsets", |m| {
        m.closure_layouts[0].capture_offsets = vec![4, 0]
    }),
    // --- Blob (v70, PKG-U13e) -----------------------------------------------------
    reported("blob.digest", |m| {
        m.blobs[0].digest = BlobDigest::of(b"other")
    }),
    reported("blob.data", |m| m.blobs[0].data.push(5)),
    // --- StructDef (fingerprinted at its use by the `PAIR` global) -------------
    reported("struct.name", |m| m.structs[0].name = "Pair2".into()),
    reported("struct.fields", |m| {
        m.structs[0].fields.push(FieldDef {
            name: "c".into(),
            ty: Ty::U8,
            offset: None,
        })
    }),
    reported("struct.size", |m| m.structs[0].size = Some(16)),
    reported("struct.align", |m| m.structs[0].align = Some(8)),
    reported("struct.repr", |m| m.structs[0].repr = StructRepr::Rust),
    reported("struct.origin", |m| {
        m.structs[0].origin = Some(rust_origin(0xa2))
    }),
    // --- EnumDef (fingerprinted at its use by the `MODE` global) ---------------
    reported("enum.name", |m| m.enums[0].name = "Mode2".into()),
    reported("enum.variants", |m| {
        m.enums[0].variants.push(unit_variant("Auto"))
    }),
    reported("enum.discriminants", |m| {
        m.enums[0].discriminants = vec![Some(1), Some(3)]
    }),
    reported("enum.repr", |m| m.enums[0].repr = Some(EnumTagRepr::U32)),
    reported("enum.layout", |m| m.enums[0].layout = None),
    reported("enum.origin", |m| m.enums[0].origin = None),
    // --- SpecModule ------------------------------------------------------------
    reported("spec.name", |m| m.spec_modules[0].name = "Counter2".into()),
    reported("spec.vars", |m| m.spec_modules[0].vars.clear()),
    reported("spec.actions", |m| {
        m.spec_modules[0].actions.push("Dec".into())
    }),
    reported("spec.invariants", |m| m.spec_modules[0].invariants.clear()),
    reported("spec.anchors", |m| m.spec_modules[0].anchors.clear()),
    // --- SpecAnchor ------------------------------------------------------------
    reported("anchor.machine", |m| {
        m.spec_modules[0].anchors[0].machine = "Other".into()
    }),
    reported("anchor.action", |m| {
        m.spec_modules[0].anchors[0].action = "Dec".into()
    }),
    reported("anchor.rust_symbol", |m| {
        m.spec_modules[0].anchors[0].rust_symbol = "other".into()
    }),
    reported("anchor.span", |m| {
        m.spec_modules[0].anchors[0].span = "src/lib.rs:4".into()
    }),
    reported("anchor.project", |m| {
        m.spec_modules[0].anchors[0].project = Some("app".into())
    }),
    reported("anchor.function", |m| {
        let callee = func_mut(m, CALLEE).id;
        m.spec_modules[0].anchors[0].function = Some(callee)
    }),
    reported("anchor.projection_target", |m| {
        m.spec_modules[0].anchors[0].projection_target =
            Some(trust_ir::spec::SpecProjectionTarget::TemporalFieldPathsV1)
    }),
    reported("spec.waivers", |m| m.spec_modules[0].waivers.clear()),
    reported("spec.proofs", |m| m.spec_modules[0].proofs.clear()),
    reported("spec.origin", |m| {
        m.spec_modules[0].origin = trust_ir::spec::SpecOrigin::External("counter.tla".into())
    }),
    reported("spec.enforcement", |m| {
        m.spec_modules[0].enforcement = trust_ir::spec::SpecEnforcementMode::Linked
    }),
    reported("spec.temporal", |m| m.spec_modules[0].temporal.clear()),
];

/// How a carrier field is covered by the harness.
enum Coverage {
    /// At least one entry of [`MUTANTS`] names this field.
    Mutated,
    /// Not mutated directly, for the stated reason.
    Structural(&'static str),
}

const TABLE: &str = "a definition table: fingerprinted structurally at every use \
                     (module.structs is the mutated representative), an unused row is \
                     invisible by design (diff.rs module doc)";

/// The fields NOT mutated directly, each with its reason. Every other
/// inventory field must have a mutant.
const STRUCTURAL: &[(&str, &str)] = &[
    ("module.enums", TABLE),
    ("module.records", TABLE),
    ("module.closure_types", TABLE),
    ("module.func_types", TABLE),
    ("module.types", TABLE),
    ("module.universes", TABLE),
    ("module.predicates", TABLE),
    (
        "struct.id",
        "renumbering: a definition is fingerprinted structurally at every use",
    ),
    (
        "enum.id",
        "renumbering: a definition is fingerprinted structurally at every use",
    ),
    (
        "function.id",
        "renumbering: functions are matched by symbol (negative twin)",
    ),
    (
        "block.id",
        "renumbering: blocks are matched by DFS visit order (negative twin)",
    ),
    (
        "obligation.id",
        "renumbering: obligations are matched by claim, every citation (certificate, \
         proof context, ProofRef) resolves by claim (negative twin; \
         proof_ref_is_resolved_by_claim)",
    ),
];

/// The field inventory, derived from EXHAUSTIVE destructures of every carrier
/// the diff reads ([`fields!`]): a field added to any of them fails to build
/// this function, and the build fix puts it in the inventory, where
/// [`every_carrier_field_has_a_mutant_or_a_stated_reason`] demands a mutant
/// or a [`STRUCTURAL`] reason (the WS4.2 `text_loss` pattern, mirrored from
/// `diff.rs` so the harness cannot silently fall behind the diff).
fn inventory(m: &Module) -> Vec<(&'static str, Coverage)> {
    let caller = m.functions.iter().find(|f| f.name == CALLER).unwrap();
    let callee = m.functions.iter().find(|f| f.name == CALLEE).unwrap();
    let ovf = m
        .proof_obligations
        .iter()
        .find(|o| o.description.starts_with("p + 1"))
        .unwrap();
    let recheck = CleanCicKernelRecheck {
        module: String::new(),
        theorems: Vec::new(),
        anchor: String::new(),
        allowed_axioms: Vec::new(),
        binding: None,
    };
    let mut names: Vec<&'static str> = Vec::new();
    names.extend(fields!(
        "module",
        m,
        Module {
            name,
            functions,
            structs,
            enums,
            records,
            closure_types,
            globals,
            func_types,
            types,
            proof_obligations,
            proof_certificates,
            target_info,
            files,
            obligation_diagnostics,
            spec_modules,
            universes,
            predicates,
            global_asm,
            imports,
            tuple_layouts,
            completeness,
            drop_glue,
            closure_layouts,
            blobs,
        }
    ));
    names.extend(fields!(
        "function",
        caller,
        Function {
            id,
            name,
            ty,
            entry,
            blocks,
            proofs,
            calling_conv,
            linkage,
            attrs,
            summary,
            producer,
            value_names,
            scopes,
            source_provenance,
            body_gate,
            display_path,
            section,
            visibility,
            retained,
        }
    ));
    names.extend(fields!(
        "attrs",
        &caller.attrs,
        FuncAttrs {
            readonly,
            readnone,
            inlinehint,
            cold,
            params,
            naked,
            target_features,
            ret,
        }
    ));
    names.extend(fields!(
        "param",
        &caller.attrs.ret,
        ParamAttrs {
            dereferenceable,
            nonnull,
            align,
            noalias,
            readonly,
            byval,
            sret,
            ext,
            pass,
        }
    ));
    names.extend(fields!(
        "block",
        &caller.blocks[0],
        Block { id, params, body }
    ));
    names.extend(fields!(
        "node",
        &caller.blocks[0].body[0],
        InstrNode {
            inst,
            results,
            proofs,
            span,
            proof_context,
            scope,
        }
    ));
    names.extend(fields!(
        "context",
        &ProofContext::default(),
        ProofContext {
            assumes,
            establishes,
        }
    ));
    names.extend(fields!(
        "summary",
        callee.summary.as_ref().unwrap(),
        FunctionSummary {
            requires,
            ensures,
            params,
            proved,
            decreases,
            backed_by,
            effects,
        }
    ));
    names.extend(fields!(
        "effects",
        callee
            .summary
            .as_ref()
            .and_then(|s| s.effects.as_ref())
            .unwrap(),
        EffectSummary {
            reads,
            writes,
            allocates,
            frees,
            may_unwind,
            io,
        }
    ));
    names.extend(fields!(
        "extern",
        &ExternRef::new(ImportId::new(0), "s"),
        ExternRef {
            module,
            symbol,
            obligation,
        }
    ));
    names.extend(fields!(
        "formula",
        &ProofFormula::new("s", "p"),
        ProofFormula {
            schema,
            payload,
            smtlib,
            sort,
            bindings,
        }
    ));
    names.extend(fields!(
        "binding",
        &bv64("x", ClausePlace::World).1,
        ClauseBinding { sort, place }
    ));
    names.extend(fields!(
        "obligation",
        ovf,
        ProofObligation {
            id,
            kind,
            status,
            description,
            formula,
            function,
            source,
            site,
            spec,
        }
    ));
    names.extend(fields!(
        "site",
        ovf.site.as_ref().unwrap(),
        ObligationSite {
            function,
            block,
            inst_index,
        }
    ));
    let live = m
        .proof_obligations
        .iter()
        .find(|o| o.description.starts_with("the counter"))
        .unwrap();
    names.extend(fields!(
        "spec_ref",
        live.spec.as_ref().unwrap(),
        SpecObligationRef { machine, temporal }
    ));
    names.extend(fields!(
        "certificate",
        &m.proof_certificates[0],
        ProofCertificate {
            obligation,
            prover,
            evidence,
            assurance,
        }
    ));
    names.extend(fields!(
        "assurance",
        m.proof_certificates[0].assurance.as_ref().unwrap(),
        CoverageAssurance {
            bound,
            request_digest
        }
    ));
    names.extend(fields!(
        "recheck",
        &recheck,
        CleanCicKernelRecheck {
            module,
            theorems,
            anchor,
            allowed_axioms,
            binding,
        }
    ));
    names.extend(fields!(
        "global",
        &m.globals[0],
        Global {
            name,
            ty,
            mutable,
            initializer,
            linkage,
            tls,
            align,
            section,
            visibility,
            retained,
        }
    ));
    names.extend(fields!(
        "target",
        m.target_info.as_ref().unwrap(),
        TargetInfo {
            triple,
            pointer_size,
            endianness,
            abi,
            struct_passing,
        }
    ));
    names.extend(fields!(
        "import",
        &m.imports[0],
        ModuleImport {
            name,
            digest,
            producer,
            scheme,
        }
    ));
    names.extend(fields!(
        "tuple_layout",
        &m.tuple_layouts[0],
        TupleLayoutDescriptor {
            tuple_type,
            size,
            align,
            field_offsets,
        }
    ));
    names.extend(fields!(
        "drop_glue",
        &m.drop_glue[0],
        DropGlueEntry { glue, ty }
    ));
    names.extend(fields!("blob", &m.blobs[0], Blob { digest, data }));
    names.extend(fields!(
        "closure_layout",
        &m.closure_layouts[0],
        ClosureLayoutDescriptor {
            origin,
            closure,
            size,
            align,
            capture_offsets,
        }
    ));
    names.extend(fields!(
        "struct",
        &m.structs[0],
        StructDef {
            id,
            name,
            fields,
            size,
            align,
            repr,
            origin,
        }
    ));
    names.extend(fields!(
        "enum",
        &m.enums[0],
        EnumDef {
            id,
            name,
            variants,
            discriminants,
            repr,
            layout,
            origin,
        }
    ));
    names.extend(fields!(
        "spec",
        &m.spec_modules[0],
        SpecModule {
            name,
            vars,
            actions,
            invariants,
            anchors,
            waivers,
            proofs,
            origin,
            enforcement,
            temporal,
        }
    ));
    names.extend(fields!(
        "anchor",
        &m.spec_modules[0].anchors[0],
        SpecAnchor {
            machine,
            action,
            rust_symbol,
            span,
            project,
            function,
            projection_target,
        }
    ));
    names
        .into_iter()
        .map(|name| {
            let coverage = STRUCTURAL
                .iter()
                .find(|(field, _)| *field == name)
                .map_or(Coverage::Mutated, |(_, reason)| {
                    Coverage::Structural(reason)
                });
            (name, coverage)
        })
        .collect()
}

/// The documented exclusions (`diff.rs` module doc, "What is ignored").
const DOCUMENTED_IGNORED: &[&str] = &[
    "module.name",
    "module.obligation_diagnostics",
    "function.value_names",
    "function.scopes",
    "node.span",
    "node.scope",
];

#[test]
fn every_carrier_field_has_a_mutant_or_a_stated_reason() {
    let m = fixture();
    let inventory = inventory(&m);
    let names: BTreeSet<&str> = inventory.iter().map(|(f, _)| *f).collect();
    assert_eq!(names.len(), inventory.len(), "duplicate inventory row");
    let mutated: BTreeSet<&str> = MUTANTS.iter().map(|mu| mu.field).collect();
    for (field, coverage) in &inventory {
        match coverage {
            Coverage::Mutated => assert!(mutated.contains(field), "no mutant for {field}"),
            Coverage::Structural(reason) => {
                assert!(!reason.is_empty());
                assert!(!mutated.contains(field), "{field} is both");
            }
        }
    }
    for field in &mutated {
        assert!(names.contains(field), "mutant for unknown field {field}");
    }
    for (field, _) in STRUCTURAL {
        assert!(names.contains(field), "stale STRUCTURAL row {field}");
    }
    // The Ignored mutants are EXACTLY the documented exclusions.
    let ignored: BTreeSet<&str> = MUTANTS
        .iter()
        .filter(|mu| mu.expect == Expect::Ignored)
        .map(|mu| mu.field)
        .collect();
    assert_eq!(
        ignored,
        DOCUMENTED_IGNORED.iter().copied().collect::<BTreeSet<_>>()
    );
}

/// THE mutation control (roadmap WS4.13): every single-field mutant that
/// moves `Module::stable_digest` produces a non-empty diff, except the
/// documented debug fields, which must diff empty. A diff that fell blind to
/// any carrier field again — or a fixture drift that turned a mutant into a
/// no-op — fails here, naming the field.
#[test]
fn every_digest_moving_mutant_is_seen() {
    let base = fixture();
    let base_digest = base.stable_digest();
    // Every mutant is checked and EVERY failure is reported together, so one
    // run names the whole set a regression (or a fixture drift) touched.
    let mut failures = Vec::new();
    for mutant in MUTANTS {
        let field = mutant.field;
        let mut m = base.clone();
        (mutant.apply)(&mut m);
        if m == base {
            failures.push(format!("{field}: the mutant is a no-op (fixture drift)"));
            continue;
        }
        if mutant.digest && m.stable_digest() == base_digest {
            failures.push(format!(
                "{field}: the mutant does not move stable_digest (fixture drift)"
            ));
        }
        let d = diff(&base, &m);
        match mutant.expect {
            Expect::Reported if d.is_empty() => {
                failures.push(format!("{field}: moves the module but diffs EMPTY"));
            }
            Expect::Ignored if !d.is_empty() => failures.push(format!(
                "{field}: a documented debug field diffs non-empty:\n{}",
                d.to_text()
            )),
            _ => {}
        }
        // And the reverse direction agrees.
        if diff(&m, &base).is_empty() != d.is_empty() {
            failures.push(format!("{field}: asymmetric"));
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} mutants failed:\n{}",
        failures.len(),
        MUTANTS.len(),
        failures.join("\n")
    );
    // A ratchet floor at the measured count (156 when WS4.13 landed: 97 from
    // the implementation, plus the review's 42 sub-carrier mutants — attrs,
    // the nine `ParamAttrs` fields, proof context, backed_by extern ref,
    // clause binding, site, the obligation's spec reference, assurance,
    // tuple layout, spec anchor — plus 3 for main's v55 drop-glue table (the
    // module row and its entry's two fields) and 17 for WS3.9's v58 surface:
    // the module's closure-layout table, its four descriptor fields, and the
    // struct and enum definitions whose nominal `origin` key it added): the
    // generator may grow, never shrink. The inventory test above is the
    // per-field half of the same guarantee.
    assert!(
        MUTANTS.len() >= 159,
        "the generator shrank to {} mutants",
        MUTANTS.len()
    );
}

/// The opt-in debug lane sees the one ignored field it exists for.
#[test]
fn include_debug_reports_the_scope_tree_mutant() {
    let base = fixture();
    let mutant = MUTANTS
        .iter()
        .find(|mu| mu.field == "function.scopes")
        .unwrap();
    let mut m = base.clone();
    (mutant.apply)(&mut m);
    let d = diff_with(
        &base,
        &m,
        DiffOptions {
            ignore_proofs: false,
            include_debug: true,
        },
    );
    assert!(d.to_text().contains("~ scopes:"), "{}", d.to_text());
}

// ---------------------------------------------------------------------------
// Ported audit row
// ---------------------------------------------------------------------------

/// `scout-emit.F2` (F-073), flipped GAP -> PASS. The scout found that
/// `trust_ir::diff` ignored `Function.body_gate`, so a codegen-license flip
/// (`Gated` -> `Ungated`, the refusal hook a consumer honours) was
/// "isomorphic". It is now the one `body_gate` row, even under
/// `--ignore-proofs`, while the renumbered twin of the licensed module stays
/// empty.
#[test]
#[allow(non_snake_case)]
fn scout_emit_F2() {
    let a = fixture();
    let mut b = a.clone();
    func_mut(&mut b, CALLER).body_gate = Some(BodyGate::Ungated);
    assert_ne!(a.stable_digest(), b.stable_digest());
    for ignore_proofs in [false, true] {
        let d = diff_with(
            &a,
            &b,
            DiffOptions {
                ignore_proofs,
                include_debug: false,
            },
        );
        match &d.changes[..] {
            [
                FuncChange::Changed {
                    name, meta_changes, ..
                },
            ] => {
                assert_eq!(name, CALLER);
                assert_eq!(
                    meta_changes,
                    &vec![MetaChange {
                        field: "body_gate".into(),
                        before: "gated \"trust-direct\"".into(),
                        after: "ungated".into(),
                    }]
                );
            }
            other => panic!("ignore_proofs={ignore_proofs}: {other:?}"),
        }
        assert_eq!(d.exit_code(), 1);
    }
    assert!(diff(&a, &fixture_with(TWIN)).is_empty());
}
