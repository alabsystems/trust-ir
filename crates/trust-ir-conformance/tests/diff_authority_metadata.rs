// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// `trust_ir::diff` must not be blind to authority / ABI / linkage metadata.
//
// Measured 2026-09-17 (two-language proof program, part B, rows
// `b1.gap.diff_blind_to_{body_gate,display_path,function_linkage,calling_conv,
// globals,spec_modules_and_target}`): the per-function metadata comparison in
// `diff.rs` read exactly `producer` and `source_provenance`, and nothing in the
// module ever read `Module.globals`, `Module.spec_modules`, or (without a tuple
// table) `Module.target_info`. Flipping any of those fields yielded an EMPTY
// diff and exit code 0 while `Module::stable_digest` moved — a reviewer diffing
// two producer builds could not see a Clean body losing its codegen license.
//
// Each test below is one field: (a) the identical / renumbered / reordered
// twin still diffs empty, (b) the single-field mutant is reported under the
// named `MetaChange::field`, with the exact before/after rendering, in text
// and JSON, with exit code 1, and (c) the report survives `--ignore-proofs`
// because none of these is proof coverage. The initializer control also runs
// the unchanged function body to show the reported metadata changes its result.
//
// Roadmap WS4.13 (gate legs): this file lived in `crates/trust-ir/tests/`,
// which no gate runs, behind a `cfg(all(feature = "diff", feature = "serde"))`
// that a feature-less `test -p trust-ir --test ...` would have compiled to an
// empty — vacuously green — target. It now lives in the conformance crate,
// whose default `all` feature enables `trust-ir/diff` + `trust-ir/serde`, and
// is on gate 8's registry (scripts/gates/
// wire-format-goldens.trust-ir-conformance.tests) beside `diff_fields`.

use trust_ir::diff::{Diff, DiffOptions, FuncChange, MetaChange, diff, diff_with};
use trust_ir::proof::ProofDigest;
use trust_ir::spec::{
    SpecAnchor, SpecEnforcementMode, SpecInvariant, SpecModule, SpecProjectionTarget, SpecVar,
};
use trust_ir::value::GlobalId;
use trust_ir::{
    Block, BlockId, BodyGate, CallingConv, Constant, Endianness, FuncId, FuncTy, Function, Global,
    Inst, InstrNode, Linkage, Module, ModuleImport, ParamAttrs, Producer, TargetInfo, Ty, ValueId,
    Visibility,
};

const SYM_CLEAN: &str = "clean_f";
const SYM_RUST: &str = "rust_g";
const GLOBAL: &str = "APP_BIAS";
const MACHINE: &str = "Counter";

fn target(triple: &str) -> TargetInfo {
    TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

/// `fn() -> u64 { 42 }` with the given ids, so two builds of the fixture can
/// use disjoint id spaces (the renumbering control).
fn nullary_u64(m: &mut Module, id: u32, name: &str, base: u32) -> FuncId {
    let ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let entry = BlockId::new(base);
    let mut f = Function::new(FuncId::new(id), name, ft, entry);
    let mut blk = Block::new(entry);
    blk.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(42),
        })
        .with_result(ValueId::new(base)),
    );
    blk.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(base)],
    }));
    f.blocks.push(blk);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    FuncId::new(id)
}

fn spec_module() -> SpecModule {
    let mut s = SpecModule::design_only(MACHINE);
    s.vars.push(SpecVar::new("n", "Nat"));
    s.actions.push("Incr".into());
    s.invariants
        .push(SpecInvariant::new("NonNeg", "n \\in Nat"));
    s
}

/// The positive fixture: one Clean-producer body under a `clean-kernel-tv`
/// license, one Rust body, one hidden global, one design-only spec module,
/// a target, an authenticated import, and a `global_asm!` block. Every field
/// this file mutates is populated here with a non-default value, so a flip is
/// a real transition and not a default-vs-default no-op.
fn fixture(base: u32) -> Module {
    let mut m = Module::new("fixture");
    m.target_info = Some(target("aarch64-apple-darwin"));
    let clean = nullary_u64(&mut m, base, SYM_CLEAN, base);
    let f = m.function_by_id_mut(clean).unwrap();
    f.producer = Some(Producer::Clean);
    f.body_gate = Some(BodyGate::Gated {
        authority: "clean-kernel-tv".into(),
        evidence: None,
    });
    f.display_path = Some("app::clean_f".into());
    f.linkage = Linkage::External;
    f.calling_conv = CallingConv::C;
    f.attrs.readonly = true;
    let rust = nullary_u64(&mut m, base + 1, SYM_RUST, base + 10);
    let f = m.function_by_id_mut(rust).unwrap();
    f.producer = Some(Producer::TRust);
    f.body_gate = Some(BodyGate::Ungated);
    f.display_path = Some("app::rust_g".into());
    f.linkage = Linkage::External;
    f.calling_conv = CallingConv::Rust;
    m.globals.push(Global {
        name: GLOBAL.into(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(Constant::Int(1)),
        linkage: Linkage::External,
        tls: None,
        align: Some(8),
        section: Some(".rodata.app".into()),
        visibility: Visibility::Hidden,
        retained: true,
    });
    m.spec_modules.push(spec_module());
    m.global_asm.push(".globl app_marker".into());
    m.intern_import(ModuleImport {
        name: "core_dep".into(),
        digest: ProofDigest::sha256([7; 32]),
        producer: Some(Producer::TRust),
        scheme: trust_ir::IdentityScheme::V2,
    })
    .expect("Module::intern_import: test fixture");
    m
}

fn fid(m: &Module, name: &str) -> FuncId {
    m.function_by_name(name).unwrap().id
}

fn func_meta(d: &Diff, func: &str) -> Vec<MetaChange> {
    d.changes
        .iter()
        .filter_map(|c| match c {
            FuncChange::Changed {
                name, meta_changes, ..
            } if name == func => Some(meta_changes.clone()),
            _ => None,
        })
        .flatten()
        .collect()
}

/// The single-field contract every mutant must satisfy: exactly one
/// `MetaChange` under `field` on `func` with the given rendering, nothing
/// else in the diff, exit 1, present in both renderings, and identical under
/// `ignore_proofs`.
fn assert_func_meta(a: &Module, b: &Module, func: &str, field: &str, before: &str, after: &str) {
    for opts in [
        DiffOptions::default(),
        DiffOptions {
            ignore_proofs: true,
            ..DiffOptions::default()
        },
    ] {
        let d = diff_with(a, b, opts);
        assert_eq!(
            d.exit_code(),
            1,
            "{field}: ignore_proofs={}",
            opts.ignore_proofs
        );
        assert_eq!(
            d.changes.len(),
            1,
            "{field}: exactly one changed function: {d:?}"
        );
        assert!(d.module_meta_changes.is_empty(), "{field}: {d:?}");
        assert!(d.proof_state_changes.is_empty(), "{field}: {d:?}");
        let FuncChange::Changed {
            block_changes,
            proof_changes,
            ..
        } = &d.changes[0]
        else {
            panic!("{field}: expected Changed, got {:?}", d.changes[0]);
        };
        assert!(block_changes.is_empty(), "{field}: body must be untouched");
        assert!(
            proof_changes.is_empty(),
            "{field}: proofs must be untouched"
        );
        assert_eq!(
            func_meta(&d, func),
            vec![MetaChange {
                field: field.into(),
                before: before.into(),
                after: after.into(),
            }],
            "{field}"
        );
        let text = d.to_text();
        assert!(
            text.contains(&format!(
                "~ function @{func}\n    ~ {field}: {before} -> {after}"
            )),
            "{field}: text:\n{text}"
        );
        let json: serde_json::Value = serde_json::from_str(&d.to_json()).unwrap();
        let meta = &json["changes"][0]["meta"][0];
        assert_eq!(meta["field"], field, "{field}: json {json}");
        assert_eq!(meta["before"], before, "{field}: json {json}");
        assert_eq!(meta["after"], after, "{field}: json {json}");
    }
    // Every one of these is content the module identity observes: the diff
    // now agrees with `stable_digest` instead of contradicting it.
    assert_ne!(a.stable_digest(), b.stable_digest(), "{field}");
    if field == "body_gate" {
        assert_eq!(
            a.executable_content_digest_v1(),
            b.executable_content_digest_v1(),
            "a codegen-license change does not change executable identity"
        );
    }
}

/// Same contract at module level: exactly one `module_meta_changes` row.
fn assert_module_meta(a: &Module, b: &Module, field: &str, before: &str, after: &str) {
    for opts in [
        DiffOptions::default(),
        DiffOptions {
            ignore_proofs: true,
            ..DiffOptions::default()
        },
    ] {
        let d = diff_with(a, b, opts);
        assert_eq!(d.exit_code(), 1, "{field}");
        assert!(
            d.changes.is_empty(),
            "{field}: no function may change: {d:?}"
        );
        assert!(d.proof_state_changes.is_empty(), "{field}: {d:?}");
        assert_eq!(
            d.module_meta_changes,
            vec![MetaChange {
                field: field.into(),
                before: before.into(),
                after: after.into(),
            }],
            "{field}"
        );
        let text = d.to_text();
        assert!(
            text.contains(&format!("~ module {field}: {before} -> {after}")),
            "{field}: text:\n{text}"
        );
        let json: serde_json::Value = serde_json::from_str(&d.to_json()).unwrap();
        let meta = &json["module_meta"][0];
        assert_eq!(meta["field"], field, "{field}: json {json}");
        assert_eq!(meta["before"], before, "{field}: json {json}");
        assert_eq!(meta["after"], after, "{field}: json {json}");
    }
    assert_ne!(a.stable_digest(), b.stable_digest(), "{field}");
}

// ---------------------------------------------------------------------------
// (a) positive: the fixture is self-isomorphic, and stays so under id
// renumbering and declaration reordering of the newly compared tables.
// ---------------------------------------------------------------------------

#[test]
fn fixture_is_isomorphic_to_itself_and_to_its_renumbered_reordered_twin() {
    let a = fixture(0);
    assert!(diff(&a, &a.clone()).is_empty());

    // Disjoint FuncId / FuncTyId / BlockId / ValueId spaces.
    let mut b = fixture(100);
    // Reverse every table the diff now reads: functions, globals, spec
    // modules, imports (a second, distinct import on both sides so order
    // is observable) — none of it is content.
    let extra = ModuleImport {
        name: "other_dep".into(),
        digest: ProofDigest::sha256([9; 32]),
        producer: Some(Producer::Clean),
        scheme: trust_ir::IdentityScheme::V2,
    };
    let mut a2 = a.clone();
    a2.intern_import(extra.clone())
        .expect("Module::intern_import: test fixture");
    b.imports.clear();
    b.intern_import(extra)
        .expect("Module::intern_import: test fixture");
    b.intern_import(ModuleImport {
        name: "core_dep".into(),
        digest: ProofDigest::sha256([7; 32]),
        producer: Some(Producer::TRust),
        scheme: trust_ir::IdentityScheme::V2,
    })
    .expect("Module::intern_import: test fixture");
    a2.globals.push(Global {
        name: "SECOND".into(),
        ty: Ty::I32,
        mutable: true,
        initializer: None,
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    b.globals.push(a2.globals[1].clone());
    a2.spec_modules.push(SpecModule::design_only("Second"));
    b.spec_modules.push(SpecModule::design_only("Second"));
    b.functions.reverse();
    b.globals.reverse();
    b.spec_modules.reverse();
    assert_ne!(
        a2.stable_digest(),
        b.stable_digest(),
        "control: renumbering/reordering IS visible to the byte-level identity"
    );
    let d = diff(&a2, &b);
    assert!(
        d.is_empty(),
        "renumbered + reordered twin must diff empty: {d:?}"
    );
    assert_eq!(d.exit_code(), 0);
    assert!(d.to_text().is_empty());
}

// ---------------------------------------------------------------------------
// (b) one test per function field
// ---------------------------------------------------------------------------

#[test]
fn body_gate_gated_to_ungated_is_reported() {
    let a = fixture(0);
    let mut b = a.clone();
    b.function_by_id_mut(fid(&a, SYM_CLEAN)).unwrap().body_gate = Some(BodyGate::Ungated);
    assert_func_meta(
        &a,
        &b,
        SYM_CLEAN,
        "body_gate",
        "gated \"clean-kernel-tv\"",
        "ungated",
    );
}

#[test]
fn body_gate_authority_swap_is_reported() {
    let a = fixture(0);
    let mut b = a.clone();
    b.function_by_id_mut(fid(&a, SYM_CLEAN)).unwrap().body_gate = Some(BodyGate::Gated {
        authority: "someone-else".into(),
        evidence: None,
    });
    assert_func_meta(
        &a,
        &b,
        SYM_CLEAN,
        "body_gate",
        "gated \"clean-kernel-tv\"",
        "gated \"someone-else\"",
    );
}

/// v61 license evidence (roadmap WS1.12(c)) is rendered by what it MEANS —
/// the cited obligation's claim and whether the body digest still holds —
/// never by arena ids. So a renumbered twin whose evidence holds on both sides
/// diffs empty although the raw digests differ (they hash the function's own
/// id), while a digest gone stale, or evidence dropped, is reported.
#[test]
fn body_gate_evidence_is_rendered_by_meaning() {
    use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};
    use trust_ir::{GateEvidence, ProofId};
    fn evidenced(base: u32) -> Module {
        let mut m = fixture(base);
        let clean = fid(&m, SYM_CLEAN);
        m.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(base),
                ObligationKind::TranslationValidation,
                ProofStatus::Certified,
                "tv",
            )
            .with_function(clean),
        );
        let body_digest = m.function_body_digest(clean).unwrap();
        m.function_by_id_mut(clean).unwrap().body_gate = Some(BodyGate::Gated {
            authority: "clean-kernel-tv".into(),
            evidence: Some(GateEvidence {
                obligation: ProofId::new(base),
                body_digest,
            }),
        });
        m
    }
    let a = evidenced(0);
    let b = evidenced(100);
    assert_ne!(
        a.function_body_digest(fid(&a, SYM_CLEAN)),
        b.function_body_digest(fid(&b, SYM_CLEAN)),
        "control: renumbering moves the raw body digests"
    );
    let d = diff(&a, &b);
    assert!(d.is_empty(), "evidence that holds on both sides: {d:?}");

    let mut stale = a.clone();
    if let Some(BodyGate::Gated {
        evidence: Some(evidence),
        ..
    }) = &mut stale
        .function_by_id_mut(fid(&a, SYM_CLEAN))
        .unwrap()
        .body_gate
    {
        evidence.body_digest.bytes[0] ^= 1;
    }
    let changes = func_meta(&diff(&a, &stale), SYM_CLEAN);
    let gate = changes
        .iter()
        .find(|c| c.field == "body_gate")
        .unwrap_or_else(|| panic!("a stale digest is reported: {changes:?}"));
    assert!(
        gate.before
            .starts_with("gated \"clean-kernel-tv\" evidence [")
            && gate.before.ends_with("body=holds")
            && gate.after.ends_with("body=stale"),
        "{gate:?}"
    );

    let mut plain = a.clone();
    assert!(
        plain
            .function_by_id_mut(fid(&a, SYM_CLEAN))
            .unwrap()
            .invalidate_gate_evidence()
    );
    let changes = func_meta(&diff(&a, &plain), SYM_CLEAN);
    let gate = changes
        .iter()
        .find(|c| c.field == "body_gate")
        .unwrap_or_else(|| panic!("dropped evidence is reported: {changes:?}"));
    assert_eq!(gate.after, "gated \"clean-kernel-tv\"");
}

/// A licensed body the binary writer cannot encode (`Ty::Error`, which it
/// panics on) has no body digest, and the diff renders its evidence as
/// `body=undigestable` — it never panics on a module the validator would
/// refuse. Control: the same evidence over the encodable body `holds`.
#[test]
fn body_gate_evidence_on_an_undigestable_body_never_panics() {
    use trust_ir::{GateEvidence, ProofId};
    let mut a = fixture(0);
    let clean = fid(&a, SYM_CLEAN);
    let body_digest = a.function_body_digest(clean).unwrap();
    a.function_by_id_mut(clean).unwrap().body_gate = Some(BodyGate::Gated {
        authority: "clean-kernel-tv".into(),
        evidence: Some(GateEvidence {
            obligation: ProofId::new(0),
            body_digest,
        }),
    });
    let mut b = a.clone();
    let Inst::Const { ty, .. } = &mut b.function_by_id_mut(clean).unwrap().blocks[0].body[0].inst
    else {
        panic!("fixture body starts with a constant");
    };
    *ty = Ty::Error;
    let refusal = b
        .function_body_digest(clean)
        .expect_err("a Ty::Error body has no identity");
    assert!(refusal.contains("Ty::Error"), "{refusal}");
    let changes = func_meta(&diff(&a, &b), SYM_CLEAN);
    let gate = changes
        .iter()
        .find(|c| c.field == "body_gate")
        .unwrap_or_else(|| panic!("the evidence stops holding: {changes:?}"));
    assert!(
        gate.before.ends_with("body=holds") && gate.after.ends_with("body=undigestable"),
        "{gate:?}"
    );
}

#[test]
fn body_gate_gated_to_none_is_reported() {
    // `None` ("no licensing claim", permitted) and `Ungated` (refused) are
    // distinct consumer verdicts, so they must render distinctly.
    let a = fixture(0);
    let mut b = a.clone();
    b.function_by_id_mut(fid(&a, SYM_CLEAN)).unwrap().body_gate = None;
    assert_func_meta(
        &a,
        &b,
        SYM_CLEAN,
        "body_gate",
        "gated \"clean-kernel-tv\"",
        "-",
    );
    let mut c = a.clone();
    c.function_by_id_mut(fid(&a, SYM_RUST)).unwrap().body_gate = None;
    assert_func_meta(&a, &c, SYM_RUST, "body_gate", "ungated", "-");
}

#[test]
fn display_path_change_is_reported() {
    let a = fixture(0);
    let mut b = a.clone();
    b.function_by_id_mut(fid(&a, SYM_RUST))
        .unwrap()
        .display_path = Some("evil::other_path".into());
    assert_func_meta(
        &a,
        &b,
        SYM_RUST,
        "display_path",
        "\"app::rust_g\"",
        "\"evil::other_path\"",
    );
    let mut c = a.clone();
    c.function_by_id_mut(fid(&a, SYM_RUST))
        .unwrap()
        .display_path = None;
    assert_func_meta(&a, &c, SYM_RUST, "display_path", "\"app::rust_g\"", "-");
}

#[test]
fn function_linkage_change_is_reported() {
    // An exported symbol disappearing from the link is not cosmetic.
    let a = fixture(0);
    let mut b = a.clone();
    b.function_by_id_mut(fid(&a, SYM_RUST)).unwrap().linkage = Linkage::Internal;
    assert_func_meta(&a, &b, SYM_RUST, "linkage", "external", "internal");
    let mut c = a.clone();
    c.function_by_id_mut(fid(&a, SYM_RUST)).unwrap().linkage = Linkage::LinkOnceOdr;
    assert_func_meta(&a, &c, SYM_RUST, "linkage", "external", "linkonce_odr");
}

#[test]
fn calling_conv_change_is_reported() {
    // The ABI of a cross-language edge.
    let a = fixture(0);
    let mut b = a.clone();
    b.function_by_id_mut(fid(&a, SYM_RUST))
        .unwrap()
        .calling_conv = CallingConv::C;
    assert_func_meta(&a, &b, SYM_RUST, "calling_conv", "rustcc", "ccc");
}

#[test]
fn signature_change_is_reported_but_func_ty_id_renumbering_is_not() {
    let a = fixture(0);
    // Mutant: a different return type behind the same FuncTyId.
    let mut b = a.clone();
    let ft = b.function_by_name(SYM_RUST).unwrap().ty;
    b.func_types[ft.as_usize()].returns = vec![Ty::U32];
    assert_func_meta(
        &a,
        &b,
        SYM_RUST,
        "signature",
        "functy(;u64)",
        "functy(;u32)",
    );
    // Control: the same signature interned again under a fresh id is cosmetic.
    let mut c = a.clone();
    let fresh = c
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    assert_ne!(fresh, ft);
    c.function_by_id_mut(fid(&a, SYM_RUST)).unwrap().ty = fresh;
    assert!(diff(&a, &c).is_empty());
}

#[test]
fn func_attrs_change_is_reported() {
    let a = fixture(0);
    let mut b = a.clone();
    let f = b.function_by_id_mut(fid(&a, SYM_CLEAN)).unwrap();
    f.attrs.readonly = false;
    f.attrs.naked = true;
    f.attrs.target_features = vec!["neon".into()];
    f.attrs.params.push(ParamAttrs {
        nonnull: true,
        ..Default::default()
    });
    const EMPTY_SLOT: &str = "{deref=- nonnull=false align=- noalias=false readonly=false byval=false \
                              sret=false ext=None pass=-}";
    assert_func_meta(
        &a,
        &b,
        SYM_CLEAN,
        "attrs",
        &format!(
            "readonly=true readnone=false inlinehint=false cold=false naked=false \
             target_features=[] ret={EMPTY_SLOT} params=[]"
        ),
        &format!(
            "readonly=false readnone=false inlinehint=false cold=false naked=true \
             target_features=[\"neon\"] ret={EMPTY_SLOT} params=[{{deref=- nonnull=true align=- \
             noalias=false readonly=false byval=false sret=false ext=None pass=-}}]"
        ),
    );

    // v45 (WS3.11): a slot ABI fact alone — the return slot's extension, or
    // a parameter's pass mode — changes the call's byte-level ABI, so it is
    // reported, never treated as cosmetic.
    let mut c = a.clone();
    c.function_by_id_mut(fid(&a, SYM_CLEAN)).unwrap().attrs.ret = ParamAttrs {
        ext: trust_ir::ArgExt::ZeroExt,
        ..Default::default()
    };
    assert_func_meta(
        &a,
        &c,
        SYM_CLEAN,
        "attrs",
        &format!(
            "readonly=true readnone=false inlinehint=false cold=false naked=false \
             target_features=[] ret={EMPTY_SLOT} params=[]"
        ),
        "readonly=true readnone=false inlinehint=false cold=false naked=false target_features=[] \
         ret={deref=- nonnull=false align=- noalias=false readonly=false byval=false sret=false \
         ext=ZeroExt pass=-} params=[]",
    );
    let mut d = a.clone();
    d.function_by_id_mut(fid(&a, SYM_CLEAN))
        .unwrap()
        .attrs
        .params = vec![ParamAttrs {
        pass: Some(trust_ir::PassMode::Cast {
            pieces: vec![trust_ir::ty::Ty::U64, trust_ir::ty::Ty::U64],
        }),
        ..Default::default()
    }];
    assert_func_meta(
        &a,
        &d,
        SYM_CLEAN,
        "attrs",
        &format!(
            "readonly=true readnone=false inlinehint=false cold=false naked=false \
             target_features=[] ret={EMPTY_SLOT} params=[]"
        ),
        &format!(
            "readonly=true readnone=false inlinehint=false cold=false naked=false \
             target_features=[] ret={EMPTY_SLOT} params=[{{deref=- nonnull=false align=- \
             noalias=false readonly=false byval=false sret=false ext=None pass=cast(u64,u64)}}]"
        ),
    );
}

// ---------------------------------------------------------------------------
// (b) one test per module table
// ---------------------------------------------------------------------------

const GLOBAL_FIELD: &str = "global @APP_BIAS";
const GLOBAL_BEFORE: &str = "ty=u64 mutable=false init=i:1 linkage=external tls=- align=8 \
                             section=\".rodata.app\" visibility=hidden retained=true";

#[test]
fn global_fingerprint_renders_every_field() {
    let a = fixture(0);
    let b = fixture(0);
    // Sanity on the rendering itself, via an added global (absent side `-`).
    let mut c = b.clone();
    c.globals.clear();
    assert_module_meta(&a, &c, GLOBAL_FIELD, GLOBAL_BEFORE, "-");
    assert_module_meta(&c, &a, GLOBAL_FIELD, "-", GLOBAL_BEFORE);
}

#[test]
fn global_visibility_change_is_reported() {
    let a = fixture(0);
    let mut b = a.clone();
    b.globals[0].visibility = Visibility::Default;
    assert_module_meta(
        &a,
        &b,
        GLOBAL_FIELD,
        GLOBAL_BEFORE,
        &GLOBAL_BEFORE.replace("visibility=hidden", "visibility=default"),
    );
}

#[test]
fn global_section_change_is_reported() {
    let a = fixture(0);
    let mut b = a.clone();
    b.globals[0].section = None;
    assert_module_meta(
        &a,
        &b,
        GLOBAL_FIELD,
        GLOBAL_BEFORE,
        &GLOBAL_BEFORE.replace("section=\".rodata.app\"", "section=-"),
    );
}

#[test]
fn global_retained_change_is_reported() {
    let a = fixture(0);
    let mut b = a.clone();
    b.globals[0].retained = false;
    assert_module_meta(
        &a,
        &b,
        GLOBAL_FIELD,
        GLOBAL_BEFORE,
        &GLOBAL_BEFORE.replace("retained=true", "retained=false"),
    );
}

#[test]
fn global_initializer_change_is_reported() {
    // Execute the unchanged body: this metadata changes what it computes.
    let mut a = fixture(0);
    let program = add_load_global_fn(&mut a, 60, "program");
    let mut b = a.clone();
    b.globals[0].initializer = Some(Constant::Int(2));
    let run = |m: &Module| {
        let out = trust_ir::interpret::Interpreter::with_module(m)
            .execute_func(program, Vec::new())
            .expect("fixture program runs");
        assert_eq!(out.host_calls, 0, "the global load needs no host calls");
        out.returns[0].as_int().expect("u64 result").as_unsigned()
    };
    assert_eq!(run(&a), 1);
    assert_eq!(run(&b), 2);
    assert_module_meta(
        &a,
        &b,
        GLOBAL_FIELD,
        GLOBAL_BEFORE,
        &GLOBAL_BEFORE.replace("init=i:1", "init=i:2"),
    );
}

#[test]
fn global_mutability_linkage_tls_align_and_type_changes_are_reported() {
    let a = fixture(0);
    let mut b = a.clone();
    b.globals[0].mutable = true;
    b.globals[0].linkage = Linkage::Private;
    b.globals[0].tls = Some(trust_ir::TlsModel::LocalExec);
    b.globals[0].align = None;
    b.globals[0].ty = Ty::I64;
    assert_module_meta(
        &a,
        &b,
        GLOBAL_FIELD,
        GLOBAL_BEFORE,
        "ty=i64 mutable=true init=i:1 linkage=private tls=local_exec align=- \
         section=\".rodata.app\" visibility=hidden retained=true",
    );
}

#[test]
fn spec_module_removal_and_change_are_reported() {
    let a = fixture(0);
    let before = "enforcement=DesignOnly origin=embedded vars=[SpecVar { name: \"n\", ty: \"Nat\", \
                  sort: None }] actions=[\"Incr\"] invariants=[SpecInvariant { name: \"NonNeg\", \
                  formula: \"n \\\\in Nat\", typed: None }] anchors=[] waivers=[] proofs=[] \
                  temporal=[]";
    // Dropping the disclosure machine.
    let mut b = a.clone();
    b.spec_modules.remove(0);
    assert_module_meta(&a, &b, "spec_module Counter", before, "-");
    // Promoting it to a certifying link.
    let mut c = a.clone();
    c.spec_modules[0].enforcement = SpecEnforcementMode::Linked;
    assert_module_meta(
        &a,
        &c,
        "spec_module Counter",
        before,
        &before.replace("enforcement=DesignOnly", "enforcement=Linked"),
    );
    // Rewriting an invariant's formula.
    let mut d = a.clone();
    d.spec_modules[0].invariants[0].formula = "TRUE".into();
    assert_module_meta(
        &a,
        &d,
        "spec_module Counter",
        before,
        &before.replace("formula: \"n \\\\in Nat\"", "formula: \"TRUE\""),
    );
}

const TARGET_BEFORE: &str =
    "triple=\"aarch64-apple-darwin\" pointer_size=8 endianness=little abi=- struct_passing=NativeC";

#[test]
fn target_info_change_is_reported_without_any_tuple_layout() {
    let a = fixture(0);
    assert!(
        a.tuple_layouts.is_empty(),
        "the pre-fix comparison only fired with a tuple table"
    );
    let mut b = a.clone();
    b.target_info = Some(target("x86_64-unknown-linux-gnu"));
    assert_module_meta(
        &a,
        &b,
        "target_info",
        TARGET_BEFORE,
        &TARGET_BEFORE.replace("aarch64-apple-darwin", "x86_64-unknown-linux-gnu"),
    );
    let mut c = a.clone();
    c.target_info.as_mut().unwrap().endianness = Endianness::Big;
    assert_module_meta(
        &a,
        &c,
        "target_info",
        TARGET_BEFORE,
        &TARGET_BEFORE.replace("endianness=little", "endianness=big"),
    );
    let mut d = a.clone();
    d.target_info = None;
    assert_module_meta(&a, &d, "target_info", TARGET_BEFORE, "-");
}

#[test]
fn global_asm_change_is_reported() {
    let a = fixture(0);
    let mut b = a.clone();
    b.global_asm.clear();
    assert_module_meta(&a, &b, "global_asm", "[\".globl app_marker\"]", "[]");
}

#[test]
fn import_repin_is_reported() {
    let a = fixture(0);
    let mut b = a.clone();
    b.imports[0].digest = ProofDigest::sha256([8; 32]);
    let before = format!("[\"core_dep@{}[trust]\"]", ProofDigest::sha256([7; 32]));
    let after = format!("[\"core_dep@{}[trust]\"]", ProofDigest::sha256([8; 32]));
    assert_module_meta(&a, &b, "imports", &before, &after);
}

/// WS4.10: the v44 identity scheme is part of the row, so re-recording the
/// same digest under another scheme is a reported change (V2 is spelled by
/// omission, V3 as `{v3}`).
#[test]
fn import_scheme_change_is_reported() {
    let a = fixture(0);
    let mut b = a.clone();
    b.imports[0].scheme = trust_ir::IdentityScheme::V3;
    let digest = ProofDigest::sha256([7; 32]);
    let before = format!("[\"core_dep@{digest}[trust]\"]");
    let after = format!("[\"core_dep@{digest}[trust]{{v3}}\"]");
    assert_module_meta(&a, &b, "imports", &before, &after);
}

/// `fn() -> u64 { load(global_addr APP_BIAS) }`.
fn add_load_global_fn(m: &mut Module, id: u32, name: &str) -> FuncId {
    let ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let entry = BlockId::new(0);
    let mut f = Function::new(FuncId::new(id), name, ft, entry);
    let mut blk = Block::new(entry);
    blk.body.push(
        InstrNode::new(Inst::GlobalAddr {
            global: GlobalId::new(0),
        })
        .with_result(ValueId::new(0)),
    );
    blk.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::U64,
            ptr: ValueId::new(0),
            volatile: false,
            align: None,
        })
        .with_result(ValueId::new(1)),
    );
    blk.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    f.blocks.push(blk);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    FuncId::new(id)
}

/// `fn() -> ptr { global_addr <global> }`.
fn add_global_addr_fn(m: &mut Module, id: u32, name: &str, global: GlobalId) {
    let ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![Ty::Ptr],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let entry = BlockId::new(0);
    let mut f = Function::new(FuncId::new(id), name, ft, entry);
    let mut blk = Block::new(entry);
    blk.body
        .push(InstrNode::new(Inst::GlobalAddr { global }).with_result(ValueId::new(0)));
    blk.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    f.blocks.push(blk);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
}

fn second_global() -> Global {
    Global {
        name: "SECOND".into(),
        ty: Ty::U64,
        mutable: true,
        initializer: Some(Constant::Int(5)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

#[test]
fn global_addr_is_matched_by_symbol_so_global_reordering_stays_cosmetic() {
    // A: globals [APP_BIAS, SECOND], `addr` takes the address of APP_BIAS (id 0).
    let mut a = fixture(0);
    a.globals.push(second_global());
    add_global_addr_fn(&mut a, 50, "addr", GlobalId::new(0));
    // B: the same program with the global table reversed, so the SAME symbol
    // now sits at id 1. Before globals were keyed by symbol the fingerprint
    // used the raw index, and this was a spurious body change.
    let mut b = fixture(0);
    b.globals.push(second_global());
    b.globals.reverse();
    add_global_addr_fn(&mut b, 50, "addr", GlobalId::new(1));
    assert_ne!(a.stable_digest(), b.stable_digest());
    let d = diff(&a, &b);
    assert!(d.is_empty(), "reordered globals must diff empty: {d:?}");

    // Mutation control: same index as A, but after the reorder id 0 names a
    // DIFFERENT global — the address now points at SECOND. That is a real
    // body change and must be reported as one (and only as one).
    let mut c = fixture(0);
    c.globals.push(second_global());
    c.globals.reverse();
    add_global_addr_fn(&mut c, 50, "addr", GlobalId::new(0));
    let d = diff(&a, &c);
    assert_eq!(d.exit_code(), 1);
    assert!(d.module_meta_changes.is_empty(), "{d:?}");
    assert_eq!(d.changes.len(), 1, "{d:?}");
    let FuncChange::Changed {
        name,
        block_changes,
        meta_changes,
        ..
    } = &d.changes[0]
    else {
        panic!("expected Changed: {d:?}");
    };
    assert_eq!(name, "addr");
    assert!(meta_changes.is_empty());
    assert_eq!(block_changes.len(), 1, "{d:?}");
}

// ---------------------------------------------------------------------------
// (c) mutation control: the report is specific — an unrelated field flip
// does not produce a `body_gate` row, and the value strings are exact.
// ---------------------------------------------------------------------------

#[test]
fn mutation_control_reports_only_the_field_that_moved() {
    let a = fixture(0);
    let mut b = a.clone();
    b.function_by_id_mut(fid(&a, SYM_CLEAN)).unwrap().producer = Some(Producer::TRust);
    let d = diff(&a, &b);
    let fields: Vec<String> = func_meta(&d, SYM_CLEAN)
        .into_iter()
        .map(|m| m.field)
        .collect();
    assert_eq!(fields, vec!["producer".to_string()], "{d:?}");
    assert!(
        func_meta(&d, SYM_RUST).is_empty(),
        "the untouched function stays untouched"
    );
    assert!(d.module_meta_changes.is_empty());

    // Two fields moved on one function: both rows, in declaration order.
    let mut c = a.clone();
    let f = c.function_by_id_mut(fid(&a, SYM_CLEAN)).unwrap();
    f.body_gate = Some(BodyGate::Ungated);
    f.linkage = Linkage::Internal;
    let d = diff(&a, &c);
    let fields: Vec<String> = func_meta(&d, SYM_CLEAN)
        .into_iter()
        .map(|m| m.field)
        .collect();
    assert_eq!(fields, vec!["body_gate".to_string(), "linkage".to_string()]);
}

// ---------------------------------------------------------------------------
// Adversarial twins (review pass): spec anchors carry `FuncId`s. They must be
// matched by the function's SYMBOL, like every other function reference in
// the diff — a raw arena index is both a false positive (renumbering) and a
// false negative (a re-point that lands on the old index).
// ---------------------------------------------------------------------------

/// A `Linked` machine whose one anchor names `func` as both the implementing
/// function and the projection target.
fn anchored_spec(func: FuncId) -> SpecModule {
    let mut s = spec_module();
    s.enforcement = SpecEnforcementMode::Linked;
    s.anchors.push(SpecAnchor {
        machine: MACHINE.into(),
        action: "Incr".into(),
        rust_symbol: "app::incr".into(),
        span: "src/app.rs:1:1".into(),
        project: None,
        function: Some(func),
        projection_target: Some(SpecProjectionTarget::Function(func)),
    });
    s
}

fn anchored(base: u32, reverse: bool, anchor_to: &str) -> Module {
    let mut m = fixture(base);
    if reverse {
        m.functions.reverse();
    }
    let id = fid(&m, anchor_to);
    m.spec_modules[0] = anchored_spec(id);
    m
}

#[test]
fn spec_anchor_is_matched_by_symbol_so_function_renumbering_stays_cosmetic() {
    let a = anchored(0, false, SYM_CLEAN);
    // Same anchor target, disjoint FuncId space and reversed function order.
    let b = anchored(100, true, SYM_CLEAN);
    assert_ne!(
        fid(&a, SYM_CLEAN),
        fid(&b, SYM_CLEAN),
        "the twin really renumbers"
    );
    let d = diff(&a, &b);
    assert!(d.is_empty(), "renumbered anchor must diff empty: {d:?}");
    let row = spec_row(&diff(&a, &fixture(0)));
    assert!(
        row.before
            .contains("function=@clean_f projection_target=function(@clean_f)"),
        "anchor renders the symbol, not the index: {}",
        row.before
    );
}

#[test]
fn spec_anchor_repoint_onto_the_old_index_is_reported() {
    // A: anchor -> clean_f, which holds FuncId(0).
    let a = anchored(0, false, SYM_CLEAN);
    // B: ids swapped so rust_g now holds FuncId(0), and the anchor is moved
    // to rust_g. The raw anchor is BYTE-IDENTICAL to A's (`Some(FuncId(0))`)
    // and both bodies are unchanged — only the symbol it names moved.
    let mut b = fixture(0);
    for f in &mut b.functions {
        f.id = FuncId::new(if f.name == SYM_CLEAN { 1 } else { 0 });
    }
    b.spec_modules[0] = anchored_spec(fid(&b, SYM_RUST));
    assert_eq!(
        a.spec_modules[0].anchors[0].function, b.spec_modules[0].anchors[0].function,
        "the raw FuncId is the same on both sides"
    );
    let d = diff(&a, &b);
    assert_eq!(
        d.exit_code(),
        1,
        "re-pointed anchor must be reported: {d:?}"
    );
    assert!(d.changes.is_empty(), "{d:?}");
    let row = spec_row(&d);
    assert!(row.before.contains("function=@clean_f"), "{row:?}");
    assert!(row.after.contains("function=@rust_g"), "{row:?}");

    // A dangling anchor id never matches a real function.
    let mut c = a.clone();
    c.spec_modules[0].anchors[0].function = Some(FuncId::new(999));
    let row = spec_row(&diff(&a, &c));
    assert!(row.after.contains("function=#dangling 999"), "{row:?}");
}

fn spec_row(d: &Diff) -> MetaChange {
    let rows: Vec<&MetaChange> = d
        .module_meta_changes
        .iter()
        .filter(|m| m.field == format!("spec_module {MACHINE}"))
        .collect();
    assert_eq!(rows.len(), 1, "{d:?}");
    rows[0].clone()
}
