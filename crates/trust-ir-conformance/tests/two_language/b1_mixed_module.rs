//! b1 — the design-complete MIXED module: one `Module` holding
//! `Producer::TRust` and `Producer::Clean` functions with call edges in both
//! directions, link-time symbols + display paths, the `body_gate` tri-state,
//! the reserved `@trust-internal::` disclosure SpecModules, linkage /
//! visibility, a pinned target, the codegen-license validator, the four codecs,
//! the reference interpreter and the semantic diff.
//!
//! Ported (roadmap WS8.6) from the archived Part B battery
//! `reports/2026-09-17-two-language-proof-program/partb/tests/b1_mixed_module.rs`, measured there
//! at trust-ir 4efb21bc and re-measured at the port. Every row is checked against
//! `RATCHETS.tsv` (see `harness.rs`). `file:line` citations are relative to
//! `crates/` and date from 4efb21bc: re-locate them by name.

mod common;

// The conformance corpus's fixture builders: b1_13 wraps the b1 module in the
// SAME complete schema-9 bundle recipe the `mixed_producer` target uses.
// The fixture generators (tests/generate.rs), compiled once as the library's
// `fixtures` module rather than again inside every test binary.
use trust_ir_conformance::fixtures as generate;

use common::{
    Expect, Outcome, feature_check, feature_gap, roundtrip_all, run_nullary, run_with_args,
};
use trust_ir::binary::{
    BinaryError, BinaryProjectionError, ModuleBinaryBody, ModuleBinaryOptions,
    ProjectedModuleBinaryPlan,
};
use trust_ir::constant::Constant;
use trust_ir::diff::{FuncChange, diff};
use trust_ir::inst::{BinOp, Inst};
use trust_ir::interpret::InterpretValue;
use trust_ir::proof::RejectingModuleProofAuthority;
use trust_ir::spec::{SpecEnforcementMode, SpecInvariant, SpecModule, SpecOrigin};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::GlobalId;
use trust_ir::{
    BodyGate, CallingConv, Endianness, FuncId, Global, Linkage, Module, NativeBundleProducer,
    NativeSourceLanguage, NativeVerificationBundle, NativeVerificationBundleError,
    NativeVerifierSuite, Producer, StructPassingPolicy, TargetInfo, TlsModel, Visibility,
};
use trust_ir_build::{
    CodegenAdmission, ModuleBuilder, RESERVED_TRUST_INTERNAL_SPEC_MODULES, ValidationError,
    validate_module, validate_module_for_codegen, validate_module_for_codegen_with,
    validate_module_with_authority,
};

// Link-time symbols (what `Function.name` normatively IS since v41) and the
// human def-paths split out into `display_path`.
const SYM_LEAF: &str = "_RNvCs1a2b3c_3app9rust_leaf";
const SYM_MID: &str = "_RNvCs1a2b3c_3app8rust_mid";
const SYM_ADDMUL: &str = "clean_App_addmul";
const SYM_VIA_RUST: &str = "clean_App_viaRust";
const SYM_PROGRAM: &str = "program";
const SYM_WEAK_HOOK: &str = "app_optional_hook";

const AUTH_RUST: &str = "trust-verify";
/// The Clean bodies' license. NOT `clean-kernel-tv`: since WS1.5 that
/// authority is bound to evidence (a kernel-rechecked `clean_backend_tv`
/// certificate per body, `EVIDENCE_BOUND_GATE_AUTHORITIES`), and this
/// hand-built module mints none — the direct-lane authority is the one a
/// Clean-origin body may wear without in-module evidence, and a consumer
/// admits it only by recognizing it (`CodegenAdmission::with_recognized`).
/// The evidence-bound authority is measured in `b1.gap.gated_authority_unpinned`.
const AUTH_CLEAN: &str = "trust-direct-lane-structural";
/// The evidence-bound Clean authority (`clean-kernel-tv`).
const AUTH_CLEAN_KERNEL_TV: &str = "clean-kernel-tv";

/// program() = clean_addmul(6,7) + clean_viaRust(3,4)
///           = (6*7+6) + ((3+BIAS)*2 + 4)   with BIAS = 1
///           = 48 + 12 = 60
const EXPECTED: u128 = 60;

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".to_string(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".to_string()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Skew {
    None,
    /// Rust `program` passes ONE argument to the two-parameter Clean callee.
    RustToLeanArity,
    /// Clean `viaRust` passes a `u32` to the Rust callee that declares `u64`.
    LeanToRustType,
    /// Rust `rust_mid` passes TWO arguments to the one-parameter Rust leaf.
    RustToRustLeafArity,
}

fn disclosure(name: &str, rows: &[(&str, &str)]) -> SpecModule {
    // `SpecModule::new` == design_only: SpecOrigin::Embedded +
    // SpecEnforcementMode::DesignOnly (trust-ir/src/spec.rs:353-358).
    let mut spec = SpecModule::new(name);
    for (row, formula) in rows {
        spec.invariants.push(SpecInvariant::new(*row, *formula));
    }
    spec
}

/// The design-complete mixed module.
///
/// ```text
/// global hidden   @APP_BIAS    : u64 = 1          (Visibility::Hidden, retained, section)
/// global tls mut  @APP_TLS_CTR : u64 = 0          (Visibility::Protected, WeakOdr)
/// [TRust, rust cc, internal     ] rust_leaf(x)        = x + *APP_BIAS
/// [TRust, rust cc, external     ] rust_mid(x)         = rust_leaf(x) * 2         Rust -> Rust leaf
/// [Clean, C cc,   linkonce_odr  ] clean_addmul(a,b)   = a*b + a
/// [Clean, C cc,   external      ] clean_viaRust(a,b)  = rust_mid(a) + b          Lean -> Rust
/// [TRust, rust cc, external     ] program()           = clean_addmul(6,7)        Rust -> Lean
///                                                     + clean_viaRust(3,4)       Rust -> Lean -> Rust -> Rust
/// [TRust, C cc,   external      ] app_optional_hook   (bodyless declaration; see b1_12 for extern_weak)
/// ```
fn build(skew: Skew) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("b1_mixed", target());
    let unary = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let binary = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);

    let bias = GlobalId::new(0); // `add_global` returns (); GlobalId = push index (builder.rs:252)
    mb.add_global(Global {
        name: "APP_BIAS".to_string(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(Constant::Int(1)),
        linkage: Linkage::External,
        tls: None,
        align: Some(8),
        section: Some("__DATA,__app_bias".to_string()),
        visibility: Visibility::Hidden,
        retained: true,
    });
    mb.add_global(Global {
        name: "APP_TLS_CTR".to_string(),
        ty: Ty::U64,
        mutable: true,
        initializer: Some(Constant::Int(0)),
        linkage: Linkage::WeakOdr,
        tls: Some(TlsModel::LocalExec),
        align: None,
        section: None,
        visibility: Visibility::Protected,
        retained: false,
    });

    let leaf = {
        let mut fb = mb.function(SYM_LEAF, unary);
        fb.set_producer(Producer::TRust);
        fb.set_calling_conv(CallingConv::Rust);
        fb.set_display_path("app::rust_leaf");
        fb.set_body_gate(BodyGate::Gated {
            authority: AUTH_RUST.into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let p = fb.global_addr(bias);
        let b = fb.load(Ty::U64, p);
        let out = fb.add(Ty::U64, x, b);
        fb.ret(vec![out]);
        fb.build()
    };

    let mid = {
        let mut fb = mb.function(SYM_MID, unary);
        fb.set_producer(Producer::TRust);
        fb.set_calling_conv(CallingConv::Rust);
        fb.set_display_path("app::rust_mid");
        fb.set_body_gate(BodyGate::Gated {
            authority: AUTH_RUST.into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let args = if skew == Skew::RustToRustLeafArity {
            vec![x, x]
        } else {
            vec![x]
        };
        let l = fb.call(leaf, args);
        let two = fb.uconst(Ty::U64, 2);
        let out = fb.mul(Ty::U64, l, two);
        fb.ret(vec![out]);
        fb.build()
    };

    let addmul = {
        let mut fb = mb.function(SYM_ADDMUL, binary);
        fb.set_producer(Producer::Clean);
        fb.set_display_path("App.addmul");
        fb.set_body_gate(BodyGate::Gated {
            authority: AUTH_CLEAN.into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let ab = fb.mul(Ty::U64, a, b);
        let out = fb.add(Ty::U64, ab, a);
        fb.ret(vec![out]);
        fb.build()
    };

    let via_rust = {
        let mut fb = mb.function(SYM_VIA_RUST, binary);
        fb.set_producer(Producer::Clean);
        fb.set_display_path("App.viaRust");
        fb.set_body_gate(BodyGate::Gated {
            authority: AUTH_CLEAN.into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let arg = if skew == Skew::LeanToRustType {
            fb.uconst(Ty::U32, 3)
        } else {
            a
        };
        let m = fb.call(mid, vec![arg]);
        let out = fb.add(Ty::U64, m, b);
        fb.ret(vec![out]);
        fb.build()
    };

    {
        let mut fb = mb.function(SYM_PROGRAM, nullary);
        fb.set_producer(Producer::TRust);
        fb.set_calling_conv(CallingConv::Rust);
        fb.set_display_path("app::program");
        fb.set_body_gate(BodyGate::Gated {
            authority: AUTH_RUST.into(),
            evidence: None,
        });
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let six = fb.uconst(Ty::U64, 6);
        let seven = fb.uconst(Ty::U64, 7);
        let three = fb.uconst(Ty::U64, 3);
        let four = fb.uconst(Ty::U64, 4);
        let args = if skew == Skew::RustToLeanArity {
            vec![six]
        } else {
            vec![six, seven]
        };
        let l = fb.call(addmul, args);
        let r = fb.call(via_rust, vec![three, four]);
        let out = fb.add(Ty::U64, l, r);
        fb.ret(vec![out]);
        fb.build();
    }

    mb.set_default_producer(Producer::TRust);
    let hook = mb.declare_function(SYM_WEAK_HOOK, nullary);

    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    // The builder has no linkage door (API_NOTES §1): assign after `build().expect("the fixture builds")`.
    m.function_by_id_mut(leaf).unwrap().linkage = Linkage::Internal;
    m.function_by_id_mut(addmul).unwrap().linkage = Linkage::LinkOnceOdr;
    {
        let h = m.function_by_id_mut(hook).unwrap();
        h.linkage = Linkage::External; // the ExternalWeak spelling is b1_12's row
        h.display_path = Some("app::optional_hook".to_string());
    }

    // The reserved DesignOnly disclosure SpecModules. trust-ir reserves THREE
    // names (`RESERVED_TRUST_INTERNAL_SPEC_MODULES` in trust-ir-build's
    // validate.rs; the archived DESIGN.md said "both", finding b1.uf11) — all
    // three are carried, shaped like the tRust compiler's disclosure minters
    // (invariants only, JSON-ish opaque formula strings).
    m.spec_modules.push(disclosure(
        "@trust-internal::clean-origin-disclosure-v1",
        &[
            ("def:App.addmul", r#"{"symbol":"clean_App_addmul","tier":"gate","body_gate":"gated","authority":"clean-kernel-tv"}"#),
            ("def:App.viaRust", r#"{"symbol":"clean_App_viaRust","tier":"structural","rust_call_chain":["_RNvCs1a2b3c_3app8rust_mid"]}"#),
        ],
    ));
    m.spec_modules.push(disclosure(
        "@trust-internal::contract-disclosure-v1",
        &[("fn:4:ensures:0", r#"{"typed":{"text":"result == 60","proposition":{"eq":[{"var":{"name":"result","domain":"UInt"}},{"uint":"60"}]}}}"#)],
    ));
    m.spec_modules.push(disclosure(
        "@trust-internal::deferred-verification-disclosure-v1",
        &[(
            "notice",
            "bodies lowered from THIR are not borrow-checked by this module's producer",
        )],
    ));
    m
}

fn fid(m: &Module, name: &str) -> FuncId {
    m.function_by_name(name)
        .unwrap_or_else(|| panic!("no @{name}"))
        .id
}

fn edges(m: &Module) -> Vec<(String, String, String, String)> {
    let mut out = Vec::new();
    for f in &m.functions {
        for b in &f.blocks {
            for n in &b.body {
                if let Inst::Call { callee, .. } = &n.inst {
                    let c = m.function_by_id(*callee).expect("callee resolves");
                    out.push((
                        f.producer
                            .as_ref()
                            .map(ToString::to_string)
                            .unwrap_or_default(),
                        f.name.clone(),
                        c.producer
                            .as_ref()
                            .map(ToString::to_string)
                            .unwrap_or_default(),
                        c.name.clone(),
                    ));
                }
            }
        }
    }
    out
}

fn u64_of(result: &Result<Vec<InterpretValue>, String>) -> Option<u128> {
    result
        .as_ref()
        .ok()
        .and_then(|v| v.first())
        .and_then(common::as_u128)
}

// ===========================================================================
// 1. shape + validate + call edges (both directions) with exact FuncTy
// ===========================================================================

fn b1_01_mixed_producers_and_call_edges() {
    let m = build(Skew::None);

    let producers: Vec<_> = m
        .functions
        .iter()
        .map(|f| (f.name.as_str(), f.producer.clone()))
        .collect();
    let trust_n = producers
        .iter()
        .filter(|(_, p)| *p == Some(Producer::TRust))
        .count();
    let clean_n = producers
        .iter()
        .filter(|(_, p)| *p == Some(Producer::Clean))
        .count();
    assert!(feature_check(
        "b1.one_module_two_producers",
        trust_n == 4 && clean_n == 2 && m.functions.len() == 6,
        &format!("trust={trust_n} clean={clean_n} {producers:?}"),
    ));

    // Every applicable entry point, strictest last: structural, the
    // authority tier with the fail-closed authority (no import / certificate is
    // taken on faith there), and the codegen-intent gate.
    let errors = validate_module(&m);
    let authority = validate_module_with_authority(&m, &RejectingModuleProofAuthority);
    let codegen = validate_module_for_codegen(&m);
    assert!(feature_check(
        "b1.validate_module",
        errors.is_empty() && authority.is_empty() && codegen.is_empty(),
        &format!(
            "validate_module={errors:?} validate_module_with_authority(Rejecting)={authority:?} \
             validate_module_for_codegen={codegen:?}"
        ),
    ));

    // Edges present: Rust->Lean (x2), Lean->Rust, Rust->Rust leaf.
    let es = edges(&m);
    let has = |cp: &str, c: &str, kp: &str, k: &str| {
        es.iter()
            .any(|e| e.0 == cp && e.1 == c && e.2 == kp && e.3 == k)
    };
    let edge_ok = has("trust", SYM_PROGRAM, "clean", SYM_ADDMUL)
        && has("trust", SYM_PROGRAM, "clean", SYM_VIA_RUST)
        && has("clean", SYM_VIA_RUST, "trust", SYM_MID)
        && has("trust", SYM_MID, "trust", SYM_LEAF);
    // exact FuncTy: each callee's signature is one interned FuncTy shared by
    // declaration and call site (Call carries only the FuncId; the validator
    // checks args against `Function.ty`).
    let sig = |n: &str| {
        m.func_type(m.function_by_name(n).unwrap().ty)
            .cloned()
            .unwrap()
    };
    let fty = |params: Vec<Ty>| FuncTy {
        params,
        returns: vec![Ty::U64],
        abi: None,
        is_vararg: false,
    };
    let sig_ok = sig(SYM_ADDMUL) == fty(vec![Ty::U64, Ty::U64])
        && sig(SYM_VIA_RUST) == fty(vec![Ty::U64, Ty::U64])
        && sig(SYM_MID) == fty(vec![Ty::U64])
        && sig(SYM_LEAF) == fty(vec![Ty::U64])
        && sig(SYM_PROGRAM) == fty(vec![]);
    assert!(feature_check(
        "b1.call_edges.rust_to_lean_and_lean_to_rust_to_rust_leaf",
        edge_ok && sig_ok && es.len() == 4,
        &format!("edges={es:?}"),
    ));

    // --- negative twins: one per direction, producer-attributed -------------
    let e = validate_module(&build(Skew::RustToLeanArity));
    let twin = e.iter().any(|e| {
        matches!(e,
        ValidationError::CallArgCountMismatch { callee, expected: 2, actual: 1,
            caller_producer: Some(cp), callee_producer: Some(kp), .. }
        if callee == SYM_ADDMUL && cp == "trust" && kp == "clean")
    });
    assert!(feature_check(
        "b1.call_edges.neg.rust_to_lean_arity",
        twin && e.len() == 1,
        &format!("{e:?}"),
    ));

    let e = validate_module(&build(Skew::LeanToRustType));
    let twin = e.iter().any(|e| matches!(e,
        ValidationError::CallArgTypeMismatch { callee, arg_index: 0, expected, actual,
            caller_producer: Some(cp), callee_producer: Some(kp), .. }
        if callee == SYM_MID && expected == "u64" && actual == "u32" && cp == "clean" && kp == "trust"));
    assert!(feature_check(
        "b1.call_edges.neg.lean_to_rust_type",
        twin && e.len() == 1,
        &format!("{e:?}"),
    ));

    let e = validate_module(&build(Skew::RustToRustLeafArity));
    let twin = e.iter().any(|e| {
        matches!(e,
        ValidationError::CallArgCountMismatch { callee, expected: 1, actual: 2,
            caller_producer: Some(cp), callee_producer: Some(kp), .. }
        if callee == SYM_LEAF && cp == "trust" && kp == "trust")
    });
    assert!(feature_check(
        "b1.call_edges.neg.rust_to_rust_leaf_arity",
        twin && e.len() == 1,
        &format!("{e:?}"),
    ));
}

// ===========================================================================
// 2. Function.name = link-time symbol, display_path = human def-path
// ===========================================================================

fn b1_02_symbol_and_display_path() {
    let m = build(Skew::None);
    let pairs: Vec<_> = m
        .functions
        .iter()
        .map(|f| (f.name.clone(), f.display_path.clone()))
        .collect();
    let ok = m
        .function_by_name(SYM_LEAF)
        .unwrap()
        .display_path
        .as_deref()
        == Some("app::rust_leaf")
        && m.function_by_name(SYM_ADDMUL)
            .unwrap()
            .display_path
            .as_deref()
            == Some("App.addmul")
        && m.function_by_name("app::rust_leaf").is_none()
        && validate_module(&m).is_empty();
    assert!(feature_check(
        "b1.symbol_and_display_path",
        ok,
        &format!("{pairs:?}")
    ));

    // Two defs may SHARE a display path (it is never an identity) ...
    let mut shared = m.clone();
    let mid = fid(&shared, SYM_MID);
    shared.function_by_id_mut(mid).unwrap().display_path = Some("app::rust_leaf".into());
    let shared_errors = validate_module(&shared);

    // ... but never a link-time symbol (validate.rs:10928-10948).
    let mut dup = m.clone();
    dup.function_by_id_mut(mid).unwrap().name = SYM_LEAF.to_string();
    let e = validate_module(&dup);
    let leaf = fid(&m, SYM_LEAF).index();
    let twin = e.len() == 1
        && matches!(&e[0], ValidationError::DuplicateFunctionSymbol { name, first, second, .. }
            if name == SYM_LEAF && *first == leaf && *second == mid.index());
    assert!(feature_check(
        "b1.symbol.neg.duplicate_link_symbol",
        twin && shared_errors.is_empty(),
        &format!("duplicate symbol => {e:?}; shared display_path => {shared_errors:?}"),
    ));

    // blank display path (validate.rs:3566-3572)
    let mut blank = m.clone();
    blank.function_by_id_mut(mid).unwrap().display_path = Some("  ".into());
    let e = validate_module(&blank);
    let twin = e.len() == 1
        && matches!(&e[0], ValidationError::InvalidDisplayPath { function, detail }
            if *function == mid.index() && detail.contains("blank"));
    assert!(feature_check(
        "b1.display_path.neg.blank",
        twin,
        &format!("{e:?}")
    ));
}

// ===========================================================================
// 3. body_gate tri-state + the codegen license
// ===========================================================================

/// One nullary `u64` function per licensing state, in one module.
fn tri_state() -> Module {
    let mut mb = ModuleBuilder::new("b1_tristate");
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    for (name, producer, gate) in [
        ("legacy_no_claim", Producer::TRust, None),
        (
            "clean_general_ungated",
            Producer::Clean,
            Some(BodyGate::Ungated),
        ),
        (
            "clean_gate_tier",
            Producer::Clean,
            Some(BodyGate::Gated {
                authority: AUTH_CLEAN.into(),
                evidence: None,
            }),
        ),
    ] {
        let mut fb = mb.function(name, nullary);
        fb.set_producer(producer);
        if let Some(g) = gate {
            fb.set_body_gate(g);
        }
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let v = fb.uconst(Ty::U64, 7);
        fb.ret(vec![v]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn b1_03_body_gate_tri_state_and_codegen_license() {
    let tri = tri_state();
    let gates = |m: &Module| {
        m.functions
            .iter()
            .map(|f| f.body_gate.clone())
            .collect::<Vec<_>>()
    };
    let want = vec![
        None,
        Some(BodyGate::Ungated),
        Some(BodyGate::Gated {
            authority: AUTH_CLEAN.into(),
            evidence: None,
        }),
    ];
    let rt = roundtrip_all(&tri);
    let survived = rt
        .all()
        .iter()
        .all(|t| t.decoded.as_ref().map(gates) == Some(want.clone()));
    let structural = validate_module(&tri);
    assert!(feature_check(
        "b1.body_gate.tri_state",
        gates(&tri) == want && structural.is_empty() && survived && rt.lossless_all(),
        &format!(
            "None/Ungated/Gated distinct in all 4 codecs; validate={structural:?}; {}",
            rt.summary()
        ),
    ));

    // The codegen entry point: Gated admitted, Ungated refused, None refused
    // under a SEPARATE variant (validate.rs:8975-9000).
    let cg = validate_module_for_codegen(&tri);
    let exact = cg
        == vec![
            ValidationError::UnlicensedBodyForCodegen {
                function: 0,
                name: "legacy_no_claim".into(),
            },
            ValidationError::UngatedBodyForCodegen {
                function: 1,
                name: "clean_general_ungated".into(),
            },
        ];
    assert!(feature_check(
        "b1.codegen.refuses_ungated_and_unlicensed",
        exact,
        &format!("{cg:?}"),
    ));

    // The full mixed module: every BODY is Gated (the bodyless External
    // declaration carries no gate and is skipped) => admitted.
    let m = build(Skew::None);
    let cg = validate_module_for_codegen(&m);
    assert!(feature_check(
        "b1.codegen.admits_gated_mixed_module",
        cg.is_empty()
            && m.function_by_name(SYM_WEAK_HOOK)
                .unwrap()
                .body_gate
                .is_none(),
        &format!("validate_module_for_codegen errors={cg:?}"),
    ));

    // negative twin of the admission: flip ONE Clean body to Ungated.
    let mut ungated = m.clone();
    let via = fid(&ungated, SYM_VIA_RUST);
    ungated.function_by_id_mut(via).unwrap().body_gate = Some(BodyGate::Ungated);
    let cg = validate_module_for_codegen(&ungated);
    let twin = cg
        == vec![ValidationError::UngatedBodyForCodegen {
            function: via.index(),
            name: SYM_VIA_RUST.into(),
        }];
    assert!(feature_check(
        "b1.codegen.neg.one_ungated_clean_body",
        twin && validate_module(&ungated).is_empty(),
        &format!("{cg:?} (validate_module still accepts the carrier)"),
    ));

    // negative twin of `Gated`: a blank authority (validate.rs:3555-3565).
    let mut blank = m.clone();
    blank.function_by_id_mut(via).unwrap().body_gate = Some(BodyGate::Gated {
        authority: " \t".into(),
        evidence: None,
    });
    let e = validate_module(&blank);
    let twin = e.len() == 1
        && matches!(&e[0], ValidationError::InvalidBodyGate { function, detail }
            if *function == via.index() && detail.contains("blank authority"));
    assert!(feature_check(
        "b1.body_gate.neg.blank_authority",
        twin,
        &format!("{e:?}")
    ));
}

/// FLIPPED by WS1.5 (re-scoped, not "a registry"): the archived ratchet
/// recorded that `BodyGate::Gated.authority` was free text — the only rule
/// was "not blank", `codegen_license_errors` matched `Gated { .. }` without
/// reading the string, and no entry point took a recognized-authority list.
///
/// Now (a) the evidence-bound authority `clean-kernel-tv`
/// (`EVIDENCE_BOUND_GATE_AUTHORITIES`) is refused by name when the module
/// carries no kernel-rechecked TV certificate for the body
/// (`GatedWithoutEvidence`), and (b) a consumer names what it recognizes
/// through `validate_module_for_codegen_with(CodegenAdmission::with_recognized)`,
/// under which every forged spelling is `UnrecognizedGateAuthority`. What
/// stays by ratified design: the POLICY-FREE entry point leaves an authority
/// outside the evidence table (case/padding variants of the real one
/// included — they are simply different, unbound strings) to the consumer.
/// Negative twin: the same bodies under the recognized direct-lane authority
/// are admitted by the same admission, so the refusals are caused by the
/// authority string alone.
fn b1_04_gap_gated_authority_is_free_text() {
    let base = build(Skew::None);
    assert!(
        validate_module_for_codegen(&base).is_empty(),
        "baseline must be admitted"
    );
    let recognized: std::collections::BTreeSet<String> =
        [AUTH_CLEAN_KERNEL_TV, AUTH_CLEAN, AUTH_RUST]
            .into_iter()
            .map(String::from)
            .collect();
    let admission = CodegenAdmission::pinned().with_recognized(&recognized);
    let relabel = |authority: &str| {
        let mut m = base.clone();
        for f in m
            .functions
            .iter_mut()
            .filter(|f| f.producer == Some(Producer::Clean) && !f.blocks.is_empty())
        {
            f.body_gate = Some(BodyGate::Gated {
                authority: authority.to_string(),
                evidence: None,
            });
        }
        m
    };
    let clean_bodies: Vec<u32> = base
        .functions
        .iter()
        .filter(|f| f.producer == Some(Producer::Clean) && !f.blocks.is_empty())
        .map(|f| f.id.index())
        .collect();

    // (a) the evidence-bound authority without its evidence.
    let kernel_tv = relabel(AUTH_CLEAN_KERNEL_TV);
    let structural = validate_module(&kernel_tv);
    let cg = validate_module_for_codegen(&kernel_tv);
    let evidence_bound = structural.is_empty()
        && cg.len() == clean_bodies.len()
        && cg.iter().zip(&clean_bodies).all(|(e, id)| {
            matches!(e, ValidationError::GatedWithoutEvidence { function, authority, detail }
                if function == id && authority == AUTH_CLEAN_KERNEL_TV
                    && detail.contains("no TranslationValidation obligation"))
        })
        && validate_module_for_codegen_with(&kernel_tv, &admission) == cg;

    // (b) forged spellings: policy-free admits (consumer decision), the
    // recognized-set admission refuses each by name.
    let forged = [
        "attacker-says-ok",
        "CLEAN-KERNEL-TV",  // case variant of the real authority
        " clean-kernel-tv", // padded spelling
        "none",
        "ungated", // the refusing token, worn as an authority
        "x",
    ];
    let mut outcomes = Vec::new();
    let mut forged_ok = true;
    for authority in forged {
        let m = relabel(authority);
        let policy_free = validate_module_for_codegen(&m);
        let under = validate_module_for_codegen_with(&m, &admission);
        let want: Vec<ValidationError> = clean_bodies
            .iter()
            .map(|id| ValidationError::UnrecognizedGateAuthority {
                function: *id,
                authority: authority.to_string(),
            })
            .collect();
        forged_ok &=
            policy_free.is_empty() && under == want && roundtrip_all(&m).lossless_production();
        outcomes.push(format!(
            "{authority:?}: policy-free={policy_free:?} recognized={under:?}"
        ));
    }

    // Negative twin: the baseline under the same admission is admitted.
    let twin = validate_module_for_codegen_with(&base, &admission);
    assert!(feature_check(
        "b1.gap.gated_authority_unpinned",
        evidence_bound && forged_ok && twin.is_empty(),
        &format!(
            "closed by WS1.5: Gated{{clean-kernel-tv}} without evidence => validate_module={structural:?} \
             for_codegen={cg:?}; forged spellings {outcomes:?}; twin (baseline under the same \
             recognized set) => {twin:?}"
        ),
    ));
}

// ===========================================================================
// 4. the reserved @trust-internal:: disclosure SpecModules
// ===========================================================================

fn reserved_errors(m: &Module) -> Vec<ValidationError> {
    validate_module(m)
        .into_iter()
        .filter(|e| matches!(e, ValidationError::ReservedSpecModuleName { .. }))
        .collect()
}

fn b1_05_trust_internal_disclosures() {
    let m = build(Skew::None);
    let names: Vec<_> = m.spec_modules.iter().map(|s| s.name.as_str()).collect();
    let shape_ok = m.spec_modules.iter().all(|s| {
        s.origin == SpecOrigin::Embedded
            && s.enforcement == SpecEnforcementMode::DesignOnly
            && !s.invariants.is_empty()
            && s.vars.is_empty()
            && s.actions.is_empty()
            && s.anchors.is_empty()
    });
    let all_reserved = RESERVED_TRUST_INTERNAL_SPEC_MODULES
        .iter()
        .all(|n| names.contains(n));
    let rt = roundtrip_all(&m);
    // WS4.2: text carries what its grammar spells, and a module with any
    // field it cannot carry is REFUSED as `#lossy` rather than dropped; the
    // spec modules must survive what text carries (`carried()`).
    let survived = rt.all().iter().all(|t| {
        t.carried()
            .map(|d| d.spec_modules == m.spec_modules)
            .unwrap_or(false)
    });
    assert!(feature_check(
        "b1.spec.trust_internal_disclosures",
        shape_ok && all_reserved && names.len() == 3 && validate_module(&m).is_empty() && survived,
        &format!(
            "DesignOnly+Embedded, invariants only, {names:?} validate and survive all 4 codecs \
             (text: what its grammar carries; this module is text-lossy={:?}) \
             (trust-ir reserves {} names)",
            rt.text.lossy,
            RESERVED_TRUST_INTERNAL_SPEC_MODULES.len()
        ),
    ));

    // neg 1: a minted name in the reserved namespace (closed set).
    let mut minted = m.clone();
    minted.spec_modules[0].name = "@trust-internal::borrow-check-disclosure-v1".into();
    let e = reserved_errors(&minted);
    let all = validate_module(&minted);
    let twin = e.len() == 1
        && all.len() == 1
        && matches!(&e[0], ValidationError::ReservedSpecModuleName { name, .. }
            if name == "@trust-internal::borrow-check-disclosure-v1")
        && e[0].to_string().contains("closed set");
    assert!(feature_check(
        "b1.spec.neg.minted_reserved_name",
        twin,
        &format!("all errors={all:?}")
    ));

    // neg 2: the right name promoted from DesignOnly to Linked enforcement.
    let mut linked = m.clone();
    linked.spec_modules[1].enforcement = SpecEnforcementMode::Linked;
    let e = reserved_errors(&linked);
    let all = validate_module(&linked);
    let twin = e.len() == 1
        && matches!(&e[0], ValidationError::ReservedSpecModuleName { name, .. }
            if name == "@trust-internal::contract-disclosure-v1")
        && e[0].to_string().contains("linked");
    assert!(feature_check(
        "b1.spec.neg.disclosure_not_design_only",
        twin,
        &format!("reserved-name errors={e:?}; ALL errors of the single mutation={all:?}"),
    ));

    // neg 3: the right name claiming an external origin.
    let mut external = m.clone();
    external.spec_modules[0].origin = SpecOrigin::External("attacker.tla".into());
    let e = reserved_errors(&external);
    let all = validate_module(&external);
    let twin = e.len() == 1
        && matches!(&e[0], ValidationError::ReservedSpecModuleName { name, .. }
            if name == "@trust-internal::clean-origin-disclosure-v1")
        && e[0].to_string().contains("external(attacker.tla)");
    assert!(feature_check(
        "b1.spec.neg.disclosure_external_origin",
        twin,
        &format!("reserved-name errors={e:?}; ALL errors of the single mutation={all:?}"),
    ));

    // neg 4: the right name smuggling AUTHORITY (a waiver-free, anchor-free
    // disclosure is the only admitted shape): give it a state variable.
    let mut with_vars = m.clone();
    with_vars.spec_modules[2]
        .vars
        .push(trust_ir::spec::SpecVar::new("pc", "Nat"));
    let e = reserved_errors(&with_vars);
    let twin = e.len() == 1
        && matches!(&e[0], ValidationError::ReservedSpecModuleName { name, detail }
            if name == "@trust-internal::deferred-verification-disclosure-v1" && detail.contains("vars"));
    assert!(feature_check(
        "b1.spec.neg.disclosure_carries_vars",
        twin,
        &format!("{e:?}")
    ));
}

/// GAP (reviewer-found; the PASS row above only passes because nothing reads
/// the rows): a reserved disclosure is held to a SHAPE
/// (`reserved_spec_module_errors`, trust-ir-build/src/validate.rs:10276-10340:
/// closed name set, invariants-only, DesignOnly, Embedded) and to nothing else.
/// Its rows are opaque strings that no entry point binds to the module they
/// disclose, so (a) this hand-written test module mints all three
/// "compiler-internal" disclosures and is accepted, and (b) a clean-origin row
/// that CONTRADICTS the function it names — a symbol that does not exist, tier
/// `general` + `body_gate: ungated` for a body whose `Function.body_gate` is
/// `Gated{clean-kernel-tv}` — validates under every entry point, codegen
/// included. Design requirement blocked: the clean-origin disclosure is the
/// per-def tier/license record of the two-language design; at the format level
/// it is decoration, and only `Function.body_gate` is a checked license.
fn b1_05b_gap_disclosure_rows_unbound_to_module() {
    let base = build(Skew::None);
    assert!(
        validate_module_for_codegen(&base).is_empty(),
        "baseline must be admitted"
    );

    let mut lying = base.clone();
    // single change: the formula text of the two clean-origin rows.
    lying.spec_modules[0].invariants[0] = SpecInvariant::new(
        "def:App.addmul",
        r#"{"symbol":"clean_App_DOES_NOT_EXIST","tier":"general","body_gate":"ungated"}"#,
    );
    lying.spec_modules[0].invariants[1] = SpecInvariant::new(
        "def:App.viaRust",
        r#"{"symbol":"clean_App_viaRust","tier":"gate","rust_call_chain":["no_such_rust_fn"]}"#,
    );
    let structural = validate_module(&lying);
    let authority = validate_module_with_authority(&lying, &RejectingModuleProofAuthority);
    let codegen = validate_module_for_codegen(&lying);
    let still_gated = lying.function_by_name(SYM_ADDMUL).unwrap().body_gate
        == Some(BodyGate::Gated {
            authority: AUTH_CLEAN.into(),
            evidence: None,
        });
    let all: Vec<&ValidationError> = structural
        .iter()
        .chain(&authority)
        .chain(&codegen)
        .collect();
    assert!(feature_gap(
        "b1.gap.disclosure_rows_unbound_to_module",
        Expect::Accepted,
        Outcome::of(&all).given(&[(
            "the named body is still Gated (its body_gate is untouched)",
            still_gated
        )]),
        &format!(
            "clean-origin rows naming a nonexistent symbol / claiming `ungated` for a Gated body / a \
             nonexistent Rust callee: validate_module={structural:?} with_authority={authority:?} \
             for_codegen={codegen:?}; only the SHAPE is checked (validate.rs:10276-10340), rows are \
             opaque strings; a hand-written module may mint all {} reserved disclosures. The KEY \
             half is closed by WS1.5 for the `fn:N` keys the Trust minter writes \
             (b1.disclosure.fn_key_names_a_body); row CONTENT stays an unauthenticated producer \
             claim until the typed slot of WS1.12c replaces the rows (LIMITATIONS.md)",
            RESERVED_TRUST_INTERNAL_SPEC_MODULES.len()
        ),
    ));

    // The KEY half (WS1.5, F-017): a `fn:N` row — the key `~/trust`
    // `clean_origin_join.rs` writes per emitted Clean-origin body — must name a
    // bodied function of THIS module. PASS: `fn:<addmul>` validates everywhere;
    // negative twin: the single change `fn:<addmul>` -> `fn:999` (no such
    // function) is refused by name, under every entry point.
    let addmul = fid(&base, SYM_ADDMUL).index();
    let keyed = |key: &str| {
        let mut m = base.clone();
        m.spec_modules[0].invariants.push(SpecInvariant::new(
            key,
            r#"{"schema":"trust.clean-origin-disclosure.v1"}"#,
        ));
        m
    };
    let honest = keyed(&format!("fn:{addmul}"));
    let honest_errors = [
        validate_module(&honest),
        validate_module_with_authority(&honest, &RejectingModuleProofAuthority),
        validate_module_for_codegen(&honest),
    ];
    let ghost = keyed("fn:999");
    let ghost_errors = [
        validate_module(&ghost),
        validate_module_with_authority(&ghost, &RejectingModuleProofAuthority),
        validate_module_for_codegen(&ghost),
    ];
    let refused_by_name = ghost_errors.iter().all(|errors| {
        errors
            == &vec![ValidationError::ReservedSpecModuleName {
                name: "@trust-internal::clean-origin-disclosure-v1".into(),
                detail: "disclosure row fn:999 names no bodied function".into(),
            }]
    });
    assert!(feature_check(
        "b1.disclosure.fn_key_names_a_body",
        honest_errors.iter().all(Vec::is_empty) && refused_by_name,
        &format!("fn:{addmul} (App.addmul) => {honest_errors:?}; twin fn:999 => {ghost_errors:?}"),
    ));
}

// ===========================================================================
// 5. Linkage + Visibility + target_info
// ===========================================================================

fn b1_06_linkage_visibility_target() {
    let m = build(Skew::None);
    let fl: Vec<_> = m
        .functions
        .iter()
        .map(|f| (f.name.as_str(), f.linkage, f.calling_conv))
        .collect();
    let gl: Vec<_> = m
        .globals
        .iter()
        .map(|g| {
            (
                g.name.as_str(),
                g.linkage,
                g.visibility,
                g.tls,
                g.retained,
                g.section.clone(),
            )
        })
        .collect();
    let rt = roundtrip_all(&m);
    let production = [&rt.binary, &rt.json, &rt.msgpack];
    let carried = production.iter().all(|t| {
        t.decoded.as_ref().is_some_and(|d| {
            d.globals == m.globals
                && d.functions.iter().map(|f| f.linkage).collect::<Vec<_>>()
                    == m.functions.iter().map(|f| f.linkage).collect::<Vec<_>>()
        })
    });
    let ok = m.function_by_name(SYM_LEAF).unwrap().linkage == Linkage::Internal
        && m.function_by_name(SYM_ADDMUL).unwrap().linkage == Linkage::LinkOnceOdr
        && m.function_by_name(SYM_WEAK_HOOK).unwrap().linkage == Linkage::External
        && m.globals[0].visibility == Visibility::Hidden
        && m.globals[0].linkage == Linkage::External // hidden-but-external: the v41 point
        && m.globals[1].visibility == Visibility::Protected
        && m.globals[1].linkage == Linkage::WeakOdr
        && validate_module(&m).is_empty()
        && carried;
    assert!(feature_check(
        "b1.linkage_and_visibility",
        ok,
        &format!("functions={fl:?} globals={gl:?}; carried by binary/JSON/MessagePack"),
    ));

    // negative twin (validator level): linkage is load-bearing for the ONE
    // structural rule that reads it — a bodyless function is a declaration
    // only under `External` (validate.rs:3022-3024, 3493). Internal => refused.
    let mut internal_decl = m.clone();
    let hook = fid(&internal_decl, SYM_WEAK_HOOK);
    internal_decl.function_by_id_mut(hook).unwrap().linkage = Linkage::Internal;
    let e = validate_module(&internal_decl);
    assert!(feature_check(
        "b1.linkage.neg.internal_bodyless_declaration_refused",
        e == vec![ValidationError::EmptyFunction],
        &format!("bodyless @{SYM_WEAK_HOOK} External -> Internal => {e:?}"),
    ));

    // negative twin (wire level): the v41 linkage/visibility residue cannot be
    // projected to v38 — the explicit RawV38 projection refuses it. Baseline:
    // the same module with ONLY legacy linkage/default visibility and no other
    // v41 feature projects fine.
    let legacy = strip_v41(&m);
    let legacy_ok =
        ProjectedModuleBinaryPlan::try_new(&legacy, ModuleBinaryOptions::default()).is_ok();
    let mut vis_only = legacy.clone();
    vis_only.globals[0].visibility = Visibility::Hidden;
    let vis_refused = matches!(
        ProjectedModuleBinaryPlan::try_new(&vis_only, ModuleBinaryOptions::default()),
        Err(BinaryProjectionError::ContractSurfaceRequiresV41)
    );
    let mut link_only = legacy.clone();
    let addmul = fid(&link_only, SYM_ADDMUL);
    link_only.function_by_id_mut(addmul).unwrap().linkage = Linkage::LinkOnceOdr;
    let link_refused = matches!(
        ProjectedModuleBinaryPlan::try_new(&link_only, ModuleBinaryOptions::default()),
        Err(BinaryProjectionError::ContractSurfaceRequiresV41)
    );
    let v_vis = common::binary_version(
        &trust_ir::binary::serialize_module(&vis_only).expect("serialize_module: test fixture"),
    );
    let v_link = common::binary_version(
        &trust_ir::binary::serialize_module(&link_only).expect("serialize_module: test fixture"),
    );
    assert!(feature_check(
        "b1.linkage_and_visibility.neg.v38_projection_refused",
        legacy_ok && vis_refused && link_refused && v_vis == 41 && v_link == 41,
        &format!(
            "legacy RawV38 ok={legacy_ok}; Visibility::Hidden alone => ContractSurfaceRequiresV41={vis_refused} (writer v{v_vis}); \
             Linkage::LinkOnceOdr alone => {link_refused} (writer v{v_link})"
        ),
    ));

    // target_info: present, canonical 64-bit LE, carried by all four codecs.
    let ti_ok = m.target_info == Some(target())
        && rt
            .all()
            .iter()
            .all(|t| t.carried().is_some_and(|d| d.target_info == m.target_info));
    assert!(feature_check(
        "b1.target_info",
        ti_ok,
        &format!(
            "{:?} survives binary/text/JSON/MessagePack (text: what its grammar carries; \
             text-lossy={:?})",
            m.target_info, rt.text.lossy
        ),
    ));

    // negative twin: this module HAS an FFI boundary (the bodyless C-conv
    // declaration and the Rust-cc <-> C-cc call edges between the two
    // languages), so dropping the target is refused (validate.rs:11122-11127,
    // boundary found by trust-ir/src/lib.rs:1263 first_ffi_boundary).
    let mut no_target = m.clone();
    no_target.target_info = None;
    let e = validate_module(&no_target);
    let twin = e.len() == 1 && matches!(&e[0], ValidationError::TargetInfoRequired { .. });
    assert!(feature_check(
        "b1.target_info.neg.required_at_ffi_boundary",
        twin,
        &format!("{e:?}")
    ));

    // second twin: with the declaration removed, the boundary that remains IS
    // the two-language call edge (cross-convention Rust cc -> C cc).
    let mut edge_only = no_target.clone();
    edge_only.functions.retain(|f| f.name != SYM_WEAK_HOOK);
    let e = validate_module(&edge_only);
    let twin = e.len() == 1
        && matches!(&e[0], ValidationError::TargetInfoRequired { boundary }
            if boundary.contains("cross-convention call edge"));
    assert!(feature_check(
        "b1.target_info.neg.cross_language_edge_is_ffi",
        twin,
        &format!("{e:?}")
    ));

    // third twin: a malformed pin.
    let mut bad = m.clone();
    bad.target_info.as_mut().unwrap().pointer_size = 3;
    let e = validate_module(&bad);
    let twin = e == vec![ValidationError::TargetPointerSizeInvalid { pointer_size: 3 }];
    assert!(feature_check(
        "b1.target_info.neg.bad_pointer_size",
        twin,
        &format!("{e:?}")
    ));
}

/// The same program with every v41 surface removed (license, display path,
/// v41 linkages, visibility/section/retained) — the writer's v38 baseline.
fn strip_v41(m: &Module) -> Module {
    let mut s = m.clone();
    for f in &mut s.functions {
        f.body_gate = None;
        f.display_path = None;
        if matches!(f.linkage, Linkage::LinkOnceOdr | Linkage::ExternalWeak) {
            f.linkage = Linkage::External;
        }
    }
    for g in &mut s.globals {
        g.visibility = Visibility::Default;
        g.section = None;
        g.retained = false;
        if g.linkage == Linkage::WeakOdr {
            g.linkage = Linkage::Weak;
        }
    }
    s
}

// ===========================================================================
// 6. four-format round trip + writer version selection
// ===========================================================================

fn b1_07_roundtrip_and_wire_version() {
    let m = build(Skew::None);
    let rt = roundtrip_all(&m);

    assert!(feature_check(
        "b1.roundtrip.binary_json_msgpack",
        rt.lossless_production(),
        &rt.summary(),
    ));

    // negative twin: the binary reader rejects a trailing byte and a
    // truncated blob (no silent partial decode).
    let mut trailing = rt.binary.encoded.clone();
    trailing.push(0);
    let truncated = &rt.binary.encoded[..rt.binary.encoded.len() - 1];
    let t1 = trust_ir::binary::deserialize_module(&trailing);
    let t2 = trust_ir::binary::deserialize_module(truncated);
    assert!(feature_check(
        "b1.roundtrip.neg.trailing_and_truncated_refused",
        matches!(&t1, Err(BinaryError::InvalidData(msg)) if msg.contains("trailing bytes"))
            && matches!(
                &t2,
                Err(BinaryError::TooLarge { .. } | BinaryError::UnexpectedEof)
            ),
        &format!(
            "trailing={:?} truncated={:?}",
            t1.as_ref().err(),
            t2.as_ref().err()
        ),
    ));

    // writer version: >= 41 for this module, 38 once the v41 surface is
    // stripped (so the selection is caused by the contract surface), and an
    // explicit v38 projection of the full module is refused by name.
    let stripped = strip_v41(&m);
    let v_stripped = common::binary_version(
        &trust_ir::binary::serialize_module(&stripped).expect("serialize_module: test fixture"),
    );
    let refused = ProjectedModuleBinaryPlan::try_new(
        &m,
        ModuleBinaryOptions {
            body: ModuleBinaryBody::RawV38,
            ..ModuleBinaryOptions::default()
        },
    );
    let refused_ok = matches!(
        refused,
        Err(BinaryProjectionError::ContractSurfaceRequiresV41)
    );
    assert!(feature_check(
        "b1.wire_version.writer_selects_v41",
        rt.binary_version >= 41 && rt.binary_version == 41 && v_stripped == 38 && refused_ok,
        &format!(
            "full module => v{} (VERSION={}); v41-stripped twin => v{v_stripped}; RawV38 projection => {:?}",
            rt.binary_version,
            trust_ir::binary::VERSION,
            refused.as_ref().err()
        ),
    ));

    // WS4.5's global subset: the unchanged mixed-language module now
    // round-trips without erasing its link-time attributes first.
    let text = String::from_utf8(rt.text.encoded.clone()).unwrap();
    let canonical = trust_ir::format::canonicalize(&m);
    let back = trust_ir::parser::parse_module(&text).expect("loss-free global metadata");
    let malformed = text.replacen("visibility(hidden)", "visibility(unknown)", 1);
    assert_ne!(malformed, text);
    assert!(feature_check(
        "b1.gap.text_drops_global_visibility_section_retained",
        back == canonical
            && back.stable_digest() == canonical.stable_digest()
            && rt.text.lossy.is_none()
            && trust_ir::parser::parse_module(&malformed).is_err(),
        "global section/visibility/retained survive text with exact structure and digest; unknown visibility is refused",
    ));
    assert!(feature_check(
        "b1.roundtrip.four_formats_modulo_global_visibility",
        rt.lossless_all() && rt.binary_version == 41 && validate_module(&m).is_empty(),
        &format!("no attributes normalized: {}", rt.summary()),
    ));
}

// ===========================================================================
// 7. the reference interpreter runs the entry through both languages
// ===========================================================================

fn b1_08_interpreter_runs_through_both_languages() {
    let m = build(Skew::None);
    let got = run_nullary(&m, SYM_PROGRAM);
    assert!(feature_check(
        "b1.interpret.entry_through_both_languages",
        u64_of(&got) == Some(EXPECTED),
        &format!(
            "program() = {got:?}, expected {EXPECTED} (Rust->Lean addmul(6,7)=48 + Rust->Lean->Rust->Rust leaf viaRust(3,4)=12)"
        ),
    ));

    // Lean -> Rust -> Rust leaf, entered directly at the Clean function.
    let via = run_with_args(
        &m,
        SYM_VIA_RUST,
        vec![
            InterpretValue::int(Ty::U64, 10).unwrap(),
            InterpretValue::int(Ty::U64, 5).unwrap(),
        ],
    );
    assert!(feature_check(
        "b1.interpret.lean_to_rust_to_rust_leaf",
        u64_of(&via) == Some((10 + 1) * 2 + 5),
        &format!("clean_App_viaRust(10,5) = {via:?}, expected 27"),
    ));

    // Every decoded copy executes to the same value (the codecs preserve
    // behaviour, not just shape).
    let rt = roundtrip_all(&m);
    let each: Vec<_> = rt
        .all()
        .iter()
        .map(|t| {
            (
                t.format,
                t.carried().map(|d| u64_of(&run_nullary(d, SYM_PROGRAM))),
            )
        })
        .collect();
    assert!(feature_check(
        "b1.interpret.decoded_copies_agree",
        each.iter().all(|(_, v)| *v == Some(Some(EXPECTED))),
        &format!("{each:?}"),
    ));

    // Mutation controls (the twin of an execution claim): the result really
    // flows through EACH language's body.
    let mut clean_mut = m.clone();
    flip_first_binop(&mut clean_mut, SYM_ADDMUL, BinOp::Mul, BinOp::Add);
    let c = run_nullary(&clean_mut, SYM_PROGRAM); // (6+7+6) + 12 = 31
    let mut leaf_mut = m.clone();
    flip_first_binop(&mut leaf_mut, SYM_LEAF, BinOp::Add, BinOp::Sub);
    let l = run_nullary(&leaf_mut, SYM_PROGRAM); // 48 + ((3-1)*2+4) = 56
    assert!(feature_check(
        "b1.interpret.neg.mutation_in_each_language_changes_result",
        u64_of(&c) == Some(31) && u64_of(&l) == Some(56),
        &format!("Clean body mul->add => {c:?} (want 31); Rust LEAF add->sub => {l:?} (want 56)"),
    ));

    // The skewed (invalid) module is not executed to a value either: the
    // interpreter refuses the arity-skewed Rust->Lean edge.
    let skewed = run_nullary(&build(Skew::RustToLeanArity), SYM_PROGRAM);
    assert!(feature_check(
        "b1.interpret.neg.skewed_edge_does_not_execute",
        matches!(&skewed, Err(msg) if msg.starts_with("SignatureMismatch") && msg.contains("expected 2, got 1")),
        &format!("{skewed:?}"),
    ));
}

fn flip_first_binop(m: &mut Module, func: &str, from: BinOp, to: BinOp) {
    let id = fid(m, func);
    let f = m.function_by_id_mut(id).unwrap();
    for b in &mut f.blocks {
        for n in &mut b.body {
            if let Inst::BinOp { op, .. } = &mut n.inst
                && *op == from
            {
                *op = to;
                return;
            }
        }
    }
    panic!("no {from:?} in @{func}");
}

// ===========================================================================
// 8. semantic diff
// ===========================================================================

fn meta_fields(d: &trust_ir::diff::Diff, func: &str) -> Vec<(String, String, String)> {
    d.changes
        .iter()
        .filter_map(|c| match c {
            FuncChange::Changed {
                name, meta_changes, ..
            } if name == func => Some(
                meta_changes
                    .iter()
                    .map(|m| (m.field.clone(), m.before.clone(), m.after.clone()))
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        })
        .flatten()
        .collect()
}

fn b1_09_diff_reports_producer_flip() {
    let a = build(Skew::None);

    // twin / control: identical modules => empty diff.
    let same = diff(&a, &a.clone());

    let mut b = a.clone();
    let id = fid(&b, SYM_ADDMUL);
    b.function_by_id_mut(id).unwrap().producer = Some(Producer::TRust);
    let d = diff(&a, &b);
    let meta = meta_fields(&d, SYM_ADDMUL);
    let ok = same.is_empty()
        && d.changes.len() == 1
        && meta
            == vec![(
                "producer".to_string(),
                "clean".to_string(),
                "trust".to_string(),
            )]
        && d.exit_code() != 0;
    assert!(feature_check(
        "b1.diff.producer_flip_reported",
        ok,
        &format!(
            "identical => empty={}; Clean->TRust on @{SYM_ADDMUL} => {meta:?} exit={}",
            same.is_empty(),
            d.exit_code()
        ),
    ));
}

/// Module-level metadata rows of a diff: `(field, before, after)`.
fn module_meta(d: &trust_ir::diff::Diff) -> Vec<(String, String, String)> {
    d.module_meta_changes
        .iter()
        .map(|m| (m.field.clone(), m.before.clone(), m.after.clone()))
        .collect()
}

/// FLIPPED (closed upstream by f3c07824 "fix(diff): report authority, ABI and
/// linkage metadata changes"): the archived ratchet `b1.gap.diff_blind_to_body_gate`
/// recorded that `diff` compared only `producer` + `source_provenance`. It now
/// reports a `body_gate` flip. PASS: each of the three license changes is
/// reported as exactly one `body_gate` metadata change on the one function,
/// with a non-zero exit. Negative twin: the unmutated copy diffs empty, exit 0
/// (the report is caused by the license change and nothing else).
fn b1_10_diff_reports_body_gate() {
    let a = build(Skew::None);
    assert!(validate_module(&a).is_empty() && validate_module_for_codegen(&a).is_empty());
    let via = fid(&a, SYM_VIA_RUST);

    let mut ungated = a.clone();
    ungated.function_by_id_mut(via).unwrap().body_gate = Some(BodyGate::Ungated);
    let mut swapped = a.clone();
    swapped.function_by_id_mut(via).unwrap().body_gate = Some(BodyGate::Gated {
        authority: "someone-else".into(),
        evidence: None,
    });
    let mut unclaimed = a.clone();
    unclaimed.function_by_id_mut(via).unwrap().body_gate = None;

    let reported: Vec<Vec<(String, String, String)>> = [&ungated, &swapped, &unclaimed]
        .iter()
        .map(|b| meta_fields(&diff(&a, b), SYM_VIA_RUST))
        .collect();
    let exits: Vec<i32> = [&ungated, &swapped, &unclaimed]
        .iter()
        .map(|b| diff(&a, b).exit_code())
        .collect();
    let each_is_one_body_gate_row = reported
        .iter()
        .all(|rows| rows.len() == 1 && rows[0].0 == "body_gate")
        && [&ungated, &swapped, &unclaimed]
            .iter()
            .all(|b| diff(&a, b).changes.len() == 1)
        && exits.iter().all(|e| *e != 0);
    let control = diff(&a, &a.clone());
    assert!(feature_check(
        "b1.gap.diff_blind_to_body_gate",
        each_is_one_body_gate_row && control.is_empty() && control.exit_code() == 0,
        &format!(
            "closed upstream by f3c07824: Gated->Ungated / authority swap / Gated->None => {reported:?} \
             exit={exits:?}; negative twin: the unmutated copy => empty={} exit {}",
            control.is_empty(),
            control.exit_code()
        ),
    ));
    // By design, the executable-content identity does NOT move with the license.
    assert!(
        a.executable_content_digest_v1() == ungated.executable_content_digest_v1(),
        "executable_content_digest_v1 is documented to exclude body_gate"
    );
}

/// FLIPPED (closed upstream by f3c07824 and d71950bf): the archived ratchets
/// `b1.gap.diff_blind_to_{display_path,function_linkage,calling_conv,globals,
/// spec_modules_and_target}` recorded a diff that read no v41 function or module
/// metadata. Each single-field mutant is now reported under its own field name;
/// the negative twin of every row is the unmutated copy, which diffs empty.
fn b1_11_diff_reports_other_v41_metadata() {
    let a = build(Skew::None);
    let mid = fid(&a, SYM_MID);
    let control = diff(&a, &a.clone());
    assert!(
        control.is_empty() && control.exit_code() == 0,
        "the unmutated copy diffs empty"
    );
    let only_fn_field = |b: &Module, field: &str| {
        let d = diff(&a, b);
        let rows = meta_fields(&d, SYM_MID);
        let ok = d.changes.len() == 1
            && rows.len() == 1
            && rows[0].0 == field
            && d.module_meta_changes.is_empty()
            && d.exit_code() != 0;
        (ok, format!("{rows:?}"))
    };

    let mut path = a.clone();
    path.function_by_id_mut(mid).unwrap().display_path = Some("evil::other_path".into());
    let (ok, rows) = only_fn_field(&path, "display_path");
    assert!(feature_check(
        "b1.gap.diff_blind_to_display_path",
        ok,
        &format!(
            "closed upstream by f3c07824: display_path app::rust_mid -> evil::other_path => {rows}; twin: unmutated copy => empty"
        ),
    ));

    let mut link = a.clone();
    link.function_by_id_mut(mid).unwrap().linkage = Linkage::Internal;
    let (ok, rows) = only_fn_field(&link, "linkage");
    assert!(feature_check(
        "b1.gap.diff_blind_to_function_linkage",
        ok,
        &format!(
            "closed upstream by f3c07824: fn linkage External -> Internal => {rows}; twin: unmutated copy => empty"
        ),
    ));

    let mut cc = a.clone();
    cc.function_by_id_mut(mid).unwrap().calling_conv = CallingConv::C;
    let (ok, rows) = only_fn_field(&cc, "calling_conv");
    assert!(feature_check(
        "b1.gap.diff_blind_to_calling_conv",
        ok,
        &format!(
            "closed upstream by f3c07824: fn calling_conv Rust -> C => {rows}; twin: unmutated copy => empty"
        ),
    ));

    // two SEPARATE single-field mutants of one global.
    let mut vis = a.clone();
    vis.globals[0].visibility = Visibility::Default;
    let mut init = a.clone();
    init.globals[0].initializer = Some(Constant::Int(2)); // changes program() from 60 to 62
    let behaviour_changed = u64_of(&run_nullary(&init, SYM_PROGRAM)) == Some(62);
    let global_row = |b: &Module| {
        let d = diff(&a, b);
        let rows = module_meta(&d);
        (
            d.changes.is_empty()
                && rows.len() == 1
                && rows[0].0 == "global @APP_BIAS"
                && d.exit_code() != 0,
            rows,
        )
    };
    let (vis_ok, vis_rows) = global_row(&vis);
    let (init_ok, init_rows) = global_row(&init);
    assert!(feature_check(
        "b1.gap.diff_blind_to_globals",
        vis_ok && init_ok && behaviour_changed,
        &format!(
            "closed upstream by f3c07824: @APP_BIAS visibility Hidden->Default => {vis_rows:?}; initializer 1->2 \
             (program() 60->62, executed) => {init_rows:?}; twin: unmutated copy => empty"
        ),
    ));

    let mut spec = a.clone();
    spec.spec_modules.remove(0);
    let mut tgt = a.clone();
    tgt.target_info.as_mut().unwrap().triple = "x86_64-unknown-linux-gnu".into();
    let d1 = diff(&a, &spec);
    let d2 = diff(&a, &tgt);
    let (r1, r2) = (module_meta(&d1), module_meta(&d2));
    assert!(feature_check(
        "b1.gap.diff_blind_to_spec_modules_and_target",
        d1.changes.is_empty()
            && r1.len() == 1
            && r1[0].0 == "spec_module @trust-internal::clean-origin-disclosure-v1"
            && r1[0].2 == "-"
            && d2.changes.is_empty()
            && r2.len() == 1
            && r2[0].0 == "target_info",
        &format!(
            "closed upstream by f3c07824/d71950bf: dropping the clean-origin disclosure => {:?}; retargeting => {:?}; \
             twin: unmutated copy => empty",
            r1.iter().map(|r| &r.0).collect::<Vec<_>>(),
            r2.iter().map(|r| &r.0).collect::<Vec<_>>()
        ),
    ));
}

/// PASS (closed upstream by WS3.15, dc416921/e95e632e; F-058): `Linkage::ExternalWeak`
/// is documented as "A weak DECLARATION: resolves to null rather than failing the
/// link when no definition exists (LLVM `extern_weak`)". The archived ratchet
/// recorded that the validator treated a bodyless function as a declaration only
/// at EXACTLY `External`, so the bodyless weak import was refused as
/// `EmptyFunction` and validated only through the linkage-agnostic contract-only
/// summary door. A bodyless `ExternalWeak` is now a declaration
/// (`Function::is_weak_declaration`).
///
/// Negative twin (right reason): the same weak hook called DIRECTLY — its symbol
/// may resolve to null — is exactly `DirectCallToWeakDeclaration`, while the SAME
/// direct call of the `External` hook validates (closeness control: one change,
/// the linkage). Mutation control: a bodyless `AvailableExternally` (by definition
/// a body copy) is still exactly `EmptyFunction`, so the admission is weak-only.
fn b1_12_gap_extern_weak_declaration_refused() {
    let base = build(Skew::None);
    let hook = fid(&base, SYM_WEAK_HOOK);
    let program = fid(&base, SYM_PROGRAM);
    assert!(
        validate_module(&base).is_empty(),
        "baseline (External bodyless declaration) validates"
    );
    assert!(
        base.function_by_name(SYM_WEAK_HOOK)
            .unwrap()
            .blocks
            .is_empty()
    );

    let with_linkage = |m: &Module, linkage: Linkage| {
        let mut m = m.clone();
        m.function_by_id_mut(hook).unwrap().linkage = linkage;
        m
    };
    let weak = with_linkage(&base, Linkage::ExternalWeak);
    let e = validate_module(&weak);

    // Twin: retarget `program`'s first direct call (to the Clean `addmul`) at
    // the nullary hook, which has the same `-> u64` result.
    let direct_call = |m: &Module| {
        let mut m = m.clone();
        let f = m.function_by_id_mut(program).unwrap();
        let node = f
            .blocks
            .iter_mut()
            .flat_map(|b| b.body.iter_mut())
            .find(|n| matches!(n.inst, Inst::Call { .. }))
            .expect("program makes a direct call");
        node.inst = Inst::Call {
            callee: hook,
            args: Vec::new(),
        };
        m
    };
    let strong_direct = validate_module(&direct_call(&base));
    let weak_direct = validate_module(&direct_call(&weak));
    let twin_named = matches!(
        weak_direct.as_slice(),
        [ValidationError::DirectCallToWeakDeclaration { callee, name, .. }]
            if *callee == hook.index() && name == SYM_WEAK_HOOK
    );

    // Mutation control: bodyless AvailableExternally stays EmptyFunction.
    let available = validate_module(&with_linkage(&base, Linkage::AvailableExternally));
    let available_refused = matches!(available.as_slice(), [ValidationError::EmptyFunction]);

    // A BODIED ExternalWeak definition still validates (recorded, not a row
    // condition: F-058's fix direction does not cover it).
    let mut bodied = base.clone();
    let mid = fid(&bodied, SYM_MID);
    bodied.function_by_id_mut(mid).unwrap().linkage = Linkage::ExternalWeak;
    let bodied_errors = validate_module(&bodied);

    // The codecs carry the external-weak linkage. The same module's global
    // attributes have their exact text round trip held separately in b1_07.
    let rt = roundtrip_all(&weak);
    let carried = rt.lossless_production()
        && rt.all().iter().all(|t| {
            t.carried().is_some_and(|d| {
                d.function_by_name(SYM_WEAK_HOOK)
                    .is_some_and(|f| f.linkage == Linkage::ExternalWeak && f.blocks.is_empty())
            })
        });

    assert!(feature_check(
        "b1.gap.extern_weak_declaration_refused",
        e.is_empty() && strong_direct.is_empty() && twin_named && available_refused && carried,
        &format!(
            "closed upstream by WS3.15 (dc416921): bodyless fn External -> ExternalWeak => {e:?}; \
             twin: a direct Call of the weak hook => {weak_direct:?}, the same call of the \
             External hook => {strong_direct:?}; mutation: bodyless AvailableExternally => \
             {available:?}; a BODIED ExternalWeak fn => {bodied_errors:?}; all 4 codecs carry \
             the bodyless extern_weak row={carried} (wire v{})",
            rt.binary_version
        ),
    ));
}

// ---------------------------------------------------------------------------
// b1_13 — the verification bundle STATES the two-language package (WS4.16,
// F-080). Three archived proof-program rows ported here, PASS with twins:
//   goal-g1-g8/g8-toolchain-language-identity
//   spec-surface-0709/28-root-verification-bundle-two-producers
//   arch-0804-and-spine/24-native-verification-bundle (its language half; the
//   TY request lane is the open GAP `f080.ty_request_lane` in the field target)
// ---------------------------------------------------------------------------

/// A complete, validating schema-9 bundle over `module` with the three
/// request lanes the design names (TrustVc / TrustMc / TrustWp), each
/// replay-identified — `generate::build_language_set_bundle`. The language
/// set is `languages`, whose first entry is the primary.
fn bundle_over(
    module: Module,
    producer: NativeBundleProducer,
    languages: &[NativeSourceLanguage],
) -> NativeVerificationBundle {
    generate::build_language_set_bundle(module, producer, languages).expect("the fixture builds")
}

fn bundle_errors(bundle: &NativeVerificationBundle) -> Vec<NativeVerificationBundleError> {
    bundle.validate().err().unwrap_or_default()
}

fn b1_13_bundle_states_two_languages() {
    use NativeSourceLanguage::{Clean as LangClean, Lean, Rust};
    let base = build(Skew::None);
    let rust_fns: Vec<FuncId> = base
        .functions
        .iter()
        .filter(|f| f.producer == Some(Producer::TRust))
        .map(|f| f.id)
        .collect();
    let clean_fns: Vec<FuncId> = base
        .functions
        .iter()
        .filter(|f| f.producer == Some(Producer::Clean))
        .map(|f| f.id)
        .collect();
    assert!(!rust_fns.is_empty() && !clean_fns.is_empty());

    // --- g8-toolchain-language-identity ------------------------------------
    // "artifacts bind pinned compiler, solver, kernel, runtime identities and
    // record BOTH source languages of a mixed package."
    let bundle = bundle_over(base.clone(), NativeBundleProducer::TRust, &[Rust, Lean]);
    let tools: Vec<&str> = bundle
        .provenance
        .toolchain
        .iter()
        .map(|t| t.name.as_str())
        .collect();
    let json = serde_json::to_value(&bundle).expect("json");
    assert!(feature_check(
        "b1.bundle.g8_toolchain_language_identity",
        bundle.validate() == Ok(())
            && NativeVerificationBundle::SCHEMA_VERSION == 9
            && bundle.schema_version == NativeVerificationBundle::SCHEMA_VERSION
            && tools == ["rustc-trust", "clean-kernel", "ay", "trust-bignum"]
            && json["provenance"]["source_languages"] == serde_json::json!(["Rust", "Lean"])
            && json["provenance"]["source_language"] == serde_json::json!("Rust"),
        &format!(
            "schema {}: provenance.toolchain = {tools:?}, source_languages = {:?} (primary {:?}); validate => {:?}",
            bundle.schema_version,
            bundle.provenance.source_languages,
            bundle.provenance.source_language,
            bundle.validate()
        ),
    ));
    // twin: the Lean half dropped from the set => the Clean functions are
    // uncovered, by name, and nothing else is wrong with the bundle.
    let twin = bundle_over(base.clone(), NativeBundleProducer::TRust, &[Rust]);
    let errors = bundle_errors(&twin);
    assert!(feature_check(
        "b1.bundle.g8_toolchain_language_identity.twin_rust_only",
        errors
            == vec![NativeVerificationBundleError::BundleLanguageUncovered {
                producer: Some(Producer::Clean),
                functions: clean_fns.clone(),
                source_languages: [Rust].into_iter().collect(),
            }],
        &format!("{{Rust}} over the mixed module => {errors:?}"),
    ));

    // --- 28-root-verification-bundle-two-producers -------------------------
    // "the verification hand-off for a module containing Clean-produced
    // functions must be able to state its producer provenance honestly."
    let mut clean_only = base.clone();
    for f in &mut clean_only.functions {
        f.producer = Some(Producer::Clean);
    }
    let bundle = bundle_over(
        clean_only.clone(),
        NativeBundleProducer::Clean,
        &[LangClean, Lean],
    );
    let json = serde_json::to_string(&bundle).expect("json");
    let msgpack = rmp_serde::to_vec_named(&bundle).expect("msgpack");
    let back_json: NativeVerificationBundle = serde_json::from_str(&json).expect("json decode");
    let back_msgpack: NativeVerificationBundle =
        rmp_serde::from_slice(&msgpack).expect("msgpack decode");
    assert!(feature_check(
        "b1.bundle.root_verification_bundle_two_producers",
        bundle.producer == NativeBundleProducer::Clean
            && bundle.validate() == Ok(())
            && json.contains("\"producer\":\"Clean\"")
            && back_json == bundle
            && back_msgpack == bundle,
        &format!(
            "NativeBundleProducer::Clean (serde \"Clean\", TMVB tag 4) labels a Clean-only module; set {:?}; validate => {:?}; JSON/MessagePack lossless",
            bundle.provenance.source_languages,
            bundle.validate()
        ),
    ));
    // twin: the Clean-only module under a Rust-only claim.
    let twin = bundle_over(clean_only, NativeBundleProducer::Clean, &[Rust]);
    let errors = bundle_errors(&twin);
    let all_fns: Vec<FuncId> = twin.module.functions.iter().map(|f| f.id).collect();
    assert!(feature_check(
        "b1.bundle.root_verification_bundle_two_producers.twin_rust_claim",
        errors
            == vec![NativeVerificationBundleError::BundleLanguageUncovered {
                producer: Some(Producer::Clean),
                functions: all_fns,
                source_languages: [Rust].into_iter().collect(),
            }],
        &format!("Clean bundle claiming {{Rust}} => {errors:?}"),
    ));

    // --- 24-native-verification-bundle (language half) ---------------------
    // "typed TrustVc/TrustMc/TrustWp requests, module digest derived
    // internally, lineage": one bundle carrying all three request lanes over
    // the mixed module, its language set covering both producers, and the
    // set bound into the bundle digest.
    let bundle = bundle_over(base.clone(), NativeBundleProducer::TrustIr, &[Rust, Lean]);
    let suites: Vec<NativeVerifierSuite> =
        bundle.requests.iter().map(|r| r.verifier_suite()).collect();
    let other = bundle_over(
        base.clone(),
        NativeBundleProducer::TrustIr,
        &[Rust, LangClean],
    );
    assert!(feature_check(
        "b1.bundle.native_verification_bundle",
        bundle.validate() == Ok(())
            && suites
                == [
                    NativeVerifierSuite::TrustVc,
                    NativeVerifierSuite::TrustMc,
                    NativeVerifierSuite::TrustWp
                ]
            && bundle.trust_ir_module_digest == bundle.module.stable_digest()
            && bundle.stable_digest() != other.stable_digest(),
        &format!(
            "requests {suites:?} over the mixed module, module digest re-derived, {{Rust,Lean}} vs {{Rust,Clean}} => distinct bundle digests; validate => {:?}",
            bundle.validate()
        ),
    ));
    // twin: an unstamped function is covered only by an explicit Unknown.
    let mut unstamped = base.clone();
    unstamped.functions[0].producer = None;
    let twin = bundle_over(unstamped, NativeBundleProducer::TrustIr, &[Rust, Lean]);
    let errors = bundle_errors(&twin);
    assert!(feature_check(
        "b1.bundle.native_verification_bundle.twin_unstamped_is_not_covered",
        errors
            == vec![NativeVerificationBundleError::BundleLanguageUncovered {
                producer: None,
                functions: vec![FuncId::new(0)],
                source_languages: [Rust, Lean].into_iter().collect(),
            }],
        &format!("f0 producer: None under {{Rust,Lean}} => {errors:?}"),
    ));
}

#[test]
fn two_language_b1() {
    common::run_target(
        "b1",
        &[
            (
                "b1_01_mixed_producers_and_call_edges",
                b1_01_mixed_producers_and_call_edges,
            ),
            (
                "b1_02_symbol_and_display_path",
                b1_02_symbol_and_display_path,
            ),
            (
                "b1_03_body_gate_tri_state_and_codegen_license",
                b1_03_body_gate_tri_state_and_codegen_license,
            ),
            (
                "b1_04_gap_gated_authority_is_free_text",
                b1_04_gap_gated_authority_is_free_text,
            ),
            (
                "b1_05_trust_internal_disclosures",
                b1_05_trust_internal_disclosures,
            ),
            (
                "b1_05b_gap_disclosure_rows_unbound_to_module",
                b1_05b_gap_disclosure_rows_unbound_to_module,
            ),
            (
                "b1_06_linkage_visibility_target",
                b1_06_linkage_visibility_target,
            ),
            (
                "b1_07_roundtrip_and_wire_version",
                b1_07_roundtrip_and_wire_version,
            ),
            (
                "b1_08_interpreter_runs_through_both_languages",
                b1_08_interpreter_runs_through_both_languages,
            ),
            (
                "b1_09_diff_reports_producer_flip",
                b1_09_diff_reports_producer_flip,
            ),
            ("b1_10_diff_reports_body_gate", b1_10_diff_reports_body_gate),
            (
                "b1_11_diff_reports_other_v41_metadata",
                b1_11_diff_reports_other_v41_metadata,
            ),
            (
                "b1_12_gap_extern_weak_declaration_refused",
                b1_12_gap_extern_weak_declaration_refused,
            ),
            (
                "b1_13_bundle_states_two_languages",
                b1_13_bundle_states_two_languages,
            ),
        ],
    );
}
