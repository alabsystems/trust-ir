// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Claim c11 (F-052, with F-047 / F-048 / F-083): what the v43 `Nat` handle
//! cannot do.
//!
//! Source: `reports/2026-09-17-two-language-proof-program/verify/c11_nat_handle_limits/`.
//! These are CAPABILITY gaps, not wrong acceptances, and most are ratified by
//! design (`docs/SPEC_RATIFICATIONS.md` §7). So the ratchets here assert
//! today's REFUSAL exactly, and the increment that widens the surface flips
//! each one:
//!
//! * only the pinned entry points are declarable (F-052). FLIPPED by WS3.2,
//!   which widened the pinned `Nat` row to the Clean kernel's native `Nat`
//!   surface: six of row (1)'s nine operations are now pins, and the three
//!   that are not the kernel's spelling (`eq`, `lt`, `cmp`) stay foreign by
//!   design;
//! * a handle cannot enter an aggregate or memory (F-047). The AGGREGATE half
//!   is FLIPPED by WS3.6: a handle now sits in a struct, tuple or enum lane
//!   under exact lane typing (and, for an enum payload, under the tag switch
//!   that selects its variant), while every seed but a pinned origin stays
//!   refused. The MEMORY half is FLIPPED by WS3.7: a handle may be spilled to
//!   a sealed function-local stack slot, and to nothing else in memory;
//! * a `Nat`-typed function can be exported, and since WS3.3 (F-048) imported
//!   — but only through `validate_linked_module`, which authenticates the
//!   declaration's `backed_by`; every single-module lane still refuses it;
//! * the reference interpreter cannot execute a path that reaches a handle
//!   entry point (F-083; WS2.12 / WS2.13).
//!
//! The `bydesign_*` rows are what IS expressible today and must stay clean;
//! the `control_*` rows are forgeries that must stay refused after every flip.

use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate;
use trust_ir::inst::CastOp;
use trust_ir::interpret::Interpreter;
use trust_ir::proof::{
    ObligationKind, ProofFormula, ProofObligation, ProofStatus, RejectingModuleProofAuthority,
};
use trust_ir::ty::{EnumDef, EnumVariant, FieldDef, StructDef};
use trust_ir::value::{EnumId, ProofId, StructId};
use trust_ir::{
    BodyGate, CallingConv, Endianness, ExternRef, FunctionSummary, Global, Linkage, Module,
    ModuleImport, Producer, StructPassingPolicy, TargetInfo, Ty, ValueId, Visibility,
};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{
    FunctionBuilder, HandleEntryPoint, HandleRegistry, HandleRuntimeDecls, HandleRuntimePin,
    ModuleBuilder, ModuleSet, PinnedTy, TRUSTED_HANDLE_RUNTIMES, validate_linked_module,
    validate_module, validate_module_for_codegen, validate_module_with_handle_registry,
};

fn nat() -> Ty {
    Ty::handle("Nat", "trust_bignum::Nat")
}

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn gate() -> BodyGate {
    BodyGate::Gated {
        authority: "c11-repro".into(),
        evidence: None,
    }
}

/// The pinned declarations plus `nat_double(x: Nat) -> Nat { <extra>; add(x, x) }`.
fn nat_module(
    name: &str,
    pre: impl FnOnce(&mut ModuleBuilder),
    extra: impl FnOnce(&mut FunctionBuilder<'_>, ValueId, &HandleRuntimeDecls),
) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info(name, target());
    mb.set_default_producer(Producer::Clean);
    let decls = mb
        .declare_handle_runtime(&TRUSTED_HANDLE_RUNTIMES[0])
        .expect("pinned runtime declares");
    pre(&mut mb);
    let sig = mb.add_func_type(vec![nat()], vec![nat()]);
    let mut fb = mb.function("nat_double", sig);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, nat());
    fb.switch_to_block(entry);
    extra(&mut fb, x, &decls);
    let r = fb.call(decls.entry("add").unwrap(), vec![x, x]);
    fb.ret(vec![r]);
    fb.set_body_gate(gate());
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn baseline(name: &str) -> Module {
    nat_module(name, |_| {}, |_, _, _| {})
}

/// The `Nat` operations a Lean/Clean program needs beyond the pinned five.
fn extra_ops() -> Vec<(&'static str, Vec<Ty>, Vec<Ty>)> {
    let h = nat;
    vec![
        ("trust_bignum_nat_mul", vec![h(), h()], vec![h()]),
        ("trust_bignum_nat_div", vec![h(), h()], vec![h()]),
        ("trust_bignum_nat_mod", vec![h(), h()], vec![h()]),
        ("trust_bignum_nat_pow", vec![h(), h()], vec![h()]),
        ("trust_bignum_nat_to_u64", vec![h()], vec![Ty::U64]),
        ("trust_bignum_nat_eq", vec![h(), h()], vec![Ty::Bool]),
        ("trust_bignum_nat_lt", vec![h(), h()], vec![Ty::Bool]),
        ("trust_bignum_nat_cmp", vec![h(), h()], vec![Ty::I32]),
        ("trust_bignum_nat_clone", vec![h()], vec![h()]),
    ]
}

const H: PinnedTy = PinnedTy::Handle;

/// A test-only registry: the pinned row plus the nine extra operations.
const EXTENDED: HandleRuntimePin = HandleRuntimePin {
    name: "Nat",
    runtime: "trust_bignum::Nat",
    calling_conv: CallingConv::C,
    entry_points: &[
        HandleEntryPoint {
            role: "from_u64",
            symbol: "trust_bignum_nat_from_u64",
            def_path: "trust_bignum::Nat::from_u64",
            params: &[PinnedTy::Scalar(Ty::U64)],
            returns: &[H],
        },
        HandleEntryPoint {
            role: "add",
            symbol: "trust_bignum_nat_add",
            def_path: "trust_bignum::Nat::add",
            params: &[H, H],
            returns: &[H],
        },
        HandleEntryPoint {
            role: "sub",
            symbol: "trust_bignum_nat_sub",
            def_path: "trust_bignum::Nat::sub",
            params: &[H, H],
            returns: &[H],
        },
        HandleEntryPoint {
            role: "is_zero",
            symbol: "trust_bignum_nat_is_zero",
            def_path: "trust_bignum::Nat::is_zero",
            params: &[H],
            returns: &[PinnedTy::Scalar(Ty::Bool)],
        },
        HandleEntryPoint {
            role: "drop",
            symbol: "trust_bignum_nat_drop",
            def_path: "trust_bignum::Nat::drop",
            params: &[H],
            returns: &[],
        },
        HandleEntryPoint {
            role: "mul",
            symbol: "trust_bignum_nat_mul",
            def_path: "trust_bignum::Nat::mul",
            params: &[H, H],
            returns: &[H],
        },
        HandleEntryPoint {
            role: "div",
            symbol: "trust_bignum_nat_div",
            def_path: "trust_bignum::Nat::div",
            params: &[H, H],
            returns: &[H],
        },
        HandleEntryPoint {
            role: "mod",
            symbol: "trust_bignum_nat_mod",
            def_path: "trust_bignum::Nat::mod",
            params: &[H, H],
            returns: &[H],
        },
        HandleEntryPoint {
            role: "pow",
            symbol: "trust_bignum_nat_pow",
            def_path: "trust_bignum::Nat::pow",
            params: &[H, H],
            returns: &[H],
        },
        HandleEntryPoint {
            role: "to_u64",
            symbol: "trust_bignum_nat_to_u64",
            def_path: "trust_bignum::Nat::to_u64",
            params: &[H],
            returns: &[PinnedTy::Scalar(Ty::U64)],
        },
        HandleEntryPoint {
            role: "eq",
            symbol: "trust_bignum_nat_eq",
            def_path: "trust_bignum::Nat::eq",
            params: &[H, H],
            returns: &[PinnedTy::Scalar(Ty::Bool)],
        },
        HandleEntryPoint {
            role: "lt",
            symbol: "trust_bignum_nat_lt",
            def_path: "trust_bignum::Nat::lt",
            params: &[H, H],
            returns: &[PinnedTy::Scalar(Ty::Bool)],
        },
        HandleEntryPoint {
            role: "cmp",
            symbol: "trust_bignum_nat_cmp",
            def_path: "trust_bignum::Nat::cmp",
            params: &[H, H],
            returns: &[PinnedTy::Scalar(Ty::I32)],
        },
        HandleEntryPoint {
            role: "clone",
            symbol: "trust_bignum_nat_clone",
            def_path: "trust_bignum::Nat::clone",
            params: &[H],
            returns: &[H],
        },
    ],
};

fn holder(mb: &mut ModuleBuilder) {
    mb.add_struct(StructDef {
        id: StructId::new(0),
        name: "Holder".into(),
        fields: vec![FieldDef {
            name: "n".into(),
            ty: nat(),
            offset: None,
        }],
        size: None,
        align: None,
        repr: trust_ir::StructRepr::C,
        origin: None,
    });
}

fn invalid_handle_uses(errors: &[ValidationError]) -> usize {
    errors
        .iter()
        .filter(|e| matches!(e, ValidationError::InvalidHandleUse { .. }))
        .count()
}

/// The v1 roles (what the archived c11 fixture declared), so a hand-written
/// declaration of a newer row entry is the ONE declaration of its symbol.
const V1_ROLES: [&str; 5] = ["from_u64", "add", "sub", "is_zero", "drop"];

/// `nat_module`, but declaring only [`V1_ROLES`] of the pinned row and then
/// one more bodyless C declaration `symbol: params -> returns`, written by hand
/// in the runtime's own symbol scheme (the archived row-(1) repro, verbatim).
fn with_hand_declared(symbol: &str, params: Vec<Ty>, returns: Vec<Ty>) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("c11_1", target());
    mb.set_default_producer(Producer::Clean);
    let decls = mb
        .declare_handle_runtime_roles(&TRUSTED_HANDLE_RUNTIMES[0], &V1_ROLES)
        .expect("the v1 roles declare");
    let sig = mb.add_func_type(params, returns);
    mb.declare_function(symbol, sig);
    let sig = mb.add_func_type(vec![nat()], vec![nat()]);
    let mut fb = mb.function("nat_double", sig);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, nat());
    fb.switch_to_block(entry);
    let r = fb.call(decls.entry("add").unwrap(), vec![x, x]);
    fb.ret(vec![r]);
    fb.set_body_gate(gate());
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The archived row-(1) operations that are NOT the Clean kernel's spelling:
/// the kernel compares with `beq` / `ble`, and has no three-way `cmp`.
const OFF_KERNEL: [&str; 3] = [
    "trust_bignum_nat_eq",
    "trust_bignum_nat_lt",
    "trust_bignum_nat_cmp",
];

/// Row `verify.c11` (1), FLIPPED by WS3.2 (F-052): six of the nine archived
/// `Nat` operations — `mul`, `div`, `mod`, `pow`, `to_u64`, `clone` — are now
/// rows of the pinned `Nat` table with exactly the runtime shape the archived
/// repro declared, so the SAME hand-written declaration validates on the plain
/// and codegen lanes (it was exactly one `HandleForeignDeclaration`), and each
/// is callable through `declare_handle_runtime`. Negative twin: the same
/// declaration with a `u64` where the table pins a handle is exactly one
/// `HandleEntryPointSignatureMismatch` naming the symbol — the pin is a
/// signature, not a name wildcard.
#[test]
fn c11_flipped_kernel_surface_nat_operations_are_pinned() {
    let row = &TRUSTED_HANDLE_RUNTIMES[0];
    let mut flipped = 0;
    for (symbol, params, returns) in extra_ops() {
        if OFF_KERNEL.contains(&symbol) {
            continue;
        }
        flipped += 1;
        let entry = row
            .entry_points
            .iter()
            .find(|e| e.symbol == symbol)
            .unwrap_or_else(|| panic!("{symbol} is a row of the pinned Nat table"));
        let pinned = row.func_ty(entry);
        assert_eq!(
            (&pinned.params, &pinned.returns),
            (&params, &returns),
            "{symbol}: the pin is the archived runtime shape"
        );
        let m = with_hand_declared(symbol, params.clone(), returns.clone());
        assert_eq!(validate_module(&m), Vec::new(), "{symbol}");
        assert_eq!(validate_module_for_codegen(&m), Vec::new(), "{symbol}");

        // Callable: a function that calls the pinned entry validates.
        let called = nat_module(
            "c11_1_call",
            |_| {},
            |fb, x, decls| {
                let args = if params.len() == 2 {
                    vec![x, x]
                } else {
                    vec![x]
                };
                let _ = fb.call(decls.entry(entry.role).unwrap(), args);
            },
        );
        assert_eq!(validate_module(&called), Vec::new(), "{symbol} called");

        // Negative twin: a scalar where the pin says handle.
        let mut forged_params = params.clone();
        forged_params[0] = Ty::U64;
        let forged = with_hand_declared(symbol, forged_params, returns);
        let errors = validate_module(&forged);
        assert!(
            matches!(errors.as_slice(),
                [ValidationError::HandleEntryPointSignatureMismatch { symbol: s, .. }] if s == symbol),
            "{symbol} forged: {errors:?}"
        );
    }
    assert_eq!(flipped, 6, "mul, div, mod, pow, to_u64, clone");
}

/// Row `verify.c11` (1), the residue WS3.2 leaves BY DESIGN: `eq`, `lt` and
/// `cmp` are not the kernel's spelling (the pinned comparisons are `beq` /
/// `ble`, and there is no three-way compare), so each, declared with the
/// runtime's own shape, is still exactly one `HandleForeignDeclaration` under
/// the pinned table on both lanes — and is admitted by a registry that pins
/// it, so widening the surface stays table content, not a wire change.
#[test]
fn c11_bydesign_off_kernel_nat_operations_stay_foreign_declarations() {
    let extended = HandleRegistry::from_pins(&[EXTENDED]).expect("extended pin is well-formed");
    let row = &TRUSTED_HANDLE_RUNTIMES[0];
    for role in ["beq", "ble"] {
        assert!(
            row.entry_points.iter().any(|e| e.role == role),
            "the kernel's {role} is pinned"
        );
    }
    let mut refused = 0;
    for (symbol, params, returns) in extra_ops() {
        if !OFF_KERNEL.contains(&symbol) {
            continue;
        }
        refused += 1;
        assert!(
            row.entry_points.iter().all(|e| e.symbol != symbol),
            "{symbol}"
        );
        let m = with_hand_declared(symbol, params, returns);
        for (lane, errors) in [
            ("validate_module", validate_module(&m)),
            ("for_codegen", validate_module_for_codegen(&m)),
        ] {
            assert!(
                matches!(errors.as_slice(),
                    [ValidationError::HandleForeignDeclaration { name, .. }] if name == symbol),
                "{symbol} in {lane}: {errors:?}"
            );
        }
        assert_eq!(
            validate_module_with_handle_registry(&m, &extended),
            Vec::new(),
            "{symbol}"
        );
    }
    assert_eq!(refused, 3, "eq, lt, cmp");
}

/// Row `verify.c11` (2): a handle cannot be SEEDED into an aggregate from
/// nothing, stored to memory that is not a sealed slot, or held in a global
/// (F-047). Each is an `InvalidHandleUse`. WS3.6 ratified the lane itself,
/// not its seed: the insert below is admitted as an operation and refused
/// because its BASE is an `Undef` of a handle-bearing type, which is exactly
/// the origin rule the widening preserves (the `MakeAggregate` twin is
/// `handle_types.rs::a_handle_struct_lane_round_trips_at_its_exact_type`).
/// WS3.7 FLIPPED the memory half the same way: the measured spill
/// (`alloca; store; load`) is a SEALED slot and now validates, while the
/// same spill whose slot pointer escapes into a call stays refused (the full
/// rule and its twins: `ws3_7_sealed_handle_slots.rs`). The global stays
/// refused — ratified, not a gap.
#[test]
fn c11_gap_nat_in_an_aggregate_or_memory_is_refused() {
    let hs = Ty::Struct(StructId::new(0));
    let inserted = nat_module("c11_2_insert", holder, move |fb, x, _| {
        let u = fb.undef(hs.clone());
        let _ = fb.insert_field(hs, u, 0, x);
    });
    assert!(invalid_handle_uses(&validate_module(&inserted)) >= 1);

    // WS3.7: the measured spill is a sealed slot and validates...
    let stored = nat_module(
        "c11_2_store",
        |_| {},
        |fb, x, _| {
            let p = fb.alloca(nat());
            fb.store(nat(), p, x);
            let _ = fb.load(nat(), p);
        },
    );
    assert_eq!(validate_module(&stored), vec![]);
    // ...and the same spill with its slot pointer escaping into a
    // `PtrToInt` cast (the leak that would read the handle's word as an
    // integer) is refused.
    let escaped = nat_module(
        "c11_2_store_escaped",
        |_| {},
        |fb, x, _| {
            let p = fb.alloca(nat());
            fb.store(nat(), p, x);
            let _ = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, p);
            let _ = fb.load(nat(), p);
        },
    );
    assert!(invalid_handle_uses(&validate_module(&escaped)) >= 1);

    let mut global = baseline("c11_2_global");
    global.globals.push(Global {
        name: "g_nat".into(),
        ty: nat(),
        mutable: false,
        initializer: None,
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    assert!(invalid_handle_uses(&validate_module(&global)) >= 1);
}

fn clause() -> ProofFormula {
    ProofFormula::smtlib2("(= 1 1)", "Bool")
}

fn contract() -> FunctionSummary {
    FunctionSummary::new()
        .with_params(vec!["x".to_string()])
        .ensuring(clause())
}

/// Dependency: defines and exports `nat_double(x: T) -> T` with a
/// kernel-certified `proved` contract; `T` is `Nat` or `u64`.
fn dependency(nat_typed: bool) -> Module {
    let mut m = if nat_typed {
        baseline("dep")
    } else {
        let mut mb = ModuleBuilder::new_with_target_info("dep", target());
        mb.set_default_producer(Producer::Clean);
        let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function("nat_double", sig);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let r = fb.add(Ty::U64, x, x);
        fb.ret(vec![r]);
        fb.set_body_gate(gate());
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let f = m.function_by_name("nat_double").unwrap().id;
    let idx = m.functions.iter().position(|g| g.id == f).unwrap();
    assert_eq!(m.functions[idx].linkage, Linkage::External, "exported");
    m.functions[idx].summary = Some(contract().proved());
    let obligation = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "ensures (= 1 1)",
    )
    .with_function(f)
    .with_formula(clause());
    let certificate = contract_clean_cic_certificate(&obligation, "contract-prover")
        .expect("kernel proves (= 1 1)");
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(certificate);
    m
}

/// Importer: an authenticated import row, a bodyless declaration of the far
/// `nat_double` backed by the far obligation, and `quad(x) = f(f(x))`.
fn importer(dep: &Module, nat_typed: bool) -> Module {
    let t = if nat_typed { nat() } else { Ty::U64 };
    let mut mb = ModuleBuilder::new_with_target_info("root", target());
    mb.set_default_producer(Producer::Clean);
    if nat_typed {
        mb.declare_handle_runtime(&TRUSTED_HANDLE_RUNTIMES[0])
            .unwrap();
    }
    let sig = mb.add_func_type(vec![t.clone()], vec![t.clone()]);
    let far = mb.declare_function("nat_double", sig);
    let mut fb = mb.function("quad", sig);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, t);
    fb.switch_to_block(entry);
    let a = fb.call(far, vec![x]);
    let b = fb.call(far, vec![a]);
    fb.ret(vec![b]);
    fb.set_body_gate(gate());
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let import = m
        .intern_import(
            ModuleImport::new(dep.name.clone(), dep.stable_digest()).with_producer(Producer::Clean),
        )
        .expect("Module::intern_import: test fixture");
    let idx = m.functions.iter().position(|g| g.id == far).unwrap();
    m.functions[idx].summary = Some(
        contract()
            .proved()
            .backed_by(ExternRef::new(import, "nat_double").relying_on(ProofId::new(0))),
    );
    m
}

/// Row `verify.c11` (3), FLIPPED by WS3.3 (F-048): the `Nat`-typed dependency
/// validates, and the importer whose declaration of its function carries a
/// `backed_by` (here a proof-bearing one) now links — the linked walk
/// authenticates the binding (rule L11) and validates the root. The single-
/// module lane still refuses the same importer (`HandleForeignDeclaration` on
/// the user symbol): only the walk that holds the dependency can admit it.
#[test]
fn c11_nat_function_is_importable_only_through_the_linked_walk() {
    let dep = dependency(true);
    assert_eq!(validate_module(&dep), Vec::new());
    let root = importer(&dep, true);
    let errors = validate_module(&root);
    assert!(
        errors.iter().any(|e| matches!(e,
            ValidationError::HandleForeignDeclaration { name, detail, .. }
                if name == "nat_double" && detail.contains("validate_linked_module"))),
        "{errors:?}"
    );
    let report = validate_linked_module(
        &root,
        &ModuleSet::new([&dep]),
        &RejectingModuleProofAuthority,
    );
    assert!(report.validated_root().is_some(), "{:?}", report.errors());
}

/// Row `verify.c11` (4), in process: a handle-free function of a handle-bearing
/// module runs, but a path that reaches a pinned entry point cannot execute
/// (the entry points are bodyless and the interpreter has no host model).
#[test]
fn c11_gap_interpreter_cannot_run_a_handle_path() {
    let m = runnable_handle_program();
    assert_eq!(validate_module(&m), Vec::new());
    let run = |name: &str| {
        let id = m.function_by_name(name).unwrap().id;
        Interpreter::with_module(&m).execute_func(id, Vec::new())
    };
    let seven = run("seven").expect("the handle-free sibling runs");
    assert_eq!(seven.returns[0].as_int().unwrap().as_unsigned(), 7);
    assert!(run("program").is_err());
}

/// `program() -> bool { is_zero(from_u64(0)) }` and a handle-free `seven()`.
fn runnable_handle_program() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("c11_4", target());
    mb.set_default_producer(Producer::Clean);
    let decls = mb
        .declare_handle_runtime(&TRUSTED_HANDLE_RUNTIMES[0])
        .unwrap();
    let sig = mb.add_func_type(vec![], vec![Ty::Bool]);
    let mut fb = mb.function("program", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let z = fb.iconst(Ty::U64, 0);
    let h = fb.call(decls.entry("from_u64").unwrap(), vec![z]);
    let b = fb.call(decls.entry("is_zero").unwrap(), vec![h]);
    fb.ret(vec![b]);
    fb.set_body_gate(gate());
    fb.build();
    let sig7 = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("seven", sig7);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let s = fb.iconst(Ty::U64, 7);
    fb.ret(vec![s]);
    fb.set_body_gate(gate());
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Positive fixtures: the baseline, a `u64` import of the same shape (it
/// authenticates), aggregate DEFINITIONS with a `Nat` lane, and pure transport
/// of a struct / tuple carrying one.
#[test]
fn c11_bydesign_what_the_handle_surface_expresses_today() {
    let base = baseline("c11_base");
    assert_eq!(validate_module(&base), Vec::new());
    assert_eq!(validate_module_for_codegen(&base), Vec::new());

    let dep64 = dependency(false);
    let root64 = importer(&dep64, false);
    let report = validate_linked_module(
        &root64,
        &ModuleSet::new([&dep64]),
        &RejectingModuleProofAuthority,
    );
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.authenticated_imports().map(|m| m.len()), Some(1));

    let def_only = nat_module("c11_def", holder, |_, _, _| {});
    assert_eq!(validate_module(&def_only), Vec::new());
    let mut enum_only = baseline("c11_enum");
    enum_only.add_enum(EnumDef::new(
        EnumId::new(0),
        "Tree",
        vec![
            EnumVariant {
                name: "leaf".into(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "node".into(),
                fields: vec![nat()],
                field_names: vec![],
            },
        ],
    ));
    assert_eq!(validate_module(&enum_only), Vec::new());

    for (tag, ty, needs_struct) in [
        ("struct", Ty::Struct(StructId::new(0)), true),
        ("tuple", Ty::Tuple(vec![nat(), Ty::U64]), false),
    ] {
        let mut mb = ModuleBuilder::new_with_target_info("c11_transport", target());
        mb.set_default_producer(Producer::Clean);
        mb.declare_handle_runtime(&TRUSTED_HANDLE_RUNTIMES[0])
            .unwrap();
        if needs_struct {
            holder(&mut mb);
        }
        let sig = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
        let mut fb = mb.function("pass_through", sig);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, ty.clone());
        fb.switch_to_block(entry);
        let c = fb.copy(ty, a);
        fb.ret(vec![c]);
        fb.set_body_gate(gate());
        fb.build();
        assert_eq!(
            validate_module(&mb.build().expect("ModuleBuilder::build: test fixture")),
            Vec::new(),
            "{tag}"
        );
    }
}

/// Mutation controls that must survive every flip: casting the handle to a
/// pointer, comparing handles and projecting a handle out of a struct are
/// forgeries (`InvalidHandleUse`), and the user symbol stays foreign even
/// under a registry that pins every `Nat` operation.
#[test]
fn c11_control_handle_forgeries_stay_refused() {
    let cast = nat_module(
        "c11_cast",
        |_| {},
        |fb, x, _| {
            let _ = fb.cast(CastOp::Bitcast, nat(), Ty::Ptr, x);
        },
    );
    assert!(invalid_handle_uses(&validate_module(&cast)) >= 1);

    let cmp = nat_module(
        "c11_icmp",
        |_| {},
        |fb, x, _| {
            let _ = fb.icmp(trust_ir::inst::ICmpOp::Eq, nat(), x, x);
        },
    );
    assert!(invalid_handle_uses(&validate_module(&cmp)) >= 1);

    // `unwrap(h: Holder) -> X { extract_field X h, 0 }`. WS3.6 (F-047,
    // aggregate half) RATIFIED this projection at the lane's EXACT type, so
    // the row flips: `X = Nat` validates, and the twin — the same lane read
    // as a `U64`, which is the `PtrToInt` leak by another spelling — stays
    // an `InvalidHandleUse`.
    let project = |read_as: Ty| -> Module {
        let mut mb = ModuleBuilder::new_with_target_info("c11_project", target());
        mb.set_default_producer(Producer::Clean);
        mb.declare_handle_runtime(&TRUSTED_HANDLE_RUNTIMES[0])
            .unwrap();
        holder(&mut mb);
        let hs = Ty::Struct(StructId::new(0));
        let sig = mb.add_func_type(vec![hs.clone()], vec![read_as.clone()]);
        let mut fb = mb.function("unwrap", sig);
        let entry = fb.create_block();
        let h = fb.add_block_param(entry, hs);
        fb.switch_to_block(entry);
        let n = fb.extract_field(read_as, h, 0);
        fb.ret(vec![n]);
        fb.set_body_gate(gate());
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let exact = validate_module(&project(nat()));
    assert!(
        exact.is_empty(),
        "the exact-typed lane read is ratified: {exact:?}"
    );
    assert!(invalid_handle_uses(&validate_module(&project(Ty::U64))) >= 1);

    let copy = nat_module(
        "c11_copy",
        |_| {},
        |fb, x, _| {
            let _ = fb.copy(nat(), x);
        },
    );
    assert_eq!(validate_module(&copy), Vec::new(), "copy is transport");

    let dep = dependency(true);
    let root = importer(&dep, true);
    let ext = validate_module_with_handle_registry(
        &root,
        &HandleRegistry::from_pins(&[EXTENDED]).unwrap(),
    );
    assert!(
        ext.iter().any(|e| matches!(e,
            ValidationError::HandleForeignDeclaration { name, .. } if name == "nat_double")),
        "{ext:?}"
    );
}
