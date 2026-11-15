// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS3.2 (F-052): the pinned `trust_bignum::Nat` row is the Clean kernel's
// native `Nat` surface.
//
// The v1 row pinned `from_u64` / `add` / `sub` / `is_zero` (+ `drop`), so a
// Lean `Nat` program using `*`, `/`, `%`, `decEq`, `<`, `toUInt64` or a copy
// of a handle had no carrier: every other bodyless declaration reaching a
// handle is `HandleForeignDeclaration`. The row now carries exactly the
// closed-`Nat` binary operations the Clean kernel reduces natively (its
// `NAT_BINOPS` allowlist: add, sub, mul, div, mod, pow, land, lor, xor,
// shiftLeft, shiftRight, beq, ble), the two-pin projection (`fits_u64` total,
// `to_u64` checked — never a wrapping projection) and `clone`.
//
// What this file pins, and why each is a separate statement:
//
// * POSITIVE — per role, the proof program's `b5_10` shape (a validating
//   handle module plus ONE bodyless C declaration of the role, spelled out
//   here literally rather than read back from the pin) validates `[]`, on the
//   plain and the codegen lane.
// * NEGATIVE TWIN — the same symbol at a wrong signature, or naming another
//   Rust item as its definition path, is exactly one
//   `HandleEntryPointSignatureMismatch`; an off-table role (`cmp`, the
//   wrapping projection `to_u64_wrapping`, the pre-ratification spellings
//   `eq` / `lt`, the unpinned `gcd`) is exactly one `HandleForeignDeclaration`.
// * MUTATION CONTROL — the ROW is what admits each role: the pinned row minus
//   that one entry refuses the same module as a foreign declaration. And
//   `from_pins` still refuses a second release-shaped entry.
// * The GAP rows of the 2026-09-17 proof program (`b5.gap.*`) that this
//   increment flips, ported under their row names.
//
// The SEMANTIC half — that each shim equals the kernel reducer (a `div` that
// panics on 0, a wrapping `sub`, an `xor` spelled `|`, a truncating `to_u64`)
// — cannot be observed here: trust-ir has no runtime for a handle. It is the
// `trust-bignum` Lean-vs-kernel differential in the Trust repo, and TRUST.md
// item 9(b) names it.

use trust_ir::Endianness;
use trust_ir::inst::{CastOp, ICmpOp};
use trust_ir::{
    BlockId, BodyGate, CallingConv, FuncId, FuncTy, Function, Linkage, Module, StructPassingPolicy,
    TargetInfo, Ty,
};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{
    HandleEntryPoint, HandlePinError, HandleRegistry, HandleRuntimePin, ModuleBuilder, PinnedTy,
    TRUSTED_HANDLE_RUNTIMES, validate_module, validate_module_for_codegen,
    validate_module_with_handle_registry,
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

fn nat_pin() -> &'static HandleRuntimePin {
    TRUSTED_HANDLE_RUNTIMES
        .iter()
        .find(|pin| pin.runtime == "trust_bignum::Nat")
        .expect("the pinned table carries trust_bignum::Nat")
}

fn gate() -> BodyGate {
    BodyGate::Gated {
        authority: "ws3-2-test".into(),
        evidence: None,
    }
}

/// A slot of a literal signature: the Nat handle or a closed scalar.
#[derive(Clone, Copy)]
enum S {
    H,
    Bool,
    U64,
}

impl S {
    fn ty(self) -> Ty {
        match self {
            S::H => nat(),
            S::Bool => Ty::Bool,
            S::U64 => Ty::U64,
        }
    }
}

/// One ratified role, spelled LITERALLY from the roadmap's WS3.2 table and
/// the kernel reducer — deliberately not read back from the pin, so a drift in
/// the pin is a test failure rather than a tautology.
struct Role {
    role: &'static str,
    /// The Rust item the shim wraps (`mod` wraps `Nat::rem`).
    method: &'static str,
    params: &'static [S],
    returns: &'static [S],
}

impl Role {
    fn symbol(&self) -> String {
        format!("trust_bignum_nat_{}", self.role)
    }

    fn def_path(&self) -> String {
        format!("trust_bignum::Nat::{}", self.method)
    }

    fn params(&self) -> Vec<Ty> {
        self.params.iter().map(|s| s.ty()).collect()
    }

    fn returns(&self) -> Vec<Ty> {
        self.returns.iter().map(|s| s.ty()).collect()
    }
}

const BIN: &[S] = &[S::H, S::H];
const UN: &[S] = &[S::H];

/// The WS3.2 rows (plus `drop`, whose "not pinned" GAP row this increment
/// also flips), in pin-table order.
const KERNEL_SURFACE: &[Role] = &[
    Role {
        role: "drop",
        method: "drop",
        params: UN,
        returns: &[],
    },
    Role {
        role: "mul",
        method: "mul",
        params: BIN,
        returns: &[S::H],
    },
    Role {
        role: "div",
        method: "div",
        params: BIN,
        returns: &[S::H],
    },
    Role {
        role: "mod",
        method: "rem",
        params: BIN,
        returns: &[S::H],
    },
    Role {
        role: "beq",
        method: "beq",
        params: BIN,
        returns: &[S::Bool],
    },
    Role {
        role: "ble",
        method: "ble",
        params: BIN,
        returns: &[S::Bool],
    },
    Role {
        role: "fits_u64",
        method: "fits_u64",
        params: UN,
        returns: &[S::Bool],
    },
    Role {
        role: "to_u64",
        method: "to_u64",
        params: UN,
        returns: &[S::U64],
    },
    Role {
        role: "clone",
        method: "clone",
        params: UN,
        returns: &[S::H],
    },
    Role {
        role: "land",
        method: "land",
        params: BIN,
        returns: &[S::H],
    },
    Role {
        role: "lor",
        method: "lor",
        params: BIN,
        returns: &[S::H],
    },
    Role {
        role: "xor",
        method: "xor",
        params: BIN,
        returns: &[S::H],
    },
    Role {
        role: "shift_left",
        method: "shift_left",
        params: BIN,
        returns: &[S::H],
    },
    Role {
        role: "shift_right",
        method: "shift_right",
        params: BIN,
        returns: &[S::H],
    },
    Role {
        role: "pow",
        method: "pow",
        params: BIN,
        returns: &[S::H],
    },
];

fn role(name: &str) -> &'static Role {
    KERNEL_SURFACE
        .iter()
        .find(|r| r.role == name)
        .unwrap_or_else(|| panic!("no ratified role `{name}`"))
}

fn next_func_id(module: &Module) -> FuncId {
    FuncId::new(
        module
            .functions
            .iter()
            .map(|f| f.id.index() + 1)
            .max()
            .unwrap_or(0),
    )
}

/// Append a bodyless C `External` declaration to a built module — what a
/// producer that does not use `declare_handle_runtime` emits by hand.
fn push_c_declaration(
    module: &mut Module,
    symbol: &str,
    display_path: Option<&str>,
    params: Vec<Ty>,
    returns: Vec<Ty>,
) -> FuncId {
    let sig = module
        .add_func_type(FuncTy {
            params,
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = next_func_id(module);
    let mut decl = Function::new(id, symbol, sig, BlockId::new(0));
    decl.calling_conv = CallingConv::C;
    decl.linkage = Linkage::External;
    decl.display_path = display_path.map(str::to_owned);
    assert!(decl.is_declaration());
    module
        .try_add_function(decl)
        .expect("Module::try_add_function: test fixture");
    id
}

/// The validating base of the `b5_10` shape: `is_zero_of(k) =
/// is_zero(from_u64(k))` over the two pinned roles it calls, licensed.
fn nat_base() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("ws3_2_nat", target());
    let decls = mb
        .declare_handle_runtime_roles(nat_pin(), &["from_u64", "is_zero"])
        .expect("pinned roles");
    let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::Bool]);
    let mut fb = mb.function("is_zero_of", sig);
    fb.set_body_gate(gate());
    let bb0 = fb.create_block();
    let k = fb.add_block_param(bb0, Ty::U64);
    fb.switch_to_block(bb0);
    let n = fb.call(decls.entry("from_u64").unwrap(), vec![k]);
    let z = fb.call(decls.entry("is_zero").unwrap(), vec![n]);
    fb.ret(vec![z]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `nat_base()` plus ONE bodyless declaration of `symbol`.
fn with_declaration(
    symbol: &str,
    display_path: Option<&str>,
    params: Vec<Ty>,
    returns: Vec<Ty>,
) -> Module {
    let mut m = nat_base();
    push_c_declaration(&mut m, symbol, display_path, params, returns);
    m
}

fn declaring(r: &Role) -> Module {
    with_declaration(&r.symbol(), Some(&r.def_path()), r.params(), r.returns())
}

fn only_signature_mismatch(errors: &[ValidationError], symbol: &str) -> bool {
    matches!(
        errors,
        [ValidationError::HandleEntryPointSignatureMismatch { symbol: s, .. }] if s == symbol
    )
}

fn only_foreign(errors: &[ValidationError], symbol: &str) -> bool {
    matches!(
        errors,
        [ValidationError::HandleForeignDeclaration { name, handle, .. }]
            if name == symbol && handle.contains("trust_bignum::Nat")
    )
}

fn invalid_handle_use_naming(errors: &[ValidationError], inst: &str) -> bool {
    let needle =
        format!("`{inst}` cannot produce, consume or reinterpret an opaque runtime handle");
    errors.iter().any(|e| {
        matches!(e, ValidationError::InvalidHandleUse { detail, .. } if detail.contains(&needle))
    })
}

// ───────────────────────────── POSITIVE ─────────────────────────────

/// The pin carries each literal row exactly: symbol, def-path, C convention,
/// signature. A drift in either direction fails here.
#[test]
fn the_pin_row_is_exactly_the_literal_kernel_surface() {
    let pin = nat_pin();
    assert_eq!(pin.calling_conv, CallingConv::C);
    for r in KERNEL_SURFACE {
        let entry = pin
            .entry_points
            .iter()
            .find(|e| e.role == r.role)
            .unwrap_or_else(|| panic!("`{}` is pinned", r.role));
        assert_eq!(entry.symbol, r.symbol(), "{}", r.role);
        assert_eq!(entry.def_path, r.def_path(), "{}", r.role);
        assert_eq!(
            pin.func_ty(entry),
            FuncTy {
                params: r.params(),
                returns: r.returns(),
                abi: None,
                is_vararg: false,
            },
            "{}",
            r.role
        );
    }
    // Five v1 roles plus the fourteen of WS3.2; `drop` is in both lists.
    assert_eq!(pin.entry_points.len(), 5 + KERNEL_SURFACE.len() - 1);
}

#[test]
fn every_kernel_surface_role_is_declarable_in_the_b5_10_shape() {
    assert_eq!(validate_module(&nat_base()), vec![], "baseline");
    for r in KERNEL_SURFACE {
        let m = declaring(r);
        assert_eq!(validate_module(&m), vec![], "{}", r.role);
        assert_eq!(validate_module_for_codegen(&m), vec![], "{}", r.role);
        // `display_path` may also be left unrecorded.
        let m = with_declaration(&r.symbol(), None, r.params(), r.returns());
        assert_eq!(validate_module(&m), vec![], "{} (no display path)", r.role);
    }
}

/// Every role is also CALLABLE: one licensed body per role, fed by
/// `from_u64` handles and consuming the role's result, validates on both
/// lanes. Admission keys on the declaration being pinned, whichever way the
/// handle flows.
#[test]
fn every_kernel_surface_role_is_callable_as_exact_typed_transport() {
    let mut mb = ModuleBuilder::new_with_target_info("ws3_2_calls", target());
    let decls = mb.declare_handle_runtime(nat_pin()).expect("the whole row");
    for r in KERNEL_SURFACE {
        let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], r.returns());
        let mut fb = mb.function(format!("use_{}", r.role), sig);
        fb.set_body_gate(gate());
        let bb0 = fb.create_block();
        let a = fb.add_block_param(bb0, Ty::U64);
        let b = fb.add_block_param(bb0, Ty::U64);
        fb.switch_to_block(bb0);
        let from_u64 = decls.entry("from_u64").unwrap();
        let x = fb.call(from_u64, vec![a]);
        let y = fb.call(from_u64, vec![b]);
        let args = if r.params.len() == 2 {
            vec![x, y]
        } else {
            vec![x]
        };
        let callee = decls.entry(r.role).unwrap();
        if r.returns.is_empty() {
            fb.call_void(callee, args);
            fb.ret(vec![]);
        } else {
            let out = fb.call(callee, args);
            fb.ret(vec![out]);
        }
        fb.build();
    }
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(validate_module_for_codegen(&m), vec![]);
}

/// Lean's `n.toUInt64` has exactly ONE spelling, and it validates:
/// `to_u64(land(n, from_u64(u64::MAX)))` — never aborts, needs no wrapping
/// pin. And a Rust `Nat::to_u64() -> Option<u64>` lowers to `fits_u64` +
/// `CondBr` + `to_u64`.
#[test]
fn the_lean_to_uint64_projection_and_the_checked_projection_validate() {
    let mut mb = ModuleBuilder::new_with_target_info("ws3_2_projection", target());
    let decls = mb
        .declare_handle_runtime_roles(nat_pin(), &["from_u64", "land", "fits_u64", "to_u64"])
        .expect("pinned roles");
    let project = mb.add_func_type(vec![nat()], vec![Ty::U64]);
    {
        let mut fb = mb.function("to_uint64", project);
        fb.set_body_gate(gate());
        let bb0 = fb.create_block();
        let n = fb.add_block_param(bb0, nat());
        fb.switch_to_block(bb0);
        let max = fb.uconst(Ty::U64, u128::from(u64::MAX));
        let mask = fb.call(decls.entry("from_u64").unwrap(), vec![max]);
        let low = fb.call(decls.entry("land").unwrap(), vec![n, mask]);
        let out = fb.call(decls.entry("to_u64").unwrap(), vec![low]);
        fb.ret(vec![out]);
        fb.build();
    }
    {
        // `n.to_u64().unwrap_or(0)`.
        let mut fb = mb.function("to_u64_or_zero", project);
        fb.set_body_gate(gate());
        let bb0 = fb.create_block();
        let fits = fb.create_block();
        let too_big = fb.create_block();
        let join = fb.create_block();
        let n = fb.add_block_param(bb0, nat());
        let out = fb.add_block_param(join, Ty::U64);
        fb.switch_to_block(bb0);
        let ok = fb.call(decls.entry("fits_u64").unwrap(), vec![n]);
        fb.condbr(ok, fits, vec![], too_big, vec![]);
        fb.switch_to_block(fits);
        let v = fb.call(decls.entry("to_u64").unwrap(), vec![n]);
        fb.br(join, vec![v]);
        fb.switch_to_block(too_big);
        let zero = fb.uconst(Ty::U64, 0);
        fb.br(join, vec![zero]);
        fb.switch_to_block(join);
        fb.ret(vec![out]);
        fb.build();
    }
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(validate_module_for_codegen(&m), vec![]);
}

// ─────────────────────────── NEGATIVE TWINS ───────────────────────────

/// The roadmap's named twin: `beq` spelled `(H, H) -> U8` is the signature
/// forgery, not an admitted declaration.
#[test]
fn beq_at_a_byte_result_is_a_signature_mismatch() {
    let m = with_declaration(
        "trust_bignum_nat_beq",
        Some("trust_bignum::Nat::beq"),
        vec![nat(), nat()],
        vec![Ty::U8],
    );
    let errors = validate_module(&m);
    assert!(
        only_signature_mismatch(&errors, "trust_bignum_nat_beq"),
        "{errors:?}"
    );
}

/// Per role: the literal row with its RESULT re-typed (a handle result to
/// `Ptr`, `Bool` to `U8`, `U64` to `I64`, the release's empty list to a
/// one-element `Unit`), and separately its first parameter re-typed to
/// `Ptr` — each exactly one `HandleEntryPointSignatureMismatch`.
#[test]
fn every_kernel_surface_role_at_a_wrong_signature_is_a_signature_mismatch() {
    for r in KERNEL_SURFACE {
        let wrong_returns = match r.returns {
            [] => vec![Ty::Unit],
            [S::H] => vec![Ty::Ptr],
            [S::Bool] => vec![Ty::U8],
            [S::U64] => vec![Ty::I64],
            _ => unreachable!("no ratified role returns more than one value"),
        };
        let m = with_declaration(&r.symbol(), Some(&r.def_path()), r.params(), wrong_returns);
        let errors = validate_module(&m);
        assert!(
            only_signature_mismatch(&errors, &r.symbol()),
            "{} result: {errors:?}",
            r.role
        );

        let mut params = r.params();
        params[0] = Ty::Ptr;
        let m = with_declaration(&r.symbol(), Some(&r.def_path()), params, r.returns());
        let errors = validate_module(&m);
        assert!(
            only_signature_mismatch(&errors, &r.symbol()),
            "{} param: {errors:?}",
            r.role
        );
    }
}

/// The def-path rule: the role is the Lean name, the `def_path` the Rust item
/// the shim wraps. `mod` naming `Nat::mod` (which does not exist) or `mul`
/// naming `Nat::add` is refused, not admitted as a relabelled declaration.
#[test]
fn a_role_naming_another_rust_item_is_a_signature_mismatch() {
    for (r, wrong) in [
        (role("mod"), "trust_bignum::Nat::mod"),
        (role("mul"), "trust_bignum::Nat::add"),
        (role("to_u64"), "trust_bignum::Nat::to_u64_wrapping"),
    ] {
        let m = with_declaration(&r.symbol(), Some(wrong), r.params(), r.returns());
        let errors = validate_module(&m);
        assert!(
            only_signature_mismatch(&errors, &r.symbol()),
            "{}: {errors:?}",
            r.role
        );
    }
}

/// Off-table roles stay foreign. `cmp` (Lean `compare` derives from
/// `beq`/`ble`; an `I32` tri-state would be a second spelling), the wrapping
/// projection (`trust-bignum` refuses one in writing; `land` then `to_u64` is
/// its one spelling), the pre-ratification spellings `eq`/`lt`, and `gcd`
/// (outside the kernel's native surface).
#[test]
fn off_table_roles_stay_foreign_declarations() {
    let h = nat();
    for (symbol, params, returns) in [
        (
            "trust_bignum_nat_cmp",
            vec![h.clone(), h.clone()],
            vec![Ty::I32],
        ),
        (
            "trust_bignum_nat_to_u64_wrapping",
            vec![h.clone()],
            vec![Ty::U64],
        ),
        (
            "trust_bignum_nat_eq",
            vec![h.clone(), h.clone()],
            vec![Ty::Bool],
        ),
        (
            "trust_bignum_nat_lt",
            vec![h.clone(), h.clone()],
            vec![Ty::Bool],
        ),
        (
            "trust_bignum_nat_gcd",
            vec![h.clone(), h.clone()],
            vec![h.clone()],
        ),
    ] {
        let m = with_declaration(symbol, None, params, returns);
        let errors = validate_module(&m);
        assert!(only_foreign(&errors, symbol), "{symbol}: {errors:?}");
    }
}

// ─────────────────────────── MUTATION CONTROLS ───────────────────────────

/// The ROW is what admits each role, not the symbol scheme: the pinned row
/// minus one entry refuses the module that declares it as exactly one
/// foreign declaration, while the full pinned row admits it.
#[test]
fn removing_a_role_from_the_row_refuses_its_declaration() {
    for r in KERNEL_SURFACE {
        let entries: Vec<HandleEntryPoint> = nat_pin()
            .entry_points
            .iter()
            .filter(|e| e.role != r.role)
            .cloned()
            .collect();
        let row = HandleRuntimePin {
            entry_points: Box::leak(entries.into_boxed_slice()),
            ..nat_pin().clone()
        };
        let without = HandleRegistry::from_pins(&[row]).expect("well-formed");
        let m = declaring(r);
        assert_eq!(
            validate_module_with_handle_registry(&m, HandleRegistry::pinned()),
            vec![],
            "{}",
            r.role
        );
        let errors = validate_module_with_handle_registry(&m, &without);
        assert!(
            only_foreign(&errors, &r.symbol()),
            "{} without its row: {errors:?}",
            r.role
        );
    }
}

/// Growing the row did not loosen the release rule: the pinned row plus a
/// second consuming entry is still refused by construction.
#[test]
fn from_pins_still_refuses_a_second_release_entry() {
    let mut entries = nat_pin().entry_points.to_vec();
    entries.push(HandleEntryPoint {
        role: "free",
        symbol: "trust_bignum_nat_free",
        def_path: "trust_bignum::Nat::free",
        params: &[PinnedTy::Handle],
        returns: &[],
    });
    let row = HandleRuntimePin {
        entry_points: Box::leak(entries.into_boxed_slice()),
        ..nat_pin().clone()
    };
    assert_eq!(
        HandleRegistry::from_pins(&[row]).map(|_| ()),
        Err(HandlePinError::MultipleReleaseEntries {
            runtime: "trust_bignum::Nat".into(),
            first: "trust_bignum_nat_drop".into(),
            second: "trust_bignum_nat_free".into(),
        })
    );
    // And exactly one pinned entry consumes without producing.
    let pin = nat_pin();
    let releases: Vec<&str> = pin
        .entry_points
        .iter()
        .filter(|e| pin.func_ty(e).returns.is_empty())
        .map(|e| e.role)
        .collect();
    assert_eq!(releases, ["drop"]);
}

// ─────────────── the proof program's b5 GAP rows, flipped ───────────────

/// `b5.gap.pin_table_is_exactly_four_entry_points` — was: one row with
/// exactly `from_u64`/`add`/`sub`/`is_zero` (it had already tripped to five
/// when `drop` landed, `454ed396`). Now PASS: the row is the v1 five plus the
/// Clean kernel's whole native `Nat` surface — every op of the kernel's
/// closed `NAT_BINOPS` allowlist maps to a pinned role — and nothing else.
/// Twin: `cmp`, which the kernel does not reduce, is not a role and is
/// refused.
#[test]
fn b5_gap_pin_table_is_exactly_four_entry_points() {
    assert_eq!(TRUSTED_HANDLE_RUNTIMES.len(), 1);
    let roles: Vec<&str> = nat_pin().entry_points.iter().map(|e| e.role).collect();
    assert_eq!(
        roles,
        [
            "from_u64",
            "add",
            "sub",
            "is_zero",
            "drop",
            "mul",
            "div",
            "mod",
            "beq",
            "ble",
            "fits_u64",
            "to_u64",
            "clone",
            "land",
            "lor",
            "xor",
            "shift_left",
            "shift_right",
            "pow",
        ]
    );
    // `clean-kernel/src/micro/native.rs` `NAT_BINOPS`, Lean name -> role.
    for (lean, role) in [
        ("Nat.add", "add"),
        ("Nat.sub", "sub"),
        ("Nat.mul", "mul"),
        ("Nat.div", "div"),
        ("Nat.mod", "mod"),
        ("Nat.pow", "pow"),
        ("Nat.land", "land"),
        ("Nat.lor", "lor"),
        ("Nat.xor", "xor"),
        ("Nat.shiftLeft", "shift_left"),
        ("Nat.shiftRight", "shift_right"),
        ("Nat.beq", "beq"),
        ("Nat.ble", "ble"),
    ] {
        assert!(roles.contains(&role), "{lean} has no pinned role");
    }
    // Twin.
    assert!(!roles.contains(&"cmp"));
    let h = nat();
    let m = with_declaration(
        "trust_bignum_nat_cmp",
        Some("trust_bignum::Nat::cmp"),
        vec![h.clone(), h],
        vec![Ty::I32],
    );
    assert!(only_foreign(&validate_module(&m), "trust_bignum_nat_cmp"));
}

/// `b5.gap.entry_point_not_pinned.<role>` — was: declaring
/// `trust_bignum_nat_<role>` was exactly one `HandleForeignDeclaration`. Now
/// PASS: the declaration validates `[]`. Right-reason twin: the same symbol
/// with a `Ptr` first parameter is exactly one
/// `HandleEntryPointSignatureMismatch` — admitted because it is pinned, not
/// because the namespace opened.
fn entry_point_now_pinned(name: &str) {
    let r = role(name);
    assert_eq!(validate_module(&declaring(r)), vec![], "{name}");
    let mut params = r.params();
    params[0] = Ty::Ptr;
    let m = with_declaration(&r.symbol(), Some(&r.def_path()), params, r.returns());
    let errors = validate_module(&m);
    assert!(
        only_signature_mismatch(&errors, &r.symbol()),
        "{name}: {errors:?}"
    );
}

/// `b5.gap.entry_point_not_pinned.mul` — flipped to PASS.
#[test]
fn b5_gap_entry_point_not_pinned_mul() {
    entry_point_now_pinned("mul");
}

/// `b5.gap.entry_point_not_pinned.div` — flipped to PASS (Lean `n / 0 = 0`).
#[test]
fn b5_gap_entry_point_not_pinned_div() {
    entry_point_now_pinned("div");
}

/// `b5.gap.entry_point_not_pinned.mod` — flipped to PASS (Lean `n % 0 = n`;
/// the shim wraps `Nat::rem`).
#[test]
fn b5_gap_entry_point_not_pinned_mod() {
    entry_point_now_pinned("mod");
}

/// `b5.gap.entry_point_not_pinned.pow` — flipped to PASS (DECIDE (1): pin it).
#[test]
fn b5_gap_entry_point_not_pinned_pow() {
    entry_point_now_pinned("pow");
}

/// `b5.gap.entry_point_not_pinned.to_u64` — flipped to PASS at the CHECKED
/// signature `(H) -> U64` (aborts when the value does not fit).
#[test]
fn b5_gap_entry_point_not_pinned_to_u64() {
    entry_point_now_pinned("to_u64");
}

/// `b5.gap.entry_point_not_pinned.clone` — flipped to PASS.
#[test]
fn b5_gap_entry_point_not_pinned_clone() {
    entry_point_now_pinned("clone");
}

/// `b5.gap.entry_point_not_pinned.drop` — closed upstream by `454ed396`
/// (the release pin) before this increment; ported as PASS.
#[test]
fn b5_gap_entry_point_not_pinned_drop() {
    entry_point_now_pinned("drop");
}

/// `b5.gap.entry_point_not_pinned.eq` — RE-SPELLED to the ratified role
/// `beq` (Lean `Nat.beq`): `beq` validates, the old `eq` spelling stays
/// foreign.
#[test]
fn b5_gap_entry_point_not_pinned_eq() {
    entry_point_now_pinned("beq");
    let h = nat();
    let m = with_declaration(
        "trust_bignum_nat_eq",
        None,
        vec![h.clone(), h],
        vec![Ty::Bool],
    );
    assert!(only_foreign(&validate_module(&m), "trust_bignum_nat_eq"));
}

/// `b5.gap.entry_point_not_pinned.lt` — RE-SPELLED to the ratified role
/// `ble` (Lean `Nat.ble`; a producer spells `x < y` as `ble (x + 1) y`):
/// `ble` validates, the old `lt` spelling stays foreign.
#[test]
fn b5_gap_entry_point_not_pinned_lt() {
    entry_point_now_pinned("ble");
    let h = nat();
    let m = with_declaration(
        "trust_bignum_nat_lt",
        None,
        vec![h.clone(), h],
        vec![Ty::Bool],
    );
    assert!(only_foreign(&validate_module(&m), "trust_bignum_nat_lt"));
}

/// `b5.gap.entry_point_not_pinned.cmp` — now a PASS row asserting it STAYS
/// refused: `cmp` is deliberately not pinned (Lean `compare` derives from
/// `beq`/`ble`, and an `I32` tri-state would be a second spelling). Twin: the
/// two roles it derives from validate.
#[test]
fn b5_gap_entry_point_not_pinned_cmp() {
    let h = nat();
    let m = with_declaration(
        "trust_bignum_nat_cmp",
        Some("trust_bignum::Nat::cmp"),
        vec![h.clone(), h],
        vec![Ty::I32],
    );
    assert!(only_foreign(&validate_module(&m), "trust_bignum_nat_cmp"));
    assert_eq!(validate_module(&declaring(role("beq"))), vec![]);
    assert_eq!(validate_module(&declaring(role("ble"))), vec![]);
}

/// `b5.gap.no_in_format_compare_project_or_release_of_a_nat` — was: there
/// was NO way to compare, project or release a Nat (`ICmp`, `PtrToInt` and
/// `Release` at a handle are `InvalidHandleUse`, and no pinned entry point
/// did it). Now PASS: compare through `beq`, project through `fits_u64` /
/// `to_u64`, release through `drop` — validates. Twin, by design: the
/// in-format `ICmp` / `PtrToInt` / `Release` at a handle stay
/// `InvalidHandleUse` (pointer identity is not Nat equality), against a `Ptr`
/// baseline of the very same three bodies that validates.
#[test]
fn b5_gap_no_in_format_compare_project_or_release_of_a_nat() {
    // PASS: through the pinned roles.
    let mut mb = ModuleBuilder::new_with_target_info("b5_nat_ops_pinned", target());
    let decls = mb
        .declare_handle_runtime_roles(nat_pin(), &["beq", "fits_u64", "to_u64", "drop"])
        .expect("pinned roles");
    let cmp = mb.add_func_type(vec![nat(), nat()], vec![Ty::Bool]);
    let to_int = mb.add_func_type(vec![nat()], vec![Ty::U64]);
    let fits = mb.add_func_type(vec![nat()], vec![Ty::Bool]);
    let drop_sig = mb.add_func_type(vec![nat()], vec![]);
    {
        let mut fb = mb.function("x_eq", cmp);
        fb.set_body_gate(gate());
        let bb0 = fb.create_block();
        let a = fb.add_block_param(bb0, nat());
        let b = fb.add_block_param(bb0, nat());
        fb.switch_to_block(bb0);
        let r = fb.call(decls.entry("beq").unwrap(), vec![a, b]);
        fb.ret(vec![r]);
        fb.build();
    }
    {
        let mut fb = mb.function("x_fits_u64", fits);
        fb.set_body_gate(gate());
        let bb0 = fb.create_block();
        let a = fb.add_block_param(bb0, nat());
        fb.switch_to_block(bb0);
        let r = fb.call(decls.entry("fits_u64").unwrap(), vec![a]);
        fb.ret(vec![r]);
        fb.build();
    }
    {
        let mut fb = mb.function("x_to_u64", to_int);
        fb.set_body_gate(gate());
        let bb0 = fb.create_block();
        let a = fb.add_block_param(bb0, nat());
        fb.switch_to_block(bb0);
        let r = fb.call(decls.entry("to_u64").unwrap(), vec![a]);
        fb.ret(vec![r]);
        fb.build();
    }
    {
        let mut fb = mb.function("x_drop", drop_sig);
        fb.set_body_gate(gate());
        let bb0 = fb.create_block();
        let a = fb.add_block_param(bb0, nat());
        fb.switch_to_block(bb0);
        fb.call_void(decls.entry("drop").unwrap(), vec![a]);
        fb.ret(vec![]);
        fb.build();
    }
    let pinned = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&pinned), vec![]);
    assert_eq!(validate_module_for_codegen(&pinned), vec![]);

    // Twin: the in-format substitutes, over `Ptr` (validates) and over the
    // Nat handle (refused by name, per instruction).
    let build = |x: Ty| -> Module {
        let mut mb = ModuleBuilder::new_with_target_info("b5_nat_ops_in_format", target());
        if x.is_handle() {
            mb.declare_handle_runtime_roles(nat_pin(), &["from_u64"])
                .unwrap();
        }
        let cmp = mb.add_func_type(vec![x.clone(), x.clone()], vec![Ty::Bool]);
        let to_int = mb.add_func_type(vec![x.clone()], vec![Ty::U64]);
        let drop_sig = mb.add_func_type(vec![x.clone()], vec![]);
        {
            let mut fb = mb.function("x_eq", cmp);
            let bb0 = fb.create_block();
            let a = fb.add_block_param(bb0, x.clone());
            let b = fb.add_block_param(bb0, x.clone());
            fb.switch_to_block(bb0);
            let r = fb.icmp(ICmpOp::Eq, x.clone(), a, b);
            fb.ret(vec![r]);
            fb.build();
        }
        {
            let mut fb = mb.function("x_to_u64", to_int);
            let bb0 = fb.create_block();
            let a = fb.add_block_param(bb0, x.clone());
            fb.switch_to_block(bb0);
            let r = fb.cast(CastOp::PtrToInt, x.clone(), Ty::U64, a);
            fb.ret(vec![r]);
            fb.build();
        }
        {
            let mut fb = mb.function("x_drop", drop_sig);
            let bb0 = fb.create_block();
            let a = fb.add_block_param(bb0, x.clone());
            fb.switch_to_block(bb0);
            fb.release(a);
            fb.ret(vec![]);
            fb.build();
        }
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let baseline = validate_module(&build(Ty::Ptr));
    assert!(baseline.is_empty(), "Ptr baseline: {baseline:?}");
    let errors = validate_module(&build(nat()));
    assert!(invalid_handle_use_naming(&errors, "ICmp"), "{errors:?}");
    assert!(invalid_handle_use_naming(&errors, "Cast"), "{errors:?}");
    assert!(invalid_handle_use_naming(&errors, "Release"), "{errors:?}");
}

// ─────────────────────── REVIEW: adversarial shapes ───────────────────────
//
// Inputs the increment's own tests did not write. Each is a spelling a real
// producer (or an attacker) plausibly reaches for, and each must be refused
// by NAME — never admitted as a relabelled pinned entry point.

/// The shapes a producer mirroring Rust or `num-bigint` would guess: a `u64`
/// shift amount, a `u32` exponent (`BigUint::pow`), an `Option<u64>`
/// projection spelled as two results, a pointer-width result, a byte-sized
/// `bool`, a tri-state under `beq`'s name, a `div_rem` pair under `div`'s
/// name, and a SECOND release spelled through `clone`'s symbol. Every one is
/// exactly one `HandleEntryPointSignatureMismatch`: the pin is `(H, H)` for
/// every binary role and one closed scalar per result, nothing else.
#[test]
fn plausible_producer_signature_drifts_are_signature_mismatches() {
    let h = nat;
    for (role_name, params, returns) in [
        ("shift_left", vec![h(), Ty::U64], vec![h()]),
        ("shift_right", vec![h(), Ty::U64], vec![h()]),
        ("pow", vec![h(), Ty::U32], vec![h()]),
        ("pow", vec![h(), Ty::U64], vec![h()]),
        ("to_u64", vec![h()], vec![Ty::U64, Ty::Bool]),
        ("to_u64", vec![h()], vec![Ty::Usize]),
        ("fits_u64", vec![h()], vec![Ty::U8]),
        ("beq", vec![h(), h()], vec![Ty::I32]),
        ("div", vec![h(), h()], vec![h(), h()]),
        ("clone", vec![h()], vec![]),
        ("mul", vec![h(), h(), h()], vec![h()]),
    ] {
        let r = role(role_name);
        let m = with_declaration(&r.symbol(), Some(&r.def_path()), params, returns);
        let errors = validate_module(&m);
        assert!(
            only_signature_mismatch(&errors, &r.symbol()),
            "{role_name}: {errors:?}"
        );
    }
}

/// A kernel-surface declaration that is interposable (`ExternalWeak` may
/// resolve to NULL; `Weak` may be overridden — and, bodyless, is also
/// `EmptyFunction`), foreign-convention, variadic or naked is refused by name — the new rows inherit every v1 declaration
/// rule, not just the signature comparison.
#[test]
fn a_kernel_surface_declaration_off_the_pinned_linkage_or_convention_is_refused() {
    for linkage in [Linkage::ExternalWeak, Linkage::Weak] {
        let mut m = declaring(role("to_u64"));
        let decl = m
            .functions
            .iter_mut()
            .find(|f| f.name == "trust_bignum_nat_to_u64")
            .unwrap();
        decl.linkage = linkage;
        let errors = validate_module(&m);
        let defined_locally = |e: &ValidationError| {
            matches!(e, ValidationError::HandleEntryPointDefinedLocally { symbol, .. }
                if symbol == "trust_bignum_nat_to_u64")
        };
        assert_eq!(
            errors.iter().filter(|e| defined_locally(e)).count(),
            1,
            "{linkage:?}: {errors:?}"
        );
        // `Weak` is a DEFINITION linkage, so a bodyless `Weak` function is
        // also `EmptyFunction`; nothing else is reported.
        assert!(
            errors
                .iter()
                .all(|e| defined_locally(e) || matches!(e, ValidationError::EmptyFunction)),
            "{linkage:?}: {errors:?}"
        );
    }

    let mut m = declaring(role("pow"));
    m.functions
        .iter_mut()
        .find(|f| f.name == "trust_bignum_nat_pow")
        .unwrap()
        .calling_conv = CallingConv::Rust;
    let errors = validate_module(&m);
    assert!(
        only_signature_mismatch(&errors, "trust_bignum_nat_pow"),
        "{errors:?}"
    );

    let r = role("beq");
    let mut m = nat_base();
    let sig = m
        .add_func_type(FuncTy {
            params: r.params(),
            returns: r.returns(),
            abi: None,
            is_vararg: true,
        })
        .expect("Module::add_func_type: test fixture");
    let id = next_func_id(&m);
    let mut decl = Function::new(id, r.symbol(), sig, BlockId::new(0));
    decl.calling_conv = CallingConv::C;
    m.try_add_function(decl)
        .expect("Module::try_add_function: test fixture");
    let errors = validate_module(&m);
    assert!(
        only_signature_mismatch(&errors, "trust_bignum_nat_beq"),
        "{errors:?}"
    );

    let mut m = declaring(role("mod"));
    m.functions
        .iter_mut()
        .find(|f| f.name == "trust_bignum_nat_mod")
        .unwrap()
        .attrs
        .naked = true;
    let errors = validate_module(&m);
    assert!(
        only_signature_mismatch(&errors, "trust_bignum_nat_mod"),
        "{errors:?}"
    );
}

/// The v43 namespace guard runs on EVERY module, handle-bearing or not, and
/// the fourteen new symbols joined it. A module that never spells a handle
/// cannot declare `to_u64` over a `Ptr`, define its own `pow`, shadow `clone`
/// with a global, or take `mul`'s address — each refused by name. Twin: the
/// very same module over an UNPINNED symbol (`gcd`) validates, so the
/// refusals are the pin's doing, not the module's shape.
#[test]
fn the_new_symbols_join_the_pinned_namespace_in_a_handle_free_module() {
    let build = |declared: &str, defined: &str, shadowed: &str, addressed: &str| -> Module {
        let mut mb = ModuleBuilder::new_with_target_info("ws3_2_no_handle", target());
        mb.add_global(trust_ir::Global {
            name: shadowed.into(),
            ty: Ty::I64,
            mutable: false,
            initializer: None,
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
        });
        let binop = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
        {
            // A local DEFINITION under a (possibly) pinned name.
            let mut fb = mb.function(defined, binop);
            let bb0 = fb.create_block();
            let a = fb.add_block_param(bb0, Ty::U64);
            let _ = fb.add_block_param(bb0, Ty::U64);
            fb.switch_to_block(bb0);
            fb.ret(vec![a]);
            fb.build();
        }
        let addr = mb.add_func_type(vec![], vec![Ty::Ptr]);
        {
            let mut fb = mb.function("address_of", addr);
            let bb0 = fb.create_block();
            fb.switch_to_block(bb0);
            let p = fb.const_value(
                Ty::Ptr,
                trust_ir::Constant::SymbolAddr {
                    symbol: addressed.into(),
                    addend: 0,
                },
            );
            fb.ret(vec![p]);
            fb.build();
        }
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        push_c_declaration(&mut m, declared, None, vec![Ty::Ptr], vec![Ty::U64]);
        m
    };

    let twin = build(
        "trust_bignum_nat_gcd",
        "trust_bignum_nat_gcd_local",
        "trust_bignum_nat_gcd_global",
        "trust_bignum_nat_gcd_addr",
    );
    assert_eq!(validate_module(&twin), vec![], "unpinned twin");

    let forged = build(
        "trust_bignum_nat_to_u64",
        "trust_bignum_nat_pow",
        "trust_bignum_nat_clone",
        "trust_bignum_nat_mul",
    );
    let errors = validate_module(&forged);
    let count = |pred: &dyn Fn(&ValidationError) -> bool| errors.iter().filter(|e| pred(e)).count();
    assert_eq!(
        count(&|e| matches!(e,
            ValidationError::HandleEntryPointSignatureMismatch { symbol, .. }
                if symbol == "trust_bignum_nat_to_u64")),
        1,
        "{errors:?}"
    );
    assert_eq!(
        count(&|e| matches!(e,
            ValidationError::HandleEntryPointSignatureMismatch { symbol, .. }
                if symbol == "trust_bignum_nat_pow")),
        1,
        "{errors:?}"
    );
    assert_eq!(
        count(&|e| matches!(e,
            ValidationError::HandleEntryPointDefinedLocally { symbol, .. }
                if symbol == "trust_bignum_nat_pow")),
        1,
        "{errors:?}"
    );
    assert_eq!(
        count(&|e| matches!(e,
            ValidationError::HandleEntryPointShadowedByGlobal { symbol, .. }
                if symbol == "trust_bignum_nat_clone")),
        1,
        "{errors:?}"
    );
    assert_eq!(
        count(&|e| matches!(e,
            ValidationError::HandleEntryPointAddressTaken { symbol, .. }
                if symbol == "trust_bignum_nat_mul")),
        1,
        "{errors:?}"
    );
    assert_eq!(errors.len(), 5, "nothing else: {errors:?}");
}
