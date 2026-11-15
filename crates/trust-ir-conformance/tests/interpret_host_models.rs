// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS2.13 (closes the model half of F-035): the reference host models of the
// pinned trusted runtimes, `trust_ir_build::PinnedHandleHost`, executed
// through the interpreter's host-call hook (WS2.12).
//
// Everything a model computes is a TRUSTED reading of the runtime (TRUST.md
// items 9 and 13). These tests pin that reading: the Lean `Nat` semantics the
// pin table documents (truncating `sub`, `n / 0 = 0`, `n % 0 = n`, checked
// `to_u64`), the exact-signature keying, the run-time surfacing of the item
// 9(c) residue (double release, use after release), and the Clean RC triple
// executed on the interpreter's own `HeapAlloc { origin: CleanHeap }` cells.

use trust_ir::inst::AllocOrigin;
use trust_ir::interpret::{
    HostCalls, InterpretErrorCode, InterpretOptions, InterpretOutcome, InterpretResult,
    InterpretValue, InterpretValueKind, Interpreter,
};
use trust_ir::ty::FuncTy;
use trust_ir::{CallingConv, Endianness, FuncId, Module, StructPassingPolicy, TargetInfo, Ty};
use trust_ir_build::builder::{FunctionBuilder, HandleRuntimeDecls};
use trust_ir_build::{
    HandleRuntimePin, ModuleBuilder, PinnedHandleHost, TRUSTED_HANDLE_RUNTIMES,
    TRUSTED_RC_RUNTIMES, validate_module,
};

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
        .expect("the Nat row is pinned")
}

fn run(module: &Module, entry: &str, host: bool) -> InterpretResult<InterpretOutcome> {
    let function = module
        .function_by_name(entry)
        .unwrap_or_else(|| panic!("no function @{entry}"));
    let pinned = PinnedHandleHost::new();
    let mut interpreter = Interpreter::with_module(module).with_options(InterpretOptions {
        fuel: 50_000_000,
        max_call_depth: 4096,
        ..InterpretOptions::default()
    });
    if host {
        interpreter = interpreter.with_host(&pinned);
    }
    interpreter.execute_function(function, Vec::new())
}

fn as_u64(value: &InterpretValue) -> u64 {
    u64::try_from(value.as_int().expect("an integer").as_unsigned()).expect("fits u64")
}

fn assert_refused(
    result: &InterpretResult<InterpretOutcome>,
    code: InterpretErrorCode,
    reason: &str,
) {
    match result {
        Ok(ok) => panic!("expected {code:?} ({reason}), got {:?}", ok.returns),
        Err(error) => {
            assert_eq!(error.code, code, "wrong code; message: {}", error.message);
            assert!(
                error.message.contains(reason),
                "{code:?} does not name `{reason}`: {}",
                error.message
            );
        }
    }
}

/// A one-block nullary function `f() -> <ret>` over the whole pinned Nat row.
fn nat_program(
    ret: Ty,
    body: impl FnOnce(&mut FunctionBuilder<'_>, &HandleRuntimeDecls) -> Vec<trust_ir::ValueId>,
) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_13_nat", target());
    let decls = mb
        .declare_handle_runtime(nat_pin())
        .expect("pinned declarations");
    let sig = mb.add_func_type(vec![], vec![ret]);
    let mut fb = mb.function("f", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let out = body(&mut fb, &decls);
    fb.ret(out);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), vec![], "the fixture validates");
    module
}

fn role(decls: &HandleRuntimeDecls, name: &str) -> FuncId {
    decls
        .entry(name)
        .unwrap_or_else(|| panic!("pinned role `{name}`"))
}

/// `from_u64(v)` inside a body.
fn lift(fb: &mut FunctionBuilder<'_>, d: &HandleRuntimeDecls, v: u64) -> trust_ir::ValueId {
    let k = fb.uconst(Ty::U64, u128::from(v));
    fb.call(role(d, "from_u64"), vec![k])
}

/// `to_u64(op(a, b))` for a binary handle role: the one exact observation.
fn binop_u64(role_name: &'static str, a: u64, b: u64) -> InterpretResult<u64> {
    let module = nat_program(Ty::U64, |fb, d| {
        let x = lift(fb, d, a);
        let y = lift(fb, d, b);
        let z = fb.call(role(d, role_name), vec![x, y]);
        let out = fb.call(role(d, "to_u64"), vec![z]);
        for h in [x, y, z] {
            fb.call_void(role(d, "drop"), vec![h]);
        }
        vec![out]
    });
    run(&module, "f", true).map(|ok| as_u64(&ok.returns[0]))
}

fn binop_bool(role_name: &'static str, a: u64, b: u64) -> bool {
    let module = nat_program(Ty::Bool, |fb, d| {
        let x = lift(fb, d, a);
        let y = lift(fb, d, b);
        let z = fb.call(role(d, role_name), vec![x, y]);
        for h in [x, y] {
            fb.call_void(role(d, "drop"), vec![h]);
        }
        vec![z]
    });
    let ok = run(&module, "f", true).expect("host-assisted");
    ok.returns[0].as_bool().expect("a bool")
}

// ───────────────────── every pinned entry point executes ─────────────────────

/// Execution twin of `every_pinned_entry_point_has_a_host_model`: each of the
/// nineteen Nat entry points is served (never `UnsupportedCall`) under the
/// exact pinned declaration, and the run is counted host-assisted.
#[test]
fn ws2_13_every_nat_entry_point_executes_under_the_pinned_host() {
    let roles: Vec<&str> = nat_pin().entry_points.iter().map(|e| e.role).collect();
    let module = nat_program(Ty::U64, |fb, d| {
        let mut acc = lift(fb, d, 0);
        let mut live = vec![acc];
        for r in &roles {
            let entry = role(d, r);
            let a = lift(fb, d, 6);
            let b = lift(fb, d, 3);
            live.push(a);
            live.push(b);
            match *r {
                "from_u64" => {}
                "drop" => {
                    let tmp = lift(fb, d, 1);
                    fb.call_void(entry, vec![tmp]);
                }
                "is_zero" | "fits_u64" => {
                    let flag = fb.call(entry, vec![a]);
                    let one = fb.uconst(Ty::U64, 1);
                    let zero = fb.uconst(Ty::U64, 0);
                    let add = fb.select(Ty::U64, flag, one, zero);
                    let add_n = fb.call(role(d, "from_u64"), vec![add]);
                    acc = fb.call(role(d, "add"), vec![acc, add_n]);
                    live.push(add_n);
                    live.push(acc);
                }
                "beq" | "ble" => {
                    let flag = fb.call(entry, vec![a, b]);
                    let one = fb.uconst(Ty::U64, 1);
                    let zero = fb.uconst(Ty::U64, 0);
                    let add = fb.select(Ty::U64, flag, one, zero);
                    let add_n = fb.call(role(d, "from_u64"), vec![add]);
                    acc = fb.call(role(d, "add"), vec![acc, add_n]);
                    live.push(add_n);
                    live.push(acc);
                }
                "to_u64" => {
                    let v = fb.call(entry, vec![a]);
                    let v_n = fb.call(role(d, "from_u64"), vec![v]);
                    acc = fb.call(role(d, "add"), vec![acc, v_n]);
                    live.push(v_n);
                    live.push(acc);
                }
                "clone" => {
                    let c = fb.call(entry, vec![a]);
                    acc = fb.call(role(d, "add"), vec![acc, c]);
                    live.push(c);
                    live.push(acc);
                }
                _ => {
                    // Every binary Nat -> Nat role.
                    let c = fb.call(entry, vec![a, b]);
                    acc = fb.call(role(d, "add"), vec![acc, c]);
                    live.push(c);
                    live.push(acc);
                }
            }
        }
        let out = fb.call(role(d, "to_u64"), vec![acc]);
        for h in live {
            fb.call_void(role(d, "drop"), vec![h]);
        }
        vec![out]
    });
    // Expected: is_zero(6)=0, fits_u64(6)=1, beq(6,3)=0, ble(6,3)=0,
    // to_u64(6)=6, clone(6)=6, add=9, sub=3, mul=18, div=2, mod=0, land=2,
    // lor=7, xor=5, shift_left=48, shift_right=0, pow=216.
    let ok = run(&module, "f", true).expect("every entry point served");
    let expected: u64 = [0, 1, 0, 0, 6, 6, 9, 3, 18, 2, 0, 2, 7, 5, 48, 0, 216]
        .iter()
        .sum();
    assert_eq!(as_u64(&ok.returns[0]), expected);
    assert!(ok.host_calls > roles.len() as u64, "{}", ok.host_calls);

    // Fail-closed twin: the same program with no host is `UnsupportedCall`.
    assert_refused(
        &run(&module, "f", false),
        InterpretErrorCode::UnsupportedCall,
        "@trust_bignum_nat_from_u64: no host model",
    );
}

// ─────────────────────────── Lean Nat semantics ───────────────────────────

/// The roadmap's mutation control: `sub(2, 5)` is 0 (truncating, Lean
/// `Nat.sub`, `handle_abi.rs` "TRUNCATED subtraction"); a wrapping
/// implementation would return `2^64 - 3`, a trapping one would not return.
#[test]
fn ws2_13_sub_truncates_at_zero() {
    assert_eq!(binop_u64("sub", 2, 5).unwrap(), 0);
    assert_eq!(binop_u64("sub", 5, 2).unwrap(), 3);
    assert_eq!(binop_u64("sub", 5, 5).unwrap(), 0);
}

#[test]
fn ws2_13_div_and_mod_by_zero_follow_lean() {
    assert_eq!(binop_u64("div", 7, 0).unwrap(), 0);
    assert_eq!(binop_u64("mod", 7, 0).unwrap(), 7);
    assert_eq!(binop_u64("div", 7, 2).unwrap(), 3);
    assert_eq!(binop_u64("mod", 7, 2).unwrap(), 1);
}

#[test]
fn ws2_13_bitwise_shift_pow_and_compare() {
    assert_eq!(binop_u64("land", 12, 10).unwrap(), 8);
    assert_eq!(binop_u64("lor", 12, 10).unwrap(), 14);
    assert_eq!(binop_u64("xor", 12, 10).unwrap(), 6);
    assert_eq!(binop_u64("shift_left", 3, 4).unwrap(), 48);
    assert_eq!(binop_u64("shift_right", 48, 4).unwrap(), 3);
    assert_eq!(binop_u64("shift_right", 48, 400).unwrap(), 0);
    assert_eq!(binop_u64("pow", 3, 4).unwrap(), 81);
    assert_eq!(binop_u64("pow", 0, 0).unwrap(), 1);
    assert_eq!(binop_u64("mul", 6, 7).unwrap(), 42);
    assert!(binop_bool("beq", 7, 7));
    assert!(!binop_bool("beq", 7, 8));
    assert!(binop_bool("ble", 7, 7));
    assert!(binop_bool("ble", 7, 8));
    assert!(!binop_bool("ble", 8, 7));
}

/// The projection is checked: `to_u64` of a value above `u64::MAX` ABORTS
/// (the pinned shim never wraps), which the interpreter spells `Panic`;
/// `fits_u64` is the total half.
#[test]
fn ws2_13_to_u64_above_u64_max_aborts_and_fits_u64_says_so() {
    let module = nat_program(Ty::Bool, |fb, d| {
        let big = lift(fb, d, u64::MAX);
        let one = lift(fb, d, 1);
        let over = fb.call(role(d, "add"), vec![big, one]);
        vec![fb.call(role(d, "fits_u64"), vec![over])]
    });
    let ok = run(&module, "f", true).unwrap();
    assert_eq!(ok.returns, vec![InterpretValue::bool(false)]);

    let module = nat_program(Ty::U64, |fb, d| {
        let big = lift(fb, d, u64::MAX);
        let one = lift(fb, d, 1);
        let over = fb.call(role(d, "add"), vec![big, one]);
        vec![fb.call(role(d, "to_u64"), vec![over])]
    });
    assert_refused(
        &run(&module, "f", true),
        InterpretErrorCode::Panic,
        "`to_u64` of a Nat above u64::MAX aborts",
    );
    // The error names the model, so it is never read as a module verdict.
    let error = run(&module, "f", true).unwrap_err();
    assert!(
        error
            .message
            .starts_with("host model for @trust_bignum_nat_to_u64:"),
        "{error}"
    );
}

/// A value wider than one limb round-trips through arithmetic: 2^64 + 5 =
/// (2^64 + 5) exactly, observed by `sub`, `shift_right` and `mod`.
#[test]
fn ws2_13_multi_limb_arithmetic_is_exact() {
    let module = nat_program(Ty::U64, |fb, d| {
        let max = lift(fb, d, u64::MAX);
        let six = lift(fb, d, 6);
        let big = fb.call(role(d, "add"), vec![max, six]); // 2^64 + 5
        let sixty_four = lift(fb, d, 64);
        let hi = fb.call(role(d, "shift_right"), vec![big, sixty_four]); // 1
        let two_64 = fb.call(role(d, "shift_left"), vec![hi, sixty_four]); // 2^64
        let lo = fb.call(role(d, "sub"), vec![big, two_64]); // 5
        let lo_u = fb.call(role(d, "to_u64"), vec![lo]);
        let hi_u = fb.call(role(d, "to_u64"), vec![hi]);
        let seven = lift(fb, d, 7);
        let r = fb.call(role(d, "mod"), vec![big, seven]); // (2^64+5) % 7
        let r_u = fb.call(role(d, "to_u64"), vec![r]);
        let sq = fb.call(role(d, "mul"), vec![big, big]);
        let q = fb.call(role(d, "div"), vec![sq, big]); // big
        let back = fb.call(role(d, "beq"), vec![q, big]);
        let one = fb.uconst(Ty::U64, 1);
        let zero = fb.uconst(Ty::U64, 0);
        let back_u = fb.select(Ty::U64, back, one, zero);
        let s1 = fb.add(Ty::U64, lo_u, hi_u);
        let s2 = fb.add(Ty::U64, s1, r_u);
        let s3 = fb.add(Ty::U64, s2, back_u);
        vec![s3]
    });
    let ok = run(&module, "f", true).unwrap();
    let expected = 5 + 1 + (((1u128 << 64) + 5) % 7) as u64 + 1;
    assert_eq!(as_u64(&ok.returns[0]), expected);
}

// ─────────────────── the item 9(c) residue, at run time ───────────────────

/// Double `drop` is UB under the model (the validator deliberately does not
/// decide it: TRUST.md item 9(c)).
#[test]
fn ws2_13_double_drop_is_undefined_behavior_under_the_model() {
    let module = nat_program(Ty::Bool, |fb, d| {
        let a = lift(fb, d, 1);
        fb.call_void(role(d, "drop"), vec![a]);
        fb.call_void(role(d, "drop"), vec![a]);
        vec![fb.bool_const(true)]
    });
    assert_refused(
        &run(&module, "f", true),
        InterpretErrorCode::UndefinedBehavior,
        "used after release",
    );
}

/// Use after drop through a `Copy` of the handle (the non-linear transport
/// the format admits) is UB under the model.
#[test]
fn ws2_13_use_after_drop_through_a_copy_is_undefined_behavior_under_the_model() {
    let module = nat_program(Ty::Bool, |fb, d| {
        let a = lift(fb, d, 1);
        let a2 = fb.copy(d.handle.clone(), a);
        fb.call_void(role(d, "drop"), vec![a]);
        vec![fb.call(role(d, "is_zero"), vec![a2])]
    });
    assert_refused(
        &run(&module, "f", true),
        InterpretErrorCode::UndefinedBehavior,
        "used after release",
    );
    // Control: the same program dropping a DIFFERENT handle executes.
    let control = nat_program(Ty::Bool, |fb, d| {
        let a = lift(fb, d, 1);
        let b = lift(fb, d, 0);
        let a2 = fb.copy(d.handle.clone(), a);
        fb.call_void(role(d, "drop"), vec![b]);
        vec![fb.call(role(d, "is_zero"), vec![a2])]
    });
    let ok = run(&control, "f", true).unwrap();
    assert_eq!(ok.returns, vec![InterpretValue::bool(false)]);
}

// ───────────────────── exact-signature keying (twins) ─────────────────────

/// The roadmap's negative twin: `trust_bignum_nat_add` declared
/// `(Ptr, Ptr) -> Ptr` is not served (the pinned signature mismatches), so
/// the call is `UnsupportedCall` exactly as without a host. The validator
/// already refuses the module; the interpreter is reached without it.
#[test]
fn ws2_13_a_mis_declared_pinned_symbol_is_not_served() {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_13_forged_add", target());
    let ptr_binop = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![Ty::Ptr]);
    let add = mb.declare_function("trust_bignum_nat_add", ptr_binop);
    let sig = mb.add_func_type(vec![], vec![Ty::Ptr]);
    let mut fb = mb.function("f", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let p = fb.null_ptr();
    let q = fb.call(add, vec![p, p]);
    fb.ret(vec![q]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(
        !validate_module(&module).is_empty(),
        "the validator refuses the off-pin declaration"
    );
    let result = run(&module, "f", true);
    assert_refused(
        &result,
        InterpretErrorCode::UnsupportedCall,
        "call to bodyless declaration @trust_bignum_nat_add: no host model",
    );
    assert_eq!(
        result.unwrap_err().unhosted_callee(),
        Some("trust_bignum_nat_add")
    );

    // A return-only mismatch, `(Nat, Nat) -> Ptr`, is not served either.
    let mut mb = ModuleBuilder::new_with_target_info("ws2_13_forged_add_ret", target());
    let nat = nat_pin().handle_ty();
    let from = mb.add_func_type(vec![Ty::U64], vec![nat.clone()]);
    let from_u64 = mb.declare_function("trust_bignum_nat_from_u64", from);
    let bad = mb.add_func_type(vec![nat.clone(), nat.clone()], vec![Ty::Ptr]);
    let add = mb.declare_function("trust_bignum_nat_add", bad);
    let sig = mb.add_func_type(vec![], vec![Ty::Ptr]);
    let mut fb = mb.function("f", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let one = fb.uconst(Ty::U64, 1);
    let a = fb.call(from_u64, vec![one]);
    let q = fb.call(add, vec![a, a]);
    fb.ret(vec![q]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_refused(
        &run(&module, "f", true),
        InterpretErrorCode::UnsupportedCall,
        "@trust_bignum_nat_add: no host model",
    );

    // And a non-C calling convention on the exact signature.
    let mut mb = ModuleBuilder::new_with_target_info("ws2_13_rust_cc", target());
    let from = mb.add_func_type(vec![Ty::U64], vec![nat.clone()]);
    let from_u64 = mb.declare_function("trust_bignum_nat_from_u64", from);
    let sig = mb.add_func_type(vec![], vec![Ty::Bool]);
    let is_zero_ty = mb.add_func_type(vec![nat.clone()], vec![Ty::Bool]);
    let is_zero = mb.declare_function("trust_bignum_nat_is_zero", is_zero_ty);
    let mut fb = mb.function("f", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let one = fb.uconst(Ty::U64, 1);
    let a = fb.call(from_u64, vec![one]);
    let z = fb.call(is_zero, vec![a]);
    fb.ret(vec![z]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module
        .functions
        .iter_mut()
        .find(|f| f.name == "trust_bignum_nat_from_u64")
        .unwrap()
        .calling_conv = CallingConv::Rust;
    assert_refused(
        &run(&module, "f", true),
        InterpretErrorCode::UnsupportedCall,
        "@trust_bignum_nat_from_u64: no host model",
    );
}

/// The model is keyed by the pin table, so a handle of another runtime, or
/// one minted by another model, is refused at a Nat entry point by the
/// interpreter's cross-runtime check.
#[test]
fn ws2_13_a_handle_of_another_model_is_refused_at_a_nat_entry_point() {
    struct OtherNat;
    impl HostCalls for OtherNat {
        fn call(
            &self,
            callee: &trust_ir::Function,
            _sig: &FuncTy,
            args: &[InterpretValue],
            host: &mut trust_ir::interpret::HostState,
        ) -> Option<InterpretResult<Vec<InterpretValue>>> {
            if callee.name != "trust_bignum_nat_from_u64" {
                return None;
            }
            Some(
                host.mint_handle(nat_pin().handle_identity(), "other-nat", as_u64(&args[0]))
                    .map(|h| vec![h]),
            )
        }
    }
    /// First model wins per call: `from_u64` is minted by `OtherNat`,
    /// `is_zero` reaches the pinned model with the other model's handle.
    struct Chain;
    impl HostCalls for Chain {
        fn call(
            &self,
            callee: &trust_ir::Function,
            sig: &FuncTy,
            args: &[InterpretValue],
            host: &mut trust_ir::interpret::HostState,
        ) -> Option<InterpretResult<Vec<InterpretValue>>> {
            OtherNat
                .call(callee, sig, args, host)
                .or_else(|| PinnedHandleHost::new().call(callee, sig, args, host))
        }
    }
    let module = nat_program(Ty::Bool, |fb, d| {
        let a = lift(fb, d, 0);
        vec![fb.call(role(d, "is_zero"), vec![a])]
    });
    let function = module.function_by_name("f").unwrap();
    let error = Interpreter::with_module(&module)
        .with_host(&Chain)
        .execute_function(function, vec![])
        .expect_err("cross-model handle");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
    assert!(
        error
            .message
            .contains("minted by host model other-nat passed to host model"),
        "{error}"
    );
}

// ──────────────────── the Clean RC triple on CleanHeap cells ────────────────────

fn clean_rc_module(body: impl FnOnce(&mut FunctionBuilder<'_>, [FuncId; 3])) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_13_clean_rc", target());
    let pin = TRUSTED_RC_RUNTIMES
        .iter()
        .find(|pin| pin.origin == AllocOrigin::CleanHeap)
        .expect("the Clean RC row");
    let mut ids = [FuncId::new(0); 3];
    for (slot, role_name) in ["retain", "release", "is_unique"].iter().enumerate() {
        let entry = pin.entry(role_name).unwrap();
        let ty = mb.add_func_type(entry.params.to_vec(), entry.returns.to_vec());
        ids[slot] = mb.declare_function(entry.symbol, ty);
    }
    let sig = mb.add_func_type(vec![], vec![Ty::U8]);
    let mut fb = mb.function("f", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    body(&mut fb, ids);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), vec![], "the RC fixture validates");
    module
}

/// `clean_inc` / `clean_dec` / `clean_is_exclusive` on a `HeapAlloc(CleanHeap)`
/// cell behave as `Retain` / `Release` / `IsUnique` on the interpreter's own
/// count: `is_exclusive` reads 1 fresh, 0 after `inc`, 1 after `dec`, and the
/// last `dec` frees the cell (a further `dec` is a double free).
#[test]
fn ws2_13_clean_rc_triple_counts_clean_heap_cells() {
    let module = clean_rc_module(|fb, [inc, dec, excl]| {
        let cell = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::CleanHeap);
        let fresh = fb.call(excl, vec![cell]); // 1
        fb.call_void(inc, vec![cell]);
        let shared = fb.call(excl, vec![cell]); // 0
        fb.call_void(dec, vec![cell]);
        let again = fb.call(excl, vec![cell]); // 1
        let two = fb.uconst(Ty::U8, 2);
        let four = fb.uconst(Ty::U8, 4);
        let s = fb.mul(Ty::U8, shared, two);
        let a = fb.mul(Ty::U8, again, four);
        let sum = fb.add(Ty::U8, fresh, s);
        let out = fb.add(Ty::U8, sum, a);
        fb.call_void(dec, vec![cell]); // count 0: freed
        fb.ret(vec![out]);
    });
    let ok = run(&module, "f", true).unwrap();
    // fresh (1) + 2 * shared (0) + 4 * again (1).
    assert_eq!(as_u64(&ok.returns[0]), 5);
    assert_eq!(ok.host_calls, 6);
    // The counts are the SAME table `Inst::IsUnique` reads.
    let mixed = clean_rc_module(|fb, [inc, _dec, _excl]| {
        let cell = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::CleanHeap);
        fb.call_void(inc, vec![cell]);
        let unique = fb.is_unique(cell);
        let one = fb.uconst(Ty::U8, 1);
        let zero = fb.uconst(Ty::U8, 0);
        let out = fb.select(Ty::U8, unique, one, zero);
        fb.ret(vec![out]);
    });
    assert_eq!(as_u64(&run(&mixed, "f", true).unwrap().returns[0]), 0);

    // Fail-closed twin: no host, the first RC call is `UnsupportedCall`.
    assert_refused(
        &run(&module, "f", false),
        InterpretErrorCode::UnsupportedCall,
        "@clean_is_exclusive: no host model",
    );
    // Double free through the pinned release entry is UB.
    let double = clean_rc_module(|fb, [_inc, dec, _excl]| {
        let cell = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::CleanHeap);
        fb.call_void(dec, vec![cell]);
        fb.call_void(dec, vec![cell]);
        let zero = fb.uconst(Ty::U8, 0);
        fb.ret(vec![zero]);
    });
    assert_refused(
        &run(&double, "f", true),
        InterpretErrorCode::UndefinedBehavior,
        "freed allocation",
    );
}

/// No ownership transfer between heaps (TRUST.md item 13(c)): a `RustHeap`
/// cell, a stack slot or a null pointer handed to `clean_inc` is UB under the
/// model; so is a pointer into the middle of a Clean cell.
#[test]
fn ws2_13_clean_rc_refuses_cells_of_another_heap_and_interior_pointers() {
    let rust_heap = clean_rc_module(|fb, [inc, _dec, _excl]| {
        let cell = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
        fb.call_void(inc, vec![cell]);
        let zero = fb.uconst(Ty::U8, 0);
        fb.ret(vec![zero]);
    });
    assert_refused(
        &run(&rust_heap, "f", true),
        InterpretErrorCode::UndefinedBehavior,
        "addresses a RustHeap heap cell, not a cell of the CleanHeap heap",
    );
    let stack = clean_rc_module(|fb, [_inc, _dec, excl]| {
        let slot = fb.alloca(Ty::U64);
        let out = fb.call(excl, vec![slot]);
        fb.ret(vec![out]);
    });
    assert_refused(
        &run(&stack, "f", true),
        InterpretErrorCode::UndefinedBehavior,
        "addresses a stack or global allocation, not a cell of the CleanHeap heap",
    );
    let interior = clean_rc_module(|fb, [_inc, dec, _excl]| {
        let two = fb.uconst(Ty::U64, 2);
        let cell = fb.heap_alloc(Ty::U64, Some(two), None, AllocOrigin::CleanHeap);
        let inner = fb.gep_byte_offset(cell, 8);
        fb.call_void(dec, vec![inner]);
        let zero = fb.uconst(Ty::U8, 0);
        fb.ret(vec![zero]);
    });
    assert_refused(
        &run(&interior, "f", true),
        InterpretErrorCode::UndefinedBehavior,
        "offset 8 of its allocation, not at the object base",
    );
    let null = clean_rc_module(|fb, [inc, _dec, _excl]| {
        let p = fb.null_ptr();
        fb.call_void(inc, vec![p]);
        let zero = fb.uconst(Ty::U8, 0);
        fb.ret(vec![zero]);
    });
    assert_refused(
        &run(&null, "f", true),
        InterpretErrorCode::UndefinedBehavior,
        "null object pointer",
    );
}

/// The RC classification is keyed by the exact pinned signature too:
/// `clean_dec(Ptr) -> I32` is not the pinned entry, so it is not served.
#[test]
fn ws2_13_a_mis_declared_rc_entry_point_is_not_served() {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_13_bad_dec", target());
    let bad = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);
    let dec = mb.declare_function("clean_dec", bad);
    let sig = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("f", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let cell = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::CleanHeap);
    let out = fb.call(dec, vec![cell]);
    fb.ret(vec![out]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(
        !validate_module(&module).is_empty(),
        "the validator refuses it"
    );
    assert_refused(
        &run(&module, "f", true),
        InterpretErrorCode::UnsupportedCall,
        "call to bodyless declaration @clean_dec: no host model",
    );
    // And a host that CLAIMS an RC role for a declaration of the wrong shape
    // is refused by the interpreter, not executed.
    struct Overclaim;
    impl HostCalls for Overclaim {
        fn call(
            &self,
            _callee: &trust_ir::Function,
            _sig: &FuncTy,
            _args: &[InterpretValue],
            _host: &mut trust_ir::interpret::HostState,
        ) -> Option<InterpretResult<Vec<InterpretValue>>> {
            None
        }
        fn rc_op(&self, _callee: &trust_ir::Function, _sig: &FuncTy) -> Option<trust_ir::HostRcOp> {
            Some(trust_ir::HostRcOp {
                role: trust_ir::HostRcRole::Release,
                origin: AllocOrigin::CleanHeap,
            })
        }
    }
    let function = module.function_by_name("f").unwrap();
    let error = Interpreter::with_module(&module)
        .with_host(&Overclaim)
        .execute_function(function, vec![])
        .expect_err("wrong shape");
    assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
    assert!(
        error.message.contains("is not that entry point's shape"),
        "{error}"
    );
}

/// A handle is not a pointer: the model's `Nat` values never appear in
/// interpreter memory, and a handle value rendered by a consumer is opaque.
#[test]
fn ws2_13_a_returned_handle_is_opaque() {
    let module = nat_program(nat_pin().handle_ty(), |fb, d| vec![lift(fb, d, 9)]);
    let ok = run(&module, "f", true).unwrap();
    assert!(matches!(
        ok.returns[0].kind,
        InterpretValueKind::Handle { .. }
    ));
    assert_eq!(ok.returns[0].ty, nat_pin().handle_ty());
}

// ───────────────────────── adversarial review (WS2.13) ─────────────────────────

/// Review: the host-served `clean_dec` that takes the count to zero FREES the
/// cell in the interpreter's own allocation table — a model keeping a private
/// refcount beside the interpreter's would leave the cell readable. After the
/// last `dec` a `Load` through the pointer, and an in-format `Inst::IsUnique`,
/// are `UndefinedBehavior` on a freed allocation; the control loads fine
/// before it.
#[test]
fn ws2_13_review_the_last_clean_dec_frees_the_cell_for_in_format_operations() {
    let control = clean_rc_module(|fb, [inc, dec, _excl]| {
        let cell = fb.heap_alloc(Ty::U8, None, None, AllocOrigin::CleanHeap);
        let seven = fb.uconst(Ty::U8, 7);
        fb.store(Ty::U8, cell, seven);
        fb.call_void(inc, vec![cell]);
        fb.call_void(dec, vec![cell]); // count back to 1: still live
        let out = fb.load(Ty::U8, cell);
        fb.ret(vec![out]);
    });
    assert_eq!(as_u64(&run(&control, "f", true).unwrap().returns[0]), 7);

    let freed_then_load = clean_rc_module(|fb, [_inc, dec, _excl]| {
        let cell = fb.heap_alloc(Ty::U8, None, None, AllocOrigin::CleanHeap);
        let seven = fb.uconst(Ty::U8, 7);
        fb.store(Ty::U8, cell, seven);
        fb.call_void(dec, vec![cell]); // count 0: freed
        let out = fb.load(Ty::U8, cell);
        fb.ret(vec![out]);
    });
    assert_refused(
        &run(&freed_then_load, "f", true),
        InterpretErrorCode::UndefinedBehavior,
        "Load: use after dealloc",
    );

    let freed_then_is_unique = clean_rc_module(|fb, [_inc, dec, _excl]| {
        let cell = fb.heap_alloc(Ty::U8, None, None, AllocOrigin::CleanHeap);
        fb.call_void(dec, vec![cell]);
        let unique = fb.is_unique(cell);
        let one = fb.uconst(Ty::U8, 1);
        let zero = fb.uconst(Ty::U8, 0);
        let out = fb.select(Ty::U8, unique, one, zero);
        fb.ret(vec![out]);
    });
    assert_refused(
        &run(&freed_then_is_unique, "f", true),
        InterpretErrorCode::UndefinedBehavior,
        "freed allocation",
    );
}

/// Review: the in-format ARC instructions and the host-served triple read and
/// write ONE count, in both directions. Two `clean_inc` then two
/// `Inst::Release` leave the cell unique; an `Inst::Release` to zero makes the
/// next `clean_is_exclusive` a use of a freed cell.
#[test]
fn ws2_13_review_instruction_arc_and_host_rc_share_one_count_in_both_directions() {
    let both_ways = clean_rc_module(|fb, [inc, _dec, excl]| {
        let cell = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::CleanHeap);
        fb.call_void(inc, vec![cell]); // 2
        fb.call_void(inc, vec![cell]); // 3
        fb.release(cell); // 2
        let shared = fb.call(excl, vec![cell]); // 0
        fb.release(cell); // 1
        let unique = fb.call(excl, vec![cell]); // 1
        let two = fb.uconst(Ty::U8, 2);
        let doubled = fb.mul(Ty::U8, unique, two);
        let out = fb.add(Ty::U8, shared, doubled);
        fb.ret(vec![out]);
    });
    let ok = run(&both_ways, "f", true).unwrap();
    assert_eq!(as_u64(&ok.returns[0]), 2);
    assert_eq!(ok.host_calls, 4);

    let instruction_frees = clean_rc_module(|fb, [_inc, _dec, excl]| {
        let cell = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::CleanHeap);
        fb.release(cell); // in-format release to zero: freed
        let out = fb.call(excl, vec![cell]);
        fb.ret(vec![out]);
    });
    assert_refused(
        &run(&instruction_frees, "f", true),
        InterpretErrorCode::UndefinedBehavior,
        "@clean_is_exclusive: pointer references a freed allocation",
    );
}

/// Review: `clone` mints a FRESH allocation (a model returning the same id
/// would make the clone dead once the original is dropped), and an entry
/// point reading one handle twice (`add(a, a)`) is not a double use.
#[test]
fn ws2_13_review_a_clone_survives_the_drop_of_its_original_and_aliased_reads_are_fine() {
    let module = nat_program(Ty::U64, |fb, d| {
        let a = lift(fb, d, 21);
        let doubled = fb.call(role(d, "add"), vec![a, a]); // 42, two reads of one handle
        let c = fb.call(role(d, "clone"), vec![doubled]);
        fb.call_void(role(d, "drop"), vec![doubled]);
        fb.call_void(role(d, "drop"), vec![a]);
        let out = fb.call(role(d, "to_u64"), vec![c]);
        fb.call_void(role(d, "drop"), vec![c]);
        vec![out]
    });
    let ok = run(&module, "f", true).unwrap();
    assert_eq!(as_u64(&ok.returns[0]), 42);
    assert_eq!(ok.host_calls, 7);

    // Twin: dropping the clone does not free the original either.
    let twin = nat_program(Ty::U64, |fb, d| {
        let a = lift(fb, d, 5);
        let c = fb.call(role(d, "clone"), vec![a]);
        fb.call_void(role(d, "drop"), vec![c]);
        let out = fb.call(role(d, "to_u64"), vec![a]);
        vec![out]
    });
    assert_eq!(as_u64(&run(&twin, "f", true).unwrap().returns[0]), 5);
}

/// Review: comparisons and the documented `toUInt64` spelling are exact past
/// one limb. A model comparing only the low limb would call `beq(2^64, 0)`
/// true and `ble(2^64, u64::MAX)` true; `to_u64(land(n, from_u64(u64::MAX)))`
/// is the never-aborting projection the pin table documents.
#[test]
fn ws2_13_review_multi_limb_compare_and_the_documented_to_uint64_spelling() {
    let module = nat_program(Ty::U64, |fb, d| {
        let max = lift(fb, d, u64::MAX);
        let one = lift(fb, d, 1);
        let two_64 = fb.call(role(d, "add"), vec![max, one]);
        let zero = lift(fb, d, 0);
        let eq_zero = fb.call(role(d, "beq"), vec![two_64, zero]); // false
        let le_max = fb.call(role(d, "ble"), vec![two_64, max]); // false
        let ge_max = fb.call(role(d, "ble"), vec![max, two_64]); // true
        let five = lift(fb, d, 5);
        let n = fb.call(role(d, "add"), vec![two_64, five]); // 2^64 + 5
        let low = fb.call(role(d, "land"), vec![n, max]);
        let low_u = fb.call(role(d, "to_u64"), vec![low]); // 5, never aborts
        let k1 = fb.uconst(Ty::U64, 1);
        let k0 = fb.uconst(Ty::U64, 0);
        let k100 = fb.uconst(Ty::U64, 100);
        let k10 = fb.uconst(Ty::U64, 10);
        let a = fb.select(Ty::U64, eq_zero, k100, k0);
        let b = fb.select(Ty::U64, le_max, k10, k0);
        let c = fb.select(Ty::U64, ge_max, k1, k0);
        let s1 = fb.add(Ty::U64, low_u, a);
        let s2 = fb.add(Ty::U64, s1, b);
        let s3 = fb.add(Ty::U64, s2, c);
        vec![s3]
    });
    let ok = run(&module, "f", true).unwrap();
    // low_u (5) + a (eq_zero false -> 0) + b (le_max false -> 0) + c (ge_max true -> 1)
    assert_eq!(as_u64(&ok.returns[0]), 6);
}

/// Review: the RC classification is keyed on the calling convention and the
/// non-variadic shape too, not just the parameter list — `clean_inc` under
/// the Rust convention, or as `clean_inc(Ptr, ...)`, is not the pinned entry
/// and is not served.
#[test]
fn ws2_13_review_rc_classification_needs_the_pinned_calling_convention_and_arity() {
    let module = clean_rc_module(|fb, [inc, _dec, _excl]| {
        let cell = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::CleanHeap);
        fb.call_void(inc, vec![cell]);
        let zero = fb.uconst(Ty::U8, 0);
        fb.ret(vec![zero]);
    });
    let mut rust_cc = module.clone();
    rust_cc
        .functions
        .iter_mut()
        .find(|f| f.name == "clean_inc")
        .unwrap()
        .calling_conv = CallingConv::Rust;
    assert_refused(
        &run(&rust_cc, "f", true),
        InterpretErrorCode::UnsupportedCall,
        "call to bodyless declaration @clean_inc: no host model",
    );

    let mut vararg = module.clone();
    let inc_ty = vararg
        .functions
        .iter()
        .find(|f| f.name == "clean_inc")
        .unwrap()
        .ty;
    vararg.func_types[inc_ty.as_usize()].is_vararg = true;
    // A variadic callee is refused at the call boundary, before any host is
    // consulted (the interpreter cannot type-check its arguments).
    assert_refused(
        &run(&vararg, "f", true),
        InterpretErrorCode::SignatureMismatch,
        "non-executable vararg signature",
    );
    // Control: the unmodified module executes.
    assert_eq!(run(&module, "f", true).unwrap().host_calls, 1);
}
