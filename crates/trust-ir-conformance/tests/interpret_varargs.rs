// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS2.15 (closes the vararg part of F-036): a call to a VARIADIC DECLARATION
// is a host call (WS2.12) carrying the full argument list; a variadic
// DEFINITION stays refused, by name.
//
// Before: `check_function_args` refused EVERY call into a vararg-typed
// function with `SignatureMismatch "non-executable vararg signature"` —
// including a call to a bodyless `printf`-shaped declaration, which is the
// shape that blocked the repaired Clean general-lane module (parta-lean
// `GENERAL.interpret`). Now:
//
// * a variadic declaration's fixed prefix is checked exactly as any call's
//   arguments are, the variadic tail is checked for what the format promises
//   about it (whole, non-poison values of their own types; never a runtime
//   handle, which has no exact type to be transported at), and the host model
//   sees every argument;
// * a variadic definition is refused with the SAME named reason as before
//   (`SignatureMismatch`, "non-executable vararg signature"): no instruction
//   reads a variadic argument (`va_arg` has no spelling), so a body could not
//   observe the tail it was passed. `LIMITATIONS.md` ratifies it out of scope
//   (`c_variadic` bodies are unstable Rust).
//
// Row ports (roadmap F-036):
// * `goal-g1-g8/g1-foreign-calls-varargs` —
//   `goal_g1_foreign_calls_varargs_a_variadic_declaration_is_a_host_call_with_every_argument`.
// * `producer-rust-thir/c-variadic-body` —
//   `producer_rust_thir_c_variadic_body_a_variadic_definition_is_refused_by_name`.
// `GENERAL.interpret` itself flips only once WS2.13 serves the Clean RC
// runtime; this file removes the vararg refusal it tripped on.

use std::sync::Mutex;

use trust_ir::inst::BinOp;
use trust_ir::interpret::{
    HostCalls, HostState, InterpretError, InterpretErrorCode, InterpretResult, InterpretValue,
    Interpreter,
};
use trust_ir::ty::FuncTy;
use trust_ir::value::FuncId;
use trust_ir::{Endianness, Function, HandleTy, Module, StructPassingPolicy, TargetInfo, Ty};
use trust_ir_build::{ModuleBuilder, validate_module};

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn as_i128(value: &InterpretValue) -> i128 {
    value.as_int().expect("an integer value").as_signed()
}

fn run(
    module: &Module,
    entry: &str,
    host: Option<&dyn HostCalls>,
) -> InterpretResult<(Vec<InterpretValue>, u64)> {
    let function = module
        .function_by_name(entry)
        .unwrap_or_else(|| panic!("no function @{entry}"));
    let mut interpreter = Interpreter::with_module(module);
    if let Some(host) = host {
        interpreter = interpreter.with_host(host);
    }
    interpreter
        .execute_function(function, Vec::new())
        .map(|outcome| (outcome.returns, outcome.host_calls))
}

fn assert_refused<T: std::fmt::Debug>(
    result: &InterpretResult<T>,
    code: InterpretErrorCode,
    reason: &str,
) {
    match result {
        Ok(ok) => panic!("expected {code:?} ({reason}), but the run returned {ok:?}"),
        Err(InterpretError {
            code: got, message, ..
        }) => {
            assert_eq!(*got, code, "wrong code; message: {message}");
            assert!(
                message.contains(reason),
                "{code:?} message does not name `{reason}`: {message}"
            );
        }
    }
}

/// A test host for `@sum_i64(i64 count, ...) -> i64`: records every argument
/// list it is handed and returns the sum of the integer arguments (a float
/// or bool in the tail counts as zero).
#[derive(Default)]
struct SumHost {
    seen: Mutex<Vec<Vec<Ty>>>,
}

impl HostCalls for SumHost {
    fn call(
        &self,
        callee: &Function,
        sig: &FuncTy,
        args: &[InterpretValue],
        _host: &mut HostState,
    ) -> Option<InterpretResult<Vec<InterpretValue>>> {
        if callee.name != "sum_i64" {
            return None;
        }
        // WS2.13 hands the host the DECLARED signature; for this entry it is
        // the variadic `(i64, ...) -> i64`, and the model is written against
        // exactly that (a non-variadic `sum_i64` is not this model).
        if !sig.is_vararg || sig.params != [Ty::I64] || sig.returns != [Ty::I64] {
            return None;
        }
        self.seen
            .lock()
            .unwrap()
            .push(args.iter().map(|a| a.ty.clone()).collect());
        let sum: i128 = args
            .iter()
            .filter_map(|a| a.as_int())
            .map(|i| i.as_signed())
            .sum();
        Some(InterpretValue::int(Ty::I64, sum).map(|v| vec![v]))
    }
}

/// `sum_i64(i64, ...) -> i64` declared bodyless at the C convention (the
/// builder's default; the validator refuses a variadic RUST signature);
/// `caller() -> i64 { sum_i64(3, 10i32, 20u8, 1.5f16) }` — three variadic
/// arguments of three different types.
fn declaration_module() -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_15_vararg_decl", target());
    let sum_sig = mb.add_vararg_func_type(vec![Ty::I64], vec![Ty::I64]);
    let sum = mb.declare_function("sum_i64", sum_sig);
    let caller_sig = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("caller", caller_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let count = fb.iconst(Ty::I64, 3);
    let ten = fb.iconst(Ty::I32, 10);
    let twenty = fb.uconst(Ty::U8, 20);
    let half = fb.fconst(Ty::F16, 1.5);
    let total = fb.call(sum, vec![count, ten, twenty, half]);
    fb.ret(vec![total]);
    fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), sum)
}

/// `goal-g1-g8/g1-foreign-calls-varargs`, ported (positive): the variadic
/// declaration is executed by the host with EVERY argument, the fixed one and
/// the three variadic ones, each at its own type.
#[test]
fn goal_g1_foreign_calls_varargs_a_variadic_declaration_is_a_host_call_with_every_argument() {
    let (module, _) = declaration_module();
    assert_eq!(validate_module(&module), vec![]);
    let host = SumHost::default();
    let (returns, host_calls) = run(&module, "caller", Some(&host)).expect("host-assisted run");
    assert_eq!(
        as_i128(&returns[0]),
        33,
        "3 + 10 + 20 (+ the f16, not an int)"
    );
    assert_eq!(host_calls, 1, "host-assisted, and counted");
    assert_eq!(
        *host.seen.lock().unwrap(),
        vec![vec![Ty::I64, Ty::I32, Ty::U8, Ty::F16]],
        "the host saw the full argument list at the arguments' own types"
    );
}

/// The declaration with NO host is the WS2.12 refusal, not the old vararg
/// one: the call is a host call that nothing serves.
#[test]
fn a_variadic_declaration_without_a_host_is_unsupported_call() {
    let (module, _) = declaration_module();
    let result = run(&module, "caller", None);
    assert_refused(
        &result,
        InterpretErrorCode::UnsupportedCall,
        "call to bodyless declaration @sum_i64: no host model",
    );
}

/// A variadic declaration reached through a FUNCTION POINTER is the same
/// host call; the pointer's signature must agree on variadicity exactly as
/// it must on the parameter list.
#[test]
fn a_variadic_declaration_through_a_function_pointer_is_a_host_call() {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_15_vararg_ptr", target());
    let sum_sig = mb.add_vararg_func_type(vec![Ty::I64], vec![Ty::I64]);
    let sum = mb.declare_function("sum_i64", sum_sig);
    let caller_sig = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("caller", caller_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let pointer = fb.fn_addr(sum_sig, sum);
    let count = fb.iconst(Ty::I64, 2);
    let a = fb.iconst(Ty::I64, 5);
    let b = fb.iconst(Ty::I64, 6);
    let total = fb.call_indirect(pointer, sum_sig, vec![count, a, b]);
    fb.ret(vec![total]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), vec![]);
    let host = SumHost::default();
    let (returns, host_calls) = run(&module, "caller", Some(&host)).expect("host-assisted run");
    assert_eq!(as_i128(&returns[0]), 13);
    assert_eq!(host_calls, 1);
}

/// `sum2(i64 count, ...) -> i64 { count + 1 }` DEFINED at the C convention
/// with a body (the validator admits it: only a variadic RUST signature is
/// the unknown-signature pattern), called by `caller()` with two variadic
/// arguments, and also reachable as the entry.
fn definition_module() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_15_vararg_def", target());
    let sum_sig = mb.add_vararg_func_type(vec![Ty::I64], vec![Ty::I64]);
    let sum = {
        let mut fb = mb.function("sum2", sum_sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let count = fb.add_block_param(entry, Ty::I64);
        let one = fb.iconst(Ty::I64, 1);
        let out = fb.binop(BinOp::Add, Ty::I64, count, one);
        fb.ret(vec![out]);
        fb.build()
    };
    let caller_sig = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("caller", caller_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let count = fb.iconst(Ty::I64, 2);
    let a = fb.iconst(Ty::I64, 5);
    let b = fb.iconst(Ty::I64, 6);
    let total = fb.call(sum, vec![count, a, b]);
    fb.ret(vec![total]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `producer-rust-thir/c-variadic-body`, ported (negative twin): a variadic
/// DEFINITION is refused with the unchanged, named reason — through a direct
/// call, as the entry, and with a host installed (a host serves
/// declarations only; a definition's body is the module's).
#[test]
fn producer_rust_thir_c_variadic_body_a_variadic_definition_is_refused_by_name() {
    let module = definition_module();
    assert_eq!(validate_module(&module), vec![]);
    let reason = "non-executable vararg signature";
    assert_refused(
        &run(&module, "caller", None),
        InterpretErrorCode::SignatureMismatch,
        reason,
    );
    assert_refused(
        &run(&module, "caller", Some(&SumHost::default())),
        InterpretErrorCode::SignatureMismatch,
        reason,
    );
    let sum2 = module.function_by_name("sum2").unwrap();
    let entry = Interpreter::with_module(&module)
        .execute_function(sum2, vec![InterpretValue::int(Ty::I64, 2).unwrap()]);
    assert_refused(&entry, InterpretErrorCode::SignatureMismatch, reason);
    // The refusal says WHY: a definition, and the instruction that is missing.
    let message = run(&module, "caller", None).unwrap_err().message;
    assert!(
        message.contains("variadic DEFINITION") && message.contains("no instruction reads"),
        "{message}"
    );
}

/// The definition through a function pointer is refused the same way.
#[test]
fn a_variadic_definition_through_a_function_pointer_is_refused_by_name() {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_15_vararg_def_ptr", target());
    let sum_sig = mb.add_vararg_func_type(vec![Ty::I64], vec![Ty::I64]);
    let sum = {
        let mut fb = mb.function("sum2", sum_sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let count = fb.add_block_param(entry, Ty::I64);
        fb.ret(vec![count]);
        fb.build()
    };
    let caller_sig = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("caller", caller_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let pointer = fb.fn_addr(sum_sig, sum);
    let count = fb.iconst(Ty::I64, 2);
    let total = fb.call_indirect(pointer, sum_sig, vec![count]);
    fb.ret(vec![total]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), vec![]);
    assert_refused(
        &run(&module, "caller", None),
        InterpretErrorCode::SignatureMismatch,
        "non-executable vararg signature",
    );
}

// ───────────────────────────── mutation control ─────────────────────────────

/// Fewer arguments than the fixed prefix: arity is still checked on the
/// prefix, so "variadic" does not mean "any arity".
#[test]
fn a_variadic_call_short_of_its_fixed_prefix_is_signature_mismatch() {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_15_vararg_short", target());
    let sum_sig = mb.add_vararg_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
    let sum = mb.declare_function("sum_i64", sum_sig);
    let caller_sig = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("caller", caller_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let count = fb.iconst(Ty::I64, 1);
    let total = fb.call(sum, vec![count]);
    fb.ret(vec![total]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    // The validator refuses it too (fewer than the fixed count); the
    // interpreter's own check is what this pins.
    assert!(!validate_module(&module).is_empty());
    assert_refused(
        &run(&module, "caller", Some(&SumHost::default())),
        InterpretErrorCode::SignatureMismatch,
        "variadic callee expects at least 2, got 1",
    );
}

/// A wrongly typed FIXED argument is a type mismatch exactly as on a
/// non-variadic call.
#[test]
fn a_variadic_call_with_a_mistyped_fixed_argument_is_signature_mismatch() {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_15_vararg_typed", target());
    let sum_sig = mb.add_vararg_func_type(vec![Ty::I64], vec![Ty::I64]);
    let sum = mb.declare_function("sum_i64", sum_sig);
    let caller_sig = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("caller", caller_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let count = fb.iconst(Ty::I32, 1);
    let tail = fb.iconst(Ty::I64, 5);
    let total = fb.call(sum, vec![count, tail]);
    fb.ret(vec![total]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(!validate_module(&module).is_empty());
    assert_refused(
        &run(&module, "caller", Some(&SumHost::default())),
        InterpretErrorCode::SignatureMismatch,
        "Call arguments type mismatch at argument 0: expected i64, got i32",
    );
}

/// A test host of a runtime whose handle carries a `u64`: `mk_h(u64)` mints.
struct MintHost;

fn handle() -> HandleTy {
    HandleTy::new("H", "test_h::H")
}

impl HostCalls for MintHost {
    fn call(
        &self,
        callee: &Function,
        _sig: &FuncTy,
        args: &[InterpretValue],
        host: &mut HostState,
    ) -> Option<InterpretResult<Vec<InterpretValue>>> {
        match callee.name.as_str() {
            "mk_h" => Some(
                host.mint_handle(handle(), "h", as_i128(&args[0]))
                    .map(|h| vec![h]),
            ),
            "sum_i64" => Some(InterpretValue::int(Ty::I64, 0).map(|v| vec![v])),
            _ => None,
        }
    }
}

/// A runtime handle in the variadic tail is refused: the tail has no exact
/// type to transport it at (the v43 rule, the validator's `InvalidHandleUse`
/// twin), so a module that writes it without validating still cannot hand a
/// handle to a variadic host entry.
#[test]
fn a_handle_in_a_variadic_tail_is_a_type_error() {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_15_vararg_handle", target());
    let handle_ty = Ty::Handle(Box::new(handle()));
    let mk_sig = mb.add_func_type(vec![Ty::U64], vec![handle_ty.clone()]);
    let mk = mb.declare_function("mk_h", mk_sig);
    let sum_sig = mb.add_vararg_func_type(vec![Ty::I64], vec![Ty::I64]);
    let sum = mb.declare_function("sum_i64", sum_sig);
    let caller_sig = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("caller", caller_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let seven = fb.uconst(Ty::U64, 7);
    let h = fb.call(mk, vec![seven]);
    let count = fb.iconst(Ty::I64, 1);
    let total = fb.call(sum, vec![count, h]);
    fb.ret(vec![total]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_refused(
        &run(&module, "caller", Some(&MintHost)),
        InterpretErrorCode::TypeError,
        "variadic argument 1 carries a runtime handle",
    );
}

// ───────────────────────── review: adversarial shapes ─────────────────────────

/// `plus1(i64) -> i64` DEFINED non-variadic, but the module takes its address
/// at a VARIADIC pointer type `(i64, ...) -> i64` and calls it through that
/// pointer with the exact fixed count. Before WS2.15 every vararg edge was
/// refused outright; now the pointer signature must AGREE on variadicity —
/// so this is still `SignatureMismatch`, and `plus1` never runs (its body
/// would otherwise execute under a signature the module lied about).
#[test]
fn a_variadic_pointer_over_a_non_variadic_definition_is_signature_mismatch() {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_15_vararg_ptr_lie_a", target());
    let plain_sig = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let vararg_sig = mb.add_vararg_func_type(vec![Ty::I64], vec![Ty::I64]);
    let plus1 = {
        let mut fb = mb.function("plus1", plain_sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let x = fb.add_block_param(entry, Ty::I64);
        let one = fb.iconst(Ty::I64, 1);
        let out = fb.binop(BinOp::Add, Ty::I64, x, one);
        fb.ret(vec![out]);
        fb.build()
    };
    let caller_sig = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("caller", caller_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let pointer = fb.fn_addr(vararg_sig, plus1);
    let x = fb.iconst(Ty::I64, 41);
    let out = fb.call_indirect(pointer, vararg_sig, vec![x]);
    fb.ret(vec![out]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    // The validator refuses the lying `FnDef` too; the interpreter's own
    // agreement rule is what this pins.
    assert!(!validate_module(&module).is_empty());
    let result = run(&module, "caller", None);
    assert_refused(
        &result,
        InterpretErrorCode::SignatureMismatch,
        "pointer signature functy.1 is variadic, callee functy.0 is not variadic",
    );
    assert!(
        !matches!(&result, Ok((returns, _)) if as_i128(&returns[0]) == 42),
        "plus1 must not execute under a variadic pointer type"
    );
}

/// The mirror lie: the variadic DECLARATION `sum_i64(i64, ...)` addressed at
/// a NON-variadic pointer type `(i64) -> i64`. With a host installed this
/// must still be `SignatureMismatch`, and the host must never see the call —
/// a pointer type that drops the variadic tail is not the declared contract.
#[test]
fn a_non_variadic_pointer_over_a_variadic_declaration_is_signature_mismatch() {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_15_vararg_ptr_lie_b", target());
    let plain_sig = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let vararg_sig = mb.add_vararg_func_type(vec![Ty::I64], vec![Ty::I64]);
    let sum = mb.declare_function("sum_i64", vararg_sig);
    let caller_sig = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("caller", caller_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let pointer = fb.fn_addr(plain_sig, sum);
    let x = fb.iconst(Ty::I64, 1);
    let out = fb.call_indirect(pointer, plain_sig, vec![x]);
    fb.ret(vec![out]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(!validate_module(&module).is_empty());
    let host = SumHost::default();
    assert_refused(
        &run(&module, "caller", Some(&host)),
        InterpretErrorCode::SignatureMismatch,
        "pointer signature functy.0 is not variadic, callee functy.1 is variadic",
    );
    assert!(
        host.seen.lock().unwrap().is_empty(),
        "the host must never be reached through a pointer type that disagrees on variadicity"
    );
}

/// The `Invoke` edge is the same host call as `Call` (it routes through the
/// direct-call path): the variadic declaration is served with every
/// argument and control continues on the normal edge.
#[test]
fn a_variadic_declaration_through_invoke_is_a_host_call_with_every_argument() {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_15_vararg_invoke", target());
    let sum_sig = mb.add_vararg_func_type(vec![Ty::I64], vec![Ty::I64]);
    let sum = mb.declare_function("sum_i64", sum_sig);
    let caller_sig = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("caller", caller_sig);
    let entry = fb.create_block();
    let normal = fb.create_block();
    let unwind = fb.create_block();
    fb.switch_to_block(entry);
    let count = fb.iconst(Ty::I64, 2);
    let a = fb.iconst(Ty::I64, 30);
    let b = fb.iconst(Ty::I64, 12);
    let total = fb.invoke(sum, vec![count, a, b], normal, vec![], unwind);
    fb.switch_to_block(normal);
    fb.ret(vec![total]);
    fb.switch_to_block(unwind);
    let (exn, _) = fb.landingpad(true, vec![]);
    fb.resume(exn);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), vec![]);
    let host = SumHost::default();
    let (returns, host_calls) = run(&module, "caller", Some(&host)).expect("host-assisted run");
    assert_eq!(as_i128(&returns[0]), 44);
    assert_eq!(host_calls, 1);
    assert_eq!(
        *host.seen.lock().unwrap(),
        vec![vec![Ty::I64, Ty::I64, Ty::I64]]
    );
}

/// A variadic declaration as the ENTRY: the embedder's arguments beyond the
/// fixed prefix reach the host, and an entry short of the prefix is refused
/// exactly as a call site would be.
#[test]
fn a_variadic_declaration_as_the_entry_is_a_host_call_with_the_tail() {
    let (module, sum) = declaration_module();
    let host = SumHost::default();
    let i64v = |v: i128| InterpretValue::int(Ty::I64, v).unwrap();
    let outcome = Interpreter::with_module(&module)
        .with_host(&host)
        .execute_func(sum, vec![i64v(2), i64v(7), i64v(9)])
        .expect("host-assisted entry");
    assert_eq!(as_i128(&outcome.returns[0]), 18);
    assert_eq!(outcome.host_calls, 1);
    assert_eq!(
        *host.seen.lock().unwrap(),
        vec![vec![Ty::I64, Ty::I64, Ty::I64]]
    );
    let short = Interpreter::with_module(&module)
        .with_host(&host)
        .execute_func(sum, vec![]);
    assert_refused(
        &short,
        InterpretErrorCode::SignatureMismatch,
        "variadic callee expects at least 1, got 0",
    );
}

/// Poison in the variadic tail is undefined behaviour at the call, never a
/// value the host is handed: a `PartialBytes` load result (uninitialized
/// stack bytes) passed as a variadic argument is refused before the host runs.
#[test]
fn poison_in_a_variadic_tail_is_undefined_behaviour_before_the_host_runs() {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_15_vararg_poison", target());
    let sum_sig = mb.add_vararg_func_type(vec![Ty::I64], vec![Ty::I64]);
    let sum = mb.declare_function("sum_i64", sum_sig);
    let caller_sig = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("caller", caller_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let slot = fb.alloca(Ty::I64);
    let junk = fb.load(Ty::I64, slot);
    let count = fb.iconst(Ty::I64, 1);
    let total = fb.call(sum, vec![count, junk]);
    fb.ret(vec![total]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), vec![]);
    let host = SumHost::default();
    assert_refused(
        &run(&module, "caller", Some(&host)),
        InterpretErrorCode::UndefinedBehavior,
        "Call arguments: use of an uninitialized value",
    );
    assert!(host.seen.lock().unwrap().is_empty());
}

/// Variadicity agreeing is not enough: the pointer type `(i32, ...) -> i64`
/// over the declaration `sum_i64(i64, ...) -> i64` disagrees on the FIXED
/// prefix, and the ordinary signature rule refuses it before the host sees a
/// single argument — the new variadic-declaration path opens no bypass of
/// the parameter-list check.
#[test]
fn a_variadic_pointer_with_a_different_fixed_prefix_is_signature_mismatch() {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_15_vararg_ptr_prefix", target());
    let callee_sig = mb.add_vararg_func_type(vec![Ty::I64], vec![Ty::I64]);
    let pointer_sig = mb.add_vararg_func_type(vec![Ty::I32], vec![Ty::I64]);
    let sum = mb.declare_function("sum_i64", callee_sig);
    let caller_sig = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("caller", caller_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let pointer = fb.fn_addr(pointer_sig, sum);
    let count = fb.iconst(Ty::I32, 1);
    let x = fb.iconst(Ty::I64, 5);
    let out = fb.call_indirect(pointer, pointer_sig, vec![count, x]);
    fb.ret(vec![out]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(!validate_module(&module).is_empty());
    let host = SumHost::default();
    let result = run(&module, "caller", Some(&host));
    assert_refused(
        &result,
        InterpretErrorCode::SignatureMismatch,
        "CallIndirect: indirect call signature mismatch",
    );
    assert!(
        host.seen.lock().unwrap().is_empty(),
        "the host must never be reached through a pointer type whose fixed prefix disagrees"
    );
}

// ─────────────────── second review: adversarial shapes ───────────────────

/// A handle hidden one level down — inside a TUPLE in the variadic tail — is
/// the same forgery as a bare one: the tail check walks the value
/// (`first_handle`), so wrapping the handle in an aggregate is no bypass of
/// the exact-typed-transport rule.
#[test]
fn a_handle_nested_in_a_variadic_tail_aggregate_is_a_type_error() {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_15_vararg_handle_nested", target());
    let handle_ty = Ty::Handle(Box::new(handle()));
    let mk_sig = mb.add_func_type(vec![Ty::U64], vec![handle_ty.clone()]);
    let mk = mb.declare_function("mk_h", mk_sig);
    let sum_sig = mb.add_vararg_func_type(vec![Ty::I64], vec![Ty::I64]);
    let sum = mb.declare_function("sum_i64", sum_sig);
    let caller_sig = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("caller", caller_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let seven = fb.uconst(Ty::U64, 7);
    let h = fb.call(mk, vec![seven]);
    let lane = fb.iconst(Ty::I32, 5);
    let pair = fb.make_aggregate(Ty::Tuple(vec![Ty::I32, handle_ty]), vec![lane, h]);
    let count = fb.iconst(Ty::I64, 1);
    let total = fb.call(sum, vec![count, pair]);
    fb.ret(vec![total]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_refused(
        &run(&module, "caller", Some(&MintHost)),
        InterpretErrorCode::TypeError,
        "variadic argument 1 carries a runtime handle",
    );
}

// ───────────── the WS2.13 interaction: pinned fixed-arity entry points ─────────────

/// `f() -> u8 { clean_inc(HeapAlloc(CleanHeap)); 0 }` with `clean_inc`
/// declared with `params` (the pinned entry is the fixed-arity
/// `(ptr) -> ()`), the pointer passed once per fixed parameter and at least
/// once. With `cc` set, the declaration's calling convention is overwritten
/// after building.
fn clean_inc_module(params: Vec<Ty>, vararg: bool, cc: Option<trust_ir::CallingConv>) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_15_vararg_pinned_rc", target());
    let nargs = params.len().max(1);
    let inc_sig = if vararg {
        mb.add_vararg_func_type(params, vec![])
    } else {
        mb.add_func_type(params, vec![])
    };
    let inc = mb.declare_function("clean_inc", inc_sig);
    let sig = mb.add_func_type(vec![], vec![Ty::U8]);
    let mut fb = mb.function("f", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let cell = fb.heap_alloc(Ty::U64, None, None, trust_ir::inst::AllocOrigin::CleanHeap);
    fb.call_void(inc, vec![cell; nargs]);
    let zero = fb.uconst(Ty::U8, 0);
    fb.ret(vec![zero]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    if let Some(cc) = cc {
        module
            .functions
            .iter_mut()
            .find(|f| f.name == "clean_inc")
            .unwrap()
            .calling_conv = cc;
    }
    module
}

/// WS2.15 made a variadic declaration a host call. That must not turn a
/// VARIADIC FORGERY of a pinned fixed-arity entry point into "no host model":
/// the pinned host models `clean_inc` (and every `trust_bignum_nat_*` entry)
/// at a fixed arity, so a variadic declaration of it is `SignatureMismatch`,
/// "non-executable vararg signature", whether the fixed prefix is the pinned
/// one or not. The WS2.13 classification of every OTHER mis-declaration
/// (a wrong fixed arity, a non-C convention) stays `UnsupportedCall`, no
/// host model. The same variadic forgery is also still that with no host at
/// all, because WS2.15's no-host rule is unchanged.
#[test]
fn a_variadic_declaration_of_a_pinned_fixed_arity_entry_is_signature_mismatch() {
    let pinned = trust_ir_build::PinnedHandleHost::new();
    let reason = "non-executable vararg signature";

    // The pinned fixed prefix `(ptr, ...)`, and a wrong fixed arity `(...)`
    // with the pointer in the variadic tail: both forged, both named.
    for params in [vec![Ty::Ptr], vec![]] {
        let module = clean_inc_module(params.clone(), true, None);
        let result = run(&module, "f", Some(&pinned));
        assert_refused(&result, InterpretErrorCode::SignatureMismatch, reason);
        assert_eq!(
            result.unwrap_err().unhosted_callee(),
            None,
            "a modelled symbol is never reported as unhosted ({params:?}, ...)"
        );
        // No host: the WS2.15 host-call refusal, unchanged.
        assert_refused(
            &run(&module, "f", None),
            InterpretErrorCode::UnsupportedCall,
            "call to bodyless declaration @clean_inc: no host model",
        );
    }

    // A Nat handle entry declared variadic is the same forgery. The exact
    // twin runs, so the refusal is the variadic flag and nothing else.
    let nat = trust_ir_build::TRUSTED_HANDLE_RUNTIMES
        .iter()
        .find(|pin| pin.runtime == "trust_bignum::Nat")
        .expect("the Nat row is pinned")
        .handle_ty();
    let nat_module = |vararg: bool| {
        let mut mb = ModuleBuilder::new_with_target_info("ws2_15_vararg_pinned_nat", target());
        let from_sig = if vararg {
            mb.add_vararg_func_type(vec![Ty::U64], vec![nat.clone()])
        } else {
            mb.add_func_type(vec![Ty::U64], vec![nat.clone()])
        };
        let from_u64 = mb.declare_function("trust_bignum_nat_from_u64", from_sig);
        let drop_sig = mb.add_func_type(vec![nat.clone()], vec![]);
        let release = mb.declare_function("trust_bignum_nat_drop", drop_sig);
        let sig = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("f", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let one = fb.uconst(Ty::U64, 1);
        let h = fb.call(from_u64, vec![one]);
        fb.call_void(release, vec![h]);
        fb.ret(vec![]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    assert_refused(
        &run(&nat_module(true), "f", Some(&pinned)),
        InterpretErrorCode::SignatureMismatch,
        reason,
    );
    let (_, host_calls) = run(&nat_module(false), "f", Some(&pinned)).expect("the exact twin runs");
    assert_eq!(host_calls, 2);

    // Controls: the WS2.13 classification of the other mis-declarations.
    // A non-variadic wrong arity is not served, and is reported as unhosted.
    let wrong_arity = clean_inc_module(vec![Ty::Ptr, Ty::Ptr], false, None);
    let result = run(&wrong_arity, "f", Some(&pinned));
    assert_refused(
        &result,
        InterpretErrorCode::UnsupportedCall,
        "call to bodyless declaration @clean_inc: no host model",
    );
    assert_eq!(result.unwrap_err().unhosted_callee(), Some("clean_inc"));
    // A variadic `clean_inc` at a NON-pinned convention is not the pinned
    // entry point at all, exactly as its fixed-arity twin (WS2.13).
    assert_refused(
        &run(
            &clean_inc_module(vec![Ty::Ptr], true, Some(trust_ir::CallingConv::Rust)),
            "f",
            Some(&pinned),
        ),
        InterpretErrorCode::UnsupportedCall,
        "call to bodyless declaration @clean_inc: no host model",
    );
    // A variadic declaration the pinned host does NOT model by name is an
    // ordinary unserved host call: the rule is not "variadic + any host".
    let (module, _) = declaration_module();
    assert_refused(
        &run(&module, "caller", Some(&pinned)),
        InterpretErrorCode::UnsupportedCall,
        "call to bodyless declaration @sum_i64: no host model",
    );
    // Control: the exact pinned declaration executes.
    let (_, host_calls) = run(
        &clean_inc_module(vec![Ty::Ptr], false, None),
        "f",
        Some(&pinned),
    )
    .expect("the exact pinned `clean_inc` runs");
    assert_eq!(host_calls, 1);
}

/// A host that claims a symbol at a fixed arity is never ASKED to serve a
/// variadic declaration of it: the refusal comes first, so a host that would
/// happily have served the call (here, `SumHost` behind the claim) records
/// nothing.
#[test]
fn a_fixed_arity_claim_is_refused_before_the_host_serves() {
    struct Claims(SumHost);
    impl HostCalls for Claims {
        fn call(
            &self,
            callee: &Function,
            sig: &FuncTy,
            args: &[InterpretValue],
            host: &mut HostState,
        ) -> Option<InterpretResult<Vec<InterpretValue>>> {
            self.0.call(callee, sig, args, host)
        }
        fn models_fixed_arity(&self, callee: &Function) -> bool {
            callee.name == "sum_i64"
        }
    }
    let (module, _) = declaration_module();
    let host = Claims(SumHost::default());
    assert_refused(
        &run(&module, "caller", Some(&host)),
        InterpretErrorCode::SignatureMismatch,
        "the installed host models @sum_i64 as a fixed-arity entry point",
    );
    assert!(
        host.0.seen.lock().unwrap().is_empty(),
        "the host must never serve a variadic declaration of a fixed-arity symbol"
    );
}
