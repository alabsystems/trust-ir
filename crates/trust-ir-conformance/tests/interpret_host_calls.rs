// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS2.12 (closes the hook half of F-035): the reference interpreter's
// host-call hook.
//
// Before: a call to a bodyless declaration ENTERED it and trapped
// `MissingBlock: block 0 not found` — a structural code on a module the
// validator accepts, which is exactly what `interpret_differential.rs`'s
// property 2 says must never happen. Now a declaration is executed only by an
// installed `HostCalls` model, and is otherwise `UnsupportedCall` with a named
// reason. A host is a TRUSTED model (TRUST.md item 9), so every run it serves
// is counted in `InterpretOutcome::host_calls`.
//
// Every host model in this file is a TEST model. None of them is a reference
// model of a real runtime; they exist to exercise the hook's checks.

use trust_ir::interpret::{
    HostCalls, HostState, InterpretError, InterpretErrorCode, InterpretResult, InterpretValue,
    InterpretValueKind, Interpreter,
};
use trust_ir::ty::FuncTy;
use trust_ir::{
    BinOp, Constant, Endianness, FuncId, Function, HandleTy, Module, StructPassingPolicy,
    TargetInfo, Ty,
};
use trust_ir_build::{ModuleBuilder, TRUSTED_HANDLE_RUNTIMES, validate_module};

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn u64_value(value: u64) -> InterpretValue {
    InterpretValue::int(Ty::U64, i128::from(value)).expect("u64 is an integer type")
}

fn as_u64(value: &InterpretValue) -> u64 {
    u64::try_from(value.as_int().expect("an integer value").as_unsigned()).expect("fits in u64")
}

fn run(module: &Module, entry: &str, host: Option<&dyn HostCalls>) -> InterpretResult<RunOk> {
    let function = module
        .function_by_name(entry)
        .unwrap_or_else(|| panic!("no function @{entry}"));
    let mut interpreter = Interpreter::with_module(module);
    if let Some(host) = host {
        interpreter = interpreter.with_host(host);
    }
    interpreter
        .execute_function(function, Vec::new())
        .map(|outcome| RunOk {
            returns: outcome.returns,
            host_calls: outcome.host_calls,
        })
}

#[derive(Debug)]
struct RunOk {
    returns: Vec<InterpretValue>,
    host_calls: u64,
}

fn assert_refused(result: &InterpretResult<RunOk>, code: InterpretErrorCode, reason: &str) {
    match result {
        Ok(ok) => panic!(
            "expected {code:?} ({reason}), but the run returned {:?}",
            ok.returns
        ),
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

// ───────────────────────── @ext_add(u64, u64) -> u64 ─────────────────────────

/// `ext_add(u64, u64) -> u64` declared bodyless; `caller() -> u64 { ext_add(40, 2) }`.
fn ext_add_module() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_12_ext_add", target());
    let add_sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let ext_add = mb.declare_function("ext_add", add_sig);
    let caller_sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("caller", caller_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let a = fb.uconst(Ty::U64, 40);
    let b = fb.uconst(Ty::U64, 2);
    let sum = fb.call(ext_add, vec![a, b]);
    fb.ret(vec![sum]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A unit host modelling `@ext_add` as wrapping `u64` addition. What it
/// returns for `@ext_add` is configurable so the same host can be buggy.
enum AddHost {
    Honest,
    /// Returns an `i32` for the `-> u64` declaration.
    WrongType,
    /// Returns a value TYPED `u64` whose payload is a 32-bit integer.
    WrongKind,
    /// Returns a value TYPED `u64` whose payload is a null pointer.
    Pointer,
    /// Registered, but declines every call.
    Declines,
}

impl HostCalls for AddHost {
    fn call(
        &self,
        callee: &Function,
        _sig: &FuncTy,
        args: &[InterpretValue],
        _host: &mut HostState,
    ) -> Option<InterpretResult<Vec<InterpretValue>>> {
        if callee.name != "ext_add" {
            return None;
        }
        let sum = as_u64(&args[0]).wrapping_add(as_u64(&args[1]));
        Some(Ok(vec![match self {
            AddHost::Honest => u64_value(sum),
            AddHost::WrongType => InterpretValue::int(Ty::I32, i128::from(sum)).unwrap(),
            AddHost::WrongKind => InterpretValue {
                ty: Ty::U64,
                kind: InterpretValue::int(Ty::U32, i128::from(sum)).unwrap().kind,
            },
            AddHost::Pointer => InterpretValue {
                ty: Ty::U64,
                kind: InterpretValueKind::NullPtr,
            },
            AddHost::Declines => return None,
        }]))
    }
}

#[test]
fn ws2_12_unit_host_executes_an_ext_add_caller() {
    let module = ext_add_module();
    assert_eq!(validate_module(&module), vec![]);
    let ok = run(&module, "caller", Some(&AddHost::Honest)).expect("host-assisted run");
    assert_eq!(ok.returns.len(), 1);
    assert_eq!(ok.returns[0].ty, Ty::U64);
    assert_eq!(as_u64(&ok.returns[0]), 42);
    // The run is marked host-assisted, and counted by the interpreter.
    assert_eq!(ok.host_calls, 1);
}

#[test]
fn ws2_12_without_a_host_a_declaration_call_is_unsupported_call_not_missing_block() {
    let module = ext_add_module();
    assert_eq!(validate_module(&module), vec![]);
    let result = run(&module, "caller", None);
    assert_refused(
        &result,
        InterpretErrorCode::UnsupportedCall,
        "call to bodyless declaration @ext_add: no host model (declarations are not \
         executable in-format)",
    );
}

#[test]
fn ws2_12_a_host_returning_i32_for_a_u64_declaration_is_signature_mismatch() {
    let result = run(&ext_add_module(), "caller", Some(&AddHost::WrongType));
    assert_refused(
        &result,
        InterpretErrorCode::SignatureMismatch,
        "Call returns type mismatch at argument 0: expected u64, got i32",
    );
}

#[test]
fn ws2_12_a_host_that_declines_still_gives_unsupported_call() {
    let result = run(&ext_add_module(), "caller", Some(&AddHost::Declines));
    assert_refused(
        &result,
        InterpretErrorCode::UnsupportedCall,
        "@ext_add: no host model",
    );
}

#[test]
fn ws2_12_a_host_cannot_smuggle_a_value_that_does_not_inhabit_its_type() {
    // Typed `u64`, so the declared-type check passes; the payload is 32-bit.
    let result = run(&ext_add_module(), "caller", Some(&AddHost::WrongKind));
    assert_refused(
        &result,
        InterpretErrorCode::TypeError,
        "host result 0 is not a well-formed u64 value",
    );
    // A pointer-kind payload is refused the same way.
    let result = run(&ext_add_module(), "caller", Some(&AddHost::Pointer));
    assert_refused(
        &result,
        InterpretErrorCode::TypeError,
        "host result 0 is not a well-formed u64 value",
    );
}

/// A host may return only integer, bool, f32/f64, unit and handle values: it
/// has no interpreter memory, so a pointer it returned would carry forged
/// provenance. A `-> ptr` declaration is refused even when the host's value is
/// the one pointer with no provenance to forge (null).
#[test]
fn ws2_12_a_host_may_not_return_a_pointer_typed_result() {
    struct NullHost;
    impl HostCalls for NullHost {
        fn call(
            &self,
            _callee: &Function,
            _sig: &FuncTy,
            _args: &[InterpretValue],
            _host: &mut HostState,
        ) -> Option<InterpretResult<Vec<InterpretValue>>> {
            Some(Ok(vec![InterpretValue {
                ty: Ty::Ptr,
                kind: InterpretValueKind::NullPtr,
            }]))
        }
    }
    let mut mb = ModuleBuilder::new_with_target_info("ws2_12_ptr", target());
    let sig = mb.add_func_type(vec![], vec![Ty::Ptr]);
    let ext_ptr = mb.declare_function("ext_ptr", sig);
    let mut fb = mb.function("caller", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let p = fb.call(ext_ptr, vec![]);
    fb.ret(vec![p]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), vec![]);
    assert_refused(
        &run(&module, "caller", Some(&NullHost)),
        InterpretErrorCode::UnsupportedCall,
        "host result 0 has type ptr, which a host model may not return",
    );
}

/// `InterpretError::unhosted_callee` names the declaration a run could not
/// enter for want of a host model (the `trust-ir run` named refusal at a
/// pinned trusted-runtime entry point reads it), and nothing else: the same
/// `UnsupportedCall` code for another reason (a host returning a pointer), a
/// host's own verdict, and a signature mismatch all answer `None`.
#[test]
fn ws2_12_unhosted_callee_names_only_the_no_host_model_refusal() {
    let module = ext_add_module();
    let no_host = run(&module, "caller", None).expect_err("no host");
    assert_eq!(no_host.unhosted_callee(), Some("ext_add"));
    let declined = run(&module, "caller", Some(&AddHost::Declines)).expect_err("declines");
    assert_eq!(declined.unhosted_callee(), Some("ext_add"));
    let entered = Interpreter::with_module(&module)
        .execute_function(
            module.function_by_name("ext_add").unwrap(),
            vec![u64_value(1), u64_value(2)],
        )
        .expect_err("bodyless entry, no host");
    assert_eq!(entered.unhosted_callee(), Some("ext_add"));

    // Mutation controls: every other refusal answers `None`.
    let mismatch = run(&module, "caller", Some(&AddHost::WrongType)).expect_err("i32 result");
    assert_eq!(mismatch.code, InterpretErrorCode::SignatureMismatch);
    assert_eq!(mismatch.unhosted_callee(), None);
    let ill_kinded = run(&module, "caller", Some(&AddHost::WrongKind)).expect_err("ill-kinded");
    assert_eq!(ill_kinded.unhosted_callee(), None);
    let forged = InterpretError::new(
        InterpretErrorCode::UnsupportedCall,
        "host result 0 has type ptr, which a host model may not return",
    );
    assert_eq!(forged.unhosted_callee(), None);
    let other_code = InterpretError::new(
        InterpretErrorCode::UndefinedBehavior,
        "call to bodyless declaration @ext_add: no host model (declarations are not \
         executable in-format)",
    );
    assert_eq!(other_code.unhosted_callee(), None);
}

/// A bodyless ENTRY point is a host call too, never `MissingBlock`.
#[test]
fn ws2_12_executing_a_declaration_directly_is_a_host_call() {
    let module = ext_add_module();
    let ext_add = module.function_by_name("ext_add").unwrap();
    let args = || vec![u64_value(5), u64_value(6)];

    let refused = Interpreter::with_module(&module)
        .execute_function(ext_add, args())
        .expect_err("no host");
    assert_eq!(refused.code, InterpretErrorCode::UnsupportedCall);
    assert!(refused.message.contains("no host model"), "{refused}");

    let outcome = Interpreter::with_module(&module)
        .with_host(&AddHost::Honest)
        .execute_function(ext_add, args())
        .expect("host-assisted");
    assert_eq!(as_u64(&outcome.returns[0]), 11);
    assert_eq!(outcome.host_calls, 1);

    // The arguments are still checked against the declaration first.
    let wrong = Interpreter::with_module(&module)
        .with_host(&AddHost::Honest)
        .execute_function(ext_add, vec![u64_value(5), InterpretValue::bool(true)])
        .expect_err("ill-typed argument");
    assert_eq!(wrong.code, InterpretErrorCode::SignatureMismatch);
}

/// Mutation control for the counter: an in-format run reports zero host calls.
#[test]
fn ws2_12_an_in_format_run_reports_zero_host_calls() {
    let mut mb = ModuleBuilder::new("ws2_12_in_format");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("f", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let a = fb.uconst(Ty::U64, 40);
    let b = fb.uconst(Ty::U64, 2);
    let sum = fb.binop(BinOp::Add, Ty::U64, a, b);
    fb.ret(vec![sum]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    // A host is installed but never consulted: there is no declaration.
    let ok = run(&module, "f", Some(&AddHost::Honest)).unwrap();
    assert_eq!(as_u64(&ok.returns[0]), 42);
    assert_eq!(ok.host_calls, 0);
}

// ────────────── ported ratchet row (proof program Part B, b7:1636) ──────────────

/// `b7.nondet.extern_nondet_call_is_unexecutable` — its shape FLIPPED by
/// WS2.12. The Kani-style carrier (a call to a bodyless `nondet_u64()`
/// declaration) validates and round-trips, and the interpreter now refuses it
/// with the named `UnsupportedCall` (fail-closed) instead of entering the
/// declaration and trapping `MissingBlock "block 0 not found"`. The ledger row
/// of the same name (`two_language/RATCHETS.tsv`, target b7) stays a GAP held
/// at this exact refusal: F-034 (no typed nondeterministic choice) is closed by
/// WS2.10/WS2.11, not by the hook.
#[test]
fn b7_nondet_extern_nondet_call_is_unexecutable() {
    let mut mb = ModuleBuilder::new_with_target_info("b7_nondet", target());
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let nondet = mb.declare_function("nondet_u64", ft);
    let mut fb = mb.function("pick", ft);
    fb.set_producer(trust_ir::Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let v = fb.call(nondet, vec![]);
    let one = fb.uconst(Ty::U64, 1);
    let out = fb.binop(BinOp::And, Ty::U64, v, one);
    fb.ret(vec![out]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    assert_eq!(validate_module(&module), vec![]);
    let bytes =
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(
        trust_ir::binary::deserialize_module(&bytes).expect("binary round trip"),
        module
    );
    let result = run(&module, "pick", None);
    assert_refused(
        &result,
        InterpretErrorCode::UnsupportedCall,
        "call to bodyless declaration @nondet_u64: no host model",
    );
    let Err(error) = result else { unreachable!() };
    assert_ne!(error.code, InterpretErrorCode::MissingBlock);
}

// ───────────────────────────── runtime handles ─────────────────────────────

fn handle_a() -> HandleTy {
    HandleTy::new("A", "test_a::A")
}

fn handle_b() -> HandleTy {
    HandleTy::new("B", "test_b::B")
}

fn ty(handle: HandleTy) -> Ty {
    Ty::Handle(Box::new(handle))
}

/// A test host model of a runtime whose handles carry a `u64`: `<p>_mk(u64)`
/// mints, `<p>_get(handle) -> u64` reads, `<p>_drop(handle)` releases. The
/// model resolves every handle argument against ITS OWN `HandleTy`, which is
/// what closes cross-runtime confusion (review item (ii)).
struct BoxModel {
    prefix: &'static str,
    handle: HandleTy,
}

impl HostCalls for BoxModel {
    fn call(
        &self,
        callee: &Function,
        _sig: &FuncTy,
        args: &[InterpretValue],
        host: &mut HostState,
    ) -> Option<InterpretResult<Vec<InterpretValue>>> {
        let role = callee.name.strip_prefix(self.prefix)?.strip_prefix('_')?;
        Some(match role {
            "mk" => host
                .mint_handle(self.handle.clone(), self.prefix, as_u64(&args[0]))
                .map(|handle| vec![handle]),
            "get" => host
                .handle::<u64>(&args[0], &self.handle, self.prefix)
                .map(|payload| vec![u64_value(*payload)]),
            "drop" => host
                .release_handle(&args[0], &self.handle, self.prefix)
                .map(|()| vec![]),
            _ => return None,
        })
    }
}

/// Two models behind one host: the first that claims a callee serves it.
struct Both([BoxModel; 2]);

impl Both {
    fn new() -> Self {
        Both([
            BoxModel {
                prefix: "a",
                handle: handle_a(),
            },
            BoxModel {
                prefix: "b",
                handle: handle_b(),
            },
        ])
    }
}

impl HostCalls for Both {
    fn call(
        &self,
        callee: &Function,
        sig: &FuncTy,
        args: &[InterpretValue],
        host: &mut HostState,
    ) -> Option<InterpretResult<Vec<InterpretValue>>> {
        self.0
            .iter()
            .find_map(|model| model.call(callee, sig, args, host))
    }
}

/// Builder for the handle probes: declares `a_mk/a_get/a_drop` at handle A,
/// `b_mk/b_drop` at handle B, and `b_get` at `b_get_param` (handle B for the
/// honest spelling, handle A for the mis-declared one a module can write
/// without validation). The body is supplied by `body`.
fn handle_module(
    b_get_param: HandleTy,
    returns: Vec<Ty>,
    body: impl FnOnce(&mut trust_ir_build::FunctionBuilder<'_>, &Decls) -> Vec<trust_ir::ValueId>,
) -> Module {
    let mut mb = ModuleBuilder::new("ws2_12_handles");
    let mk_a = mb.add_func_type(vec![Ty::U64], vec![ty(handle_a())]);
    let mk_b = mb.add_func_type(vec![Ty::U64], vec![ty(handle_b())]);
    let get_a = mb.add_func_type(vec![ty(handle_a())], vec![Ty::U64]);
    let get_b = mb.add_func_type(vec![ty(b_get_param)], vec![Ty::U64]);
    let drop_a = mb.add_func_type(vec![ty(handle_a())], vec![]);
    let decls = Decls {
        a_mk: mb.declare_function("a_mk", mk_a),
        a_get: mb.declare_function("a_get", get_a),
        a_drop: mb.declare_function("a_drop", drop_a),
        b_mk: mb.declare_function("b_mk", mk_b),
        b_get: mb.declare_function("b_get", get_b),
    };
    let sig = mb.add_func_type(vec![], returns);
    let mut fb = mb.function("probe", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let values = body(&mut fb, &decls);
    fb.ret(values);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

struct Decls {
    a_mk: FuncId,
    a_get: FuncId,
    a_drop: FuncId,
    b_mk: FuncId,
    b_get: FuncId,
}

/// Positive: a handle is minted, transported by `copy`, `select` and a call,
/// and read back by its own model.
#[test]
fn ws2_12_a_handle_round_trips_through_the_transport_set() {
    let module = handle_module(handle_b(), vec![Ty::U64], |fb, d| {
        let seven = fb.uconst(Ty::U64, 7);
        let nine = fb.uconst(Ty::U64, 9);
        let h7 = fb.call(d.a_mk, vec![seven]);
        let h9 = fb.call(d.a_mk, vec![nine]);
        let copied = fb.copy(ty(handle_a()), h9);
        let cond = fb.bool_const(false);
        let chosen = fb.select(ty(handle_a()), cond, h7, copied);
        vec![fb.call(d.a_get, vec![chosen])]
    });
    let ok = run(&module, "probe", Some(&Both::new())).expect("transport-only use");
    assert_eq!(as_u64(&ok.returns[0]), 9);
    assert_eq!(ok.host_calls, 3);
}

/// Review item (i): ids come from ONE counter shared by every model.
#[test]
fn ws2_12_handle_ids_are_unique_across_models() {
    let module = handle_module(handle_b(), vec![ty(handle_a()), ty(handle_b())], |fb, d| {
        let one = fb.uconst(Ty::U64, 1);
        let a = fb.call(d.a_mk, vec![one]);
        let b = fb.call(d.b_mk, vec![one]);
        vec![a, b]
    });
    let ok = run(&module, "probe", Some(&Both::new())).unwrap();
    let ids: Vec<_> = ok
        .returns
        .iter()
        .map(|value| match value.kind {
            InterpretValueKind::Handle { id } => id,
            ref other => panic!("not a handle: {other:?}"),
        })
        .collect();
    assert_eq!(ids.len(), 2);
    assert_ne!(ids[0], ids[1], "two live handles share an id");
    assert_eq!(ok.returns[0].ty, ty(handle_a()));
    assert_eq!(ok.returns[1].ty, ty(handle_b()));
}

/// Review item (ii): model A's handle reaching model B's entry point is
/// undefined behaviour, even when the module MIS-DECLARES `b_get` to take a
/// handle A (so the call-boundary type check alone cannot catch it).
#[test]
fn ws2_12_model_a_handle_passed_to_model_b_is_undefined_behavior() {
    let confused = handle_module(handle_a(), vec![Ty::U64], |fb, d| {
        let one = fb.uconst(Ty::U64, 1);
        let a = fb.call(d.a_mk, vec![one]);
        vec![fb.call(d.b_get, vec![a])]
    });
    assert_refused(
        &run(&confused, "probe", Some(&Both::new())),
        InterpretErrorCode::UndefinedBehavior,
        "handle of runtime test_a::A passed to test_b::B",
    );

    // Review item (iii): with the honest declaration the call boundary refuses
    // it first, because the handle's type is the one it was minted at.
    let honest = handle_module(handle_b(), vec![Ty::U64], |fb, d| {
        let one = fb.uconst(Ty::U64, 1);
        let a = fb.call(d.a_mk, vec![one]);
        vec![fb.call(d.b_get, vec![a])]
    });
    assert_refused(
        &run(&honest, "probe", Some(&Both::new())),
        InterpretErrorCode::SignatureMismatch,
        "Call arguments type mismatch at argument 0",
    );

    // Mutation control: model B's own handle at the honest declaration runs.
    let own = handle_module(handle_b(), vec![Ty::U64], |fb, d| {
        let five = fb.uconst(Ty::U64, 5);
        let b = fb.call(d.b_mk, vec![five]);
        vec![fb.call(d.b_get, vec![b])]
    });
    let ok = run(&own, "probe", Some(&Both::new())).expect("own handle");
    assert_eq!(as_u64(&ok.returns[0]), 5);
}

/// Mutation control: a handle fed to `add` is a `TypeError` — the refusal is
/// caused by the non-transport use, since the twin that only transports the
/// same handle runs.
#[test]
fn ws2_12_a_handle_fed_to_add_is_a_type_error() {
    let added = handle_module(handle_b(), vec![Ty::U64], |fb, d| {
        let one = fb.uconst(Ty::U64, 1);
        let a = fb.call(d.a_mk, vec![one]);
        vec![fb.binop(BinOp::Add, Ty::U64, a, one)]
    });
    let result = run(&added, "probe", Some(&Both::new()));
    assert_refused(
        &result,
        InterpretErrorCode::TypeError,
        "expected value of type u64, got handle<\"A\", \"test_a::A\">",
    );
    // Spelled at the handle's own type the operand types agree, and the
    // handle's KIND is what refuses it: a handle is not an integer.
    let added_at_handle = handle_module(handle_b(), vec![ty(handle_a())], |fb, d| {
        let one = fb.uconst(Ty::U64, 1);
        let a = fb.call(d.a_mk, vec![one]);
        vec![fb.binop(BinOp::Add, ty(handle_a()), a, a)]
    });
    assert_refused(
        &run(&added_at_handle, "probe", Some(&Both::new())),
        InterpretErrorCode::TypeError,
        "expected integer value, got handle",
    );

    let transported = handle_module(handle_b(), vec![Ty::U64], |fb, d| {
        let one = fb.uconst(Ty::U64, 1);
        let a = fb.call(d.a_mk, vec![one]);
        let a2 = fb.copy(ty(handle_a()), a);
        vec![fb.call(d.a_get, vec![a2])]
    });
    assert!(run(&transported, "probe", Some(&Both::new())).is_ok());
}

/// A handle cannot be placed in an aggregate (outside the transport set).
#[test]
fn ws2_12_a_handle_inserted_into_an_aggregate_is_a_type_error() {
    let pair = Ty::Tuple(vec![Ty::U64, Ty::U64]);
    let module = handle_module(handle_b(), vec![pair.clone()], |fb, d| {
        let one = fb.uconst(Ty::U64, 1);
        let a = fb.call(d.a_mk, vec![one]);
        let base = fb.const_value(
            pair.clone(),
            Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]),
        );
        vec![fb.insert_field(pair.clone(), base, 1, a)]
    });
    assert_refused(
        &run(&module, "probe", Some(&Both::new())),
        InterpretErrorCode::TypeError,
        "InsertField: a runtime handle",
    );
}

/// WS3.6 (F-047, aggregate half), as the REFERENCE INTERPRETER runs it. The
/// validator now admits a handle in a struct/tuple lane; the interpreter
/// executes the build (`make_aggregate`) and the exact-typed projection
/// (`extract_field`), and the minted handle comes back out intact. It still
/// refuses `insert_field` of a runtime handle even at the lane's exact type —
/// the fail-closed divergence `docs/SPEC_RATIFICATIONS.md` §7 records (the
/// interpreter refuses MORE than the validator admits, never less). This test
/// pins both halves, so the divergence cannot close or widen unnoticed.
#[test]
fn ws3_6_a_handle_lane_is_built_and_projected_but_not_rewritten_in_place() {
    let pair = Ty::Tuple(vec![Ty::U64, ty(handle_a())]);
    let built = handle_module(handle_b(), vec![Ty::U64], |fb, d| {
        let seven = fb.uconst(Ty::U64, 7);
        let h = fb.call(d.a_mk, vec![seven]);
        let agg = fb.make_aggregate(pair.clone(), vec![seven, h]);
        let back = fb.extract_field(ty(handle_a()), agg, 1);
        vec![fb.call(d.a_get, vec![back])]
    });
    let ok = run(&built, "probe", Some(&Both::new())).expect("build + exact projection");
    assert_eq!(as_u64(&ok.returns[0]), 7);
    assert_eq!(ok.host_calls, 2);

    let rewritten = handle_module(handle_b(), vec![Ty::U64], |fb, d| {
        let seven = fb.uconst(Ty::U64, 7);
        let nine = fb.uconst(Ty::U64, 9);
        let h7 = fb.call(d.a_mk, vec![seven]);
        let h9 = fb.call(d.a_mk, vec![nine]);
        let agg = fb.make_aggregate(pair.clone(), vec![seven, h7]);
        let swapped = fb.insert_field(pair.clone(), agg, 1, h9);
        let back = fb.extract_field(ty(handle_a()), swapped, 1);
        vec![fb.call(d.a_get, vec![back])]
    });
    assert_refused(
        &run(&rewritten, "probe", Some(&Both::new())),
        InterpretErrorCode::TypeError,
        "InsertField: a runtime handle",
    );
}

/// The rest of the non-transport set: storing a handle (there is never an
/// in-memory handle image), comparing two handles, and casting one to an
/// integer are each a `TypeError`.
#[test]
fn ws2_12_a_handle_stored_compared_or_cast_is_a_type_error() {
    let stored = handle_module(handle_b(), vec![], |fb, d| {
        let one = fb.uconst(Ty::U64, 1);
        let a = fb.call(d.a_mk, vec![one]);
        let slot = fb.alloca(Ty::U64);
        fb.store(ty(handle_a()), slot, a);
        vec![]
    });
    assert_refused(
        &run(&stored, "probe", Some(&Both::new())),
        InterpretErrorCode::TypeError,
        "Store: a runtime handle",
    );

    let compared = handle_module(handle_b(), vec![Ty::Bool], |fb, d| {
        let one = fb.uconst(Ty::U64, 1);
        let a = fb.call(d.a_mk, vec![one]);
        vec![fb.icmp(trust_ir::ICmpOp::Eq, ty(handle_a()), a, a)]
    });
    let result = run(&compared, "probe", Some(&Both::new()));
    assert!(
        matches!(&result, Err(e) if e.code == InterpretErrorCode::TypeError),
        "ICmp over handles must be a TypeError, got {:?}",
        result.as_ref().map(|ok| &ok.returns)
    );

    let cast = handle_module(handle_b(), vec![Ty::U64], |fb, d| {
        let one = fb.uconst(Ty::U64, 1);
        let a = fb.call(d.a_mk, vec![one]);
        vec![fb.cast(trust_ir::CastOp::PtrToInt, ty(handle_a()), Ty::U64, a)]
    });
    let result = run(&cast, "probe", Some(&Both::new()));
    assert!(
        matches!(&result, Err(e) if e.code == InterpretErrorCode::TypeError),
        "PtrToInt of a handle must be a TypeError, got {:?}",
        result.as_ref().map(|ok| &ok.returns)
    );
}

/// A released handle is dead: reading it, or releasing it again, is UB.
#[test]
fn ws2_12_a_released_handle_is_dead() {
    let module = handle_module(handle_b(), vec![Ty::U64], |fb, d| {
        let one = fb.uconst(Ty::U64, 1);
        let a = fb.call(d.a_mk, vec![one]);
        fb.call_void(d.a_drop, vec![a]);
        vec![fb.call(d.a_get, vec![a])]
    });
    assert_refused(
        &run(&module, "probe", Some(&Both::new())),
        InterpretErrorCode::UndefinedBehavior,
        "used after release",
    );
}

/// A handle value forged outside a host (an entry argument no model minted)
/// is refused at the entry, BEFORE a host could mint a real handle under the
/// same id: `probe(h)` mints `a_mk(3)` (id 0) and then reads `h`, so an
/// embedder-built `Handle { id: 0 }` would otherwise alias it and read 3. The
/// same forged value nested in an aggregate argument is refused too, and a
/// forged value that reaches a host some other way is refused by the model.
#[test]
fn ws2_12_a_handle_never_minted_in_this_execution_is_undefined_behavior() {
    let mut mb = ModuleBuilder::new("ws2_12_forged");
    let mk_a = mb.add_func_type(vec![Ty::U64], vec![ty(handle_a())]);
    let get_a = mb.add_func_type(vec![ty(handle_a())], vec![Ty::U64]);
    let a_mk = mb.declare_function("a_mk", mk_a);
    let a_get = mb.declare_function("a_get", get_a);
    let mut fb = mb.function("probe", get_a);
    let entry = fb.create_block();
    let h = fb.add_block_param(entry, ty(handle_a()));
    fb.switch_to_block(entry);
    let three = fb.uconst(Ty::U64, 3);
    let _minted = fb.call(a_mk, vec![three]);
    let got = fb.call(a_get, vec![h]);
    fb.ret(vec![got]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let forged = || InterpretValue {
        ty: ty(handle_a()),
        kind: InterpretValueKind::Handle { id: 0 },
    };
    let probe = module.function_by_name("probe").unwrap();
    let both = Both::new();
    let interpreter = Interpreter::with_module(&module).with_host(&both);

    let error = interpreter
        .execute_function(probe, vec![forged()])
        .expect_err("forged handle");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
    assert!(
        error.message.contains("entry argument carries handle #0")
            && error.message.contains("was never minted in this execution"),
        "{error}"
    );

    let nested = InterpretValue {
        ty: Ty::Tuple(vec![ty(handle_a())]),
        kind: InterpretValueKind::Aggregate(vec![forged()]),
    };
    let error = interpreter
        .execute_function(probe, vec![nested])
        .expect_err("nested forged handle");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
    assert!(
        error.message.contains("entry argument carries handle #0"),
        "{error}"
    );

    // The model's own check: a host is asked to read an id nothing minted.
    // `a_get` is (mis)declared `(u64) -> u64`, and the relay host forwards a
    // handle it never minted to model A's reader in place of the argument.
    let mut mb = ModuleBuilder::new("ws2_12_unminted");
    let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let a_get = mb.declare_function("a_get", sig);
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let a_get = module.function_by_id(a_get).unwrap();
    struct Relay;
    impl HostCalls for Relay {
        fn call(
            &self,
            callee: &Function,
            sig: &FuncTy,
            _args: &[InterpretValue],
            host: &mut HostState,
        ) -> Option<InterpretResult<Vec<InterpretValue>>> {
            let forged = InterpretValue {
                ty: ty(handle_a()),
                kind: InterpretValueKind::Handle { id: 7 },
            };
            Both::new().call(callee, sig, &[forged], host)
        }
    }
    let error = Interpreter::with_module(&module)
        .with_host(&Relay)
        .execute_function(a_get, vec![u64_value(0)])
        .expect_err("model refuses an unminted id");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
    assert!(
        error.message.contains("handle #7") && error.message.contains("was never minted"),
        "{error}"
    );
}

// ─────────────── the pinned Nat row, under a TEST host model ───────────────

/// A TEST model of the pinned `trust_bignum::Nat` row over `u128` payloads
/// (overflow is refused, never wrapped). It is not a reference model of
/// `trust-bignum`; it shows a validated handle program is now executable
/// host-assisted, and that the run says so.
struct TestNatModel;

impl HostCalls for TestNatModel {
    fn call(
        &self,
        callee: &Function,
        _sig: &FuncTy,
        args: &[InterpretValue],
        host: &mut HostState,
    ) -> Option<InterpretResult<Vec<InterpretValue>>> {
        const OWNER: &str = "test-nat";
        let nat = HandleTy::new("Nat", "trust_bignum::Nat");
        let read = |host: &HostState, value: &InterpretValue| {
            host.handle::<u128>(value, &nat, OWNER).copied()
        };
        let role = callee.name.strip_prefix("trust_bignum_nat_")?;
        Some((|| match role {
            "from_u64" => Ok(vec![host.mint_handle(
                nat.clone(),
                OWNER,
                u128::from(as_u64(&args[0])),
            )?]),
            "add" | "sub" => {
                let (x, y) = (read(host, &args[0])?, read(host, &args[1])?);
                let z = if role == "add" {
                    x.checked_add(y).ok_or_else(|| {
                        InterpretError::new(
                            InterpretErrorCode::UnsupportedCall,
                            "test Nat model: sum exceeds u128",
                        )
                    })?
                } else {
                    x.saturating_sub(y)
                };
                Ok(vec![host.mint_handle(nat.clone(), OWNER, z)?])
            }
            "is_zero" => Ok(vec![InterpretValue::bool(read(host, &args[0])? == 0)]),
            "drop" => host.release_handle(&args[0], &nat, OWNER).map(|()| vec![]),
            _ => Err(InterpretError::new(
                InterpretErrorCode::UnsupportedCall,
                format!("test Nat model: unknown role {role}"),
            )),
        })())
    }
}

/// `f() -> bool { is_zero(sub(add(2, 40), k)) }` over the pinned declarations,
/// dropping every handle it minted.
fn nat_module(k: u64) -> Module {
    let pin = TRUSTED_HANDLE_RUNTIMES
        .iter()
        .find(|pin| pin.runtime == "trust_bignum::Nat")
        .expect("v1 pins trust_bignum::Nat");
    let mut mb = ModuleBuilder::new_with_target_info("ws2_12_nat", target());
    let decls = mb.declare_handle_runtime(pin).unwrap();
    let role = |name: &str| decls.entry(name).unwrap();
    let sig = mb.add_func_type(vec![], vec![Ty::Bool]);
    let mut fb = mb.function("f", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let two = fb.uconst(Ty::U64, 2);
    let forty = fb.uconst(Ty::U64, 40);
    let k = fb.uconst(Ty::U64, u128::from(k));
    let a = fb.call(role("from_u64"), vec![two]);
    let b = fb.call(role("from_u64"), vec![forty]);
    let c = fb.call(role("add"), vec![a, b]);
    let kk = fb.call(role("from_u64"), vec![k]);
    let d = fb.call(role("sub"), vec![c, kk]);
    let z = fb.call(role("is_zero"), vec![d]);
    for h in [a, b, c, kk, d] {
        fb.call_void(role("drop"), vec![h]);
    }
    fb.ret(vec![z]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn ws2_12_a_validated_nat_program_executes_host_assisted() {
    let module = nat_module(42);
    assert_eq!(validate_module(&module), vec![]);

    // Fail-closed without a host.
    assert_refused(
        &run(&module, "f", None),
        InterpretErrorCode::UnsupportedCall,
        "@trust_bignum_nat_from_u64: no host model",
    );

    let ok = run(&module, "f", Some(&TestNatModel)).expect("host-assisted Nat run");
    assert_eq!(ok.returns, vec![InterpretValue::bool(true)]);
    // 3 from_u64 + add + sub + is_zero + 5 drop.
    assert_eq!(ok.host_calls, 11);

    // Mutation control: a different constant flips the answer.
    let ok = run(&nat_module(41), "f", Some(&TestNatModel)).unwrap();
    assert_eq!(ok.returns, vec![InterpretValue::bool(false)]);
}

// ─────────────────── adversarial review (WS2.12 review pass) ───────────────────

/// A binding frame is an aggregate: `BindSlot` would carry a handle inside a
/// `Frame` value, which is outside the v43 transport set (copy, select,
/// branch, call, return) exactly like `InsertField`. Before the review fix the
/// handle round-tripped through the frame and was read back by its model.
#[test]
fn ws2_12_review_a_handle_bound_into_a_binding_frame_is_a_type_error() {
    use trust_ir::inst::{BindingFrameDef, BindingSlot};
    use trust_ir::value::BindingFrameId;
    let module = handle_module(handle_b(), vec![Ty::U64], |fb, d| {
        let one = fb.uconst(Ty::U64, 1);
        let a = fb.call(d.a_mk, vec![one]);
        let frame = fb.open_frame(BindingFrameDef::new(
            BindingFrameId::new(0),
            "h",
            vec![BindingSlot::new("h", ty(handle_a()))],
        ));
        let bound = fb.bind_slot(frame, 0, a);
        let back = fb.load_slot(bound, 0, ty(handle_a()));
        fb.close_frame(bound);
        vec![fb.call(d.a_get, vec![back])]
    });
    assert_refused(
        &run(&module, "probe", Some(&Both::new())),
        InterpretErrorCode::TypeError,
        "BindSlot: a runtime handle",
    );
    // Mutation control: the same frame over a plain `u64` executes.
    let control = handle_module(handle_b(), vec![Ty::U64], |fb, _| {
        let one = fb.uconst(Ty::U64, 1);
        let frame = fb.open_frame(BindingFrameDef::new(
            BindingFrameId::new(0),
            "x",
            vec![BindingSlot::new("x", Ty::U64)],
        ));
        let bound = fb.bind_slot(frame, 0, one);
        let back = fb.load_slot(bound, 0, Ty::U64);
        fb.close_frame(bound);
        vec![back]
    });
    assert!(run(&control, "probe", Some(&Both::new())).is_ok());
}

/// A cast is never handle transport, not even the identity `Bitcast` at the
/// handle's own type (which `eval_bitcast` passed through verbatim before the
/// review fix, so an in-format "cast" of a handle executed).
#[test]
fn ws2_12_review_an_identity_bitcast_of_a_handle_is_a_type_error() {
    let module = handle_module(handle_b(), vec![Ty::U64], |fb, d| {
        let one = fb.uconst(Ty::U64, 1);
        let a = fb.call(d.a_mk, vec![one]);
        let same = fb.cast(trust_ir::CastOp::Bitcast, ty(handle_a()), ty(handle_a()), a);
        vec![fb.call(d.a_get, vec![same])]
    });
    assert_refused(
        &run(&module, "probe", Some(&Both::new())),
        InterpretErrorCode::TypeError,
        "bitcast: a runtime handle",
    );
    // Relabelling at another runtime's handle type is refused the same way.
    let relabel = handle_module(handle_a(), vec![Ty::U64], |fb, d| {
        let one = fb.uconst(Ty::U64, 1);
        let a = fb.call(d.a_mk, vec![one]);
        let as_b = fb.cast(trust_ir::CastOp::Bitcast, ty(handle_a()), ty(handle_b()), a);
        vec![fb.call(d.b_get, vec![as_b])]
    });
    let result = run(&relabel, "probe", Some(&Both::new()));
    assert!(
        matches!(&result, Err(e) if e.code == InterpretErrorCode::TypeError),
        "Bitcast handle A -> handle B must be a TypeError, got {:?}",
        result.as_ref().map(|ok| &ok.returns)
    );
}

/// A host's `char` result must be a Unicode scalar value: a surrogate or a
/// value past U+10FFFF typed `char` does not inhabit the type, whatever its
/// 32-bit carrier says. Before the review fix both were admitted.
#[test]
fn ws2_12_review_a_host_char_result_must_be_a_unicode_scalar_value() {
    struct CharHost(u32);
    impl HostCalls for CharHost {
        fn call(
            &self,
            _callee: &Function,
            _sig: &FuncTy,
            _args: &[InterpretValue],
            _host: &mut HostState,
        ) -> Option<InterpretResult<Vec<InterpretValue>>> {
            Some(InterpretValue::int(Ty::Char, i128::from(self.0)).map(|value| vec![value]))
        }
    }
    let mut mb = ModuleBuilder::new_with_target_info("ws2_12_char", target());
    let sig = mb.add_func_type(vec![], vec![Ty::Char]);
    let ext_char = mb.declare_function("ext_char", sig);
    let mut fb = mb.function("caller", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let c = fb.call(ext_char, vec![]);
    fb.ret(vec![c]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), vec![]);

    for bad in [0xD800_u32, 0xDFFF, 0x11_0000, u32::MAX] {
        assert_refused(
            &run(&module, "caller", Some(&CharHost(bad))),
            InterpretErrorCode::TypeError,
            "host result 0 is not a well-formed char value",
        );
    }
    // Mutation control: scalar values on both sides of the surrogate gap run.
    for good in [0x41_u32, 0xD7FF, 0xE000, 0x10_FFFF] {
        let ok = run(&module, "caller", Some(&CharHost(good))).expect("a scalar value");
        assert_eq!(
            ok.returns[0].as_int().unwrap().as_unsigned(),
            u128::from(good)
        );
    }
}

/// No handle exists before a run starts, so an entry argument AT a handle type
/// is refused whatever its payload claims. Before the review fix only a
/// `Handle { .. }` payload was caught: an integer payload typed as a handle
/// passed the (type-only) signature check and was returned from an in-format
/// run (`host_calls == 0`) as if it were a handle.
#[test]
fn ws2_12_review_an_entry_argument_at_a_handle_type_is_refused_whatever_its_payload() {
    let mut mb = ModuleBuilder::new("ws2_12_forged_int");
    let sig = mb.add_func_type(vec![ty(handle_a())], vec![ty(handle_a())]);
    let mut fb = mb.function("id", sig);
    let entry = fb.create_block();
    let h = fb.add_block_param(entry, ty(handle_a()));
    fb.switch_to_block(entry);
    fb.ret(vec![h]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let id = module.function_by_name("id").unwrap();
    let forged_int = InterpretValue {
        ty: ty(handle_a()),
        kind: InterpretValue::int(Ty::U64, 0).unwrap().kind,
    };
    for arg in [
        forged_int.clone(),
        InterpretValue {
            ty: Ty::Tuple(vec![ty(handle_a())]),
            kind: InterpretValueKind::Aggregate(vec![forged_int.clone()]),
        },
    ] {
        let error = Interpreter::with_module(&module)
            .execute_function(id, vec![arg])
            .expect_err("a handle-typed entry argument");
        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{error}");
        assert!(
            error.message.contains("entry argument carries a")
                && error.message.contains("never minted in this execution"),
            "{error}"
        );
    }
}

/// A host's error is the host's claim, not a verdict about the module: the
/// interpreter names the model it came from, so a host-originated
/// `UndefinedBehavior` cannot be read as the module's own UB (the error path
/// carries no `host_calls` count to tell them apart).
#[test]
fn ws2_12_review_a_host_error_names_its_host_origin() {
    struct UbHost;
    impl HostCalls for UbHost {
        fn call(
            &self,
            _callee: &Function,
            _sig: &FuncTy,
            _args: &[InterpretValue],
            _host: &mut HostState,
        ) -> Option<InterpretResult<Vec<InterpretValue>>> {
            Some(Err(InterpretError::new(
                InterpretErrorCode::UndefinedBehavior,
                "model says so",
            )))
        }
    }
    let result = run(&ext_add_module(), "caller", Some(&UbHost));
    assert_refused(
        &result,
        InterpretErrorCode::UndefinedBehavior,
        "host model for @ext_add: model says so",
    );
}
