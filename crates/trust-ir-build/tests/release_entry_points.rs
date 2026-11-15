// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS3.22 (F-060): `Inst::Dealloc` cannot state a free — the ratified
// workaround (G18-1) and its one open edge.
//
// The format half is a ratification plus a refusal, not a gap: `Dealloc { ptr }`
// names neither the `AllocOrigin` whose runtime owns the region nor the layout
// being released, so it is excluded from the lowering-target subset and
// `validate_module_for_codegen` refuses it by name (`UnlowerableForCodegen`);
// every shipping producer spells a free as a CALL to the owning runtime's
// release entry point. The open edge is the consequence: a free is opaque to
// the reference interpreter and to Lean unless the callee is KNOWN to be a
// release. `pinned_release_entry_points()` is the one place that knowledge
// lives — derived from `TRUSTED_HANDLE_RUNTIMES` (the `drop` role) and
// `TRUSTED_RC_RUNTIMES` (the `release` role), never listed a third time — and
// the reference host model (`PinnedHandleHost`, WS2.13) keys its dead-marking
// on it: a call to a symbol the table names is the same step Lean's
// `semDealloc` performs, so a double release or a use after release through a
// pinned runtime is an interpreter FAULT instead of an opaque call.
//
// Rows ported from the archived proof program
// (`reports/2026-09-17-two-language-proof-program`):
// `trust-ir-self-declared/dealloc-cannot-state-a-free` and
// `consumer-trust-cg/18-dealloc`. The ledger rows live in the b5 battery
// (`crates/trust-ir-conformance/tests/two_language/b5_nat_handle.rs`).

use trust_ir::inst::AllocOrigin;
use trust_ir::interpret::{
    HostCalls, HostRcOp, HostState, InterpretErrorCode, InterpretResult, InterpretValue,
    Interpreter,
};
use trust_ir::{
    BodyGate, CallingConv, Endianness, FuncTy, Function, HandleTy, Module, StructPassingPolicy,
    TargetInfo, Ty,
};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{
    HandleEntryPoint, HandleRegistry, HandleRuntimePin, ModuleBuilder, PinnedHandleHost,
    PinnedReleaseEntry, PinnedReleaseSubject, PinnedTy, TRUSTED_HANDLE_RUNTIMES,
    TRUSTED_RC_RUNTIMES, pinned_release_entry_for_symbol, pinned_release_entry_points,
    validate_module, validate_module_for_codegen,
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
        .find(|pin| pin.name == "Nat" && pin.runtime == "trust_bignum::Nat")
        .expect("v1 pins (Nat, trust_bignum::Nat)")
}

fn nat() -> HandleTy {
    HandleTy::new("Nat", "trust_bignum::Nat")
}

fn gate_bodies(module: &mut Module) {
    for function in &mut module.functions {
        if !function.is_declaration() {
            function.body_gate = Some(BodyGate::Gated {
                authority: "release-entry-points-test".into(),
                evidence: None,
            });
        }
    }
}

// ───────────────────────── the ONE place (design item 1) ─────────────────────────

/// v1 pins exactly two release entry points, one per table, each the exact
/// consuming-only C signature, and nothing for `RustHeap`.
#[test]
fn the_pinned_release_entry_points_are_named_once() {
    let entries = pinned_release_entry_points();
    let summary: Vec<(&str, &str, &PinnedReleaseSubject)> = entries
        .iter()
        .map(|e| (e.symbol, e.runtime, &e.subject))
        .collect();
    assert_eq!(
        summary,
        vec![
            (
                "trust_bignum_nat_drop",
                "trust_bignum::Nat",
                &PinnedReleaseSubject::Handle(nat())
            ),
            (
                "clean_dec",
                "clean_runtime",
                &PinnedReleaseSubject::RcCell(AllocOrigin::CleanHeap)
            ),
        ]
    );
    for entry in entries {
        assert_eq!(entry.calling_conv, CallingConv::C, "{}", entry.symbol);
        assert_eq!(entry.func_ty.params.len(), 1, "{}", entry.symbol);
        assert!(entry.func_ty.returns.is_empty(), "{}", entry.symbol);
        assert!(!entry.func_ty.is_vararg, "{}", entry.symbol);
        assert_eq!(
            pinned_release_entry_for_symbol(entry.symbol),
            Some(entry),
            "{}",
            entry.symbol
        );
    }
    // The signatures are the tables' own, not restated.
    let drop = nat_pin().release_entry().expect("Nat pins drop");
    assert_eq!(drop.role, "drop");
    assert_eq!(entries[0].func_ty, nat_pin().func_ty(drop));
    assert_eq!(entries[0].func_ty.params, vec![Ty::Handle(Box::new(nat()))]);
    let clean = TRUSTED_RC_RUNTIMES
        .iter()
        .find(|pin| pin.origin == AllocOrigin::CleanHeap)
        .expect("v1 pins the Clean heap");
    assert_eq!(entries[1].func_ty, clean.release_entry().unwrap().func_ty());
    assert_eq!(entries[1].func_ty.params, vec![Ty::Ptr]);

    // Deliberately absent: a RustHeap free is unpinned and stays opaque; a
    // pinned symbol that is not a release is not a release; and the other
    // Clean runtime entries are not releases.
    for symbol in [
        "__rust_dealloc",
        "free",
        "trust_bignum_nat_add",
        "trust_bignum_nat_from_u64",
        "clean_inc",
        "clean_is_exclusive",
        "clean_alloc_ctor",
        "",
    ] {
        assert_eq!(pinned_release_entry_for_symbol(symbol), None, "{symbol:?}");
    }
    assert!(
        !TRUSTED_RC_RUNTIMES
            .iter()
            .any(|pin| pin.origin == AllocOrigin::RustHeap),
        "no table pins a RustHeap runtime"
    );
}

/// Mutation control: the list is DERIVED from the rows. A registry whose
/// `Nat` row releases through another symbol names that symbol; a row with no
/// consuming entry names nothing (the correct-by-leak state).
#[test]
fn the_release_list_is_derived_from_the_rows_not_restated() {
    const RENAMED: &[HandleEntryPoint] = &[
        HandleEntryPoint {
            role: "from_u64",
            symbol: "x_nat_from_u64",
            def_path: "x::Nat::from_u64",
            params: &[PinnedTy::Scalar(Ty::U64)],
            returns: &[PinnedTy::Handle],
        },
        HandleEntryPoint {
            role: "free",
            symbol: "x_nat_free",
            def_path: "x::Nat::free",
            params: &[PinnedTy::Handle],
            returns: &[],
        },
    ];
    let renamed = HandleRegistry::from_pins(&[HandleRuntimePin {
        name: "Nat",
        runtime: "x::Nat",
        calling_conv: CallingConv::C,
        entry_points: RENAMED,
    }])
    .expect("well-formed row");
    let releases = renamed.release_entry_points();
    assert_eq!(releases.len(), 1);
    assert_eq!(releases[0].symbol, "x_nat_free");
    assert_eq!(
        releases[0].subject,
        PinnedReleaseSubject::Handle(HandleTy::new("Nat", "x::Nat"))
    );
    assert_eq!(
        releases[0].func_ty,
        FuncTy {
            params: vec![Ty::handle("Nat", "x::Nat")],
            returns: vec![],
            abi: None,
            is_vararg: false,
        }
    );

    let leaky = HandleRegistry::from_pins(&[HandleRuntimePin {
        name: "Nat",
        runtime: "x::Nat",
        calling_conv: CallingConv::C,
        entry_points: &RENAMED[..1],
    }])
    .expect("a row with no release is well-formed");
    assert_eq!(
        leaky.release_entry_points(),
        Vec::<PinnedReleaseEntry>::new()
    );
    assert!(leaky.pins()[0].release_entry().is_none());
    assert!(leaky.pins()[0].pinned_release().is_none());
}

// ───────────────────── the G18-1 state (the ratified workaround) ─────────────────────

/// `f() -> u64 { p = HeapAlloc(RustHeap, u64); store 7 -> p; v = load p; Dealloc p;
///              [w = load p]; ret v|w }`
fn dealloc_module_with(load_after: bool) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("dealloc_free", target());
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("f", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let p = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
    let seven = fb.uconst(Ty::U64, 7);
    fb.store(Ty::U64, p, seven);
    let v = fb.load(Ty::U64, p);
    fb.dealloc(p);
    let out = if load_after { fb.load(Ty::U64, p) } else { v };
    fb.ret(vec![out]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    gate_bodies(&mut module);
    module
}

fn dealloc_module() -> Module {
    dealloc_module_with(false)
}

/// The SAME free spelled the ratified way: through the pinned release entry
/// point of the runtime that owns the value, `drops` times.
/// `f() -> bool { n = from_u64(7); z = is_zero(n); drop(n) x drops; ret z }`
fn drop_module_with(drops: usize) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("drop_free", target());
    let decls = mb
        .declare_handle_runtime_roles(nat_pin(), &["from_u64", "is_zero", "drop"])
        .expect("pinned declarations");
    let sig = mb.add_func_type(vec![], vec![Ty::Bool]);
    let mut fb = mb.function("f", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let seven = fb.uconst(Ty::U64, 7);
    let n = fb.call(decls.entry("from_u64").unwrap(), vec![seven]);
    let z = fb.call(decls.entry("is_zero").unwrap(), vec![n]);
    for _ in 0..drops {
        fb.call_void(decls.entry("drop").unwrap(), vec![n]);
    }
    fb.ret(vec![z]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    gate_bodies(&mut module);
    module
}

fn drop_module() -> Module {
    drop_module_with(1)
}

/// The same free over a `CleanHeap` cell: `decs` calls to the pinned
/// `clean_dec`, then (when `load_after`) a load through the freed pointer.
/// `f() -> u64 { p = HeapAlloc(CleanHeap, u64); store 7 -> p; v = load p;
///              clean_dec(p) x decs; [w = load p]; ret v|w }`
fn clean_dec_module_with(decs: usize, load_after: bool) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("clean_dec_free", target());
    let release = pinned_release_entry_for_symbol("clean_dec").expect("pinned");
    let dec_ty = mb.add_func_type(
        release.func_ty.params.clone(),
        release.func_ty.returns.clone(),
    );
    let dec = mb.declare_function(release.symbol, dec_ty);
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("f", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let p = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::CleanHeap);
    let seven = fb.uconst(Ty::U64, 7);
    fb.store(Ty::U64, p, seven);
    let v = fb.load(Ty::U64, p);
    for _ in 0..decs {
        fb.call_void(dec, vec![p]);
    }
    let out = if load_after { fb.load(Ty::U64, p) } else { v };
    fb.ret(vec![out]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    gate_bodies(&mut module);
    module
}

fn clean_dec_module() -> Module {
    clean_dec_module_with(1, false)
}

fn run(module: &Module, host: Option<&dyn HostCalls>) -> InterpretResult<Vec<InterpretValue>> {
    let f = module.function_by_name("f").expect("@f");
    let mut interpreter = Interpreter::with_module(module);
    if let Some(host) = host {
        interpreter = interpreter.with_host(host);
    }
    interpreter
        .execute_function(f, Vec::new())
        .map(|outcome| outcome.returns)
}

/// Rows `trust-ir-self-declared/dealloc-cannot-state-a-free` and
/// `consumer-trust-cg/18-dealloc`: `Dealloc` is well-formed TrustIr, the
/// reference interpreter executes it, and `validate_module_for_codegen`
/// refuses it as exactly one `UnlowerableForCodegen` naming the instruction
/// and the missing information.
#[test]
fn dealloc_validates_structurally_executes_and_is_unlowerable_for_codegen() {
    let module = dealloc_module();
    assert_eq!(validate_module(&module), vec![]);
    assert_eq!(
        run(&module, None).expect("Dealloc executes in-format"),
        vec![InterpretValue::int(Ty::U64, 7).unwrap()]
    );
    let codegen = validate_module_for_codegen(&module);
    match codegen.as_slice() {
        [
            ValidationError::UnlowerableForCodegen {
                name, inst, detail, ..
            },
        ] => {
            assert_eq!(name, "f");
            assert_eq!(*inst, "Dealloc");
            assert!(detail.contains("AllocOrigin"), "{detail}");
            assert!(detail.contains("layout"), "{detail}");
        }
        other => panic!("expected exactly one UnlowerableForCodegen(Dealloc), got {other:?}"),
    }
}

/// The close twin: the same free spelled as a call to the pinned release entry
/// point of the owning runtime — `trust_bignum_nat_drop` for a `Nat`,
/// `clean_dec` for a `CleanHeap` cell — validates AND passes
/// `validate_module_for_codegen`. Each callee is a row of the one-place table.
#[test]
fn the_same_free_spelled_as_a_pinned_release_call_is_lowerable() {
    for module in [drop_module(), clean_dec_module()] {
        assert_eq!(validate_module(&module), vec![], "{}", module.name);
        assert_eq!(
            validate_module_for_codegen(&module),
            vec![],
            "{}",
            module.name
        );
        let f = module.function_by_name("f").unwrap();
        let mut release_calls = 0;
        for block in &f.blocks {
            for node in &block.body {
                if let trust_ir::Inst::Call { callee, .. } = &node.inst {
                    let callee = module.function_by_id(*callee).unwrap();
                    if pinned_release_entry_for_symbol(&callee.name).is_some() {
                        release_calls += 1;
                    }
                }
            }
        }
        assert_eq!(
            release_calls, 1,
            "{}: exactly one pinned release call",
            module.name
        );
    }
}

/// Mutation control on the twin: a release symbol OUTSIDE the table is not a
/// free the format knows. A `Nat` released through `trust_bignum_nat_free`
/// (unpinned) is refused by name, so the pinned-symbol key is load-bearing.
#[test]
fn a_release_through_an_unpinned_symbol_is_a_foreign_declaration() {
    let mut mb = ModuleBuilder::new_with_target_info("unpinned_free", target());
    let decls = mb
        .declare_handle_runtime_roles(nat_pin(), &["from_u64"])
        .expect("pinned declarations");
    let free_ty = mb.add_func_type(vec![Ty::Handle(Box::new(nat()))], vec![]);
    let free = mb.declare_function("trust_bignum_nat_free", free_ty);
    let sig = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("f", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let seven = fb.uconst(Ty::U64, 7);
    let n = fb.call(decls.entry("from_u64").unwrap(), vec![seven]);
    fb.call_void(free, vec![n]);
    fb.ret(vec![]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    gate_bodies(&mut module);
    assert_eq!(
        pinned_release_entry_for_symbol("trust_bignum_nat_free"),
        None
    );
    let errors = validate_module(&module);
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::HandleForeignDeclaration { name, .. }] if name == "trust_bignum_nat_free"
        ),
        "{errors:?}"
    );
}

// ─────────────── the open edge: a release is a dead-marking step (design item 2) ───────────────

/// The MUTANT of the reference model: every call goes to `PinnedHandleHost`,
/// except that a call to a symbol the one-place release table names is
/// treated as a NO-OP (the handle stays live; the RC cell is never counted
/// down). This is what a host that does not key its dead-marking on the table
/// would do, and it is what the double-release tests must be able to tell
/// from the reference model.
struct NoOpRelease;

impl HostCalls for NoOpRelease {
    fn call(
        &self,
        callee: &Function,
        sig: &FuncTy,
        args: &[InterpretValue],
        host: &mut HostState,
    ) -> Option<InterpretResult<Vec<InterpretValue>>> {
        if pinned_release_entry_for_symbol(&callee.name).is_some() {
            return Some(Ok(Vec::new()));
        }
        PinnedHandleHost::new().call(callee, sig, args, host)
    }

    fn rc_op(&self, callee: &Function, sig: &FuncTy) -> Option<HostRcOp> {
        if pinned_release_entry_for_symbol(&callee.name).is_some() {
            // Not an RC op as far as the mutant is concerned: `call` above
            // then serves it as a no-op.
            return None;
        }
        PinnedHandleHost::new().rc_op(callee, sig)
    }
}

/// Positive: a double `trust_bignum_nat_drop` of one handle faults in the
/// interpreter under the reference host model, whose release is keyed on the
/// one-place table. Negative twin: a single drop runs clean. Both modules
/// VALIDATE (the validator makes no liveness claim about a handle —
/// `TRUST.md` item 9(c)), so this is the first executable witness for that
/// non-guarantee: it is a host-assisted run, a trusted model, never in-format
/// evidence.
#[test]
fn a_double_drop_faults_under_a_release_marking_host_and_a_single_drop_runs_clean() {
    let single = drop_module_with(1);
    let double = drop_module_with(2);
    assert_eq!(validate_module(&single), vec![]);
    assert_eq!(validate_module(&double), vec![]);
    assert_eq!(validate_module_for_codegen(&double), vec![]);

    // Without a host: fail closed at the first pinned call, never a silent free.
    let unhosted = run(&double, None).expect_err("no host model");
    assert_eq!(unhosted.code, InterpretErrorCode::UnsupportedCall);
    assert_eq!(
        unhosted.unhosted_callee(),
        Some("trust_bignum_nat_from_u64")
    );

    let marking = PinnedHandleHost::new();
    assert_eq!(
        run(&single, Some(&marking)).expect("one drop runs clean"),
        vec![InterpretValue::bool(false)]
    );
    let fault = run(&double, Some(&marking)).expect_err("the second drop is a fault");
    assert_eq!(fault.code, InterpretErrorCode::UndefinedBehavior, "{fault}");
    assert!(fault.message.contains("used after release"), "{fault}");
    assert!(fault.message.contains("trust_bignum_nat_drop"), "{fault}");
}

/// Mutation control: a host that treats the pinned release as a no-op cannot
/// see the double drop — the run "succeeds". The dead-marking keyed on the
/// one-place table is what turns the opaque call into a fault, so a reference
/// model that lost it would be caught by the test above.
#[test]
fn a_host_that_treats_drop_as_a_no_op_fails_the_double_drop_test() {
    let double = drop_module_with(2);
    assert_eq!(
        run(&double, Some(&NoOpRelease)).expect("the mutant host hides the double free"),
        vec![InterpretValue::bool(false)]
    );
}

/// The `CleanHeap` twin of the same edge: under the reference model the
/// pinned `clean_dec` is the interpreter's own `Release`, which marks the
/// cell dead at count zero (the `semDealloc` step), so a second `clean_dec`
/// and a load through the freed pointer are each `UndefinedBehavior`; a
/// single `clean_dec` runs clean. Under the no-op mutant all three "succeed".
#[test]
fn a_double_clean_dec_and_a_load_after_it_fault_under_the_reference_model() {
    let single = clean_dec_module_with(1, false);
    let double = clean_dec_module_with(2, false);
    let use_after = clean_dec_module_with(1, true);
    for module in [&single, &double, &use_after] {
        assert_eq!(validate_module(module), vec![]);
        assert_eq!(validate_module_for_codegen(module), vec![]);
    }
    let seven = vec![InterpretValue::int(Ty::U64, 7).unwrap()];

    let marking = PinnedHandleHost::new();
    assert_eq!(
        run(&single, Some(&marking)).expect("one dec runs clean"),
        seven
    );
    let double_free = run(&double, Some(&marking)).expect_err("second dec");
    assert_eq!(
        double_free.code,
        InterpretErrorCode::UndefinedBehavior,
        "{double_free}"
    );
    assert!(
        double_free.message.contains("freed allocation"),
        "{double_free}"
    );
    assert!(double_free.message.contains("clean_dec"), "{double_free}");
    // A load through the released cell is the SAME fault a load after
    // `Inst::Dealloc` is: the pinned release IS the dealloc step.
    let stale = run(&use_after, Some(&marking)).expect_err("load after dec");
    assert_eq!(stale.code, InterpretErrorCode::UndefinedBehavior, "{stale}");
    assert!(stale.message.contains("use after dealloc"), "{stale}");
    let after_dealloc = run(&dealloc_module_with(true), None).expect_err("load after Dealloc");
    assert_eq!(after_dealloc.code, InterpretErrorCode::UndefinedBehavior);
    assert!(
        after_dealloc.message.contains("use after dealloc"),
        "{after_dealloc}"
    );

    // Mutation control: the no-op mutant sees none of it.
    for module in [&single, &double, &use_after] {
        assert_eq!(
            run(module, Some(&NoOpRelease)).expect("the mutant host hides the free"),
            seven
        );
    }
    // Without a host: the first pinned call is refused by name.
    let unhosted = run(&double, None).expect_err("no host model");
    assert_eq!(unhosted.unhosted_callee(), Some("clean_dec"));
}

/// The unpinned `RustHeap` free stays OPAQUE: without a host a call to
/// `__rust_dealloc` is refused as `UnsupportedCall` naming the callee (fail
/// closed, never a silent no-op), the release table does not name it, and the
/// reference model does not serve it either — a use after such a free is
/// invisible, which is stated, not hidden.
#[test]
fn a_rust_heap_free_is_unpinned_and_stays_an_opaque_call() {
    let mut mb = ModuleBuilder::new_with_target_info("rust_dealloc", target());
    let dealloc_ty = mb.add_func_type(vec![Ty::Ptr, Ty::Usize, Ty::Usize], vec![]);
    let dealloc = mb.declare_function("__rust_dealloc", dealloc_ty);
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("f", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let p = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
    let seven = fb.uconst(Ty::U64, 7);
    fb.store(Ty::U64, p, seven);
    let v = fb.load(Ty::U64, p);
    let size = fb.uconst(Ty::Usize, 8);
    let align = fb.uconst(Ty::Usize, 8);
    fb.call_void(dealloc, vec![p, size, align]);
    fb.ret(vec![v]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    gate_bodies(&mut module);
    assert_eq!(validate_module(&module), vec![]);
    assert_eq!(validate_module_for_codegen(&module), vec![]);
    assert_eq!(pinned_release_entry_for_symbol("__rust_dealloc"), None);
    for host in [None, Some(&PinnedHandleHost::new() as &dyn HostCalls)] {
        let refused = run(&module, host).expect_err("opaque");
        assert_eq!(refused.code, InterpretErrorCode::UnsupportedCall);
        assert_eq!(refused.unhosted_callee(), Some("__rust_dealloc"));
    }
}

// ───────────────────── adversarial review (WS3.22) ─────────────────────
//
// Five inputs the implementation did not write, each aimed at the increment's
// load-bearing claim — "a call to a pinned release entry point IS the
// dead-marking step `semDealloc` performs, keyed on the one-place table and on
// nothing else".

/// A void entry that merely REACHES a handle does not CONSUME it. The
/// `returns.is_empty()` bound `HandleRegistry::from_pins` enforces is an upper
/// bound on "is the release", not the predicate: an in-place mutator
/// `set_u64(H, u64) -> ()` returns nothing and satisfies
/// `EntryDoesNotReachHandle`, so the weak predicate would name it the release
/// of its row — and a host model keyed on this table would then dead-mark a
/// handle that is still live, faulting a legitimate program on its next use.
/// `release_entry` requires the consuming shape `(H) -> ()`, so such a row
/// pins NO release (fail closed: the call is served by no arm).
#[test]
fn a_void_entry_that_does_not_consume_the_handle_is_not_a_release() {
    const MUTATOR: &[HandleEntryPoint] = &[
        HandleEntryPoint {
            role: "from_u64",
            symbol: "y_nat_from_u64",
            def_path: "y::Nat::from_u64",
            params: &[PinnedTy::Scalar(Ty::U64)],
            returns: &[PinnedTy::Handle],
        },
        // Returns nothing and reaches a handle, but does not consume it.
        HandleEntryPoint {
            role: "set_u64",
            symbol: "y_nat_set_u64",
            def_path: "y::Nat::set_u64",
            params: &[PinnedTy::Handle, PinnedTy::Scalar(Ty::U64)],
            returns: &[],
        },
    ];
    let row = HandleRuntimePin {
        name: "Nat",
        runtime: "y::Nat",
        calling_conv: CallingConv::C,
        entry_points: MUTATOR,
    };
    let registry = HandleRegistry::from_pins(std::slice::from_ref(&row))
        .expect("a row with a void mutator is well-formed");
    assert!(
        row.release_entry().is_none(),
        "a non-consuming void entry must not be named the release"
    );
    assert_eq!(row.pinned_release(), None);
    assert_eq!(
        registry.release_entry_points(),
        Vec::<PinnedReleaseEntry>::new()
    );

    // The narrower predicate is still singular: it is a subset of the one
    // `from_pins` bounds at one per row, which that bound refuses to exceed.
    const TWO_VOIDS: &[HandleEntryPoint] = &[
        HandleEntryPoint {
            role: "set_u64",
            symbol: "z_nat_set_u64",
            def_path: "z::Nat::set_u64",
            params: &[PinnedTy::Handle, PinnedTy::Scalar(Ty::U64)],
            returns: &[],
        },
        HandleEntryPoint {
            role: "drop",
            symbol: "z_nat_drop",
            def_path: "z::Nat::drop",
            params: &[PinnedTy::Handle],
            returns: &[],
        },
    ];
    assert!(
        HandleRegistry::from_pins(&[HandleRuntimePin {
            name: "Nat",
            runtime: "z::Nat",
            calling_conv: CallingConv::C,
            entry_points: TWO_VOIDS,
        }])
        .is_err(),
        "two void entries on one row stay refused, so the release stays singular"
    );

    // And v1 is unaffected: both pinned releases have the consuming shape.
    for entry in pinned_release_entry_points() {
        assert_eq!(entry.func_ty.params.len(), 1, "{}", entry.symbol);
        assert!(entry.func_ty.returns.is_empty(), "{}", entry.symbol);
    }
}

/// The dead-marking follows the HANDLE IDENTITY, not the SSA value that
/// carries it. A handle copied to a second value and released through one of
/// them is released for both: the next use through the surviving copy, and a
/// second release through it, are each `UndefinedBehavior`. Keying on the SSA
/// value instead would let this program run clean.
/// `f() -> bool { n = from_u64(7); m = copy n; drop(n); ret is_zero(m) }`
#[test]
fn a_release_through_one_copy_of_a_handle_kills_every_copy() {
    let handle_ty = Ty::Handle(Box::new(nat()));
    let build = |second_drop: bool| {
        let mut mb = ModuleBuilder::new_with_target_info("aliased_drop", target());
        let decls = mb
            .declare_handle_runtime_roles(nat_pin(), &["from_u64", "is_zero", "drop"])
            .expect("pinned declarations");
        let sig = mb.add_func_type(vec![], vec![Ty::Bool]);
        let mut fb = mb.function("f", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let seven = fb.uconst(Ty::U64, 7);
        let n = fb.call(decls.entry("from_u64").unwrap(), vec![seven]);
        let m = fb.copy(handle_ty.clone(), n);
        fb.call_void(decls.entry("drop").unwrap(), vec![n]);
        if second_drop {
            fb.call_void(decls.entry("drop").unwrap(), vec![m]);
            let f = fb.bool_const(false);
            fb.ret(vec![f]);
        } else {
            let z = fb.call(decls.entry("is_zero").unwrap(), vec![m]);
            fb.ret(vec![z]);
        }
        fb.build();
        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
        gate_bodies(&mut module);
        module
    };
    let host = PinnedHandleHost::new();
    for second_drop in [false, true] {
        let module = build(second_drop);
        assert_eq!(validate_module(&module), vec![]);
        assert_eq!(validate_module_for_codegen(&module), vec![]);
        let fault = run(&module, Some(&host)).expect_err("the copy names the released handle");
        assert_eq!(fault.code, InterpretErrorCode::UndefinedBehavior, "{fault}");
        assert!(fault.message.contains("used after release"), "{fault}");
        // The no-op mutant sees neither.
        assert!(
            run(&module, Some(&NoOpRelease)).is_ok(),
            "the mutant host hides the aliased free"
        );
    }
}

/// The table key cannot be dodged by INDIRECT dispatch. Reached through a
/// `Constant::FnDef` function pointer the call still resolves to the pinned
/// declaration, so the reference model still releases and a double release
/// still faults; reached through a relocatable `Constant::SymbolAddr` — the
/// spelling with no `FnDef` provenance — the module never validates at all
/// (`HandleEntryPointAddressTaken` / `RcEntryPointAddressTaken` by name).
#[test]
fn a_pinned_release_reached_through_a_function_pointer_is_still_a_release() {
    let mut mb = ModuleBuilder::new_with_target_info("indirect_drop", target());
    let decls = mb
        .declare_handle_runtime_roles(nat_pin(), &["from_u64", "drop"])
        .expect("pinned declarations");
    let drop_id = decls.entry("drop").unwrap();
    // The pinned declaration's OWN signature row, not a second equal one.
    let drop_ty = mb.intern_func_type(FuncTy {
        params: vec![Ty::Handle(Box::new(nat()))],
        returns: vec![],
        abi: None,
        is_vararg: false,
    });
    let sig = mb.add_func_type(vec![], vec![Ty::Bool]);
    let mut fb = mb.function("f", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let seven = fb.uconst(Ty::U64, 7);
    let n = fb.call(decls.entry("from_u64").unwrap(), vec![seven]);
    let fp = fb.const_value(Ty::Func(drop_ty), trust_ir::Constant::FnDef(drop_id));
    fb.call_indirect_void(fp, drop_ty, vec![n]);
    fb.call_indirect_void(fp, drop_ty, vec![n]);
    let f = fb.bool_const(false);
    fb.ret(vec![f]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    gate_bodies(&mut module);
    assert_eq!(validate_module(&module), vec![]);
    assert_eq!(validate_module_for_codegen(&module), vec![]);
    let fault = run(&module, Some(&PinnedHandleHost::new()))
        .expect_err("the indirect second drop is still a double release");
    assert_eq!(fault.code, InterpretErrorCode::UndefinedBehavior, "{fault}");
    assert!(fault.message.contains("used after release"), "{fault}");
    assert!(
        run(&module, Some(&NoOpRelease)).is_ok(),
        "the mutant host hides the indirect free"
    );

    // The provenance-free spelling never gets that far.
    for (symbol, expected) in [
        ("trust_bignum_nat_drop", "HandleEntryPointAddressTaken"),
        ("clean_dec", "RcEntryPointAddressTaken"),
    ] {
        let mut mb = ModuleBuilder::new_with_target_info("symbol_addr_drop", target());
        let fn_ty = mb.add_func_type(vec![Ty::Ptr], vec![]);
        let sig = mb.add_func_type(vec![], vec![Ty::Bool]);
        let mut fb = mb.function("g", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let callee = fb.const_value(Ty::Func(fn_ty), trust_ir::Constant::symbol_addr(symbol));
        let p = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::CleanHeap);
        fb.call_indirect_void(callee, fn_ty, vec![p]);
        let f = fb.bool_const(false);
        fb.ret(vec![f]);
        fb.build();
        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
        gate_bodies(&mut module);
        let errors = validate_module(&module);
        assert!(
            errors.iter().any(|error| match (expected, error) {
                (
                    "HandleEntryPointAddressTaken",
                    ValidationError::HandleEntryPointAddressTaken { symbol: s, .. },
                ) => s == symbol,
                (
                    "RcEntryPointAddressTaken",
                    ValidationError::RcEntryPointAddressTaken { symbol: s, .. },
                ) => s == symbol,
                _ => false,
            }),
            "taking the address of {symbol} must be {expected}: {errors:?}"
        );
    }
}

/// The pinned `clean_dec` and `Inst::Release` are the SAME step, in both
/// orders: whichever of the two takes the count to zero marks the cell dead,
/// and the other one then faults as a double free. If the host call were a
/// separate bookkeeping path the two spellings would not compose.
#[test]
fn the_pinned_clean_dec_and_inst_release_are_one_count() {
    // `f() -> u64 { p = HeapAlloc(CleanHeap, u64); store 7; v = load p;
    //               [clean_dec(p); Release p] | [Release p; clean_dec(p)]; ret v }`
    let build = |call_first: bool| {
        let mut mb = ModuleBuilder::new_with_target_info("mixed_release", target());
        let release = pinned_release_entry_for_symbol("clean_dec").expect("pinned");
        let dec_ty = mb.add_func_type(
            release.func_ty.params.clone(),
            release.func_ty.returns.clone(),
        );
        let dec = mb.declare_function(release.symbol, dec_ty);
        let sig = mb.add_func_type(vec![], vec![Ty::U64]);
        let mut fb = mb.function("f", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let p = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::CleanHeap);
        let seven = fb.uconst(Ty::U64, 7);
        fb.store(Ty::U64, p, seven);
        let v = fb.load(Ty::U64, p);
        if call_first {
            fb.call_void(dec, vec![p]);
            fb.release(p);
        } else {
            fb.release(p);
            fb.call_void(dec, vec![p]);
        }
        fb.ret(vec![v]);
        fb.build();
        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
        gate_bodies(&mut module);
        module
    };
    let host = PinnedHandleHost::new();
    for call_first in [true, false] {
        let module = build(call_first);
        assert_eq!(validate_module(&module), vec![]);
        let fault = run(&module, Some(&host)).expect_err("two releases, one count");
        assert_eq!(fault.code, InterpretErrorCode::UndefinedBehavior, "{fault}");
        assert!(
            fault.message.contains("freed allocation")
                || fault.message.contains("double free")
                || fault.message.contains("use after dealloc"),
            "{fault}"
        );
    }
    // The mutant only skips the CALL, so the `Inst::Release` alone runs clean
    // — which is exactly why the call has to be the same step.
    for call_first in [true, false] {
        assert!(run(&build(call_first), Some(&NoOpRelease)).is_ok());
    }
}

/// A pinned release does not release just anything: `clean_dec` on a cell of
/// another heap is refused by the owning-heap check (no ownership transfer),
/// and a retain after the release is a use of a freed cell. Both are modules
/// the validator admits — the residue item 13 names — so the model is what
/// catches them.
#[test]
fn a_pinned_release_is_refused_on_a_foreign_cell_and_after_the_free() {
    let clean = TRUSTED_RC_RUNTIMES
        .iter()
        .find(|pin| pin.origin == AllocOrigin::CleanHeap)
        .expect("v1 pins the Clean heap");
    let inc = clean.entry("retain").expect("clean_inc");
    let build = |origin: AllocOrigin, retain_after: bool| {
        let mut mb = ModuleBuilder::new_with_target_info("foreign_dec", target());
        let dec_ty = mb.add_func_type(vec![Ty::Ptr], vec![]);
        let dec = mb.declare_function("clean_dec", dec_ty);
        let inc_ty = mb.add_func_type(inc.params.to_vec(), inc.returns.to_vec());
        let inc_decl = mb.declare_function(inc.symbol, inc_ty);
        let sig = mb.add_func_type(vec![], vec![Ty::U64]);
        let mut fb = mb.function("f", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let p = fb.heap_alloc(Ty::U64, None, None, origin);
        let seven = fb.uconst(Ty::U64, 7);
        fb.store(Ty::U64, p, seven);
        let v = fb.load(Ty::U64, p);
        fb.call_void(dec, vec![p]);
        if retain_after {
            fb.call_void(inc_decl, vec![p]);
        }
        fb.ret(vec![v]);
        fb.build();
        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
        gate_bodies(&mut module);
        module
    };
    let host = PinnedHandleHost::new();

    // A RustHeap cell is not a cell of the heap this runtime counts.
    let foreign = build(AllocOrigin::RustHeap, false);
    assert_eq!(validate_module(&foreign), vec![]);
    let fault = run(&foreign, Some(&host)).expect_err("no ownership transfer between heaps");
    assert_eq!(fault.code, InterpretErrorCode::UndefinedBehavior, "{fault}");
    assert!(fault.message.contains("clean_dec"), "{fault}");

    // A retain of the cell the pinned release freed is a use after free.
    let resurrect = build(AllocOrigin::CleanHeap, true);
    assert_eq!(validate_module(&resurrect), vec![]);
    let fault = run(&resurrect, Some(&host)).expect_err("retain after the pinned free");
    assert_eq!(fault.code, InterpretErrorCode::UndefinedBehavior, "{fault}");
    assert!(fault.message.contains("freed allocation"), "{fault}");
    assert!(
        run(&resurrect, Some(&NoOpRelease)).is_ok(),
        "the mutant host hides the resurrection"
    );
}
