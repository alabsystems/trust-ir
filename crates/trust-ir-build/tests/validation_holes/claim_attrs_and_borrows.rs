// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! WS2.7: claim-style attributes and borrow discipline — the cheap, sound part
//! turned into checks (F-021, F-040; audit c15 items 3 and 4). Run by standing
//! gate 9 (`validator-fail-closed`) as a module of `validation_holes`.
//!
//! (a) `FuncAttrs.readnone` / `readonly` on a DEFINED body are checked against
//!     the body (`FuncAttrClaimViolated`). A store/load through an address
//!     that roots at the function's own `Alloca` — tracing ONLY `GEP` base,
//!     `Copy` and `Cast PtrToPtr` — is exempt; `Select`, a block parameter and
//!     `IntToPtr` are roots, never transparent (the mutation controls below
//!     pin each). Declarations keep the attributes as a claim.
//! (b) Borrow STRUCTURE: `BorrowMut` through a shared reference
//!     (`BorrowMutThroughSharedRef`, by static type `&T` / `*const T` OR by
//!     rooting at a shared `Borrow` result, which is typed `Ptr`) and
//!     `EndBorrow` of a non-borrow (`EndBorrowOfNonBorrow`). Borrow LIVENESS
//!     is a ratified producer obligation (`TRUST.md` item 12), pinned below as
//!     still validating so it cannot be misread as a guarantee.
//!
//! Every negative is a one-mutation twin of a validating baseline and asserts
//! the SPECIFIC named error.

use trust_ir::inst::{AllocOrigin, CastOp, Ordering};
use trust_ir::interpret::Interpreter;
use trust_ir::{BodyGate, FuncAttrs, Inst, Module, Producer, Ty, ValueId};
use trust_ir_build::{
    FunctionBuilder, ModuleBuilder, ValidationError, validate_function, validate_module,
    validate_module_for_codegen,
};

// ---------------------------------------------------------------------------
// Fixtures and helpers
// ---------------------------------------------------------------------------

fn licensed(module: &Module) -> Module {
    let mut module = module.clone();
    for function in &mut module.functions {
        if function.body_gate.is_none() && !function.blocks.is_empty() {
            function.body_gate = Some(BodyGate::Gated {
                authority: "trust-verify".into(),
                evidence: None,
            });
        }
    }
    module
}

/// A bodyless declaration needs a pinned target (`TargetInfoRequired`).
fn pinned_target() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("sysv64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

fn readnone() -> FuncAttrs {
    FuncAttrs {
        readnone: true,
        ..FuncAttrs::default()
    }
}

fn readonly() -> FuncAttrs {
    FuncAttrs {
        readonly: true,
        ..FuncAttrs::default()
    }
}

/// `fn w(p: ptr) { <body> ; ret }` carrying `attrs`. `body` may create and
/// switch blocks; the trailing `ret` lands in whatever block is current.
fn effect_module(attrs: FuncAttrs, body: impl FnOnce(&mut FunctionBuilder<'_>, ValueId)) -> Module {
    let mut mb = ModuleBuilder::new("ws2_7_effects");
    let sig = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let mut fb = mb.function("w", sig);
    fb.set_attrs(attrs);
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    body(&mut fb, p);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Every entry point agrees the module is well-formed.
fn assert_valid(module: &Module) {
    assert_eq!(validate_module(module), [], "validate_module");
    assert_eq!(
        validate_module_for_codegen(&licensed(module)),
        [],
        "validate_module_for_codegen"
    );
}

fn claim_violations(errors: &[ValidationError]) -> Vec<(&'static str, String)> {
    errors
        .iter()
        .filter_map(|error| match error {
            ValidationError::FuncAttrClaimViolated { attr, inst, .. } => {
                Some((*attr, inst.clone()))
            }
            _ => None,
        })
        .collect()
}

/// `module` is refused by module validation with exactly one
/// `FuncAttrClaimViolated` on `w`, naming `attr` and an instruction whose
/// description starts with `inst`, and nothing else.
fn assert_claim_violated(module: &Module, attr: &str, inst: &str) {
    for errors in [
        validate_module(module),
        validate_module_for_codegen(&licensed(module)),
    ] {
        assert_eq!(errors.len(), 1, "exactly the claim violation: {errors:?}");
        assert!(
            matches!(
                &errors[0],
                ValidationError::FuncAttrClaimViolated { function, attr: a, inst: i, .. }
                    if function == "w" && *a == attr && i.starts_with(inst)
            ),
            "expected FuncAttrClaimViolated {{ attr: {attr}, inst: {inst}.. }}, got {errors:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// (a) positives
// ---------------------------------------------------------------------------

#[test]
fn readnone_function_with_only_arithmetic_validates() {
    let module = effect_module(readnone(), |fb, _| {
        let one = fb.uconst(Ty::U64, 1);
        let _ = fb.add(Ty::U64, one, one);
    });
    assert_valid(&module);
    assert_eq!(validate_function(&module.functions[0]), []);
}

#[test]
fn readnone_function_storing_to_its_own_alloca_is_exempt() {
    let module = effect_module(readnone(), |fb, _| {
        let slot = fb.alloca(Ty::U64);
        let nine = fb.uconst(Ty::U64, 9);
        fb.store(Ty::U64, slot, nine);
        let _ = fb.load(Ty::U64, slot);
    });
    assert_valid(&module);
    assert_eq!(validate_function(&module.functions[0]), []);
}

#[test]
fn readonly_function_may_read_through_a_parameter() {
    let module = effect_module(readonly(), |fb, p| {
        let _ = fb.load(Ty::U64, p);
        let _ = fb.atomic_load(Ty::U64, p, Ordering::Relaxed);
    });
    assert_valid(&module);
}

#[test]
fn declaration_attributes_stay_a_claim() {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_7_decl", pinned_target());
    let sig = mb.add_func_type(vec![Ty::Ptr], vec![]);
    mb.declare_function("ext", sig);
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.functions[0].attrs = FuncAttrs {
        readnone: true,
        readonly: true,
        ..FuncAttrs::default()
    };
    assert_eq!(validate_module(&module), []);
}

// ---------------------------------------------------------------------------
// (a) negative twins — c15 4a / 4b and the refused classes
// ---------------------------------------------------------------------------

/// c15 4a: readnone on a body that stores through its parameter.
#[test]
fn c15_4a_readnone_with_store_through_param_is_refused() {
    let store = |fb: &mut FunctionBuilder<'_>, p| {
        let five = fb.uconst(Ty::U64, 5);
        fb.store(Ty::U64, p, five);
    };
    assert_valid(&effect_module(FuncAttrs::default(), store));
    assert_claim_violated(&effect_module(readnone(), store), "readnone", "store");
}

/// c15 4b: readonly on a body that stores through its parameter.
#[test]
fn c15_4b_readonly_with_store_through_param_is_refused() {
    let store = |fb: &mut FunctionBuilder<'_>, p| {
        let five = fb.uconst(Ty::U64, 5);
        fb.store(Ty::U64, p, five);
    };
    assert_claim_violated(&effect_module(readonly(), store), "readonly", "store");
}

#[test]
fn readnone_refuses_a_read_through_a_parameter() {
    let load = |fb: &mut FunctionBuilder<'_>, p| {
        let _ = fb.load(Ty::U64, p);
    };
    assert_valid(&effect_module(readonly(), load));
    assert_claim_violated(&effect_module(readnone(), load), "readnone", "load");
}

#[test]
fn readonly_refuses_a_synchronizing_atomic_load() {
    assert_valid(&effect_module(readonly(), |fb, p| {
        let _ = fb.atomic_load(Ty::U64, p, Ordering::Relaxed);
    }));
    for ordering in [Ordering::Acquire, Ordering::SeqCst] {
        assert_claim_violated(
            &effect_module(readonly(), |fb, p| {
                let _ = fb.atomic_load(Ty::U64, p, ordering);
            }),
            "readonly",
            "atomic_load",
        );
    }
}

#[test]
fn heap_fence_and_indirect_calls_are_refused_under_either_claim() {
    for (attrs, attr) in [(readnone(), "readnone"), (readonly(), "readonly")] {
        assert_claim_violated(
            &effect_module(attrs.clone(), |fb, _| {
                let _ = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
            }),
            attr,
            "heap_alloc",
        );
        assert_claim_violated(
            &effect_module(attrs.clone(), |fb, _| fb.fence(Ordering::SeqCst)),
            attr,
            "fence",
        );
    }
}

#[test]
fn call_indirect_is_refused() {
    let mut mb = ModuleBuilder::new("ws2_7_indirect");
    let leaf_sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let leaf = {
        let mut fb = mb.function("leaf", leaf_sig);
        fb.set_attrs(readnone());
        let e = fb.create_block();
        fb.switch_to_block(e);
        let c = fb.uconst(Ty::U64, 1);
        fb.ret(vec![c]);
        fb.build()
    };
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("w", sig);
    fb.set_attrs(readnone());
    let e = fb.create_block();
    fb.switch_to_block(e);
    let target = fb.fn_addr(leaf_sig, leaf);
    let r = fb.call_indirect(target, leaf_sig, vec![]);
    fb.ret(vec![r]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let violations = claim_violations(&validate_module(&module));
    assert_eq!(violations.len(), 1, "{violations:?}");
    assert_eq!(violations[0].0, "readnone");
    assert!(
        violations[0].1.starts_with("call_indirect"),
        "{violations:?}"
    );
}

// ---------------------------------------------------------------------------
// (a) call edges
// ---------------------------------------------------------------------------

/// `fn g() -> u64 { 7 }` with `callee_attrs`, and `fn w() -> u64 { g() }`
/// with `caller_attrs`. `g` is `functions[0]`, `w` is `functions[1]`.
fn call_module(caller_attrs: FuncAttrs, callee_attrs: FuncAttrs) -> Module {
    let mut mb = ModuleBuilder::new("ws2_7_calls");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let g = {
        let mut fb = mb.function("g", sig);
        fb.set_attrs(callee_attrs);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let c = fb.uconst(Ty::U64, 7);
        fb.ret(vec![c]);
        fb.build()
    };
    let mut fb = mb.function("w", sig);
    fb.set_attrs(caller_attrs);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let r = fb.call(g, vec![]);
    fb.ret(vec![r]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn readonly_function_calling_an_unattributed_function_is_refused() {
    assert_claim_violated(
        &call_module(readonly(), FuncAttrs::default()),
        "readonly",
        "call @g",
    );
    // Mutation control: the same edge to a readonly or readnone callee.
    assert_valid(&call_module(readonly(), readonly()));
    assert_valid(&call_module(readonly(), readnone()));
}

#[test]
fn readnone_function_requires_a_readnone_callee() {
    assert_claim_violated(&call_module(readnone(), readonly()), "readnone", "call @g");
    assert_claim_violated(
        &call_module(readnone(), FuncAttrs::default()),
        "readnone",
        "call @g",
    );
    assert_valid(&call_module(readnone(), readnone()));
}

#[test]
fn a_readnone_declaration_discharges_the_edge_as_a_claim() {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_7_decl_edge", pinned_target());
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let ext = mb.declare_function("ext", sig);
    let mut fb = mb.function("w", sig);
    fb.set_attrs(readnone());
    let e = fb.create_block();
    fb.switch_to_block(e);
    let r = fb.call(ext, vec![]);
    fb.ret(vec![r]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errors = validate_module(&module);
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::FuncAttrClaimViolated { inst, .. }] if inst.starts_with("call @ext")
        ),
        "{errors:?}"
    );
    module.functions[0].attrs = readnone();
    assert_eq!(validate_module(&module), []);
}

#[test]
fn standalone_validation_fails_call_edges_closed() {
    let module = call_module(readnone(), readnone());
    assert_eq!(validate_module(&module), []);
    let errors = validate_function(&module.functions[1]);
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::FuncAttrClaimViolated { attr: "readnone", inst, .. }]
                if inst.contains("without module context")
        ),
        "{errors:?}"
    );
}

// ---------------------------------------------------------------------------
// (a) mutation controls — the root trace
// ---------------------------------------------------------------------------

#[test]
fn root_trace_follows_gep_from_alloca_but_not_from_param() {
    let through_gep = |from_param: bool| {
        effect_module(readnone(), move |fb, p| {
            let slot = fb.alloca(Ty::U64);
            let zero = fb.iconst(Ty::I64, 0);
            let base = if from_param { p } else { slot };
            let field = fb.gep(Ty::U64, base, vec![zero]);
            let five = fb.uconst(Ty::U64, 5);
            fb.store(Ty::U64, field, five);
        })
    };
    assert_valid(&through_gep(false));
    assert_claim_violated(&through_gep(true), "readnone", "store");
}

#[test]
fn root_trace_follows_copy_and_ptrtoptr_from_alloca() {
    let module = effect_module(readnone(), |fb, _| {
        let slot = fb.alloca(Ty::U64);
        let copied = fb.copy(Ty::Ptr, slot);
        let typed = fb.cast(
            CastOp::PtrToPtr,
            Ty::Ptr,
            Ty::PtrMut(Box::new(Ty::U64)),
            copied,
        );
        let five = fb.uconst(Ty::U64, 5);
        fb.store(Ty::U64, typed, five);
    });
    assert_valid(&module);
}

/// `select %c, %alloca, %param` is a ROOT: a trace that followed `Select`
/// would launder the parameter pointer into the alloca exemption.
#[test]
fn root_trace_does_not_follow_select() {
    let module = effect_module(readnone(), |fb, p| {
        let slot = fb.alloca(Ty::U64);
        let c = fb.bool_const(true);
        let either = fb.select(Ty::Ptr, c, slot, p);
        let five = fb.uconst(Ty::U64, 5);
        fb.store(Ty::U64, either, five);
    });
    assert_claim_violated(&module, "readnone", "store");
}

/// A loop-carried block parameter is a ROOT, even when its first incoming
/// value is the alloca.
#[test]
fn root_trace_does_not_follow_a_block_parameter() {
    let module = effect_module(readnone(), |fb, p| {
        let slot = fb.alloca(Ty::U64);
        let header = fb.create_block();
        let exit = fb.create_block();
        let q = fb.add_block_param(header, Ty::Ptr);
        fb.br(header, vec![slot]);
        fb.switch_to_block(header);
        let five = fb.uconst(Ty::U64, 5);
        fb.store(Ty::U64, q, five);
        let c = fb.bool_const(false);
        fb.condbr(c, header, vec![p], exit, vec![]);
        fb.switch_to_block(exit);
    });
    assert_claim_violated(&module, "readnone", "store");
}

/// `inttoptr (ptrtoint %alloca)` is a ROOT: the integer round trip forgets
/// provenance.
#[test]
fn root_trace_does_not_follow_inttoptr() {
    let module = effect_module(readnone(), |fb, _| {
        let slot = fb.alloca(Ty::U64);
        let addr = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, slot);
        let back = fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, addr);
        let five = fb.uconst(Ty::U64, 5);
        fb.store(Ty::U64, back, five);
    });
    assert_claim_violated(&module, "readnone", "store");
}

// ---------------------------------------------------------------------------
// (b) borrow structure
// ---------------------------------------------------------------------------

/// `fn w(p: <param_ty>) { <body> ; ret }`.
fn borrow_module(param_ty: Ty, body: impl FnOnce(&mut FunctionBuilder<'_>, ValueId)) -> Module {
    let mut mb = ModuleBuilder::new("ws2_7_borrows");
    let sig = mb.add_func_type(vec![param_ty.clone()], vec![]);
    let mut fb = mb.function("w", sig);
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, param_ty);
    fb.switch_to_block(entry);
    body(&mut fb, p);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn assert_only(module: &Module, pred: impl Fn(&ValidationError) -> bool, what: &str) {
    for errors in [
        validate_module(module),
        validate_module_for_codegen(&licensed(module)),
        validate_function(&module.functions[0]),
    ] {
        assert!(
            errors.len() == 1 && pred(&errors[0]),
            "expected exactly {what}, got {errors:?}"
        );
    }
}

fn is_mut_through_shared(error: &ValidationError) -> bool {
    matches!(
        error,
        ValidationError::BorrowMutThroughSharedRef { block: 0 }
    )
}

fn is_end_of_non_borrow(error: &ValidationError) -> bool {
    matches!(error, ValidationError::EndBorrowOfNonBorrow { block: 0 })
}

fn ref_u64() -> Ty {
    Ty::Ref(Box::new(Ty::U64))
}

fn ref_mut_u64() -> Ty {
    Ty::RefMut(Box::new(Ty::U64))
}

#[test]
fn borrow_and_end_borrow_pair_validates() {
    assert_valid(&borrow_module(ref_u64(), |fb, p| {
        let b = fb.borrow(p);
        let _ = fb.load(Ty::U64, b);
        fb.end_borrow(b);
    }));
    assert_valid(&borrow_module(ref_mut_u64(), |fb, p| {
        let b = fb.borrow_mut(p);
        let five = fb.uconst(Ty::U64, 5);
        fb.store(Ty::U64, b, five);
        fb.end_borrow(b);
    }));
}

/// A mutable reborrow of a mutable borrow, and a shared reborrow of either,
/// are the ordinary Rust shapes and stay admitted.
#[test]
fn reborrows_that_do_not_upgrade_validate() {
    assert_valid(&borrow_module(ref_mut_u64(), |fb, p| {
        let outer = fb.borrow_mut(p);
        let inner = fb.borrow_mut(outer);
        let shared = fb.borrow(inner);
        fb.end_borrow(shared);
        fb.end_borrow(inner);
        fb.end_borrow(outer);
    }));
}

/// c15 3a: `BorrowMut` of a `Ref(U64)` parameter.
#[test]
fn c15_3a_borrow_mut_through_shared_ref_param_is_refused() {
    let body = |fb: &mut FunctionBuilder<'_>, p| {
        let b = fb.borrow_mut(p);
        let five = fb.uconst(Ty::U64, 5);
        fb.store(Ty::U64, b, five);
        fb.end_borrow(b);
    };
    assert_valid(&borrow_module(ref_mut_u64(), body));
    assert_only(
        &borrow_module(ref_u64(), body),
        is_mut_through_shared,
        "BorrowMutThroughSharedRef",
    );
    assert_only(
        &borrow_module(Ty::PtrConst(Box::new(Ty::U64)), body),
        is_mut_through_shared,
        "BorrowMutThroughSharedRef",
    );
}

/// Mutation control for a TYPE-ONLY rule: `%r = borrow %x; borrow_mut %r` —
/// the shared borrow's result is typed `Ptr`, so only the root trace sees it.
#[test]
fn borrow_mut_of_a_shared_borrow_result_is_refused() {
    let module = borrow_module(Ty::Ptr, |fb, p| {
        let shared = fb.borrow(p);
        let upgraded = fb.borrow_mut(shared);
        fb.end_borrow(upgraded);
        fb.end_borrow(shared);
    });
    let shared = module.functions[0].blocks[0]
        .body
        .iter()
        .find(|n| matches!(n.inst, Inst::Borrow { .. }))
        .map(|n| n.results[0])
        .expect("the shared borrow");
    let typed = module.functions[0].typed_values(&module);
    assert!(
        typed.iter().any(|m| m.value == shared && m.ty == Ty::Ptr),
        "the shared borrow result is typed ptr, so a type-only rule misses it: {typed:?}"
    );
    assert_only(&module, is_mut_through_shared, "BorrowMutThroughSharedRef");
}

#[test]
fn borrow_mut_rooted_at_a_shared_borrow_through_the_trace_is_refused() {
    for hop in 0..3 {
        let module = borrow_module(Ty::Ptr, |fb, p| {
            let shared = fb.borrow(p);
            let via = match hop {
                0 => fb.copy(Ty::Ptr, shared),
                1 => {
                    let zero = fb.iconst(Ty::I64, 0);
                    fb.gep(Ty::U64, shared, vec![zero])
                }
                _ => fb.cast(
                    CastOp::PtrToPtr,
                    Ty::Ptr,
                    Ty::PtrMut(Box::new(Ty::U64)),
                    shared,
                ),
            };
            let upgraded = fb.borrow_mut(via);
            fb.end_borrow(upgraded);
            fb.end_borrow(shared);
        });
        assert_only(&module, is_mut_through_shared, "BorrowMutThroughSharedRef");
    }
}

#[test]
fn end_borrow_of_a_load_result_is_refused() {
    let module = borrow_module(Ty::Ptr, |fb, p| {
        let loaded = fb.load(Ty::Ptr, p);
        fb.end_borrow(loaded);
    });
    assert_only(&module, is_end_of_non_borrow, "EndBorrowOfNonBorrow");
    // Nor of a parameter.
    let module = borrow_module(ref_u64(), |fb, p| fb.end_borrow(p));
    assert_only(&module, is_end_of_non_borrow, "EndBorrowOfNonBorrow");
}

// ---------------------------------------------------------------------------
// Ported ratchets (2026-09-17 proof program, Part B)
// ---------------------------------------------------------------------------

/// `b2.gap.readnone_claim_on_a_storing_function_accepted`, ported in shape:
/// `b2_bump_into(x: u64, out: ptr) -> u64 { r = x + 1; *out = r; r }` stamped
/// `readnone` + `readonly`. The ratchet asserted the errors were EMPTY; the
/// hole is closed, so the named claim violation is reported.
#[test]
fn ratchet_b2_gap_readnone_claim_on_a_storing_function_accepted() {
    let build = |attrs: FuncAttrs| {
        let mut mb = ModuleBuilder::new("b2_readnone");
        let sig = mb.add_func_type(vec![Ty::U64, Ty::Ptr], vec![Ty::U64]);
        let mut fb = mb.function("b2_bump_into", sig);
        fb.set_producer(Producer::TRust);
        fb.set_attrs(attrs);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        let out = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        let one = fb.uconst(Ty::U64, 1);
        let r = fb.add(Ty::U64, x, one);
        fb.store(Ty::U64, out, r);
        fb.ret(vec![r]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    assert_valid(&build(FuncAttrs::default()));
    let errors = validate_module(&build(FuncAttrs {
        readnone: true,
        readonly: true,
        ..FuncAttrs::default()
    }));
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::FuncAttrClaimViolated { function, attr: "readnone", block: 0, inst }]
                if function == "b2_bump_into" && inst.starts_with("store")
        ),
        "{errors:?}"
    );
}

/// The Part B `build_borrow_rc(0)` module: a Rust `&mut` bump, a Clean `&`
/// read, a Clean `Rc` get, and a `program` that returns 42.
fn build_borrow_rc() -> Module {
    let mut mb = ModuleBuilder::new("b6_borrow_rc");
    let refm = ref_mut_u64();
    let refs = ref_u64();
    let rc = Ty::Rc(Box::new(Ty::U64));
    let bump_ty = mb.add_func_type(vec![refm.clone()], vec![]);
    let read_ty = mb.add_func_type(vec![refs.clone()], vec![Ty::U64]);
    let rc_ty = mb.add_func_type(vec![rc.clone()], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let bump = {
        // Stamped `TRust`, so spelled as a Rust producer spells it: the `&mut`
        // parameter is used directly, never re-borrowed through the permission
        // machine (SPEC "A Rust reference carries no permission instruction").
        let mut fb = mb.function("rust_bump", bump_ty);
        fb.set_producer(Producer::TRust);
        let e = fb.create_block();
        let r = fb.add_block_param(e, refm.clone());
        fb.switch_to_block(e);
        let v = fb.load(Ty::U64, r);
        let one = fb.uconst(Ty::U64, 1);
        let s = fb.add(Ty::U64, v, one);
        fb.store(Ty::U64, r, s);
        fb.ret(vec![]);
        fb.build()
    };
    let read = {
        let mut fb = mb.function("clean_read", read_ty);
        fb.set_producer(Producer::Clean);
        let e = fb.create_block();
        let r = fb.add_block_param(e, refs.clone());
        fb.switch_to_block(e);
        let b = fb.borrow(r);
        let v = fb.load(Ty::U64, b);
        fb.end_borrow(b);
        fb.ret(vec![v]);
        fb.build()
    };
    let rc_get = {
        let mut fb = mb.function("clean_rc_get", rc_ty);
        fb.set_producer(Producer::Clean);
        let e = fb.create_block();
        let r = fb.add_block_param(e, rc.clone());
        fb.switch_to_block(e);
        fb.retain(r);
        let shared = fb.is_unique(r);
        let v = fb.load(Ty::U64, r);
        fb.release(r);
        let unique = fb.is_unique(r);
        let s = fb.zext(Ty::Bool, Ty::U64, shared);
        let u = fb.zext(Ty::Bool, Ty::U64, unique);
        let ten = fb.uconst(Ty::U64, 10);
        let s10 = fb.mul(Ty::U64, s, ten);
        let a = fb.add(Ty::U64, v, s10);
        let out = fb.add(Ty::U64, a, u);
        fb.ret(vec![out]);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let slot = fb.alloca(Ty::U64);
        let c = fb.uconst(Ty::U64, 30);
        fb.store(Ty::U64, slot, c);
        let rm = fb.cast(CastOp::PtrToPtr, Ty::Ptr, refm, slot);
        fb.call_void(bump, vec![rm]);
        let rs = fb.cast(CastOp::PtrToPtr, Ty::Ptr, refs, slot);
        let got = fb.call(read, vec![rs]);
        let cell = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::CleanHeap);
        let ten = fb.uconst(Ty::U64, 10);
        fb.store(Ty::U64, cell, ten);
        let rcv = fb.cast(CastOp::PtrToPtr, Ty::Ptr, rc, cell);
        let r = fb.call(rc_get, vec![rcv]);
        fb.release(cell);
        let out = fb.add(Ty::U64, got, r);
        fb.ret(vec![out]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn run_program(module: &Module) -> Option<u128> {
    let program = module.function_by_name("program")?;
    let outcome = Interpreter::with_module(module)
        .execute_function(program, [])
        .ok()?;
    outcome.returns.first()?.as_int().map(|i| i.as_unsigned())
}

fn clean_read(module: &mut Module) -> &mut trust_ir::Function {
    module
        .functions
        .iter_mut()
        .find(|f| f.name == "clean_read")
        .expect("clean_read")
}

/// `b6.ref_refmut.borrow_discipline_unchecked`, SPLIT (WS2.7).
///
/// Structural half — `BorrowMut` taken through the Clean `&u64` parameter —
/// flips to PASS: it is refused by name under `validate_module_for_codegen`.
#[test]
fn ratchet_b6_ref_refmut_borrow_discipline_unchecked_structural_half() {
    let baseline = build_borrow_rc();
    assert_eq!(validate_module_for_codegen(&licensed(&baseline)), []);
    assert_eq!(run_program(&baseline), Some(42));

    let mut mut_through_shared = baseline.clone();
    let mut replaced = 0;
    for node in clean_read(&mut mut_through_shared)
        .blocks
        .iter_mut()
        .flat_map(|b| b.body.iter_mut())
    {
        if let Inst::Borrow { ptr } = node.inst {
            node.inst = Inst::BorrowMut { ptr };
            replaced += 1;
        }
    }
    assert_eq!(replaced, 1);
    let errors = validate_module_for_codegen(&licensed(&mut_through_shared));
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::BorrowMutThroughSharedRef { block: 0 }]
        ),
        "{errors:?}"
    );
}

/// Liveness half — a `Borrow` with no `EndBorrow` — is re-labelled
/// RATIFIED-PRODUCER-OBLIGATION (`TRUST.md` item 12): it still validates and
/// still runs, and this test pins that NON-guarantee so it cannot be misread
/// as one. A flow-sensitive borrow checker is what would flip it.
#[test]
fn ratchet_b6_ref_refmut_borrow_discipline_unchecked_liveness_half_ratified_producer_obligation() {
    let mut no_end = build_borrow_rc();
    clean_read(&mut no_end).blocks[0]
        .body
        .retain(|n| !matches!(n.inst, Inst::EndBorrow { .. }));
    assert_eq!(validate_module_for_codegen(&licensed(&no_end)), []);
    assert_eq!(run_program(&no_end), Some(42));
}

// ---------------------------------------------------------------------------
// Adversarial review (WS2.7): shapes the implementation was not written for
// ---------------------------------------------------------------------------

fn is_mut_through_shared_in(block: u32) -> impl Fn(&ValidationError) -> bool {
    move |error| {
        matches!(
            error,
            ValidationError::BorrowMutThroughSharedRef { block: b } if *b == block
        )
    }
}

/// REVIEW BREAK: the shared-borrow question is ANY-root, so stopping at a
/// `Select` was the permissive direction — `select %c, %r, %r` (both arms a
/// shared borrow) upgraded to `borrow_mut` and validated. Both arms are now
/// followed. Mutation control: the same select over two MUTABLE borrows (a
/// legitimate reborrow) still validates.
#[test]
fn review_borrow_mut_through_a_select_of_a_shared_borrow_is_refused() {
    let through_select = |shared_arm: bool, other_is_param: bool| {
        borrow_module(Ty::Ptr, move |fb, p| {
            let left = if shared_arm {
                fb.borrow(p)
            } else {
                fb.borrow_mut(p)
            };
            let right = if other_is_param { p } else { left };
            let c = fb.bool_const(true);
            let either = fb.select(Ty::Ptr, c, left, right);
            let upgraded = fb.borrow_mut(either);
            fb.end_borrow(upgraded);
            fb.end_borrow(left);
        })
    };
    assert_valid(&through_select(false, false));
    assert_valid(&through_select(false, true));
    for other_is_param in [false, true] {
        assert_only(
            &through_select(true, other_is_param),
            is_mut_through_shared,
            "BorrowMutThroughSharedRef",
        );
    }
}

/// REVIEW BREAK: a shared borrow carried into a block parameter (forward
/// edge, and loop-carried on the back edge) laundered the upgrade. Every
/// incoming argument is now followed; a cycle adds no root. Mutation control:
/// the same CFG carrying the raw parameter validates.
#[test]
fn review_borrow_mut_through_a_block_parameter_carrying_a_shared_borrow_is_refused() {
    // `back_edge == false`: `br bb1(%arg)`. `back_edge == true`: bb1 loops
    // to itself carrying `%arg` while its entry edge carries the parameter.
    let through_param = |shared: bool, back_edge: bool| {
        borrow_module(Ty::Ptr, move |fb, p| {
            let arg = if shared { fb.borrow(p) } else { p };
            let header = fb.create_block();
            let exit = fb.create_block();
            let q = fb.add_block_param(header, Ty::Ptr);
            fb.br(header, vec![if back_edge { p } else { arg }]);
            fb.switch_to_block(header);
            let upgraded = fb.borrow_mut(q);
            fb.end_borrow(upgraded);
            let c = fb.bool_const(false);
            fb.condbr(
                c,
                header,
                vec![if back_edge { arg } else { q }],
                exit,
                vec![],
            );
            fb.switch_to_block(exit);
        })
    };
    for back_edge in [false, true] {
        assert_valid(&through_param(false, back_edge));
        assert_only(
            &through_param(true, back_edge),
            is_mut_through_shared_in(1),
            "BorrowMutThroughSharedRef in bb1",
        );
    }
}

/// REVIEW PIN: `Invoke` is a call edge exactly like `Call` — the implementer
/// tested only `Call`. An invoke of an unattributed callee from a `readnone`
/// body is refused; the same invoke of a `readnone` callee validates (the
/// landing pad and `resume` carry no claim-relevant effect).
#[test]
fn review_invoke_edge_is_checked_like_a_call() {
    let build = |callee_attrs: FuncAttrs| {
        let mut mb = ModuleBuilder::new("ws2_7_invoke");
        let sig = mb.add_func_type(vec![], vec![Ty::U64]);
        let g = {
            let mut fb = mb.function("g", sig);
            fb.set_attrs(callee_attrs);
            let e = fb.create_block();
            fb.switch_to_block(e);
            let c = fb.uconst(Ty::U64, 7);
            fb.ret(vec![c]);
            fb.build()
        };
        let mut fb = mb.function("w", sig);
        fb.set_attrs(readnone());
        let entry = fb.create_block();
        let normal = fb.create_block();
        let unwind = fb.create_block();
        fb.switch_to_block(entry);
        let r = fb.invoke(g, vec![], normal, vec![], unwind);
        fb.switch_to_block(normal);
        fb.ret(vec![r]);
        fb.switch_to_block(unwind);
        let (exception, _) = fb.landingpad(true, vec![]);
        fb.resume(exception);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    assert_valid(&build(readnone()));
    assert_claim_violated(&build(FuncAttrs::default()), "readnone", "invoke @g");
    assert_claim_violated(&build(readonly()), "readnone", "invoke @g");
}

/// REVIEW PIN: a module global is caller-visible memory, never an alloca
/// root. `readonly` admits a load through `GlobalAddr` and refuses a store;
/// `readnone` refuses the load too.
#[test]
fn review_global_memory_is_not_exempt() {
    let build = |attrs: FuncAttrs, store: bool| {
        let mut mb = ModuleBuilder::new("ws2_7_global");
        mb.add_global(trust_ir::Global {
            name: "COUNTER".into(),
            ty: Ty::U64,
            mutable: true,
            initializer: Some(trust_ir::Constant::Int(0)),
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        let sig = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("w", sig);
        fb.set_attrs(attrs);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let g = fb.global_addr(trust_ir::value::GlobalId::new(0));
        if store {
            let one = fb.uconst(Ty::U64, 1);
            fb.store(Ty::U64, g, one);
        } else {
            let _ = fb.load(Ty::U64, g);
        }
        fb.ret(vec![]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    assert_valid(&build(readonly(), false));
    assert_claim_violated(&build(readonly(), true), "readonly", "store");
    assert_claim_violated(&build(readnone(), false), "readnone", "load");
}

/// REVIEW PIN: the alloca exemption covers only NON-synchronizing accesses.
/// A `cmpxchg` on the function's own alloca is exempt when both orderings are
/// `Relaxed`, and refused when either (here only the FAILURE ordering)
/// synchronizes; a relaxed `atomicrmw` through a parameter is a write and is
/// refused under `readonly`.
#[test]
fn review_atomic_orderings_and_rmw_through_a_parameter() {
    let cmpxchg = |failure: Ordering| {
        effect_module(readnone(), move |fb, _| {
            let slot = fb.alloca(Ty::U64);
            let zero = fb.uconst(Ty::U64, 0);
            fb.store(Ty::U64, slot, zero);
            let one = fb.uconst(Ty::U64, 1);
            let _ = fb.cmpxchg(Ty::U64, slot, zero, one, Ordering::Relaxed, failure);
        })
    };
    assert_valid(&cmpxchg(Ordering::Relaxed));
    assert_claim_violated(&cmpxchg(Ordering::Acquire), "readnone", "cmpxchg");

    let rmw = |attrs: FuncAttrs| {
        effect_module(attrs, |fb, p| {
            let one = fb.uconst(Ty::U64, 1);
            let _ = fb.atomic_rmw(
                trust_ir::inst::AtomicRMWOp::Add,
                Ty::U64,
                p,
                one,
                Ordering::Relaxed,
            );
        })
    };
    assert_valid(&rmw(FuncAttrs::default()));
    assert_claim_violated(&rmw(readonly()), "readonly", "atomic_rmw");
}

// ---------------------------------------------------------------------------
// A Rust reference carries no permission instruction (docs/SPEC_RATIFICATIONS.md,
// the section of that name): the validator half, keyed on `Producer::TRust`.
// ---------------------------------------------------------------------------

/// `fn w(p: &mut u64) { <body> ; ret }`, stamped `producer`.
fn stamped_borrow_module(
    producer: Option<Producer>,
    body: impl FnOnce(&mut FunctionBuilder<'_>, ValueId),
) -> Module {
    let mut module = borrow_module(ref_mut_u64(), body);
    module.functions[0].producer = producer;
    module
}

/// A named body over the `&mut u64` parameter.
type PermissionShape = (&'static str, fn(&mut FunctionBuilder<'_>, ValueId));

/// The three permission instructions, each the only one in its body, each in
/// the shape the WS2.7 structure checks accept (so a refusal below is the
/// producer rule and nothing else).
fn permission_shapes() -> [PermissionShape; 3] {
    [
        ("borrow", |fb, p| {
            let b = fb.borrow(p);
            let _ = fb.load(Ty::U64, b);
        }),
        ("borrow_mut", |fb, p| {
            let b = fb.borrow_mut(p);
            let five = fb.uconst(Ty::U64, 5);
            fb.store(Ty::U64, b, five);
        }),
        ("end_borrow", |fb, p| {
            let b = fb.borrow(p);
            fb.end_borrow(b);
        }),
    ]
}

fn rust_reference_refusals(errors: &[ValidationError]) -> Vec<(u32, usize)> {
    errors
        .iter()
        .filter_map(|error| match error {
            ValidationError::RustReferenceAsPermissionBorrow {
                function,
                block,
                inst_index,
            } if function == "w" => Some((*block, *inst_index)),
            _ => None,
        })
        .collect()
}

/// A permission instruction in a function stamped `Producer::TRust` is refused
/// by name at every node that carries one, by plain `validate_module`, by the
/// codegen gate and by `validate_function`. Fails with the rule deleted.
#[test]
fn rust_producer_permission_borrow_is_refused() {
    let expected: [&[(u32, usize)]; 3] = [&[(0, 0)], &[(0, 0)], &[(0, 0), (0, 1)]];
    for ((name, body), expected) in permission_shapes().into_iter().zip(expected) {
        let module = stamped_borrow_module(Some(Producer::TRust), body);
        for errors in [
            validate_module(&module),
            validate_module_for_codegen(&licensed(&module)),
            validate_function(&module.functions[0]),
        ] {
            assert_eq!(
                rust_reference_refusals(&errors),
                expected,
                "{name}: {errors:?}"
            );
            assert_eq!(
                errors.len(),
                expected.len(),
                "{name}: only the rule fires: {errors:?}"
            );
        }
    }
}

/// The Rust producers' spelling of the same references, in a function stamped
/// `Producer::TRust`: the parameter used directly, and a `Copy` of the address
/// at its own type (`&mut u64`).
#[test]
fn rust_producer_reference_as_copy_validates() {
    assert_valid(&stamped_borrow_module(Some(Producer::TRust), |fb, p| {
        let five = fb.uconst(Ty::U64, 5);
        fb.store(Ty::U64, p, five);
        let r = fb.copy(ref_mut_u64(), p);
        let _ = fb.load(Ty::U64, r);
    }));
}

/// The permission machine stays the format's model for every other producer:
/// unstamped, `TrustIr` (the MIR bridge, for the bundle check's `RustMir` key) and
/// `Clean`. Fails if the rule is keyed on every producer or on `TrustIr`.
#[test]
fn permission_machine_stays_valid_for_other_producers() {
    for producer in [None, Some(Producer::TrustIr), Some(Producer::Clean)] {
        for (name, body) in permission_shapes() {
            let module = stamped_borrow_module(producer.clone(), body);
            let errors = validate_module(&module);
            assert!(
                rust_reference_refusals(&errors).is_empty(),
                "{producer:?} {name}: {errors:?}"
            );
        }
        assert_valid(&stamped_borrow_module(producer, |fb, p| {
            let b = fb.borrow(p);
            let _ = fb.load(Ty::U64, b);
            fb.end_borrow(b);
        }));
    }
}
