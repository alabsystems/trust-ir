// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// M0 — self-hosting acceptance gate.
//
// The end goal is "lower trust-ir-the-crate (and the rest of the Trust
// toolchain) to trust-ir and validate it." That full test needs a frontend
// (tRust), which does not exist yet, so this file is the achievable PROXY: a
// hand-built module exercising the self-hosting-critical constructs, asserting
// it expresses + validates + executes. Landed criteria are active tests; this
// file doubles as a living regression checklist. Unimplemented criteria belong
// in the roadmap until they can become bounded, fail-closed tests.
//
// See docs/roadmap/README.md (Wave plan) and docs/roadmap/B*-*.md.

use trust_ir::interpret::Interpreter;
use trust_ir::ty::Ty;
use trust_ir::value::GlobalId;
use trust_ir::{Constant, Global, Linkage};
use trust_ir_build::{ModuleBuilder, validate_module};

/// PASSES TODAY (B1 landed): a function that reads a module `static` through
/// `GlobalAddr` and computes with it — the shape every compiler emits for a
/// `static` / `&str` literal — now expresses, validates, and executes.
#[test]
fn m0_static_addressing_expresses_validates_executes() {
    let mut mb = ModuleBuilder::new("m0_selfhost");
    mb.add_global(Global {
        name: "VERSION_MAJOR".into(),
        ty: Ty::I32,
        mutable: false,
        initializer: Some(Constant::Int(2)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });

    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("version_plus_one", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let p = fb.global_addr(GlobalId::new(0));
    let v = fb.load(Ty::I32, p);
    let one = fb.iconst(Ty::I32, 1);
    let sum = fb.add(Ty::I32, v, one);
    fb.ret(vec![sum]);
    fb.build();
    let module = mb.build();

    assert!(
        validate_module(&module).is_empty(),
        "self-hosting static-addressing module must validate: {:?}",
        validate_module(&module)
    );
    let out = Interpreter::with_module(&module)
        .execute_func(module.functions[0].id, [])
        .expect("executes");
    assert_eq!(out.returns[0].as_int().unwrap().as_signed(), 3);
}

// ---------------------------------------------------------------------------
// Landed acceptance criteria for the self-hosting blockers. Every criterion
// below is active: a regression fails instead of silently becoming an ignored
// placeholder.
// ---------------------------------------------------------------------------

/// B2 — heap allocation. The toolchain is Box/Vec/String/HashMap-heavy; today
/// allocation is unrepresentable and unexecutable while `Dealloc` is modeled,
/// so the alloc/dealloc pair is broken. Acceptance: a `HeapAlloc { size, align }`
/// (or an alloc-binding annotation on a `Call`) that the interpreter executes
/// with a `rustHeap` origin and `validate_module` pairs with its `Dealloc`.
/// See docs/roadmap/B2-heap-alloc.md.
#[test]
fn m0_heap_allocation_pairs_with_dealloc() {
    // B2 landed: heap_alloc -> store -> load -> dealloc, all validated + executed.
    use trust_ir::inst::AllocOrigin;
    let mut mb = ModuleBuilder::new("m0_heap");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("box_roundtrip", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    let p = fb.heap_alloc(Ty::I32, None, None, AllocOrigin::RustHeap);
    fb.store(Ty::I32, p, x);
    let v = fb.load(Ty::I32, p);
    fb.dealloc(p);
    fb.ret(vec![v]);
    fb.build();
    let module = mb.build();

    assert!(
        validate_module(&module).is_empty(),
        "heap alloc/store/load/dealloc must validate: {:?}",
        validate_module(&module)
    );
    let out = Interpreter::with_module(&module)
        .execute_func(
            module.functions[0].id,
            [trust_ir::interpret::InterpretValue::int(Ty::I32, 77).unwrap()],
        )
        .expect("executes");
    assert_eq!(out.returns[0].as_int().unwrap().as_signed(), 77);
}

/// B5 — cross-function proof composition. Acceptance: a caller that discharges
/// an obligation via a callee's postcondition through a `ProofContext` on the
/// `Call`, where `validate_module` confirms "this exact callee discharged this
/// exact obligation" (not merely "discharged somewhere in the module").
/// See docs/roadmap/B5-proofcontext-call.md.
#[test]
fn m0_callsite_proof_composition_requires_authority_and_scope() {
    use trust_ir::Inst;
    use trust_ir::proof::{ObligationKind, ProofContext, ProofObligation, ProofStatus};
    use trust_ir::value::{FuncId, ProofId};

    // callee = fn#0: returns a constant — stands in for a function whose
    // postcondition obligation has been discharged.
    let mut mb = ModuleBuilder::new("m0_proof_composition");
    let cft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("callee", cft);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let z = fb.iconst(Ty::I32, 7);
    fb.ret(vec![z]);
    fb.build();

    // caller = fn#1: calls the callee and returns its result.
    let kft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("caller", kft);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let r = fb.call(FuncId::new(0), vec![]);
    fb.ret(vec![r]);
    fb.build();

    let mut module = mb.build();

    // The callee's postcondition obligation is scoped to the callee but remains
    // Pending: this structural fixture has no proof engine and must not mint a
    // discharge from a public label.
    let mut postcond = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Pending,
        "callee establishes its return postcondition",
    );
    postcond.function = Some(FuncId::new(0));
    module.proof_obligations.push(postcond);

    // The per-call-site ProofContext (B5): the caller ASSUMES the callee's
    // postcondition (#0) after the call returns — the Lean side of
    // this transfer is `proof_context_assume_sound` (CallProps.lean).
    let call_idx = module.functions[1].blocks[0]
        .body
        .iter()
        .position(|n| matches!(n.inst, Inst::Call { .. }))
        .expect("caller has a Call node");
    module.functions[1].blocks[0].body[call_idx].proof_context = Some(ProofContext {
        assumes: vec![ProofId::new(0)],
        establishes: vec![],
    });

    // Scope and existence alone do not authorize the assumption. Until an
    // exact certificate is replayed, the validator must fail closed.
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|error| matches!(
            error,
            trust_ir_build::validate::ValidationError::ProofContextAssumeNotAuthoritative {
                obligation: 0,
                ..
            }
        )),
        "scoped pending call-site assumption must be rejected: {errors:?}"
    );

    // Executes end-to-end (ProofContext is proof metadata; semantics unchanged).
    let out = Interpreter::with_module(&module)
        .execute_func(module.functions[1].id, [])
        .expect("executes");
    assert_eq!(out.returns[0].as_int().unwrap().as_signed(), 7);

    // SCOPED, not "anything goes": a ProofContext that references an obligation
    // absent from the module is rejected — a caller cannot fabricate a discharge.
    let mut bad = module.clone();
    bad.functions[1].blocks[0].body[call_idx].proof_context = Some(ProofContext {
        assumes: vec![ProofId::new(99)],
        establishes: vec![],
    });
    let errs = validate_module(&bad);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::ProofContextUnknownObligation { .. }
        )),
        "a ProofContext referencing a non-existent obligation must be rejected: {errs:?}"
    );
}
