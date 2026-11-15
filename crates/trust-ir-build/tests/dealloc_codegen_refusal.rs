//! G18-1, re-decided 2026-09-27: `Inst::Dealloc` is refused for codegen
//! REGARDLESS of how well its pointer's provenance can be recovered. The
//! shapes below are exactly the ones a backend analysis can resolve to one
//! allocator and one layout (the set trust-cg's `translate_dealloc` lowered
//! from 2026-09-18 until its conformance change, trust-cg main c1b7c2c54,
//! deleted it), plus the ones it cannot; every one is well-formed and every
//! `Dealloc` is refused exactly once. A provenance exemption in
//! `codegen_lowerability_errors` fails this file by function name.
//!
//! The refusal is in EVERY body a consumer would lower, not only a licensed
//! one: the second test holds a claim-less body (`body_gate: None`) and an
//! affirmatively `Ungated` body under `UnlicensedBodyPolicy::Permit`, the
//! policy of a consumer that admits claim-less bodies (trust-cg's). An
//! exemption keyed on the license fails that test and not the first.

use trust_ir::inst::AllocOrigin;
use trust_ir::{BinOp, CastOp, ICmpOp, Inst, Module, Ty};
use trust_ir_build::{
    CodegenAdmission, ModuleBuilder, UnlicensedBodyPolicy, ValidationError, validate_module,
    validate_module_for_codegen, validate_module_for_codegen_with,
};

fn gate() -> trust_ir::BodyGate {
    trust_ir::BodyGate::Gated {
        authority: "dealloc-refusal".into(),
        evidence: None,
    }
}

fn corpus() -> Module {
    let mut mb = ModuleBuilder::new("dealloc_codegen_refusal");
    let unit = mb.add_func_type(vec![], vec![]);
    let unary = mb.add_func_type(vec![Ty::U64], vec![]);
    let take_ptr = mb.add_func_type(vec![Ty::Ptr], vec![]);

    // Resolvable: one direct RustHeap allocation (the must-refuse row's shape).
    for (name, origin) in [
        ("rust_direct", AllocOrigin::RustHeap),
        ("cmalloc_direct", AllocOrigin::CMalloc),
    ] {
        let mut f = mb.function(name, unit);
        let e = f.create_block();
        f.switch_to_block(e);
        let c = f.heap_alloc(Ty::U64, None, None, origin);
        f.dealloc(c);
        f.ret(vec![]);
        f.set_body_gate(gate());
        f.build();
    }
    // Resolvable: dynamic count on a direct chain through Copy + PtrToPtr.
    {
        let mut f = mb.function("rust_dynamic_count_through_casts", unary);
        let e = f.create_block();
        let n = f.add_block_param(e, Ty::U64);
        f.switch_to_block(e);
        let c = f.heap_alloc(Ty::U32, Some(n), None, AllocOrigin::RustHeap);
        let copied = f.copy(Ty::Ptr, c);
        let typed = f.cast(
            CastOp::PtrToPtr,
            Ty::Ptr,
            Ty::PtrMut(Box::new(Ty::U32)),
            copied,
        );
        f.dealloc(typed);
        f.ret(vec![]);
        f.set_body_gate(gate());
        f.build();
    }
    // Resolvable: a Select of two same-layout RustHeap allocations.
    {
        let mut f = mb.function("rust_select_same_layout", unary);
        let e = f.create_block();
        let x = f.add_block_param(e, Ty::U64);
        f.switch_to_block(e);
        let a = f.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
        let b = f.heap_alloc(Ty::I64, None, None, AllocOrigin::RustHeap);
        let zero = f.iconst(Ty::U64, 0);
        let cond = f.icmp(ICmpOp::Ne, Ty::U64, x, zero);
        let either = f.select(Ty::Ptr, cond, a, b);
        f.dealloc(either);
        f.ret(vec![]);
        f.set_body_gate(gate());
        f.build();
    }
    // Resolvable: a block-parameter join of two same-layout allocations.
    {
        let mut f = mb.function("rust_join_same_layout", unary);
        let entry = f.create_block();
        let left = f.create_block();
        let right = f.create_block();
        let join = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        let cell = f.add_block_param(join, Ty::Ptr);
        f.switch_to_block(entry);
        let zero = f.iconst(Ty::U64, 0);
        let cond = f.icmp(ICmpOp::Ne, Ty::U64, x, zero);
        f.condbr(cond, left, vec![], right, vec![]);
        f.switch_to_block(left);
        let a = f.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
        f.br(join, vec![a]);
        f.switch_to_block(right);
        let b = f.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
        f.br(join, vec![b]);
        f.switch_to_block(join);
        f.dealloc(cell);
        f.ret(vec![]);
        f.set_body_gate(gate());
        f.build();
    }
    // Unresolvable: a caller's cell, a stack slot, a CleanHeap cell.
    {
        let mut f = mb.function("param_cell", take_ptr);
        let e = f.create_block();
        let p = f.add_block_param(e, Ty::Ptr);
        f.switch_to_block(e);
        f.dealloc(p);
        f.ret(vec![]);
        f.set_body_gate(gate());
        f.build();
    }
    {
        let mut f = mb.function("stack_slot", unit);
        let e = f.create_block();
        f.switch_to_block(e);
        let s = f.alloca(Ty::U64);
        f.dealloc(s);
        f.ret(vec![]);
        f.set_body_gate(gate());
        f.build();
    }
    {
        let mut f = mb.function("clean_cell", unit);
        let e = f.create_block();
        f.switch_to_block(e);
        let c = f.heap_alloc(Ty::U64, None, None, AllocOrigin::CleanHeap);
        f.dealloc(c);
        f.ret(vec![]);
        f.set_body_gate(gate());
        f.build();
    }
    // A loop that re-frees one direct-chain allocation: no Dealloc dominates
    // another, so a dominance-based double-free check cannot see it.
    {
        let mut f = mb.function("loop_refree", unary);
        let entry = f.create_block();
        let body = f.create_block();
        let exit = f.create_block();
        let n = f.add_block_param(entry, Ty::U64);
        let i = f.add_block_param(body, Ty::U64);
        f.switch_to_block(entry);
        let cell = f.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
        let zero = f.iconst(Ty::U64, 0);
        f.br(body, vec![zero]);
        f.switch_to_block(body);
        f.dealloc(cell);
        let one = f.iconst(Ty::U64, 1);
        let next = f.binop(BinOp::Add, Ty::U64, i, one);
        let more = f.icmp(ICmpOp::Ult, Ty::U64, next, n);
        f.condbr(more, body, vec![next], exit, vec![]);
        f.switch_to_block(exit);
        f.ret(vec![]);
        f.set_body_gate(gate());
        f.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn every_dealloc_is_refused_for_codegen_whatever_its_provenance() {
    let module = corpus();
    assert_eq!(
        validate_module(&module),
        [],
        "every shape is well-formed TrustIr"
    );
    let refused = validate_module_for_codegen(&module);
    for func in &module.functions {
        let deallocs = func
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .filter(|n| matches!(n.inst, Inst::Dealloc { .. }))
            .count();
        let named = refused
            .iter()
            .filter(|e| {
                matches!(e, ValidationError::UnlowerableForCodegen { name, inst: "Dealloc", .. }
                    if *name == func.name)
            })
            .count();
        assert!(
            deallocs > 0,
            "{}: corpus function without a Dealloc",
            func.name
        );
        assert_eq!(
            named, deallocs,
            "{}: every Dealloc must be refused for codegen exactly once, whatever the pointer's \
             provenance (G18-1); got {refused:?}",
            func.name
        );
    }
    assert!(
        refused.iter().all(|e| matches!(
            e,
            ValidationError::UnlowerableForCodegen {
                inst: "Dealloc",
                ..
            }
        )),
        "the corpus is licensed and otherwise lowerable: {refused:?}"
    );
}

#[test]
fn dealloc_is_refused_for_codegen_in_a_claimless_body_under_permit() {
    let mut mb = ModuleBuilder::new("dealloc_codegen_refusal_unlicensed");
    let unit = mb.add_func_type(vec![], vec![]);
    // `None` is the claim-less (pre-v41 grandfather) state a Permit consumer
    // admits; `Ungated` is refused as a license under either policy, and its
    // Dealloc must be named too, so the refusal does not ride on the license.
    for (name, body_gate) in [
        ("claimless_rust_direct", None),
        ("ungated_rust_direct", Some(trust_ir::BodyGate::Ungated)),
    ] {
        let mut f = mb.function(name, unit);
        let e = f.create_block();
        f.switch_to_block(e);
        let c = f.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
        f.dealloc(c);
        f.ret(vec![]);
        if let Some(gate) = body_gate {
            f.set_body_gate(gate);
        }
        f.build();
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(
        validate_module(&module),
        [],
        "both bodies are well-formed TrustIr"
    );
    assert_eq!(
        module.functions[0].body_gate, None,
        "the first body must make no licensing claim"
    );
    let refused = validate_module_for_codegen_with(
        &module,
        &CodegenAdmission::pinned().with_unlicensed(UnlicensedBodyPolicy::Permit),
    );
    for func in &module.functions {
        let named: Vec<_> = refused
            .iter()
            .filter(|e| {
                matches!(e, ValidationError::UnlowerableForCodegen { name, inst: "Dealloc", .. }
                    if *name == func.name)
            })
            .collect();
        assert_eq!(
            named.len(),
            1,
            "{}: body under Permit: a Dealloc is refused for codegen in every body, whatever \
             the license policy (G18-1); got {refused:?}",
            func.name
        );
    }
    // Under Permit the claim-less body raises nothing else; the Ungated body
    // is refused as a license as well, which is not what this test is about.
    assert!(
        refused.iter().all(|e| matches!(
            e,
            ValidationError::UnlowerableForCodegen {
                inst: "Dealloc",
                ..
            } | ValidationError::UngatedBodyForCodegen { .. }
        )),
        "claim-less body under Permit: only the Dealloc (and the Ungated license) may be \
         refused: {refused:?}"
    );
}
