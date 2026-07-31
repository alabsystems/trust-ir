// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// B5: per-call-site ProofContext (assumes / establishes).
//
// `InstrNode.proof_context` lets a Call site declare which callee
// postconditions the caller may ASSUME and which callee preconditions it must
// ESTABLISH — the data contract for composing per-function proofs into a
// whole-program proof. Validation: it may only attach to a Call/CallIndirect
// node, and every referenced obligation must exist. B5.1 tightens `assumes`
// on a direct Call: an obligation B4-scoped (`ProofObligation::function`) to
// some function must be scoped to the callee the call names; unscoped
// (`function: None`) obligations stay legacy-tolerated, mirroring
// `validate_inherited_proofs`' B4 policy.
//
// (The Lean soundness theorem for inheritance is tracked separately — see
// docs/roadmap/specs/B5-proofcontext.md.)

use trust_ir::proof::{ObligationKind, ProofContext, ProofObligation, ProofStatus};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, ProofId};
use trust_ir::{Inst, Module};
use trust_ir_build::{ModuleBuilder, validate_module};

/// Build: fn#0 `caller` calls fn#1 `callee`; plus two obligations (#0, #1).
fn caller_callee_module() -> Module {
    let mut mb = ModuleBuilder::new("b5");
    // callee = fn#0
    let cft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("callee", cft);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let z = fb.iconst(Ty::I32, 0);
    fb.ret(vec![z]);
    fb.build();
    // caller = fn#1, calls fn#0
    let kft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("caller", kft);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let r = fb.call(FuncId::new(0), vec![]);
    fb.ret(vec![r]);
    fb.build();

    let mut m = mb.build();
    for (id, kind) in [
        (0u32, ObligationKind::Postcondition),
        (1u32, ObligationKind::Precondition),
    ] {
        m.proof_obligations.push(ProofObligation::new(
            ProofId::new(id),
            kind,
            // These fixtures exercise the structural B5 scope rules, not a
            // proof engine. Keep their rows Pending so they cannot accidentally
            // manufacture discharge authority.
            ProofStatus::Pending,
            "o",
        ));
    }
    m
}

/// Returns (func_idx, block_idx, node_idx) of the Call node in `caller`.
fn call_site(m: &Module) -> (usize, usize, usize) {
    for (fi, f) in m.functions.iter().enumerate() {
        for (bi, b) in f.blocks.iter().enumerate() {
            for (ni, node) in b.body.iter().enumerate() {
                if matches!(node.inst, Inst::Call { .. }) {
                    return (fi, bi, ni);
                }
            }
        }
    }
    panic!("no call node");
}

#[test]
fn pending_assume_is_rejected_even_when_context_is_well_formed() {
    // Both obligations here are UNSCOPED (`function: None`) — the legacy
    // B4-tolerated form, which B5.1 must keep accepting.
    let mut m = caller_callee_module();
    let (fi, bi, ni) = call_site(&m);
    m.functions[fi].blocks[bi].body[ni].proof_context = Some(ProofContext {
        assumes: vec![ProofId::new(0)],
        establishes: vec![ProofId::new(1)],
    });
    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|error| matches!(
            error,
            trust_ir_build::validate::ValidationError::ProofContextAssumeNotAuthoritative {
                obligation: 0,
                ..
            }
        )),
        "structural well-formedness must not authorize a pending assumption: {errors:?}"
    );
    // (Binary v6 round-trip of proof_context is exercised by the conformance
    // corpus once a fixture carries one; here we keep to the always-available
    // validate path so this test needs no extra features.)
}

#[test]
fn pending_assume_scoped_to_named_callee_is_still_rejected() {
    // B5.1: `assumes` obligation scoped to the callee the Call names (fn#0)
    // is exactly the composition the rule admits.
    let mut m = caller_callee_module();
    m.proof_obligations[0].function = Some(FuncId::new(0));
    let (fi, bi, ni) = call_site(&m);
    m.functions[fi].blocks[bi].body[ni].proof_context = Some(ProofContext {
        assumes: vec![ProofId::new(0)],
        establishes: vec![],
    });
    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|error| matches!(
            error,
            trust_ir_build::validate::ValidationError::ProofContextAssumeNotAuthoritative {
                obligation: 0,
                ..
            }
        )),
        "correct callee scope cannot replace replayed authority: {errors:?}"
    );
}

#[test]
fn assume_scoped_to_other_function_is_rejected() {
    // B5.1: obligation #0 is owned by the CALLER (fn#1), but the Call names
    // fn#0 — assuming another function's postcondition is a scope mismatch.
    let mut m = caller_callee_module();
    m.proof_obligations[0].function = Some(FuncId::new(1));
    let (fi, bi, ni) = call_site(&m);
    m.functions[fi].blocks[bi].body[ni].proof_context = Some(ProofContext {
        assumes: vec![ProofId::new(0)],
        establishes: vec![],
    });
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::ProofContextAssumeScopeMismatch {
                obligation: 0,
                callee: 0,
                actual_owner: 1,
                ..
            }
        )),
        "assume scoped to a non-callee function must be rejected: {errs:?}"
    );
}

#[test]
fn mis_scoped_establishes_is_rejected_symmetrically() {
    // Both contract directions are scope-checked: `establishes` names callee
    // PRECONDITIONS the caller discharges, so an obligation B4-scoped to a
    // non-callee function is the same confusion class as a mis-scoped assume
    // (it gets its own error variant, not the assume one).
    let mut m = caller_callee_module();
    m.proof_obligations[1].function = Some(FuncId::new(1));
    let (fi, bi, ni) = call_site(&m);
    m.functions[fi].blocks[bi].body[ni].proof_context = Some(ProofContext {
        assumes: vec![],
        establishes: vec![ProofId::new(1)],
    });
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::ProofContextEstablishScopeMismatch {
                obligation: 1,
                callee: 0,
                actual_owner: 1,
                ..
            }
        )),
        "establishes scoped to a non-callee function must be rejected: {errs:?}"
    );
    assert!(
        !errs.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::ProofContextAssumeScopeMismatch { .. }
        )),
        "a mis-scoped establishes must not fire the assume rule: {errs:?}"
    );
}

#[test]
fn establishes_scoped_to_named_callee_validates() {
    // The admitted composition: the caller discharges the CALLEE's
    // B4-scoped precondition.
    let mut m = caller_callee_module();
    m.proof_obligations[1].function = Some(FuncId::new(0));
    let (fi, bi, ni) = call_site(&m);
    m.functions[fi].blocks[bi].body[ni].proof_context = Some(ProofContext {
        assumes: vec![],
        establishes: vec![ProofId::new(1)],
    });
    assert!(
        validate_module(&m).is_empty(),
        "callee-scoped establishes must validate: {:?}",
        validate_module(&m)
    );
}

#[test]
fn invoke_with_dangling_callee_is_rejected() {
    // Invoke gets the same callee-existence check as a direct Call — a
    // dangling FuncId must not validate (and must not anchor a B5.1 scope
    // check on a nonexistent function).
    let mut m = invoke_caller_callee_module();
    let (fi, bi, ni) = invoke_site(&m);
    if let Inst::Invoke { callee, .. } = &mut m.functions[fi].blocks[bi].body[ni].inst {
        *callee = FuncId::new(42);
    }
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::CalleeNotFound { callee_id: 42, .. }
        )),
        "invoke naming a nonexistent callee must be rejected: {errs:?}"
    );
}

#[test]
fn invoke_arg_count_mismatch_is_rejected() {
    // Invoke passing the wrong argument count gets the same arity check as
    // a direct Call.
    let mut m = invoke_caller_callee_module();
    let (fi, bi, ni) = invoke_site(&m);
    if let Inst::Invoke { args, .. } = &mut m.functions[fi].blocks[bi].body[ni].inst {
        args.push(trust_ir::value::ValueId::new(0));
    }
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::CallArgCountMismatch { .. }
        )),
        "invoke with wrong arg count must be rejected: {errs:?}"
    );
}

#[test]
fn proof_context_referencing_unknown_obligation_is_rejected() {
    let mut m = caller_callee_module();
    let (fi, bi, ni) = call_site(&m);
    m.functions[fi].blocks[bi].body[ni].proof_context = Some(ProofContext {
        assumes: vec![ProofId::new(99)], // does not exist
        establishes: vec![],
    });
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::ProofContextUnknownObligation { .. }
        )),
        "unknown obligation in proof context must be rejected: {errs:?}"
    );
}

/// Rebuild `caller` (fn#1) into an invoke-shaped CFG:
///   b0: invoke fn#0() -> %r, normal b1, unwind b2
///   b1: %c = const 0; ret %c
///   b2: %exn/%sel = landing_pad (cleanup); resume %exn
fn invoke_caller_callee_module() -> Module {
    use trust_ir::value::{BlockId, ValueId};
    use trust_ir::{Block, Constant, InstrNode};
    let mut m = caller_callee_module();
    let (fi, _, _) = call_site(&m);
    let caller = &mut m.functions[fi];
    let r = ValueId::new(100);
    let c = ValueId::new(101);
    let exn = ValueId::new(102);
    let sel = ValueId::new(103);
    let b0 = caller.blocks[0].id;
    let b1 = BlockId::new(b0.index() + 1);
    let b2 = BlockId::new(b0.index() + 2);
    caller.blocks = vec![
        Block {
            id: b0,
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Invoke {
                    callee: FuncId::new(0),
                    args: vec![],
                    normal_dest: b1,
                    normal_args: vec![],
                    unwind_dest: b2,
                })
                .with_result(r),
            ],
        },
        Block {
            id: b1,
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(0),
                })
                .with_result(c),
                InstrNode::new(Inst::Return { values: vec![c] }),
            ],
        },
        Block {
            id: b2,
            params: vec![],
            body: vec![
                InstrNode::new(Inst::LandingPad {
                    is_cleanup: true,
                    catch_type_indices: vec![],
                })
                .with_results([exn, sel]),
                InstrNode::new(Inst::Resume { exn }),
            ],
        },
    ];
    m
}

/// Returns (func_idx, block_idx, node_idx) of the Invoke node.
fn invoke_site(m: &Module) -> (usize, usize, usize) {
    for (fi, f) in m.functions.iter().enumerate() {
        for (bi, b) in f.blocks.iter().enumerate() {
            for (ni, node) in b.body.iter().enumerate() {
                if matches!(node.inst, Inst::Invoke { .. }) {
                    return (fi, bi, ni);
                }
            }
        }
    }
    panic!("no invoke node");
}

#[test]
fn pending_assume_on_invoke_scoped_to_named_callee_is_rejected() {
    // Invoke is a call with an unwind edge: a proof context is legal on it,
    // and a callee-scoped assume composes exactly as on a direct Call.
    let mut m = invoke_caller_callee_module();
    assert!(
        validate_module(&m).is_empty(),
        "invoke-shaped module must validate before the proof context: {:?}",
        validate_module(&m)
    );
    m.proof_obligations[0].function = Some(FuncId::new(0));
    let (fi, bi, ni) = invoke_site(&m);
    m.functions[fi].blocks[bi].body[ni].proof_context = Some(ProofContext {
        assumes: vec![ProofId::new(0)],
        establishes: vec![],
    });
    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|error| matches!(
            error,
            trust_ir_build::validate::ValidationError::ProofContextAssumeNotAuthoritative {
                obligation: 0,
                ..
            }
        )),
        "correct invoke scope cannot replace replayed authority: {errors:?}"
    );
}

#[test]
fn assume_on_invoke_scoped_to_other_function_is_rejected() {
    let mut m = invoke_caller_callee_module();
    m.proof_obligations[0].function = Some(FuncId::new(1));
    let (fi, bi, ni) = invoke_site(&m);
    m.functions[fi].blocks[bi].body[ni].proof_context = Some(ProofContext {
        assumes: vec![ProofId::new(0)],
        establishes: vec![],
    });
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::ProofContextAssumeScopeMismatch {
                obligation: 0,
                callee: 0,
                actual_owner: 1,
                ..
            }
        )),
        "assume scoped to a non-callee function must be rejected on invoke: {errs:?}"
    );
}

#[test]
fn proof_context_on_non_call_node_is_rejected() {
    let mut m = caller_callee_module();
    // Attach a context to the `ret`/`iconst` node in callee (non-call).
    let (fi, bi, _) = call_site(&m);
    // Put it on the caller's first node that is NOT a call.
    let f = &mut m.functions[fi].blocks[bi].body;
    let idx = f
        .iter()
        .position(|n| !matches!(n.inst, Inst::Call { .. }))
        .expect("a non-call node");
    f[idx].proof_context = Some(ProofContext {
        assumes: vec![],
        establishes: vec![],
    });
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::ProofContextOnNonCallNode { .. }
        )),
        "proof context on a non-call node must be rejected: {errs:?}"
    );
}
