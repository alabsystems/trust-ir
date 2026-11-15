// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Amendment D, Part 2 (wire v56, `docs/SPEC_RATIFICATIONS.md` §21): what the
// validator does with `Inst::InvokeIndirect`, `CallIndirect`'s unwinding twin.
// No new `ValidationError` variant: the twin takes
//
//   * `CallIndirect`'s callee, signature, argument and convention checks
//     (`CallIndirectSigNotFound`, `CallIndirectArgCountMismatch`,
//     `CallIndirectArgTypeMismatch`, the closure-callee codegen refusal);
//   * `Invoke`'s edges: its results are defined on the normal edge ONLY, the
//     normal edge is arity- and type-checked like a branch, the unwind edge
//     carries no arguments, and `validate_unwind_structure` applies
//     (`UnwindDestWithoutLandingPad`, `MisplacedLandingPad`);
//   * the unwind surface, and the call-node rules (a proof context on it).
//
// `unwind_structure_applies_to_every_twin` holds the four unwinding
// terminators (`Invoke`, `AssertInvoke`, `DropInvoke`, `InvokeIndirect`) to
// rule (a) together, so a fifth twin cannot skip it unnoticed.

use trust_ir::proof::{ObligationKind, ProofContext, ProofObligation, ProofStatus};
use trust_ir::ty::{ClosureTy, FuncTy};
use trust_ir::value::{FuncTyId, GlobalId};
use trust_ir::{
    AssertKind, Block, BlockId, CallingConv, Constant, Endianness, FuncId, Function, Inst,
    InstrNode, Linkage, Module, PanicLocation, PanicSite, TargetInfo, Ty, ValueId,
};
use trust_ir_build::validate::{
    ValidationError, codegen_lowerability_errors, validate_module_report,
};
use trust_ir_build::validate_module;

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

/// `functy.0 = (i64) -> i64`: the callee's signature. `functy.1 = (i64) ->
/// i64` is the caller's.
fn base() -> Module {
    let mut m = Module::new("unwind_twins_validation");
    m.target_info = Some(target());
    m.add_func_type(FuncTy {
        abi: None,
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    })
    .expect("Module::add_func_type: test fixture");
    m.add_func_type(FuncTy {
        abi: None,
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    })
    .expect("Module::add_func_type: test fixture");
    // func.0 `id(%0: i64) -> i64`.
    let mut id = Function::new(FuncId::new(0), "id", FuncTyId::new(0), b(0));
    let mut block = Block::new(b(0));
    block.params.push((v(0), Ty::I64));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
    id.blocks.push(block);
    m.try_add_function(id)
        .expect("Module::try_add_function: test fixture");
    m
}

/// The twin itself, at `sig`, calling `%1` with `args`.
fn twin(sig: u32, args: Vec<ValueId>, unwind_dest: BlockId) -> Inst {
    Inst::InvokeIndirect {
        callee: v(1),
        sig: FuncTyId::new(sig),
        args,
        calling_conv: CallingConv::C,
        normal_dest: b(1),
        normal_args: vec![],
        unwind_dest,
    }
}

/// func.1 `f(%0: i64) -> i64`:
///
/// ```text
/// bb0(%0): %1 = const fn(functy.0) @id
///          %2 = <inst>                       ; an InvokeIndirect, normally
/// bb1:     ret %2
/// bb2:     %3, %4 = landingpad cleanup       ; when `pad`
///          resume %3
/// ```
fn caller(m: &mut Module, inst: Inst, pad: bool) -> FuncId {
    let mut f = Function::new(FuncId::new(1), "f", FuncTyId::new(1), b(0));
    let mut entry = Block::new(b(0));
    entry.params.push((v(0), Ty::I64));
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Func(FuncTyId::new(0)),
            value: Constant::FnDef(FuncId::new(0)),
        })
        .with_results(vec![v(1)]),
    );
    entry
        .body
        .push(InstrNode::new(inst).with_results(vec![v(2)]));
    f.blocks.push(entry);
    let mut normal = Block::new(b(1));
    normal
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
    f.blocks.push(normal);
    let mut unwind = Block::new(b(2));
    if pad {
        unwind.body.push(
            InstrNode::new(Inst::LandingPad {
                is_cleanup: true,
                catch_type_indices: vec![],
            })
            .with_results(vec![v(3), v(4)]),
        );
        unwind.body.push(InstrNode::new(Inst::Resume { exn: v(3) }));
    } else {
        unwind
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
    }
    f.blocks.push(unwind);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    FuncId::new(1)
}

fn well_formed() -> Module {
    let mut m = base();
    caller(&mut m, twin(0, vec![v(0)], b(2)), true);
    m
}

fn the_twin(m: &mut Module) -> &mut Inst {
    &mut m.functions[1].blocks[0].body[1].inst
}

#[test]
fn a_well_formed_invoke_indirect_validates() {
    let m = well_formed();
    assert_eq!(validate_module(&m), vec![]);
}

#[test]
fn invoke_indirect_is_checked_as_call_indirect_plus_invoke_edges() {
    // CallIndirect's checks, verbatim.
    let mut m = well_formed();
    if let Inst::InvokeIndirect { sig, .. } = the_twin(&mut m) {
        *sig = FuncTyId::new(9);
    }
    assert!(
        validate_module(&m).iter().any(|e| matches!(
            e,
            ValidationError::CallIndirectSigNotFound { sig_id: 9, .. }
        )),
        "{:?}",
        validate_module(&m)
    );
    let mut m = well_formed();
    if let Inst::InvokeIndirect { args, .. } = the_twin(&mut m) {
        args.clear();
    }
    assert!(validate_module(&m).iter().any(|e| matches!(
        e,
        ValidationError::CallIndirectArgCountMismatch {
            expected: 1,
            actual: 0,
            ..
        }
    )));
    let mut m = well_formed();
    if let Inst::InvokeIndirect { args, .. } = the_twin(&mut m) {
        // `%1` is the callee (a `fn` value), not an `i64`.
        args[0] = v(1);
    }
    assert!(
        validate_module(&m)
            .iter()
            .any(|e| matches!(e, ValidationError::CallIndirectArgTypeMismatch { .. }))
    );
    // Invoke's edges: the normal edge is arity-checked like a branch, the
    // unwind edge carries no arguments, and a dangling target is refused.
    let arity = |m: &Module| {
        validate_module(m)
            .into_iter()
            .filter(|e| matches!(e, ValidationError::BranchArgCountMismatch { .. }))
            .count()
    };
    assert_eq!(arity(&well_formed()), 0);
    let mut m = well_formed();
    if let Inst::InvokeIndirect { normal_args, .. } = the_twin(&mut m) {
        normal_args.push(v(0));
    }
    assert_eq!(arity(&m), 1, "normal edge arity");
    let mut m = well_formed();
    m.functions[1].blocks[2].params.push((v(9), Ty::Ptr));
    assert_eq!(arity(&m), 1, "unwind edge carries no arguments");
    let mut m = well_formed();
    if let Inst::InvokeIndirect { normal_dest, .. } = the_twin(&mut m) {
        *normal_dest = b(7);
    }
    assert!(
        validate_module(&m)
            .iter()
            .any(|e| matches!(e, ValidationError::BranchTargetNotFound { .. }))
    );
}

#[test]
fn invoke_indirect_results_are_defined_on_its_normal_edge_only() {
    // A use of the result in the landing pad is refused: the unwind edge
    // leaves the call without a return value.
    let mut m = well_formed();
    m.functions[1].blocks[2].body.insert(
        1,
        InstrNode::new(Inst::Copy {
            ty: Ty::I64,
            operand: v(2),
        })
        .with_results(vec![v(10)]),
    );
    assert!(
        validate_module(&m).contains(&ValidationError::UseBeforeDefInBlock { value: 2, block: 2 }),
        "{:?}",
        validate_module(&m)
    );
    // Passed as a normal-edge argument, the result is defined there.
    let mut m = well_formed();
    if let Inst::InvokeIndirect { normal_args, .. } = the_twin(&mut m) {
        normal_args.push(v(2));
    }
    m.functions[1].blocks[1].params.push((v(11), Ty::I64));
    m.functions[1].blocks[1].body[0] = InstrNode::new(Inst::Return {
        values: vec![v(11)],
    });
    assert_eq!(validate_module(&m), vec![]);
    // As a CALL argument it is used before it exists.
    let mut m = well_formed();
    if let Inst::InvokeIndirect { args, .. } = the_twin(&mut m) {
        args[0] = v(2);
    }
    assert!(
        validate_module(&m)
            .iter()
            .any(|e| matches!(e, ValidationError::UseBeforeDefInBlock { value: 2, .. })),
        "{:?}",
        validate_module(&m)
    );
}

/// Each unwinding twin of the format, built over the same CFG shape:
/// `bb0` ends in the twin with normal edge `bb1` and unwind edge `bb2`.
fn every_twin(m: &mut Module, pad: bool) -> Vec<(&'static str, FuncId)> {
    // An entry and a location for the sited check.
    let loc_ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    // A bodyless declaration (no blocks).
    m.try_add_function(Function::new(FuncId::new(10), "panic_entry", loc_ft, b(0)))
        .expect("Module::try_add_function: test fixture");
    m.globals.push(trust_ir::Global {
        name: "loc".into(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(Constant::Int(0)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    let mut out = Vec::new();
    for (index, name) in [
        (20u32, "invoke"),
        (21, "assert_invoke"),
        (22, "invoke_indirect"),
    ] {
        let mut f = Function::new(FuncId::new(index), name, FuncTyId::new(1), b(0));
        let mut entry = Block::new(b(0));
        entry.params.push((v(0), Ty::I64));
        let (setup, inst, results) = match name {
            "invoke" => (
                None,
                Inst::Invoke {
                    callee: FuncId::new(0),
                    args: vec![v(0)],
                    normal_dest: b(1),
                    normal_args: vec![],
                    unwind_dest: b(2),
                },
                vec![v(2)],
            ),
            "assert_invoke" => (
                Some(
                    InstrNode::new(Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(true),
                    })
                    .with_results(vec![v(1)]),
                ),
                Inst::AssertInvoke {
                    cond: v(1),
                    kind: AssertKind::DivByZero,
                    site: PanicSite {
                        entry: FuncId::new(10),
                        location: PanicLocation::Global(GlobalId::new(0)),
                    },
                    normal_dest: b(1),
                    normal_args: vec![],
                    unwind_dest: b(2),
                },
                vec![],
            ),
            _ => (
                Some(
                    InstrNode::new(Inst::Const {
                        ty: Ty::Func(FuncTyId::new(0)),
                        value: Constant::FnDef(FuncId::new(0)),
                    })
                    .with_results(vec![v(1)]),
                ),
                twin(0, vec![v(0)], b(2)),
                vec![v(2)],
            ),
        };
        entry.body.extend(setup);
        entry.body.push(InstrNode::new(inst).with_results(results));
        f.blocks.push(entry);
        let mut normal = Block::new(b(1));
        normal
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        f.blocks.push(normal);
        let mut unwind = Block::new(b(2));
        if pad {
            unwind.body.push(
                InstrNode::new(Inst::LandingPad {
                    is_cleanup: true,
                    catch_type_indices: vec![],
                })
                .with_results(vec![v(3), v(4)]),
            );
            unwind.body.push(InstrNode::new(Inst::Resume { exn: v(3) }));
        } else {
            unwind
                .body
                .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        }
        f.blocks.push(unwind);
        m.try_add_function(f)
            .expect("Module::try_add_function: test fixture");
        out.push((name, FuncId::new(index)));
    }
    out
}

#[test]
fn unwind_structure_applies_to_every_twin() {
    // `DropInvoke`'s own rule-(a) case is `refuse/drop_invoke_unwind_dest_
    // without_landing_pad` (drop_glue.rs); the three others are held here
    // against one CFG shape, the twin included.
    let mut good = base();
    let names = every_twin(&mut good, true);
    let pad_errors = |m: &Module| -> Vec<ValidationError> {
        validate_module(m)
            .into_iter()
            .filter(|e| matches!(e, ValidationError::UnwindDestWithoutLandingPad { .. }))
            .collect()
    };
    assert_eq!(pad_errors(&good), vec![], "{:?}", validate_module(&good));
    let mut bad = base();
    every_twin(&mut bad, false);
    let errors = pad_errors(&bad);
    assert_eq!(
        errors.len(),
        names.len(),
        "one rule-(a) refusal per twin: {errors:?}"
    );
    // The twin's unwind edge may not double as its normal edge.
    let mut m = well_formed();
    if let Inst::InvokeIndirect { unwind_dest, .. } = the_twin(&mut m) {
        *unwind_dest = b(1);
    }
    assert!(
        pad_errors(&m).iter().any(|e| matches!(
            e,
            ValidationError::UnwindDestWithoutLandingPad { target: 1, .. }
        )),
        "{:?}",
        validate_module(&m)
    );
}

#[test]
fn invoke_indirect_functions_are_in_the_unwind_surface() {
    let mut m = base();
    let f = caller(&mut m, twin(0, vec![v(0)], b(2)), false);
    // The twin alone (its "pad" is an ordinary block) puts the function on
    // the surface; `id` has none.
    let surface = validate_module_report(&m).unwind_surface();
    assert_eq!(surface, vec![f]);
}

#[test]
fn a_closure_callee_of_invoke_indirect_is_unlowerable_for_codegen() {
    // The twin applies a closure exactly as `CallIndirect` does, so the
    // codegen gate refuses its closure application too, by its own name.
    let mut m = base();
    let closure = m
        .add_closure_type(ClosureTy {
            func: FuncTyId::new(0),
            captures: vec![],
        })
        .expect("Module::add_closure_type: test fixture");
    caller(&mut m, twin(0, vec![v(0)], b(2)), true);
    let Inst::Const { ty, value } = &mut m.functions[1].blocks[0].body[0].inst else {
        unreachable!("the callee constant");
    };
    *ty = Ty::Closure(closure);
    *value = Constant::Closure {
        func: FuncId::new(0),
        captures: vec![],
    };
    let errors = codegen_lowerability_errors(&m);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::UnlowerableForCodegen {
                inst: "InvokeIndirect",
                ..
            }
        )),
        "{errors:?}"
    );
    // The `fn`-item callee is not refused.
    assert!(
        codegen_lowerability_errors(&well_formed())
            .iter()
            .all(|e| !matches!(
                e,
                ValidationError::UnlowerableForCodegen {
                    inst: "InvokeIndirect",
                    ..
                }
            ))
    );
}

#[test]
fn proof_context_on_invoke_indirect_is_a_call_node() {
    let mut m = well_formed();
    m.proof_obligations.push(ProofObligation::new(
        trust_ir::value::ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Pending,
        "the callee's postcondition",
    ));
    m.functions[1].blocks[0].body[1].proof_context = Some(ProofContext {
        assumes: vec![trust_ir::value::ProofId::new(0)],
        establishes: vec![],
    });
    let errors = validate_module(&m);
    assert!(
        !errors
            .iter()
            .any(|e| matches!(e, ValidationError::ProofContextOnNonCallNode { .. })),
        "{errors:?}"
    );
}
