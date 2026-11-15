// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! WS2.5 unwind structure (F-032 / F-041; audit c15 item 1) and the WS1.8
//! B4 function-scope resolution item landed early (audit c15 item 5). Run by
//! standing gate 9 (`validator-fail-closed`) as a module of `validation_holes`.
//!
//! The format's normative text (`inst.rs`, `Invoke` / `LandingPad`) says an
//! `Invoke`'s unwind edge enters "a block that BEGINS with an
//! `Inst::LandingPad`", and that a `LandingPad` is "the first instruction of a
//! block that an `Invoke`'s `unwind_dest` names", whose two results are reads
//! of the registers the unwinder loaded on the taken edge. Until this rule the
//! only unwind-edge check was "parameter-free", so an `unwind_dest` with no
//! pad, a pad in the entry block, a pad mid-block, an orphan pad, and a pad
//! block entered by a plain `Br` all validated under every entry point
//! (2026-09-17 proof-program rows `b6.eh.landingpad_placement_unchecked`,
//! repro notes 1a–1d / 6a).
//!
//! A `Resume` is additionally refused when it re-raises a value no landing pad
//! produced (no pad in the function, the pad's selector, or a literal).
//!
//! Separately, `ProofObligation.function = Some(f)` was never resolved unless
//! a `site` accompanied it (row `b2.gap.dangling_function_scope_accepted`,
//! repro note 5d).
//!
//! Every negative here is a ONE-mutation twin of a validating baseline, and
//! each asserts the SPECIFIC named error.

use trust_ir::proof::{ObligationKind, ObligationSite, ProofObligation, ProofStatus};
use trust_ir::{
    BlockId, BodyGate, Constant, FuncId, Inst, InstrNode, Module, Producer, ProofId, Ty, ValueId,
};
use trust_ir_build::{
    ModuleBuilder, ValidationError, validate_function, validate_module,
    validate_module_for_codegen, validate_module_report,
};

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

/// The well-formed baseline, the same shape the invoke-edge SSA tests use:
///
/// ```text
/// fn callee() -> i32 { bb0: %0 = const 0; ret %0 }
/// fn caller() -> i32 {
///   bb0: %r = invoke @callee() to bb1 unwind bb2
///   bb1: ret %r
///   bb2: %exn, %sel = landingpad cleanup; resume %exn
/// }
/// ```
///
/// `caller` is `functions[1]`, its blocks are `[bb0, bb1, bb2]` in order.
fn baseline() -> Module {
    let mut module = ModuleBuilder::new("eh_placement");
    let signature = module.add_func_type(vec![], vec![Ty::I32]);
    let callee = {
        let mut function = module.function("callee", signature);
        let entry = function.create_block();
        function.switch_to_block(entry);
        let zero = function.iconst(Ty::I32, 0);
        function.ret(vec![zero]);
        function.build()
    };
    let mut function = module.function("caller", signature);
    let entry = function.create_block();
    let normal = function.create_block();
    let unwind = function.create_block();
    function.switch_to_block(entry);
    let result = function.invoke(callee, vec![], normal, vec![], unwind);
    function.switch_to_block(normal);
    function.ret(vec![result]);
    function.switch_to_block(unwind);
    let (exception, _) = function.landingpad(true, vec![]);
    function.resume(exception);
    function.build();
    module.build().expect("ModuleBuilder::build: test fixture")
}

/// The END-STATE form for `validate_module_for_codegen`, which refuses an
/// unlicensed body (`UnlicensedBodyForCodegen`) before anything else.
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

fn caller(module: &mut Module) -> &mut trust_ir::Function {
    module
        .functions
        .iter_mut()
        .find(|f| f.name == "caller")
        .expect("caller")
}

fn has(errors: &[ValidationError], pred: impl Fn(&ValidationError) -> bool) -> bool {
    errors.iter().any(pred)
}

fn is_placement_error(error: &ValidationError) -> bool {
    matches!(
        error,
        ValidationError::UnwindDestWithoutLandingPad { .. }
            | ValidationError::MisplacedLandingPad { .. }
    )
}

fn is_resume_error(error: &ValidationError) -> bool {
    matches!(
        error,
        ValidationError::MisplacedLandingPad { reason, .. }
            if reason.starts_with("resume of a value no landing pad produced")
    )
}

/// Run the mutated module through every validator door and return the errors
/// of the strictest (`validate_module_for_codegen` on the licensed clone),
/// after asserting that plain `validate_module` and the per-function
/// `validate_function` on `caller` agree on the placement verdict.
fn all_doors(module: &Module) -> Vec<ValidationError> {
    let plain = validate_module(module);
    let report = validate_module_report(module).into_errors();
    let codegen = validate_module_for_codegen(&licensed(module));
    let per_function = validate_function(
        module
            .functions
            .iter()
            .find(|f| f.name == "caller")
            .expect("caller"),
    );
    let placement =
        |errors: &[ValidationError]| errors.iter().filter(|e| is_placement_error(e)).count();
    assert_eq!(
        placement(&plain),
        placement(&codegen),
        "validate_module and validate_module_for_codegen disagree: {plain:?} vs {codegen:?}"
    );
    assert_eq!(
        placement(&plain),
        placement(&report),
        "validate_module and validate_module_report disagree: {plain:?} vs {report:?}"
    );
    assert_eq!(
        placement(&plain),
        placement(&per_function),
        "the placement rule is per-function; validate_function must agree: {plain:?} vs {per_function:?}"
    );
    codegen
}

// ---------------------------------------------------------------------------
// (a) positive fixture
// ---------------------------------------------------------------------------

#[test]
fn well_formed_invoke_landingpad_resume_validates_under_every_door() {
    let module = baseline();
    assert_eq!(validate_module(&module), []);
    assert_eq!(validate_module_for_codegen(&licensed(&module)), []);
    assert!(validate_module_report(&module).is_ok());
    for function in &module.functions {
        assert_eq!(validate_function(function), [], "{}", function.name);
    }
}

/// Two invokes sharing one cleanup pad is the ordinary rustc shape (one
/// cleanup block per scope, many unwinding calls into it) and must stay legal:
/// the rule is "≥1 invoke names the block", not "exactly one".
#[test]
fn a_landing_pad_shared_by_two_invokes_validates() {
    let mut module = baseline();
    let callee = module.functions[0].id;
    let function = caller(&mut module);
    // bb0: invoke @callee() to bb3 unwind bb2
    // bb3: %r2 = invoke @callee() to bb1 unwind bb2
    let first = ValueId::new(50);
    let second = ValueId::new(51);
    let mid = BlockId::new(3);
    function.blocks[0].body[0] = InstrNode::new(Inst::Invoke {
        callee,
        args: vec![],
        normal_dest: mid,
        normal_args: vec![],
        unwind_dest: BlockId::new(2),
    })
    .with_result(first);
    let mut mid_block = trust_ir::Block::new(mid);
    mid_block.body.push(
        InstrNode::new(Inst::Invoke {
            callee,
            args: vec![],
            normal_dest: BlockId::new(1),
            normal_args: vec![second],
            unwind_dest: BlockId::new(2),
        })
        .with_result(second),
    );
    function.blocks[1].params.push((ValueId::new(52), Ty::I32));
    function.blocks[1].body[0] = InstrNode::new(Inst::Return {
        values: vec![ValueId::new(52)],
    });
    function.blocks.push(mid_block);
    assert_eq!(validate_module(&module), []);
    assert_eq!(validate_module_for_codegen(&licensed(&module)), []);
}

/// The shape the in-repo Rust producer actually emits under its EH lane
/// (`frontend/src/mir_lower.rs`, `eh_unwind_dest`): each `Invoke` gets a
/// FRESH synthesized pad block (`landingpad; store exn -> slot; br cleanup`),
/// the shared MIR cleanup body is an ordinary block entered by those `Br`s and
/// ends in `resume (load slot)`, and a per-reason TERMINATE pad is shared by
/// every invoke that names it (`landingpad; call abort; unreachable`). The
/// placement rules must accept all of it: the pads are entered only by unwind
/// edges, and the pad-free cleanup body entered by plain branches is not a
/// landing-pad block at all.
#[test]
fn producer_shaped_eh_lane_validates() {
    let mut mb = ModuleBuilder::new("eh_lane");
    let nullary_void = mb.add_func_type(vec![], vec![]);
    let may_unwind = {
        let mut fb = mb.function("may_unwind", nullary_void);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.ret(vec![]);
        fb.build()
    };
    let abort = {
        let mut fb = mb.function("panic_cannot_unwind", nullary_void);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.ret(vec![]);
        fb.build()
    };
    let mut fb = mb.function("program", nullary_void);
    let entry = fb.create_block();
    let second = fb.create_block();
    let third = fb.create_block();
    let done = fb.create_block();
    let pad_a = fb.create_block();
    let pad_b = fb.create_block();
    let cleanup = fb.create_block();
    let terminate = fb.create_block();

    fb.switch_to_block(entry);
    let slot = fb.alloca(Ty::Ptr);
    fb.invoke_void(may_unwind, vec![], second, vec![], pad_a);
    fb.switch_to_block(second);
    fb.invoke_void(may_unwind, vec![], third, vec![], pad_b);
    fb.switch_to_block(third);
    fb.invoke_void(may_unwind, vec![], done, vec![], terminate);
    fb.switch_to_block(done);
    fb.ret(vec![]);

    for pad in [pad_a, pad_b] {
        fb.switch_to_block(pad);
        let (exn, _sel) = fb.landingpad(true, vec![]);
        fb.store(Ty::Ptr, slot, exn);
        fb.br(cleanup, vec![]);
    }
    fb.switch_to_block(cleanup);
    let exn = fb.load(Ty::Ptr, slot);
    fb.resume(exn);

    fb.switch_to_block(terminate);
    let _ = fb.landingpad(true, vec![]);
    fb.call_void(abort, vec![]);
    fb.unreachable();
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

    assert_eq!(validate_module(&module), []);
    assert_eq!(validate_module_for_codegen(&licensed(&module)), []);
    assert!(validate_module_report(&module).is_ok());
    for function in &module.functions {
        assert_eq!(validate_function(function), [], "{}", function.name);
    }

    // Mutation control on the SAME fixture: route the second invoke's unwind
    // edge straight at the pad-free cleanup body (skipping the synthesized
    // pad). Rule (a) refuses the edge, and rule (b) independently refuses the
    // pad it bypassed, which no invoke names any more.
    let mut mutated = module.clone();
    let program = mutated
        .functions
        .iter_mut()
        .find(|f| f.name == "program")
        .expect("program");
    let invoke_block = program
        .blocks
        .iter_mut()
        .find(|b| b.id == second)
        .expect("second");
    let Inst::Invoke { unwind_dest, .. } = &mut invoke_block.body.last_mut().unwrap().inst else {
        unreachable!()
    };
    *unwind_dest = cleanup;
    let errors = validate_module(&mutated);
    assert!(
        errors.contains(&ValidationError::UnwindDestWithoutLandingPad {
            block: second.index(),
            target: cleanup.index(),
        }),
        "{errors:?}"
    );
    let pad_b_index = pad_b.index();
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::MisplacedLandingPad { block, reason }
                if *block == pad_b_index && reason.contains("no invoke names this block")
        )),
        "{errors:?}"
    );
    assert_eq!(
        errors.iter().filter(|e| is_placement_error(e)).count(),
        2,
        "pad_a and the terminate pad are untouched: {errors:?}"
    );
}

/// Physical block order is not the CFG: the pad block stored FIRST is still
/// not the entry block, and the rule keys on `Function.entry`, not position.
#[test]
fn block_storage_order_does_not_affect_placement() {
    let mut module = baseline();
    caller(&mut module).blocks.reverse();
    assert_eq!(validate_module(&module), []);
}

// ---------------------------------------------------------------------------
// (b) close negative twins — rule (a): unwind_dest must begin with a pad
// ---------------------------------------------------------------------------

/// Repro row 1a: the unwind block is `resume null` with no `LandingPad`.
#[test]
fn unwind_dest_without_a_landing_pad_is_refused() {
    let mut module = baseline();
    let function = caller(&mut module);
    let null = ValueId::new(60);
    function.blocks[2].body = vec![
        InstrNode::new(Inst::NullPtr).with_result(null),
        InstrNode::new(Inst::Resume { exn: null }),
    ];
    let errors = all_doors(&module);
    assert!(
        errors.contains(&ValidationError::UnwindDestWithoutLandingPad {
            block: 0,
            target: 2,
        }),
        "{errors:?}"
    );
    // No pad exists, so no pad can be misplaced; the only `MisplacedLandingPad`
    // is rule (c) on the `resume null`, which re-raises nothing a pad produced.
    let misplaced: Vec<_> = errors
        .iter()
        .filter(|e| matches!(e, ValidationError::MisplacedLandingPad { .. }))
        .collect();
    assert_eq!(
        misplaced,
        [&ValidationError::MisplacedLandingPad {
            block: 2,
            reason:
                "resume of a value no landing pad produced: the function contains no landingpad"
                    .into(),
        }],
        "{errors:?}"
    );
}

/// The unwind block is `unreachable` — the exact 1a mutation in the notes.
#[test]
fn unwind_dest_that_is_unreachable_is_refused() {
    let mut module = baseline();
    caller(&mut module).blocks[2].body = vec![InstrNode::new(Inst::Unreachable)];
    let errors = all_doors(&module);
    assert!(
        errors.contains(&ValidationError::UnwindDestWithoutLandingPad {
            block: 0,
            target: 2,
        }),
        "{errors:?}"
    );
}

/// A pad that is present but NOT first (repro row 1c): rule (a) fires on the
/// invoke AND rule (b) fires on the pad, each naming its own position.
#[test]
fn landing_pad_mid_block_is_refused_on_both_sides() {
    let mut module = baseline();
    caller(&mut module).blocks[2].body.insert(
        0,
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(61)),
    );
    let errors = all_doors(&module);
    assert!(
        errors.contains(&ValidationError::UnwindDestWithoutLandingPad {
            block: 0,
            target: 2,
        }),
        "{errors:?}"
    );
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::MisplacedLandingPad { block: 2, reason }
                if reason.contains("not the first instruction")
        )),
        "{errors:?}"
    );
}

// ---------------------------------------------------------------------------
// (b) close negative twins — rule (b): a pad only heads an unwind_dest block
// ---------------------------------------------------------------------------

/// Repro row 1b: a function whose ENTRY block is `landingpad; resume`.
#[test]
fn landing_pad_in_the_entry_block_is_refused() {
    let mut mb = ModuleBuilder::new("resume_direct");
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", nullary);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let (exn, _sel) = fb.landingpad(true, vec![]);
    fb.resume(exn);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errors = validate_module(&module);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::MisplacedLandingPad { block: 0, reason }
                if reason.contains("entry block")
        )),
        "{errors:?}"
    );
    assert_eq!(
        validate_function(&module.functions[0])
            .iter()
            .filter(|e| is_placement_error(e))
            .count(),
        1
    );
}

/// The pad block is intact but no `Invoke` names it: the call is a plain
/// `Call` + `Br`, so bb2 is an orphan handler.
#[test]
fn landing_pad_no_invoke_targets_is_refused() {
    let mut module = baseline();
    let callee = module.functions[0].id;
    let function = caller(&mut module);
    let result = function.blocks[0].body[0].results[0];
    function.blocks[0].body = vec![
        InstrNode::new(Inst::Call {
            callee,
            args: vec![],
        })
        .with_result(result),
        InstrNode::new(Inst::Br {
            target: BlockId::new(1),
            args: vec![],
        }),
    ];
    let errors = validate_module(&module);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::MisplacedLandingPad { block: 2, reason }
                if reason.contains("no invoke names this block")
        )),
        "{errors:?}"
    );
    // The orphan pad is also unreachable, which is a separate, pre-existing
    // diagnostic; the placement rule does not depend on it.
    assert!(
        !has(&errors, |e| matches!(
            e,
            ValidationError::UnwindDestWithoutLandingPad { .. }
        )),
        "{errors:?}"
    );
}

/// Repro row 6a: the pad block is a legitimate unwind_dest AND the normal
/// continuation branches into it. On the `Br` edge nothing loaded the
/// exception registers the pad reads.
#[test]
fn landing_pad_block_entered_by_a_plain_branch_is_refused() {
    let mut module = baseline();
    caller(&mut module).blocks[1].body[0] = InstrNode::new(Inst::Br {
        target: BlockId::new(2),
        args: vec![],
    });
    let errors = all_doors(&module);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::MisplacedLandingPad { block: 2, reason }
                if reason.contains("non-unwind edge from bb1")
        )),
        "{errors:?}"
    );
}

/// Repro row 1d: `normal_dest == unwind_dest`. The block begins with a pad,
/// but a continuation cannot also be a pad: the invoke is refused with
/// `UnwindDestWithoutLandingPad` (roadmap WS2.5), and the pad it heads is
/// independently refused for its NORMAL entry.
#[test]
fn invoke_whose_normal_and_unwind_destinations_coincide_is_refused() {
    let mut module = baseline();
    let function = caller(&mut module);
    let Inst::Invoke { normal_dest, .. } = &mut function.blocks[0].body[0].inst else {
        unreachable!()
    };
    *normal_dest = BlockId::new(2);
    // bb1 is now unreachable but still well-formed; keep it.
    let errors = all_doors(&module);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::MisplacedLandingPad { block: 2, reason }
                if reason.contains("non-unwind edge from bb0")
        )),
        "{errors:?}"
    );
    assert!(
        errors.contains(&ValidationError::UnwindDestWithoutLandingPad {
            block: 0,
            target: 2,
        }),
        "a continuation cannot also be a pad: {errors:?}"
    );
}

// ---------------------------------------------------------------------------
// (b') review twins: edge kinds and shapes the first cut did not exercise
// ---------------------------------------------------------------------------

/// The non-unwind entry arrives through a `Switch` CASE edge rather than a
/// `Br`: every non-unwind successor kind counts, not only the plain branch.
#[test]
fn landing_pad_block_entered_by_a_switch_case_is_refused() {
    let mut module = baseline();
    let function = caller(&mut module);
    let result = function.blocks[0].body[0].results[0];
    let exit = BlockId::new(3);
    function.blocks[1].body = vec![InstrNode::new(Inst::Switch {
        value: result,
        default: exit,
        default_args: vec![],
        cases: vec![trust_ir::SwitchCase {
            value: Constant::Int(0),
            target: BlockId::new(2),
            args: vec![],
        }],
        exhaustive_enum_unreachable: false,
    })];
    let mut exit_block = trust_ir::Block::new(exit);
    exit_block.body.push(InstrNode::new(Inst::Return {
        values: vec![result],
    }));
    function.blocks.push(exit_block);
    let errors = all_doors(&module);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::MisplacedLandingPad { block: 2, reason }
                if reason.contains("non-unwind edge from bb1")
        )),
        "{errors:?}"
    );
    assert!(
        !has(&errors, |e| matches!(
            e,
            ValidationError::UnwindDestWithoutLandingPad { .. }
        )),
        "{errors:?}"
    );
}

/// A correctly placed pad followed by a SECOND pad in the same block: the
/// block does begin with a pad and only unwind edges enter it, so rule (a) is
/// satisfied and the leading pad is legal — the trailing one must still be
/// refused on its own position, not excused by its well-placed neighbour.
#[test]
fn second_landing_pad_behind_a_well_placed_one_is_refused() {
    let mut module = baseline();
    caller(&mut module).blocks[2].body.insert(
        1,
        InstrNode::new(Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        })
        .with_results([ValueId::new(80), ValueId::new(81)]),
    );
    let errors = all_doors(&module);
    let placement: Vec<_> = errors.iter().filter(|e| is_placement_error(e)).collect();
    assert_eq!(
        placement,
        [&ValidationError::MisplacedLandingPad {
            block: 2,
            reason: "not the first instruction of its block (position 1)".into(),
        }],
        "{errors:?}"
    );
}

/// A DUPLICATED unwind block id (`DuplicateBlockId`) must not let a
/// pad-bearing twin vouch for a pad-less one. Stored pad-less-first, a
/// last-writer-wins lookup would see "begins with a pad" and stay silent;
/// the rule requires every block carrying the id to lead with a pad.
#[test]
fn duplicated_unwind_block_id_cannot_borrow_its_twins_pad() {
    let mut module = baseline();
    let function = caller(&mut module);
    let mut padless = trust_ir::Block::new(BlockId::new(2));
    padless.body.push(InstrNode::new(Inst::Unreachable));
    // [bb0, bb1, bb2 (pad-less), bb2 (pad)]
    function.blocks.insert(2, padless);
    let errors = validate_module(&module);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::DuplicateBlockId(2)
        )),
        "{errors:?}"
    );
    assert!(
        errors.contains(&ValidationError::UnwindDestWithoutLandingPad {
            block: 0,
            target: 2,
        }),
        "{errors:?}"
    );
}

// ---------------------------------------------------------------------------
// (c) mutation controls
// ---------------------------------------------------------------------------

/// The one unwind-edge rule that existed before (parameter-free) still fires
/// on its own mutation, and the NEW rules stay silent on it: the pad is still
/// first in a block only invoke unwind edges enter.
#[test]
fn control_parameterised_pad_block_is_the_old_error_only() {
    let mut module = baseline();
    caller(&mut module).blocks[2]
        .params
        .push((ValueId::new(70), Ty::Ptr));
    let errors = validate_module(&module);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::BranchArgCountMismatch {
                block: 0,
                target: 2,
                expected: 1,
                actual: 0,
            }
        )),
        "{errors:?}"
    );
    assert!(
        !has(&errors, is_placement_error),
        "placement is correct here; only arity is wrong: {errors:?}"
    );
}

/// A dangling unwind target is `BranchTargetNotFound`'s to report; the
/// placement rule must not double-report it as a missing pad.
#[test]
fn control_dangling_unwind_target_is_not_a_placement_error() {
    let mut module = baseline();
    let function = caller(&mut module);
    let Inst::Invoke { unwind_dest, .. } = &mut function.blocks[0].body[0].inst else {
        unreachable!()
    };
    *unwind_dest = BlockId::new(9);
    let errors = validate_module(&module);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::BranchTargetNotFound {
                block: 0,
                target: 9
            }
        )),
        "{errors:?}"
    );
    assert!(
        !has(&errors, |e| matches!(
            e,
            ValidationError::UnwindDestWithoutLandingPad { .. }
        )),
        "{errors:?}"
    );
}

// ---------------------------------------------------------------------------
// (b'') rule (c): resume re-raises only what a landing pad produced
// ---------------------------------------------------------------------------

/// A function with a `Resume` and NO pad at all: nothing in this frame ever
/// held an exception, so the resumed value is not one. (Before WS2.5 this was
/// the branch's control asserting the opposite; the roadmap schedules the rule.)
#[test]
fn resume_in_a_function_without_any_landing_pad_is_refused() {
    let mut module = baseline();
    let callee = module.functions[0].id;
    let function = caller(&mut module);
    let result = function.blocks[0].body[0].results[0];
    let null = ValueId::new(71);
    function.blocks[0].body = vec![
        InstrNode::new(Inst::Call {
            callee,
            args: vec![],
        })
        .with_result(result),
        InstrNode::new(Inst::Br {
            target: BlockId::new(1),
            args: vec![],
        }),
    ];
    function.blocks[2].body = vec![
        InstrNode::new(Inst::NullPtr).with_result(null),
        InstrNode::new(Inst::Resume { exn: null }),
    ];
    let errors = all_doors(&module);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::MisplacedLandingPad { block: 2, reason }
                if reason.contains("resume of a value no landing pad produced")
                    && reason.contains("contains no landingpad")
        )),
        "{errors:?}"
    );
}

/// One mutation of the baseline: resume the pad's SELECTOR (its `i32` second
/// result) instead of its exception object.
#[test]
fn resume_of_the_landing_pad_selector_is_refused() {
    let mut module = baseline();
    let function = caller(&mut module);
    let selector = function.blocks[2].body[0].results[1];
    function.blocks[2].body[1] = InstrNode::new(Inst::Resume { exn: selector });
    let errors = all_doors(&module);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::MisplacedLandingPad { block: 2, reason }
                if reason.contains("resume of a value no landing pad produced")
                    && reason.contains("type selector")
        )),
        "{errors:?}"
    );
}

/// One mutation of the baseline: the pad is kept, but the block resumes a
/// freshly minted `null` rather than the pad's exception object.
#[test]
fn resume_of_a_literal_beside_a_well_placed_pad_is_refused() {
    let mut module = baseline();
    let function = caller(&mut module);
    let null = ValueId::new(72);
    function.blocks[2].body[1] = InstrNode::new(Inst::NullPtr).with_result(null);
    function.blocks[2]
        .body
        .push(InstrNode::new(Inst::Resume { exn: null }));
    let errors = all_doors(&module);
    let resume_errors: Vec<_> = errors.iter().filter(|e| is_resume_error(e)).collect();
    assert_eq!(
        resume_errors,
        [&ValidationError::MisplacedLandingPad {
            block: 2,
            reason: "resume of a value no landing pad produced: the operand is a literal".into(),
        }],
        "{errors:?}"
    );
    // The pad itself is still well placed.
    assert!(
        !has(&errors, |e| is_placement_error(e) && !is_resume_error(e)),
        "{errors:?}"
    );
}

/// Mutation control for rule (c): the exception object may reach the
/// `Resume` through MEMORY (the in-repo producer's `store exn -> slot` in each
/// pad, `resume (load slot)` in the shared cleanup body) or through a COPY,
/// not only as the pad's own SSA result. A rule demanding the pad's result
/// itself would over-refuse every shared cleanup: under SSA dominance no pad
/// result is available in a block several pads branch into.
#[test]
fn control_resume_through_memory_or_copy_validates() {
    // Through memory: `producer_shaped_eh_lane_validates` covers the shared
    // shape; here the single-pad baseline spills and reloads.
    let mut module = baseline();
    let function = caller(&mut module);
    let exn = function.blocks[2].body[0].results[0];
    let slot = ValueId::new(90);
    let reloaded = ValueId::new(91);
    function.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Alloca {
            ty: Ty::Ptr,
            count: None,
            align: None,
        })
        .with_result(slot),
    );
    function.blocks[2].body = vec![
        function.blocks[2].body[0].clone(),
        InstrNode::new(Inst::Store {
            ty: Ty::Ptr,
            ptr: slot,
            value: exn,
            align: None,
            volatile: false,
        }),
        InstrNode::new(Inst::Load {
            ty: Ty::Ptr,
            ptr: slot,
            align: None,
            volatile: false,
        })
        .with_result(reloaded),
        InstrNode::new(Inst::Resume { exn: reloaded }),
    ];
    let errors = all_doors(&module);
    assert!(!has(&errors, is_placement_error), "{errors:?}");
    assert_eq!(validate_module(&module), []);

    // Through a copy.
    let mut module = baseline();
    let function = caller(&mut module);
    let exn = function.blocks[2].body[0].results[0];
    let copied = ValueId::new(92);
    function.blocks[2].body.insert(
        1,
        InstrNode::new(Inst::Copy {
            ty: Ty::Ptr,
            operand: exn,
        })
        .with_result(copied),
    );
    function.blocks[2].body[2] = InstrNode::new(Inst::Resume { exn: copied });
    assert_eq!(validate_module(&module), []);
}

// ---------------------------------------------------------------------------
// (d) ported ratchet: b6.eh.landingpad_placement_unchecked
// ---------------------------------------------------------------------------

/// The 2026-09-17 proof-program ratchet, ported verbatim in shape: `build_eh(3)`
/// (unwind_dest = `resume null`, no pad) and `build_resume_direct()` (entry
/// block is a pad) through `validate_module_for_codegen` on the licensed clone.
/// The ratchet asserted `no_pad.is_empty() && entry_pad.is_empty()`; the hole
/// is now CLOSED, so each is refused with its named error.
#[test]
fn ratchet_b6_eh_landingpad_placement_is_now_checked() {
    fn build_eh(mode: u8) -> Module {
        let mut mb = ModuleBuilder::new("b6_eh");
        let unary = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
        let callee = {
            let mut fb = mb.function("clean_may_unwind", unary);
            fb.set_producer(Producer::Clean);
            let e = fb.create_block();
            let x = fb.add_block_param(e, Ty::U64);
            fb.switch_to_block(e);
            let one = fb.uconst(Ty::U64, 1);
            let s = fb.add(Ty::U64, x, one);
            fb.ret(vec![s]);
            fb.build()
        };
        {
            let mut fb = mb.function("program", nullary);
            fb.set_producer(Producer::TRust);
            let e = fb.create_block();
            let cont = fb.create_block();
            let pad = fb.create_block();
            let v = fb.add_block_param(cont, Ty::U64);
            fb.switch_to_block(e);
            let c = fb.uconst(Ty::U64, 41);
            let _ = fb.invoke(callee, vec![c], cont, vec![], pad);
            fb.switch_to_block(cont);
            fb.ret(vec![v]);
            fb.switch_to_block(pad);
            if mode == 3 {
                let n = fb.null_ptr();
                fb.resume(n);
            } else {
                let (exn, _sel) = fb.landingpad(true, vec![]);
                fb.resume(exn);
            }
            fb.build();
        }
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        let f = m
            .functions
            .iter_mut()
            .find(|f| f.name == "program")
            .unwrap();
        let node = f.blocks[0].body.last_mut().unwrap();
        let result = node.results[0];
        if let Inst::Invoke { normal_args, .. } = &mut node.inst {
            normal_args.push(result);
        }
        m
    }
    fn build_resume_direct() -> Module {
        let mut mb = ModuleBuilder::new("b6_resume_direct");
        let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let (exn, _sel) = fb.landingpad(true, vec![]);
        fb.resume(exn);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    // Baseline (mode 0) still validates end to end.
    assert_eq!(validate_module_for_codegen(&licensed(&build_eh(0))), []);

    let no_pad = validate_module_for_codegen(&licensed(&build_eh(3)));
    let entry_pad = validate_module_for_codegen(&licensed(&build_resume_direct()));
    assert!(
        no_pad.contains(&ValidationError::UnwindDestWithoutLandingPad {
            block: 0,
            target: 2,
        }),
        "unwind_dest without a LandingPad: {no_pad:?}"
    );
    assert!(
        has(&entry_pad, |e| matches!(
            e,
            ValidationError::MisplacedLandingPad { block: 0, reason }
                if reason.contains("entry block")
        )),
        "LandingPad in the entry block: {entry_pad:?}"
    );
}

// ---------------------------------------------------------------------------
// ModuleValidationReport::unwind_surface (WS2.5 design item 4)
// ---------------------------------------------------------------------------

/// The report names exactly the functions carrying `Invoke` / `LandingPad` /
/// `Resume` — the set a panic=unwind consumer must not rely on a verdict for
/// (ub-numerics-policy §4) — and nothing else.
#[test]
fn unwind_surface_lists_exactly_the_functions_with_eh_instructions() {
    let module = baseline();
    let report = validate_module_report(&module);
    assert!(report.is_ok());
    // `callee` (f0) has no EH instruction; `caller` (f1) has all three.
    assert_eq!(report.unwind_surface(), [FuncId::new(1)]);

    // Each instruction alone puts its function on the surface: a lone
    // `Resume` (refused module) and a lone `LandingPad` (refused module) are
    // listed too — the list is reported regardless of the verdict.
    let mut resume_only = baseline();
    {
        let function = caller(&mut resume_only);
        let callee = FuncId::new(0);
        let result = function.blocks[0].body[0].results[0];
        function.blocks[0].body = vec![
            InstrNode::new(Inst::Call {
                callee,
                args: vec![],
            })
            .with_result(result),
            InstrNode::new(Inst::Br {
                target: BlockId::new(1),
                args: vec![],
            }),
        ];
        let null = ValueId::new(95);
        function.blocks[2].body = vec![
            InstrNode::new(Inst::NullPtr).with_result(null),
            InstrNode::new(Inst::Resume { exn: null }),
        ];
    }
    let report = validate_module_report(&resume_only);
    assert!(!report.is_ok());
    assert_eq!(report.unwind_surface(), [FuncId::new(1)]);

    // Mutation control: an EH-free module has an empty surface.
    let mut mb = ModuleBuilder::new("no_eh");
    let signature = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("plain", signature);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I32, 0);
    fb.ret(vec![zero]);
    fb.build();
    let plain = mb.build().expect("ModuleBuilder::build: test fixture");
    let report = validate_module_report(&plain);
    assert!(report.is_ok());
    assert!(report.unwind_surface().is_empty());
}

// ---------------------------------------------------------------------------
// Display text names what and why
// ---------------------------------------------------------------------------

#[test]
fn placement_errors_display_the_rule() {
    let a = ValidationError::UnwindDestWithoutLandingPad {
        block: 0,
        target: 2,
    }
    .to_string();
    assert!(
        a.contains("bb0") && a.contains("bb2") && a.contains("landingpad"),
        "{a}"
    );
    let b = ValidationError::MisplacedLandingPad {
        block: 4,
        reason: "not the first instruction of its block (position 1)".into(),
    }
    .to_string();
    assert!(
        b.contains("bb4") && b.contains("position 1") && b.contains("not the first instruction"),
        "{b}"
    );
}

// ===========================================================================
// B4 function scope resolution (c15 item 5)
// ===========================================================================

/// The baseline plus one Pending precondition scoped to `caller` (f1) by
/// `function` alone — no site. Legal: a contract obligation is about a whole
/// function, not one instruction.
fn scoped_obligation_module(scope: FuncId) -> Module {
    let mut module = baseline();
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Precondition,
            ProofStatus::Pending,
            "caller precondition",
        )
        .with_function(scope),
    );
    module
}

#[test]
fn obligation_scoped_to_an_existing_function_validates() {
    let module = scoped_obligation_module(FuncId::new(1));
    assert_eq!(validate_module(&module), []);
    assert!(validate_module_report(&module).is_ok());
}

/// Repro row 5d / ratchet `b2.gap.dangling_function_scope_accepted`:
/// `function = Some(FuncId(77))`, `site = None`, in a module with two
/// functions. The ratchet asserted the errors were EMPTY; the hole is closed.
#[test]
fn ratchet_b2_dangling_function_scope_is_now_refused() {
    let module = scoped_obligation_module(FuncId::new(77));
    let errors = validate_module(&module);
    assert!(
        errors.contains(&ValidationError::ObligationFunctionScopeUnresolved {
            obligation: 0,
            function: 77,
            reason: "no such function",
        }),
        "{errors:?}"
    );
    // Every module door agrees.
    let report = validate_module_report(&module).into_errors();
    assert!(
        report.contains(&ValidationError::ObligationFunctionScopeUnresolved {
            obligation: 0,
            function: 77,
            reason: "no such function",
        }),
        "{report:?}"
    );
    let codegen = validate_module_for_codegen(&licensed(&module));
    assert!(
        codegen.contains(&ValidationError::ObligationFunctionScopeUnresolved {
            obligation: 0,
            function: 77,
            reason: "no such function",
        }),
        "{codegen:?}"
    );
    let text = ValidationError::ObligationFunctionScopeUnresolved {
        obligation: 0,
        function: 77,
        reason: "no such function",
    }
    .to_string();
    assert!(
        text.contains("obligation #0") && text.contains("f77") && text.contains("no such function"),
        "{text}"
    );
}

/// An id declared TWICE resolves to no function (the catalog refuses to pick
/// one), so a scope naming it is unresolved for a different stated reason —
/// beside the `DuplicateFuncId` the duplication itself earns.
#[test]
fn obligation_scoped_to_a_duplicated_function_id_is_refused() {
    let mut module = scoped_obligation_module(FuncId::new(1));
    let mut clone = module.functions[1].clone();
    clone.name = "caller_twin".into();
    module.functions.push(clone);
    let errors = validate_module(&module);
    assert!(
        errors.contains(&ValidationError::ObligationFunctionScopeUnresolved {
            obligation: 0,
            function: 1,
            reason: "the id names more than one function",
        }),
        "{errors:?}"
    );
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::DuplicateFuncId(1)
        )),
        "{errors:?}"
    );
}

/// Mutation control: the SAME dangling id supplied through `site` was already
/// refused (`ObligationSiteOutOfRange`); with `function` set as well, the
/// scope rule reports it and the site rule — which would only restate the same
/// dangling id — is not reached. The old refusal is untouched when the scope
/// is absent.
#[test]
fn control_dangling_site_alone_is_still_the_site_error() {
    let mut module = baseline();
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::BoundsCheck,
            ProofStatus::Pending,
            "sited",
        )
        .with_site(ObligationSite::new(FuncId::new(77), BlockId::new(0), 0)),
    );
    let errors = validate_module(&module);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::ObligationSiteOutOfRange { obligation: 0, function: 77, reason, .. }
                if *reason == "no such function"
        )),
        "{errors:?}"
    );
    assert!(
        !has(&errors, |e| matches!(
            e,
            ValidationError::ObligationFunctionScopeUnresolved { .. }
        )),
        "no scope was set, so the scope rule has nothing to say: {errors:?}"
    );

    // With both set to the same dangling id, exactly the scope error names it.
    let mut module = baseline();
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::BoundsCheck,
            ProofStatus::Pending,
            "sited and scoped",
        )
        .with_function(FuncId::new(77))
        .with_site(ObligationSite::new(FuncId::new(77), BlockId::new(0), 0)),
    );
    let errors = validate_module(&module);
    assert!(
        errors.contains(&ValidationError::ObligationFunctionScopeUnresolved {
            obligation: 0,
            function: 77,
            reason: "no such function",
        }),
        "{errors:?}"
    );
    assert!(
        !has(&errors, |e| matches!(
            e,
            ValidationError::ObligationSiteOutOfRange { .. }
        )),
        "{errors:?}"
    );
}

/// Mutation control: a scope that resolves but disagrees with a resolving site
/// is the pre-existing `ObligationSiteFunctionMismatch`, not the new error.
#[test]
fn control_scope_site_disagreement_is_the_mismatch_error_only() {
    let mut module = baseline();
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::BoundsCheck,
            ProofStatus::Pending,
            "mismatched",
        )
        .with_function(FuncId::new(0))
        .with_site(ObligationSite::new(FuncId::new(1), BlockId::new(0), 0)),
    );
    let errors = validate_module(&module);
    assert!(
        errors.contains(&ValidationError::ObligationSiteFunctionMismatch {
            obligation: 0,
            site_function: 1,
            scope_function: 0,
        }),
        "{errors:?}"
    );
    assert!(
        !has(&errors, |e| matches!(
            e,
            ValidationError::ObligationFunctionScopeUnresolved { .. }
        )),
        "{errors:?}"
    );
}
