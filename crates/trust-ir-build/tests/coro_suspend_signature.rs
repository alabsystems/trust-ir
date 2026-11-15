// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// `Inst::CoroSuspend` is held to the function signature like the `Return`
// it macro-expands to (roadmap increment WS2.1, finding F-028; audit row c03,
// 2026-09-17 two-language proof program). The spec-named twins live in
// `validation_holes.rs` and `handle_types.rs`; this file is the end-to-end
// two-language generator (validate AND run) plus the adversarial review
// twins. All three run under standing gate 9 (`validator-fail-closed`).
//
// The instruction is DEFINED (`trust_ir::inst::Inst::CoroSuspend`) as
// `GEP(frame, state_slot)` + `Store(next_state)` + `Return(value)`, and the
// reference interpreter executes exactly that (`Step::Return(vec![yielded])`).
// Before this rule the validator compared only `Inst::Return` operands with
// `FuncTy::returns` and never looked at `frame`, so:
//
//   * a `-> u64` generator could yield a `Bool`, a `-> ()` function could
//     yield at all, and a `-> (u64, u64)` function could yield one value —
//     each was caught only DYNAMICALLY, by the interpreter's
//     `SignatureMismatch`, or by trust-cg's own return-signature check
//     (b6.coro_suspend.yield_type_unchecked);
//   * `frame` could be a `u64` (b6.coro_suspend.frame_operand_unchecked);
//   * and, the v43 consequence, a `-> handle<..>` function could yield a
//     `Ptr` — a forged handle (`handle_types.rs`,
//     b5.gap.UNEXPECTED.coro_suspend_value_not_checked_against_return_type_forges_a_nat).
//
// Every row below is one edit away from the positive generator, and every
// refusal is a NAMED variant: the suspend shares `check_return_values` with
// `Return`, so its refusals are `ReturnArityMismatch` / `ReturnTypeMismatch`,
// and a refined yield is decided at the same `ReturnValues` consumption site.

use trust_ir::inst::CastOp;
use trust_ir::interpret::Interpreter;
use trust_ir::{BodyGate, Constant, Function, Inst, InstrNode, Module, Producer, SwitchCase, Ty};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{
    HandleRegistry, ModuleBuilder, TRUSTED_HANDLE_RUNTIMES, validate_function, validate_module,
    validate_module_for_codegen, validate_module_with_handle_registry,
};

/// How the generator's suspends are perturbed. `Good` is the positive
/// fixture; every other arm is a single edit to it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Shape {
    /// `clean_gen_step(frame: Ptr) -> u64`, yielding 10 then 30 then done.
    Good,
    /// The state-1 suspend yields a `Bool` into the `-> u64` signature.
    YieldBool,
    /// The state-0 suspend names its own u64 yield as the frame.
    U64Frame,
    /// The generator is declared `-> ()`: nothing to yield into.
    ReturnsUnit,
    /// The generator is declared `-> (u64, u64)`: one value yielded of two.
    ReturnsPair,
    /// Control: the same yield, spelled as a plain `Return` — the shared rule
    /// must report the identical finding for both spellings.
    YieldBoolViaReturn,
}

/// The b6 generator: a Clean `clean_gen_step(frame: Ptr) -> u64` that
/// dispatches on `frame[0]` and yields 10 (state 0 -> 1), 30 (state 1 -> 2),
/// then returns 0 once done; a Rust `program() -> u64` that owns the frame,
/// resumes three times and sums the yields with the final state:
/// 10 + 30 + 0 + 2 = 42.
fn generator(shape: Shape) -> Module {
    let mut mb = ModuleBuilder::new("coro_signature");
    let returns = match shape {
        Shape::ReturnsUnit => vec![],
        Shape::ReturnsPair => vec![Ty::U64, Ty::U64],
        _ => vec![Ty::U64],
    };
    let step_ty = mb.add_func_type(vec![Ty::Ptr], returns);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let step = {
        let mut fb = mb.function("clean_gen_step", step_ty);
        fb.set_producer(Producer::Clean);
        let entry = fb.create_block();
        let s0 = fb.create_block();
        let s1 = fb.create_block();
        let done = fb.create_block();
        let frame = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        let state = fb.load(Ty::I64, frame);
        fb.switch(
            state,
            vec![
                SwitchCase {
                    value: Constant::Int(0),
                    target: s0,
                    args: vec![],
                },
                SwitchCase {
                    value: Constant::Int(1),
                    target: s1,
                    args: vec![],
                },
            ],
            done,
            vec![],
        );
        fb.switch_to_block(s0);
        let v = fb.uconst(Ty::U64, 10);
        fb.ret(vec![v]);
        fb.switch_to_block(s1);
        let v = if matches!(shape, Shape::YieldBool | Shape::YieldBoolViaReturn) {
            fb.bool_const(true)
        } else {
            fb.uconst(Ty::U64, 30)
        };
        fb.ret(vec![v]);
        fb.switch_to_block(done);
        let z = fb.uconst(Ty::U64, 0);
        fb.ret(vec![z]);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let frame = fb.alloca(Ty::I64);
        let zero = fb.iconst(Ty::I64, 0);
        fb.store(Ty::I64, frame, zero);
        let a = fb.call(step, vec![frame]); // 10
        let b = fb.call(step, vec![frame]); // 30
        let c = fb.call(step, vec![frame]); // 0 (done)
        let state = fb.load(Ty::I64, frame); // 2
        let state = fb.cast(CastOp::Bitcast, Ty::I64, Ty::U64, state);
        let ab = fb.add(Ty::U64, a, b);
        let abc = fb.add(Ty::U64, ab, c);
        let out = fb.add(Ty::U64, abc, state); // 42
        fb.ret(vec![out]);
        fb.build();
    }
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    // Rewrite the two `ret`s of the live states into suspends; the `done`
    // state keeps its plain `Return`. The block bodies were emitted by the
    // builder, so the terminator is the last node of each.
    let func = module
        .functions
        .iter_mut()
        .find(|f| f.name == "clean_gen_step")
        .expect("generator");
    let frame = func.blocks[0].params[0].0;
    for (block_index, next_state) in [(1usize, 1i64), (2, 2)] {
        let node = func.blocks[block_index]
            .body
            .last_mut()
            .expect("terminator");
        let Inst::Return { values } = &node.inst else {
            panic!("builder emitted a non-return terminator");
        };
        let value = values[0];
        if shape == Shape::YieldBoolViaReturn && block_index == 2 {
            continue;
        }
        let frame = if shape == Shape::U64Frame && block_index == 1 {
            value
        } else {
            frame
        };
        *node = InstrNode::new(Inst::CoroSuspend {
            frame,
            state_slot: 0,
            next_state,
            value,
        });
    }
    // In the `ReturnsUnit` / `ReturnsPair` shapes the `program` side's
    // `call` binds one u64 result to a signature that has none / two — that
    // is a second, unrelated defect. Keep the twin ONE edit from the positive
    // fixture by making `program` a plain `-> 42` that never calls the
    // generator, so the only thing wrong with the module is the suspend.
    if matches!(shape, Shape::ReturnsUnit | Shape::ReturnsPair) {
        let program = module
            .functions
            .iter_mut()
            .find(|f| f.name == "program")
            .expect("program");
        let entry = &mut program.blocks[0];
        entry.body.clear();
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(42),
            })
            .with_result(trust_ir::ValueId::new(0)),
        );
        entry.body.push(InstrNode::new(Inst::Return {
            values: vec![trust_ir::ValueId::new(0)],
        }));
    }
    module
}

/// Every body-bearing function `Gated`, so `validate_module_for_codegen`
/// reports only structural findings. The authorities are ones the codegen
/// layer binds to NO evidence: since WS1.5, `clean-kernel-tv` demands a
/// kernel-rechecked TranslationValidation certificate per body, which these
/// fixtures do not mint.
fn licensed(module: &Module) -> Module {
    let mut module = module.clone();
    for f in &mut module.functions {
        if f.body_gate.is_none() && !f.blocks.is_empty() {
            let authority = if f.producer == Some(Producer::Clean) {
                "trust-direct-lane-structural"
            } else {
                "trust-verify"
            };
            f.body_gate = Some(BodyGate::Gated {
                authority: authority.into(),
                evidence: None,
            });
        }
    }
    module
}

fn generator_function(module: &Module) -> &Function {
    module
        .functions
        .iter()
        .find(|f| f.name == "clean_gen_step")
        .expect("generator")
}

fn run_program(module: &Module) -> Result<u128, String> {
    let program = module
        .functions
        .iter()
        .find(|f| f.name == "program")
        .expect("program");
    Interpreter::with_module(module)
        .execute_func(program.id, [])
        .map(|outcome| {
            outcome.returns[0]
                .as_int()
                .expect("u64 return")
                .as_unsigned()
        })
        .map_err(|e| format!("{:?}: {e}", e.code))
}

fn has<F: Fn(&ValidationError) -> bool>(errors: &[ValidationError], pred: F) -> bool {
    errors.iter().any(pred)
}

/// The retained C03 controls exercised each scalar defect through every
/// admission tier. A different finding must not stand in for the named one.
fn assert_other_tiers_report(module: &Module, expected: &[ValidationError]) {
    assert!(
        !expected.is_empty(),
        "a refusal control must name its finding"
    );
    let module = licensed(module);
    let registry = HandleRegistry::from_pins(TRUSTED_HANDLE_RUNTIMES).unwrap();
    for (tier, errors) in [
        ("codegen", validate_module_for_codegen(&module)),
        (
            "registry",
            validate_module_with_handle_registry(&module, &registry),
        ),
    ] {
        for error in expected {
            assert!(
                errors.contains(error),
                "{tier}: missing {error:?}: {errors:?}"
            );
        }
    }
}

// ───────────────────────────── (a) positive ─────────────────────────────

#[test]
fn a_well_typed_generator_validates_and_runs_as_before() {
    let module = generator(Shape::Good);
    assert_eq!(validate_module(&module), Vec::new());
    assert_eq!(validate_module_for_codegen(&licensed(&module)), Vec::new());
    assert_eq!(validate_function(generator_function(&module)), Vec::new());
    let registry = HandleRegistry::from_pins(TRUSTED_HANDLE_RUNTIMES).unwrap();
    assert_eq!(
        validate_module_with_handle_registry(&licensed(&module), &registry),
        Vec::new()
    );
    // The dynamic meaning is untouched: 10 + 30 + 0 + final state 2.
    assert_eq!(run_program(&module), Ok(42));
}

// ───────────────────── (b) twins, each one edit away ─────────────────────

/// Port of `b6.coro_suspend.yield_type_unchecked`: the ratchet asserted
/// `validate_module_for_codegen(all Gated) == []` while the interpreter
/// trapped with `SignatureMismatch`. The static rule now agrees with the
/// dynamic one.
#[test]
fn a_yield_of_the_wrong_type_is_refused_as_return_type_mismatch() {
    let module = generator(Shape::YieldBool);
    let mismatch = |e: &ValidationError| {
        matches!(
            e,
            ValidationError::ReturnTypeMismatch { block: 2, expected, actual }
                if expected == "u64" && actual == "bool"
        )
    };
    let errors = validate_module(&module);
    assert!(has(&errors, mismatch), "{errors:?}");
    // Exactly the one defect, at the one site: the state-0 suspend (bb1)
    // yields a u64 and stays clean.
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].to_string(),
        "bb2: return type mismatch: expected u64, got bool"
    );
    assert_other_tiers_report(&module, &errors);
    // The dynamic check that used to be the only guard still fires.
    let run = run_program(&module);
    assert!(
        matches!(&run, Err(e) if e.starts_with("SignatureMismatch")),
        "{run:?}"
    );
}

/// Port of `b6.coro_suspend.frame_operand_unchecked`: the ratchet asserted
/// `validate_module_for_codegen(all Gated) == []` while the interpreter
/// trapped in the macro-expanded GEP (`expected pointer value, got u64`).
#[test]
fn a_non_pointer_frame_is_refused_as_operand_not_pointer() {
    let module = generator(Shape::U64Frame);
    let not_pointer = |e: &ValidationError| {
        matches!(
            e,
            ValidationError::OperandNotPointer { block: 1, op, ty }
                if op == "coro_suspend" && ty == "u64"
        )
    };
    let errors = validate_module(&module);
    assert!(has(&errors, not_pointer), "{errors:?}");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].to_string(),
        "bb1: coro_suspend operand must be pointer-like, got u64"
    );
    assert_other_tiers_report(&module, &errors);
    // The operand rule lives in the per-function type pass, so standalone
    // function validation refuses it too (the yield rule needs the module's
    // signature table and is a module rule).
    let standalone = validate_function(generator_function(&module));
    assert!(has(&standalone, not_pointer), "{standalone:?}");
    let run = run_program(&module);
    assert!(
        matches!(&run, Err(e) if e.starts_with("TypeError") && e.contains("GEP: expected pointer value, got u64")),
        "{run:?}"
    );
}

#[test]
fn a_suspend_in_a_function_returning_nothing_is_refused_as_arity_mismatch() {
    let module = generator(Shape::ReturnsUnit);
    let errors = validate_module(&module);
    // Both suspends (bb1, bb2) are wrong; the `done` block's `ret 0` into
    // `-> ()` is the ordinary `ReturnArityMismatch` and is not this rule's.
    // Both suspends (bb1, bb2) AND the `done` block's `ret 0` are the same
    // finding: each hands back one value to a signature with no slot.
    for block in [1u32, 2, 3] {
        assert!(
            has(&errors, |e| matches!(
                e,
                ValidationError::ReturnArityMismatch { block: b, expected: 0, actual: 1 }
                    if *b == block
            )),
            "bb{block}: {errors:?}"
        );
    }
    assert_eq!(errors.len(), 3, "{errors:?}");
    // No TYPE finding: with no return slot there is nothing to compare
    // against, and the arity finding already names the defect.
    assert!(
        !has(&errors, |e| matches!(
            e,
            ValidationError::ReturnTypeMismatch { .. }
        )),
        "{errors:?}"
    );
    let text = errors
        .iter()
        .find(|e| matches!(e, ValidationError::ReturnArityMismatch { block: 1, .. }))
        .expect("bb1 arity")
        .to_string();
    assert_eq!(text, "bb1: return arity mismatch: expected 0 values, got 1");
    assert_other_tiers_report(&module, &errors);
}

#[test]
fn a_suspend_in_a_function_returning_two_values_is_refused_as_arity_mismatch() {
    let module = generator(Shape::ReturnsPair);
    let errors = validate_module(&module);
    for block in [1u32, 2] {
        assert!(
            has(&errors, |e| matches!(
                e,
                ValidationError::ReturnArityMismatch { block: b, expected: 2, actual: 1 }
                    if *b == block
            )),
            "bb{block}: {errors:?}"
        );
    }
    // The single yielded u64 does match the FIRST return slot, so the type
    // rule stays silent: arity is the whole defect.
    assert!(
        !has(&errors, |e| matches!(
            e,
            ValidationError::ReturnTypeMismatch { .. }
        )),
        "{errors:?}"
    );
    assert_other_tiers_report(&module, &errors);
}

// ───────────────────────── (c) mutation controls ─────────────────────────

#[test]
fn a_suspend_with_an_undefined_yield_is_refused_by_each_tier() {
    let mut module = generator(Shape::Good);
    assert_eq!(validate_module(&module), Vec::new());
    let step = module
        .functions
        .iter_mut()
        .find(|f| f.name == "clean_gen_step")
        .expect("generator");
    let Inst::CoroSuspend { value, .. } =
        &mut step.blocks[1].body.last_mut().expect("suspend").inst
    else {
        panic!("state zero must end in a suspend");
    };
    *value = trust_ir::ValueId::new(99);
    let errors = validate_module(&module);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::UseBeforeDef {
                value: 99,
                block: 1
            }
        )),
        "{errors:?}"
    );
    assert_other_tiers_report(&module, &errors);
}

/// The same Bool yield spelled as a plain `Return` is refused with the
/// IDENTICAL finding: the two terminators share `check_return_values`, so the
/// rule cannot drift between them.
#[test]
fn the_return_spelling_of_the_same_defect_is_the_same_finding() {
    let via_return = validate_module(&generator(Shape::YieldBoolViaReturn));
    let via_suspend = validate_module(&generator(Shape::YieldBool));
    assert_eq!(via_return, via_suspend);
    assert!(
        matches!(
            via_return.as_slice(),
            [ValidationError::ReturnTypeMismatch { block: 2, expected, actual }]
                if expected == "u64" && actual == "bool"
        ),
        "{via_return:?}"
    );
}

/// Undoing the single edit restores the clean verdict: the refusal is caused
/// by the mutated field and nothing else in the fixture.
#[test]
fn repairing_the_mutated_field_restores_the_clean_verdict() {
    // Wrong yield -> retype the yield back to u64 by replacing the Bool
    // constant's node with a u64 constant of the same result id.
    let mut module = generator(Shape::YieldBool);
    {
        let func = module
            .functions
            .iter_mut()
            .find(|f| f.name == "clean_gen_step")
            .expect("generator");
        let bb2 = &mut func.blocks[2];
        let const_node = &mut bb2.body[0];
        assert!(matches!(const_node.inst, Inst::Const { ty: Ty::Bool, .. }));
        const_node.inst = Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(30),
        };
    }
    assert_eq!(validate_module(&module), Vec::new());
    assert_eq!(run_program(&module), Ok(42));

    // Wrong frame -> point the suspend back at the frame parameter.
    let mut module = generator(Shape::U64Frame);
    {
        let func = module
            .functions
            .iter_mut()
            .find(|f| f.name == "clean_gen_step")
            .expect("generator");
        let frame = func.blocks[0].params[0].0;
        let Inst::CoroSuspend { frame: slot, .. } =
            &mut func.blocks[1].body.last_mut().expect("suspend").inst
        else {
            panic!("bb1 must end in a suspend");
        };
        *slot = frame;
    }
    assert_eq!(validate_module(&module), Vec::new());
    assert_eq!(run_program(&module), Ok(42));
}

// ───────────────── (d) adversarial twins (review pass) ──────────────────

/// How `refined_gen` hands `x` back.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum RefinedExit {
    Return,
    CoroSuspend,
}

/// ```text
/// fn refined_gen(frame: Ptr, x: <param_ty>) -> Refine(i64, 0..=8) { <exit> x }
/// ```
///
/// `param_ty` is either the plain `i64` (nothing is known about `x`) or the
/// signature's own `Refine(i64, 0..=8)`.
fn refined_gen(refined_param: bool, exit: RefinedExit) -> Module {
    let mut m = Module::new("coro_refined_yield");
    let i64_ty = m.add_type(Ty::I64).expect("Module::add_type: test fixture");
    let pred = m
        .intern_pred(trust_ir::Pred::Interval { lo: 0, hi: 8 })
        .expect("Module::intern_pred: test fixture")
        .expect("canonical interval");
    let refined = Ty::Refine(i64_ty, pred);
    let param_ty = if refined_param {
        refined.clone()
    } else {
        Ty::I64
    };
    let sig = m
        .add_func_type(trust_ir::FuncTy {
            params: vec![Ty::Ptr, param_ty.clone()],
            returns: vec![refined],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(
        trust_ir::FuncId::new(0),
        "refined_gen",
        sig,
        trust_ir::BlockId::new(0),
    );
    let mut entry = trust_ir::Block::new(trust_ir::BlockId::new(0))
        .with_param(trust_ir::ValueId::new(0), Ty::Ptr)
        .with_param(trust_ir::ValueId::new(1), param_ty);
    entry.body.push(InstrNode::new(match exit {
        RefinedExit::Return => Inst::Return {
            values: vec![trust_ir::ValueId::new(1)],
        },
        RefinedExit::CoroSuspend => Inst::CoroSuspend {
            frame: trust_ir::ValueId::new(0),
            state_slot: 0,
            next_state: 1,
            value: trust_ir::ValueId::new(1),
        },
    }));
    f.blocks.push(entry);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

/// A refined signature is a PROMISE about every value handed back. `Return`
/// earns the promise by implication in `validate_refinements`, which is why
/// the plain return-type rule exempts `Refine`. The suspend shares that
/// exemption (WS2.1), so it MUST also share the implication check —
/// `consumption_role` files `CoroSuspend` under the same `ReturnValues` site.
/// Without that routing the exemption would re-open the hole one layer down:
/// an unconstrained `i64` yielded out of a `-> Refine(i64, 0..=8)` coroutine
/// with no check at all.
#[test]
fn an_unrefined_yield_out_of_a_refined_signature_is_refused() {
    // Control: the SAME escape through `Return` is decided by the refinement
    // layer (implication fails: a bare i64 is `top`).
    let via_return = validate_module(&refined_gen(false, RefinedExit::Return));
    assert!(
        has(&via_return, |e| matches!(
            e,
            ValidationError::RefinementNotImplied { .. }
        )),
        "{via_return:?}"
    );
    // The twin: the suspend is refused by the same refinement layer, at the
    // yield site, by name.
    let errors = validate_module(&refined_gen(false, RefinedExit::CoroSuspend));
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::RefinementNotImplied { location, .. }
                if location.contains("bb0: coro_suspend yield 0")
        )),
        "{errors:?}"
    );
    // Positive: yielding a value that already carries the signature's exact
    // refinement is clean.
    assert_eq!(
        validate_module(&refined_gen(true, RefinedExit::CoroSuspend)),
        Vec::new()
    );
}
