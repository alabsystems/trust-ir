// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS3.13 (F-055): the executable half of the G18-2 ratification that
//! first-class closure APPLICATION is **by value** — `FnOnce`-shaped.
//!
//! `lowering-target-subset.md` "Closure application" ratifies that a
//! `CallIndirect` over a `Ty::Closure` callee supplies the captured
//! environment as leading arguments, spread in capture order. Everything
//! below is the consequence, pinned so a later change cannot quietly acquire
//! by-reference application semantics:
//!
//! * the captures are ARGUMENTS, so a write inside the body cannot reach the
//!   caller's closure value: the next application sees the ORIGINAL captures
//!   (`first_class_closure_application_is_by_value`);
//! * **capture MODE therefore needs no new `ClosureTy` field**: a
//!   by-reference capture is a capture SLOT WHOSE TYPE IS A POINTER, and the
//!   by-value argument is then the pointer, so the pointee IS shared across
//!   applications (`by_reference_capture_is_a_pointer_typed_capture_slot`);
//! * a stateful Rust `Fn`/`FnMut` whose state must persist across calls uses
//!   the explicit spelling the codegen refusal already prescribes — an
//!   environment aggregate in memory plus a `Ty::Func` that takes the
//!   environment pointer — which validates, lowers, and persists
//!   (`explicit_env_pointer_spelling_persists_and_is_lowerable`).
//!
//! An undeclared closure frame keeps its named codegen refusal and has no
//! byte layout. A coherent `Module.closure_layouts` declaration supplies the
//! capture image; the memory cases below check both that negative and actual
//! capture-only transport through a declared frame. Application remains by
//! value in either case. Layout and lowerability checks grant no proof or
//! codegen license.

use trust_ir::constant::Constant;
use trust_ir::interpret::{InterpretErrorCode, Interpreter};
use trust_ir::shape::LayoutError;
use trust_ir::ty::{ClosureTy, Ty};
use trust_ir::value::ClosureTyId;
use trust_ir::{ClosureLayoutDescriptor, Module};
use trust_ir_build::builder::ModuleBuilder;
use trust_ir_build::validate::{ValidationError, codegen_lowerability_errors, validate_module};

/// `@program()` under the reference interpreter, as an unsigned integer.
fn run_program(module: &Module) -> u128 {
    let func = module
        .function_by_name("program")
        .expect("every fixture here defines @program");
    let outcome = Interpreter::with_module(module)
        .execute_func(func.id, [])
        .expect("a structurally valid fixture must execute");
    outcome.returns[0]
        .as_int()
        .expect("@program returns u64")
        .as_unsigned()
}

/// The `UnlowerableForCodegen` rows that name a `Ty::Closure` callee.
fn closure_callee_refusals(module: &Module) -> Vec<String> {
    codegen_lowerability_errors(module)
        .into_iter()
        .filter_map(|e| match e {
            ValidationError::UnlowerableForCodegen { inst, detail, .. }
                if inst == "CallIndirect" && detail.contains("Ty::Closure") =>
            {
                Some(detail)
            }
            _ => None,
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Fixtures. All three compute THE SAME source-level program: a counter that
// starts at 0 and is bumped twice, reported as `first * 10 + second`. The
// spelling of the environment is the only thing that differs, so the returned
// number is a direct readout of the capture discipline: 12 = the second call
// saw the first call's write, 11 = it did not.
// ---------------------------------------------------------------------------

/// The ratified explicit spelling: an environment aggregate in memory plus a
/// `Ty::Func` that takes the environment pointer. `bump(env) = *env += 1`.
fn build_env_pointer_counter() -> Module {
    let mut mb = ModuleBuilder::new("ws3_13_env_pointer_counter");
    let bump_sig = mb.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);

    let bump = {
        let mut fb = mb.function("bump", bump_sig);
        let e = fb.create_block();
        let env = fb.add_block_param(e, Ty::Ptr);
        fb.switch_to_block(e);
        let n = fb.load(Ty::U64, env);
        let one = fb.uconst(Ty::U64, 1);
        let n1 = fb.add(Ty::U64, n, one);
        fb.store(Ty::U64, env, n1);
        fb.ret(vec![n1]);
        fb.build()
    };

    {
        let mut fb = mb.function("program", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let env = fb.alloca(Ty::U64);
        let zero = fb.uconst(Ty::U64, 0);
        fb.store(Ty::U64, env, zero);
        // A `Ty::Func` VALUE, applied twice through `CallIndirect` — the same
        // elimination form the closure fixtures use, so the two modules differ
        // in the callee's TYPE and nothing else.
        let f = fb.fn_addr(bump_sig, bump);
        let a = fb.call_indirect(f, bump_sig, vec![env]);
        let b = fb.call_indirect(f, bump_sig, vec![env]);
        let ten = fb.uconst(Ty::U64, 10);
        let a10 = fb.mul(Ty::U64, a, ten);
        let r = fb.add(Ty::U64, a10, b);
        fb.ret(vec![r]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The first-class spelling with a BY-VALUE capture: `ClosureTy { func: () ->
/// u64, captures: [u64] }`, applied twice.
fn build_first_class_value_capture(apply_twice: bool) -> Module {
    let mut mb = ModuleBuilder::new("ws3_13_first_class_value_capture");
    let apparent = mb.add_func_type(vec![], vec![Ty::U64]);
    // physical = captures ++ apparent params -> apparent returns
    let physical = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let clos_id = mb.add_closure_type(ClosureTy {
        func: apparent,
        captures: vec![Ty::U64],
    });
    let clos = Ty::Closure(clos_id);

    let bump = {
        let mut fb = mb.function("bump", physical);
        let e = fb.create_block();
        let n = fb.add_block_param(e, Ty::U64);
        fb.switch_to_block(e);
        let one = fb.uconst(Ty::U64, 1);
        let n1 = fb.add(Ty::U64, n, one);
        fb.ret(vec![n1]);
        fb.build()
    };

    {
        let mut fb = mb.function("program", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let c = fb.const_value(
            clos.clone(),
            Constant::Closure {
                func: bump,
                captures: vec![Constant::Int(0)],
            },
        );
        let a = fb.call_indirect(c, apparent, vec![]);
        let b = if apply_twice {
            fb.call_indirect(c, apparent, vec![])
        } else {
            // Mutation control: INTRODUCTION plus capture PROJECTION, with no
            // second application. `ExtractField` reads capture 0 (the seed).
            fb.extract_field(Ty::U64, c, 0)
        };
        let ten = fb.uconst(Ty::U64, 10);
        let a10 = fb.mul(Ty::U64, a, ten);
        let r = fb.add(Ty::U64, a10, b);
        fb.ret(vec![r]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The first-class spelling with a BY-REFERENCE capture: the capture SLOT is
/// typed `Ty::Ptr` and is filled at run time with the address of an `Alloca`.
/// No new `ClosureTy` field is involved; the mode is the slot's type.
fn build_first_class_pointer_capture() -> Module {
    let mut mb = ModuleBuilder::new("ws3_13_first_class_pointer_capture");
    let apparent = mb.add_func_type(vec![], vec![Ty::U64]);
    let physical = mb.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let clos_id = mb.add_closure_type(ClosureTy {
        func: apparent,
        captures: vec![Ty::Ptr],
    });
    let clos = Ty::Closure(clos_id);

    let bump = {
        let mut fb = mb.function("bump", physical);
        let e = fb.create_block();
        let env = fb.add_block_param(e, Ty::Ptr);
        fb.switch_to_block(e);
        let n = fb.load(Ty::U64, env);
        let one = fb.uconst(Ty::U64, 1);
        let n1 = fb.add(Ty::U64, n, one);
        fb.store(Ty::U64, env, n1);
        fb.ret(vec![n1]);
        fb.build()
    };

    {
        let mut fb = mb.function("program", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let env = fb.alloca(Ty::U64);
        let zero = fb.uconst(Ty::U64, 0);
        fb.store(Ty::U64, env, zero);
        // The literal's capture is the null seed; the register-level construct
        // lane overwrites capture 0 with the runtime address.
        let seed = fb.const_value(
            clos.clone(),
            Constant::Closure {
                func: bump,
                captures: vec![Constant::Int(0)],
            },
        );
        let c = fb.insert_field(clos.clone(), seed, 0, env);
        let a = fb.call_indirect(c, apparent, vec![]);
        let b = fb.call_indirect(c, apparent, vec![]);
        let ten = fb.uconst(Ty::U64, 10);
        let a10 = fb.mul(Ty::U64, a, ten);
        let r = fb.add(Ty::U64, a10, b);
        fb.ret(vec![r]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

// ---------------------------------------------------------------------------
// Positive fixture
// ---------------------------------------------------------------------------

/// The spelling the codegen refusal prescribes for a stateful `Fn`/`FnMut`:
/// it validates, it is LOWERABLE, and the state persists across applications.
#[test]
fn explicit_env_pointer_spelling_persists_and_is_lowerable() {
    let m = build_env_pointer_counter();
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(
        codegen_lowerability_errors(&m),
        vec![],
        "the prescribed replacement must itself be lowerable, or the refusal \
         names no way out"
    );
    // 1 then 2: the second application observes the first one's write.
    assert_eq!(run_program(&m), 12);
}

// ---------------------------------------------------------------------------
// Negative twin — ONE mutation: the callee's TYPE is `Ty::Closure`, not
// `Ty::Func`. Refused with the specific named reason.
// ---------------------------------------------------------------------------

#[test]
fn first_class_closure_application_is_by_value() {
    let m = build_first_class_value_capture(true);
    // Structurally valid and executable: G18-2 made `Ty::Closure` eliminable.
    assert_eq!(validate_module(&m), vec![]);
    // 1 then 1: the capture is passed as an ARGUMENT, so the second
    // application sees the ORIGINAL seed. `FnOnce`-shaped, by ratification.
    assert_eq!(
        run_program(&m),
        11,
        "first-class closure application is by value: a body's write to a \
         by-value capture must not reach the caller's closure value"
    );

    // ... and it is refused for codegen, by the NAMED reason, once per
    // application site.
    let refusals = closure_callee_refusals(&m);
    assert_eq!(
        refusals.len(),
        2,
        "one refusal per application: {refusals:?}"
    );
    for detail in &refusals {
        assert!(
            detail.contains("the callee is a Ty::Closure value"),
            "refusal must name the closure callee: {detail}"
        );
        assert!(
            detail.contains("an environment aggregate plus a Ty::Func pointer"),
            "refusal must name the prescribed replacement: {detail}"
        );
    }
    assert_eq!(
        codegen_lowerability_errors(&m).len(),
        2,
        "the closure applications are the ONLY unlowerable constructs here"
    );

    // The wire half of WS3.13 is not in this commit: without a declared
    // closure layout a `Ty::Closure` still has no shape, which is why the
    // refusal cannot be lifted yet.
    assert!(matches!(
        m.ty_layout_shape(&Ty::Closure(ClosureTyId::new(0))),
        Err(LayoutError::UnsupportedTyShape(_))
    ));
}

/// The by-value/by-reference pair, read off the SAME two-bump program: the
/// only difference is the capture slot's TYPE, which is why capture mode
/// needs no field of its own.
#[test]
fn by_reference_capture_is_a_pointer_typed_capture_slot() {
    let by_value = build_first_class_value_capture(true);
    let by_ref = build_first_class_pointer_capture();
    assert_eq!(validate_module(&by_ref), vec![]);
    assert_eq!(run_program(&by_value), 11);
    assert_eq!(
        run_program(&by_ref),
        12,
        "a pointer-typed capture slot IS the by-reference mode: the pointer \
         is still passed by value, so the pointee is shared"
    );
    // Both spellings stay refused for codegen for the same reason.
    assert_eq!(closure_callee_refusals(&by_ref).len(), 2);
}

// ---------------------------------------------------------------------------
// Mutation controls — the rule does not over-refuse.
// ---------------------------------------------------------------------------

/// Closure INTRODUCTION (`Const`) and capture PROJECTION (`ExtractField`)
/// stay lowerable: exactly one of the two applications is removed, and
/// exactly one refusal goes with it.
#[test]
fn closure_introduction_and_capture_projection_are_not_refused() {
    let two = build_first_class_value_capture(true);
    let one = build_first_class_value_capture(false);
    assert_eq!(validate_module(&one), vec![]);
    assert_eq!(closure_callee_refusals(&two).len(), 2);
    assert_eq!(
        closure_callee_refusals(&one).len(),
        1,
        "removing one APPLICATION removes exactly one refusal; the surviving \
         Const + ExtractField are not refused"
    );
    // 1 then the projected seed 0.
    assert_eq!(run_program(&one), 10);
}

/// The refusal is caused by the callee's TYPE, not by indirect calls, by
/// `Alloca` environments, or by the module's shape: the env-pointer fixture
/// applies a `Ty::Func` value through the very same `CallIndirect` twice and
/// is not refused.
#[test]
fn a_ty_func_callee_is_not_refused() {
    let m = build_env_pointer_counter();
    let indirect_calls = m
        .functions
        .iter()
        .flat_map(|f| f.blocks.iter())
        .flat_map(|b| b.body.iter())
        .filter(|n| matches!(n.inst, trust_ir::inst::Inst::CallIndirect { .. }))
        .count();
    assert_eq!(indirect_calls, 2);
    assert_eq!(closure_callee_refusals(&m), Vec::<String>::new());
    assert_eq!(codegen_lowerability_errors(&m), vec![]);
}

/// The prescribed replacement is not merely "some other module": it computes
/// what the stateful closure was FOR. A producer that reaches for a
/// first-class closure to spell `FnMut`-with-state silently gets a different
/// answer, which is why the ratification makes that the producer's error.
#[test]
fn the_two_spellings_disagree_and_only_one_is_lowerable() {
    let explicit = build_env_pointer_counter();
    let first_class = build_first_class_value_capture(true);
    assert_ne!(run_program(&explicit), run_program(&first_class));
    assert_eq!(run_program(&explicit), 12);
    assert_eq!(run_program(&first_class), 11);
    assert!(codegen_lowerability_errors(&explicit).is_empty());
    assert!(!codegen_lowerability_errors(&first_class).is_empty());
}

/// Sanity: the physical signature a `Constant::Closure` names really is
/// `captures ++ apparent params -> apparent returns`, in both capture modes.
#[test]
fn closure_literal_names_the_physical_signature() {
    for m in [
        build_first_class_value_capture(true),
        build_first_class_pointer_capture(),
    ] {
        let bump = &m.functions[0];
        assert_eq!(bump.name, "bump");
        let physical = m.func_type(bump.ty).expect("declared signature");
        let closure = &m.closure_types[0];
        let apparent = m.func_type(closure.func).expect("apparent signature");
        assert_eq!(
            physical.params,
            closure
                .captures
                .iter()
                .cloned()
                .chain(apparent.params.iter().cloned())
                .collect::<Vec<_>>()
        );
        assert_eq!(physical.returns, apparent.returns);
    }
}

// ---------------------------------------------------------------------------
// Adversarial review (WS3.13): the by-value ruling and the refusal must hold
// for every way a closure VALUE can reach an application site, not only for a
// `Const` in the applying function. `codegen_lowerability_errors` reads the
// callee's type off `build_module_value_types`, so a definition form that map
// missed would be an application accepted for codegen — exactly the miscompile
// the refusal exists to prevent. Each fixture below routes the SAME two-bump
// program through one definition form the implementer did not write.
// ---------------------------------------------------------------------------

/// Shared skeleton: the `bump` target and the closure type of the by-value
/// fixture, so each routing fixture differs from it in the ROUTE alone.
struct ValueCaptureSkeleton {
    mb: ModuleBuilder,
    apparent: trust_ir::value::FuncTyId,
    nullary: trust_ir::value::FuncTyId,
    clos: Ty,
    bump: trust_ir::value::FuncId,
}

fn value_capture_skeleton(name: &str) -> ValueCaptureSkeleton {
    let mut mb = ModuleBuilder::new(name);
    let apparent = mb.add_func_type(vec![], vec![Ty::U64]);
    let physical = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let clos_id = mb.add_closure_type(ClosureTy {
        func: apparent,
        captures: vec![Ty::U64],
    });
    let bump = {
        let mut fb = mb.function("bump", physical);
        let e = fb.create_block();
        let n = fb.add_block_param(e, Ty::U64);
        fb.switch_to_block(e);
        let one = fb.uconst(Ty::U64, 1);
        let n1 = fb.add(Ty::U64, n, one);
        fb.ret(vec![n1]);
        fb.build()
    };
    ValueCaptureSkeleton {
        mb,
        apparent,
        nullary,
        clos: Ty::Closure(clos_id),
        bump,
    }
}

/// `first * 10 + second` from two already-computed bumps.
fn report(
    fb: &mut trust_ir_build::builder::FunctionBuilder<'_>,
    a: trust_ir::value::ValueId,
    b: trust_ir::value::ValueId,
) {
    let ten = fb.uconst(Ty::U64, 10);
    let a10 = fb.mul(Ty::U64, a, ten);
    let r = fb.add(Ty::U64, a10, b);
    fb.ret(vec![r]);
}

/// This fixture's sole capture is one u64, with no function-pointer word.
fn declare_value_capture_frame(module: &mut Module, clos: &Ty) {
    let Ty::Closure(closure) = clos else {
        panic!("the value-capture fixture has a closure type");
    };
    module.closure_layouts.push(ClosureLayoutDescriptor {
        closure: *closure,
        size: 8,
        align: 8,
        capture_offsets: vec![0],
        origin: None,
    });
    assert!(matches!(
        module.ty_layout_shape(clos),
        Err(LayoutError::ClosureLayoutTargetMissing)
    ));
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
}

/// The closure is INTRODUCED in `@program` and APPLIED in `@apply_twice`,
/// which receives it as a FUNCTION PARAMETER — the "trusted as declared"
/// flow the G18-2 enforcement note names, where no defining constant is
/// visible to the applying function.
fn build_closure_through_parameter() -> Module {
    let ValueCaptureSkeleton {
        mut mb,
        apparent,
        nullary,
        clos,
        bump,
    } = value_capture_skeleton("ws3_13_closure_through_parameter");
    let apply_sig = mb.add_func_type(vec![clos.clone()], vec![Ty::U64]);
    let apply_twice = {
        let mut fb = mb.function("apply_twice", apply_sig);
        let e = fb.create_block();
        let c = fb.add_block_param(e, clos.clone());
        fb.switch_to_block(e);
        let a = fb.call_indirect(c, apparent, vec![]);
        let b = fb.call_indirect(c, apparent, vec![]);
        report(&mut fb, a, b);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let c = fb.const_value(
            clos,
            Constant::Closure {
                func: bump,
                captures: vec![Constant::Int(0)],
            },
        );
        let r = fb.call(apply_twice, vec![c]);
        fb.ret(vec![r]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The closure is the RESULT of a direct `Call` to a factory (`@make`), so
/// the applying function's value type for the callee comes from the callee's
/// declared return type, not from any instruction operand.
fn build_closure_through_call_result() -> Module {
    let ValueCaptureSkeleton {
        mut mb,
        apparent,
        nullary,
        clos,
        bump,
    } = value_capture_skeleton("ws3_13_closure_through_call_result");
    let make_sig = mb.add_func_type(vec![], vec![clos.clone()]);
    let make = {
        let mut fb = mb.function("make", make_sig);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let c = fb.const_value(
            clos.clone(),
            Constant::Closure {
                func: bump,
                captures: vec![Constant::Int(0)],
            },
        );
        fb.ret(vec![c]);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let c = fb.call(make, vec![]);
        let a = fb.call_indirect(c, apparent, vec![]);
        let b = fb.call_indirect(c, apparent, vec![]);
        report(&mut fb, a, b);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The applied value is a `Select` between two closure literals, then a
/// `Copy` of that — the pseudo-instructions that forward a value unchanged.
fn build_closure_through_select_and_copy() -> Module {
    let ValueCaptureSkeleton {
        mut mb,
        apparent,
        nullary,
        clos,
        bump,
    } = value_capture_skeleton("ws3_13_closure_through_select_and_copy");
    {
        let mut fb = mb.function("program", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let seed0 = fb.const_value(
            clos.clone(),
            Constant::Closure {
                func: bump,
                captures: vec![Constant::Int(0)],
            },
        );
        let seed5 = fb.const_value(
            clos.clone(),
            Constant::Closure {
                func: bump,
                captures: vec![Constant::Int(5)],
            },
        );
        let t = fb.bool_const(true);
        let sel = fb.select(clos.clone(), t, seed0, seed5);
        let c = fb.copy(clos, sel);
        let a = fb.call_indirect(sel, apparent, vec![]);
        let b = fb.call_indirect(c, apparent, vec![]);
        report(&mut fb, a, b);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The closure is LOOP-CARRIED as a block parameter: `bb1(c, i, acc)` applies
/// `c` once per trip and passes the SAME register back around. A by-reference
/// application would let trip 1's write reach trip 2 through the carried
/// value; by value, every trip sees the seed.
fn build_closure_loop_carried() -> Module {
    let ValueCaptureSkeleton {
        mut mb,
        apparent,
        nullary,
        clos,
        bump,
    } = value_capture_skeleton("ws3_13_closure_loop_carried");
    {
        let mut fb = mb.function("program", nullary);
        let entry = fb.create_block();
        let header = fb.create_block();
        let exit = fb.create_block();
        let c = fb.add_block_param(header, clos.clone());
        let i = fb.add_block_param(header, Ty::U64);
        let acc = fb.add_block_param(header, Ty::U64);

        fb.switch_to_block(entry);
        let seed = fb.const_value(
            clos,
            Constant::Closure {
                func: bump,
                captures: vec![Constant::Int(0)],
            },
        );
        let zero = fb.uconst(Ty::U64, 0);
        fb.br(header, vec![seed, zero, zero]);

        fb.switch_to_block(header);
        // acc = acc * 10 + bump(); i += 1; loop while i < 2
        let r = fb.call_indirect(c, apparent, vec![]);
        let ten = fb.uconst(Ty::U64, 10);
        let acc10 = fb.mul(Ty::U64, acc, ten);
        let acc_next = fb.add(Ty::U64, acc10, r);
        let one = fb.uconst(Ty::U64, 1);
        let i_next = fb.add(Ty::U64, i, one);
        let two = fb.uconst(Ty::U64, 2);
        let again = fb.icmp(trust_ir::inst::ICmpOp::Ult, Ty::U64, i_next, two);
        fb.condbr(
            again,
            header,
            vec![c, i_next, acc_next],
            exit,
            vec![acc_next],
        );

        fb.switch_to_block(exit);
        let out = fb.add_block_param(exit, Ty::U64);
        fb.ret(vec![out]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Every routing form: still by value (returns `11`), and every application
/// is still refused by the NAMED reason — the value-type map that the refusal
/// reads covers parameters, call results, `Select`, `Copy` and loop-carried
/// block parameters, not only a `Const` in the applying function.
#[test]
fn by_value_and_refused_for_every_route_to_the_application_site() {
    // (route, module, applying function, STATIC application sites — the
    // loop-carried fixture applies ONE site twice, so it is refused once)
    let cases: [(&str, Module, &str, usize); 4] = [
        (
            "parameter",
            build_closure_through_parameter(),
            "apply_twice",
            2,
        ),
        (
            "call result",
            build_closure_through_call_result(),
            "program",
            2,
        ),
        (
            "select+copy",
            build_closure_through_select_and_copy(),
            "program",
            2,
        ),
        ("loop-carried", build_closure_loop_carried(), "program", 1),
    ];
    for (route, m, applying_fn, sites) in cases {
        assert_eq!(validate_module(&m), vec![], "{route}: structurally valid");
        assert_eq!(
            run_program(&m),
            11,
            "{route}: application is by value however the closure arrives"
        );
        let refusals = closure_callee_refusals(&m);
        assert_eq!(
            refusals.len(),
            sites,
            "{route}: one refusal per static application site: {refusals:?}"
        );
        let sited_in: Vec<&str> = codegen_lowerability_errors(&m)
            .iter()
            .filter_map(|e| match e {
                ValidationError::UnlowerableForCodegen { name, .. } => Some(name.as_str()),
                _ => None,
            })
            .map(|n| if n == applying_fn { "ok" } else { "other" })
            .collect();
        assert_eq!(
            sited_in,
            vec!["ok"; sites],
            "{route}: the refusal is sited in the APPLYING function {applying_fn}"
        );
        assert_eq!(
            codegen_lowerability_errors(&m).len(),
            sites,
            "{route}: introduction, projection, Select, Copy, Call and Br are not refused"
        );
    }
}

/// `Select` over two `Ty::Func` values through the same `CallIndirect` is
/// NOT refused: the routing forms above add refusals only because of the
/// callee's TYPE. A wrongly-refused legitimate module is the other failure
/// direction, and this pins it for the pseudo-instruction route.
#[test]
fn a_selected_ty_func_callee_is_not_refused() {
    let mut mb = ModuleBuilder::new("ws3_13_selected_func_callee");
    let bump_sig = mb.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let bump = {
        let mut fb = mb.function("bump", bump_sig);
        let e = fb.create_block();
        let env = fb.add_block_param(e, Ty::Ptr);
        fb.switch_to_block(e);
        let n = fb.load(Ty::U64, env);
        let one = fb.uconst(Ty::U64, 1);
        let n1 = fb.add(Ty::U64, n, one);
        fb.store(Ty::U64, env, n1);
        fb.ret(vec![n1]);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let env = fb.alloca(Ty::U64);
        let zero = fb.uconst(Ty::U64, 0);
        fb.store(Ty::U64, env, zero);
        let f1 = fb.fn_addr(bump_sig, bump);
        let f2 = fb.fn_addr(bump_sig, bump);
        let t = fb.bool_const(true);
        let sel = fb.select(Ty::Func(bump_sig), t, f1, f2);
        let f = fb.copy(Ty::Func(bump_sig), sel);
        let a = fb.call_indirect(sel, bump_sig, vec![env]);
        let b = fb.call_indirect(f, bump_sig, vec![env]);
        report(&mut fb, a, b);
        fb.build();
    }
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(codegen_lowerability_errors(&m), vec![]);
    assert_eq!(run_program(&m), 12);
}

/// A closure value that round-trips through MEMORY (`Alloca` at the closure
/// type, `Store`, `Load`) and is then applied. Without a declared frame the
/// layout and execution refuse. The same module with its genuine capture
/// frame round-trips the capture and applies it by value twice.
#[test]
fn a_closure_round_tripped_through_memory_is_still_refused_for_application() {
    let ValueCaptureSkeleton {
        mut mb,
        apparent,
        nullary,
        clos,
        bump,
    } = value_capture_skeleton("ws3_13_closure_through_memory");
    {
        let mut fb = mb.function("program", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let seed = fb.const_value(
            clos.clone(),
            Constant::Closure {
                func: bump,
                captures: vec![Constant::Int(0)],
            },
        );
        let slot = fb.alloca(clos.clone());
        fb.store(clos.clone(), slot, seed);
        let c = fb.load(clos.clone(), slot);
        let a = fb.call_indirect(c, apparent, vec![]);
        let b = fb.call_indirect(c, apparent, vec![]);
        report(&mut fb, a, b);
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let refusals = closure_callee_refusals(&m);
    assert_eq!(
        refusals.len(),
        2,
        "both applications of the loaded closure are refused: {refusals:?}"
    );
    assert!(matches!(
        m.ty_layout_shape(&clos),
        Err(LayoutError::UnsupportedTyShape(_))
    ));
    // Structural validity does not manufacture an absent byte layout.
    assert_eq!(
        validate_module(&m),
        vec![],
        "the memory ops are structurally valid"
    );
    let mut declared = m.clone();
    declared.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    declared
        .closure_layouts
        .push(trust_ir::ClosureLayoutDescriptor {
            origin: None,
            closure: ClosureTyId::new(0),
            size: 8,
            align: 8,
            capture_offsets: vec![0],
        });
    assert_eq!(validate_module(&declared), vec![]);
    assert_eq!(
        run_program(&declared),
        11,
        "memory preserves by-value capture semantics"
    );
    let func = m.function_by_name("program").unwrap();
    let Err(err) = Interpreter::with_module(&m).execute_func(func.id, []) else {
        panic!("an undeclared closure frame must fail closed");
    };
    assert_eq!(err.code, InterpretErrorCode::TypeError);
    assert_eq!(err.message, "missing closure layout");
    assert_eq!(err.block, Some(trust_ir::BlockId::new(0)));

    declare_value_capture_frame(&mut m, &clos);
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    let shape = m.ty_layout_shape(&clos).expect("the declared u64 frame");
    assert_eq!(shape.size_bits, 64);
    assert_eq!(shape.align_bits, Some(64));
    let Ty::Closure(id) = clos else {
        unreachable!()
    };
    assert_eq!(m.closure_storage_binding(id).unwrap().target, bump);
    assert!(closure_callee_refusals(&m).is_empty());
    assert!(codegen_lowerability_errors(&m).is_empty());
    assert_eq!(
        run_program(&m),
        11,
        "both loads retain the original capture"
    );
}

/// By-reference APPLICATION is not expressible. The draft design's spelling
/// — a callee typed `RefMut(Closure)` — CAN be declared (as a parameter), but
/// it is not a closure application and never becomes one: the
/// closure-application arm fires only on a callee typed `Ty::Closure` itself,
/// and the reference interpreter refuses every callee that is neither
/// `Ty::Func` nor `Ty::Closure` at run time. (The structural validator admits
/// the callee because it has NO callee-type rule outside the nominal-type
/// path — see `a_non_callable_callee_type_is_a_recorded_gap` — not because
/// of any rule about pointers.) So the value that arrives is never "the
/// caller's closure register by reference" — there is no such thing — and the
/// ruling's claim is pinned as the format actually behaves, not as the draft
/// assumed.
#[test]
fn a_ref_mut_closure_callee_is_not_a_closure_application() {
    let ValueCaptureSkeleton {
        mut mb,
        apparent,
        clos,
        ..
    } = value_capture_skeleton("ws3_13_ref_mut_closure_callee");
    let by_ref = Ty::RefMut(Box::new(clos));
    let apply_sig = mb.add_func_type(vec![by_ref.clone()], vec![Ty::U64]);
    let apply_by_ref = {
        let mut fb = mb.function("apply_by_ref", apply_sig);
        let e = fb.create_block();
        let c = fb.add_block_param(e, by_ref.clone());
        fb.switch_to_block(e);
        let r = fb.call_indirect(c, apparent, vec![]);
        fb.ret(vec![r]);
        fb.build()
    };
    // The only way to obtain a `RefMut(Closure)`-typed VALUE is to declare
    // one: a `Borrow` yields a thin `Ptr`, and a closure register has no
    // address to take. So `@apply_by_ref` is driven as the ENTRY, with a
    // null pointer of the declared type standing in for the caller's
    // "reference".
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    // Structurally: admitted — NOT as a closure application, so none of the
    // closure edge rules (`CallIndirectClosureSigMismatch` /
    // `CallIndirectClosureTargetMismatch`) and none of the
    // closure-application refusals apply to it.
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(
        closure_callee_refusals(&m),
        Vec::<String>::new(),
        "a RefMut(Closure) callee is not a Ty::Closure callee"
    );
    // Operationally: refused, never applied. A backend that admits the
    // callee jumps to the pointer's bits; the format gives it no
    // closure-application meaning either way.
    let fake_ref = trust_ir::interpret::InterpretValue {
        ty: by_ref,
        kind: trust_ir::interpret::InterpretValueKind::NullPtr,
    };
    let Err(err) = Interpreter::with_module(&m).execute_func(apply_by_ref, [fake_ref]) else {
        panic!("a pointer-like callee is refused at run time");
    };
    assert!(
        err.message.contains("non-function type"),
        "the refusal names the callee's non-function type: {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Second adversarial review (WS3.13): routes that go through an AGGREGATE or a
// GLOBAL rather than a register, the cast LAUNDERINGS that would turn a
// closure into a callee the closure arm cannot see, and the callee-type gap
// those launderings would have landed in.
// ---------------------------------------------------------------------------

/// The closure is a FIELD of a tuple constant and is projected out with
/// `ExtractField` before application — the `Ty::Closure` value's type comes
/// from the projection's declared result type, not from any closure literal.
fn build_closure_through_tuple_projection() -> Module {
    let ValueCaptureSkeleton {
        mut mb,
        apparent,
        nullary,
        clos,
        bump,
    } = value_capture_skeleton("ws3_13_closure_through_tuple_projection");
    let tuple = Ty::Tuple(vec![clos.clone(), Ty::U64]);
    {
        let mut fb = mb.function("program", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let t = fb.const_value(
            tuple,
            Constant::Aggregate(vec![
                Constant::Closure {
                    func: bump,
                    captures: vec![Constant::Int(0)],
                },
                Constant::Int(7),
            ]),
        );
        let c = fb.extract_field(clos, t, 0);
        let a = fb.call_indirect(c, apparent, vec![]);
        let b = fb.call_indirect(c, apparent, vec![]);
        report(&mut fb, a, b);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A closure nested in an aggregate is applied by value like any other, and
/// both applications are refused: `ExtractField` types its result, so the
/// value-type map the refusal reads sees the projected closure.
#[test]
fn a_closure_projected_out_of_an_aggregate_is_by_value_and_refused() {
    let m = build_closure_through_tuple_projection();
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(run_program(&m), 11, "by value through the aggregate");
    let refusals = closure_callee_refusals(&m);
    assert_eq!(refusals.len(), 2, "{refusals:?}");
    assert_eq!(
        codegen_lowerability_errors(&m).len(),
        2,
        "the tuple Const and the ExtractField are not refused"
    );
}

/// A closure that lives in a GLOBAL's initializer and is `Load`ed through
/// `GlobalAddr`: an absent frame fails closed, and the genuine declared frame
/// transports the capture without making application mutate global storage.
#[test]
fn a_closure_in_a_global_initializer_is_refused_and_fails_closed() {
    let ValueCaptureSkeleton {
        mut mb,
        apparent,
        nullary,
        clos,
        bump,
    } = value_capture_skeleton("ws3_13_closure_in_global");
    mb.add_global(trust_ir::Global {
        name: "CLOSURE_STATIC".into(),
        ty: clos.clone(),
        mutable: true,
        initializer: Some(Constant::Closure {
            func: bump,
            captures: vec![Constant::Int(0)],
        }),
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    {
        let mut fb = mb.function("program", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let g = fb.global_addr(trust_ir::value::GlobalId::new(0));
        let c = fb.load(clos.clone(), g);
        let a = fb.call_indirect(c, apparent, vec![]);
        let b = fb.call_indirect(c, apparent, vec![]);
        report(&mut fb, a, b);
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(closure_callee_refusals(&m).len(), 2);
    let mut declared = m.clone();
    declared.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    declared
        .closure_layouts
        .push(trust_ir::ClosureLayoutDescriptor {
            origin: None,
            closure: ClosureTyId::new(0),
            size: 8,
            align: 8,
            capture_offsets: vec![0],
        });
    assert_eq!(validate_module(&declared), vec![]);
    assert_eq!(
        run_program(&declared),
        11,
        "memory preserves by-value capture semantics"
    );
    let func = m.function_by_name("program").unwrap();
    let Err(err) = Interpreter::with_module(&m).execute_func(func.id, []) else {
        panic!("an undeclared global closure frame must fail closed");
    };
    assert_eq!(err.code, InterpretErrorCode::TypeError);
    assert_eq!(err.message, "missing closure layout");
    assert_eq!(err.block, Some(trust_ir::BlockId::new(0)));

    declare_value_capture_frame(&mut m, &clos);
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    let Ty::Closure(id) = clos else {
        unreachable!()
    };
    assert_eq!(m.closure_storage_binding(id).unwrap().target, bump);
    assert!(closure_callee_refusals(&m).is_empty());
    assert!(codegen_lowerability_errors(&m).is_empty());
    assert_eq!(
        run_program(&m),
        11,
        "the global's capture is passed by value"
    );
}

/// LAUNDERING: cast the closure to a pointer (or an integer) and apply THAT
/// through `CallIndirect`. The callee is then not `Ty::Closure`, so the
/// closure arm cannot fire, and a backend would jump to the capture's bits.
/// Every spelling is refused STRUCTURALLY, before codegen, and by the reason
/// this increment is about — the closure has no layout to cast through.
/// The wire half (`Module.closure_layouts`) must keep this true: a declared
/// layout gives the closure a SIZE, and a width-equality cast rule must not
/// then admit `Bitcast closure -> ptr` as a way past the application refusal.
#[test]
fn casting_a_closure_to_a_callable_type_is_refused_structurally() {
    use trust_ir::inst::CastOp;
    for (op, dst) in [
        (CastOp::Bitcast, Ty::Ptr),
        (CastOp::Transmute, Ty::Ptr),
        (CastOp::PtrToPtr, Ty::Ptr),
        (CastOp::Transmute, Ty::U64),
    ] {
        let ValueCaptureSkeleton {
            mut mb,
            nullary,
            clos,
            bump,
            ..
        } = value_capture_skeleton("ws3_13_closure_cast_laundering");
        // The PHYSICAL signature, so the laundered call would even look
        // arity-correct to a backend that took the bits as a code address.
        let physical = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        {
            let mut fb = mb.function("program", nullary);
            let e = fb.create_block();
            fb.switch_to_block(e);
            let c = fb.const_value(
                clos.clone(),
                Constant::Closure {
                    func: bump,
                    captures: vec![Constant::Int(0)],
                },
            );
            let laundered = fb.cast(op, clos.clone(), dst.clone(), c);
            let zero = fb.uconst(Ty::U64, 0);
            let r = fb.call_indirect(laundered, physical, vec![zero]);
            fb.ret(vec![r]);
            fb.build();
        }
        let m = mb.build().expect("ModuleBuilder::build: test fixture");
        let errors = validate_module(&m);
        assert!(
            errors.iter().any(|e| matches!(
                e,
                ValidationError::CastLayoutUnsupported { src, .. } if src.starts_with("closure.")
            )),
            "{op:?} closure -> {dst}: must be refused as a cast the closure's \
             (absent) layout cannot support, got {errors:?}"
        );
        assert_eq!(
            closure_callee_refusals(&m),
            Vec::<String>::new(),
            "{op:?}: the laundered callee is NOT a Ty::Closure, so the closure \
             arm is silent — which is exactly why the cast itself must be refused"
        );
        // And the interpreter never reaches the call either.
        let func = m.function_by_name("program").unwrap();
        assert!(
            Interpreter::with_module(&m)
                .execute_func(func.id, [])
                .is_err(),
            "{op:?}: refused at run time"
        );
    }
}

/// RECORDED GAP (not a rule, and not this increment's): the structural
/// validator has no callee-TYPE rule for `CallIndirect` outside the
/// nominal-type path. A callee typed `U64` is admitted by `validate_module`
/// and is not refused by `codegen_lowerability_errors` (whose closure arm is
/// silent on a non-closure callee, correctly); only the reference interpreter
/// refuses it, at run time, as a non-function type. This pins today's
/// behavior so that (a) the `RefMut(Closure)` admission above is read as this
/// gap and not as a pointer rule, and (b) the fix — a structural refusal for
/// every callee that is neither `Ty::Func`, `Ty::Closure` nor pointer-like —
/// has to change this test deliberately.
#[test]
fn a_non_callable_callee_type_is_a_recorded_gap() {
    let ValueCaptureSkeleton {
        mut mb,
        apparent,
        nullary,
        ..
    } = value_capture_skeleton("ws3_13_non_callable_callee");
    {
        let mut fb = mb.function("program", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let not_a_function = fb.uconst(Ty::U64, 0x1234);
        let r = fb.call_indirect(not_a_function, apparent, vec![]);
        fb.ret(vec![r]);
        fb.build();
    }
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(
        validate_module(&m),
        vec![],
        "recorded: no structural callee-type rule for a non-nominal callee"
    );
    assert_eq!(
        codegen_lowerability_errors(&m),
        vec![],
        "recorded: the closure arm is (correctly) silent, and nothing else looks"
    );
    let func = m.function_by_name("program").unwrap();
    let Err(err) = Interpreter::with_module(&m).execute_func(func.id, []) else {
        panic!("the interpreter refuses a non-function callee");
    };
    assert!(
        err.message.contains("non-function type"),
        "the only refusal is the interpreter's: {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Validated dynamic closure convention controls. These use G18-2's existing
// capture-spread contract; the apparent signature has no explicit parameters,
// and the physical target receives the one U64 capture by value.
// ---------------------------------------------------------------------------

fn build_validated_dynamic_closure_convention_parameter(
    edge: trust_ir::CallingConv,
) -> (Module, trust_ir::FuncId) {
    use trust_ir::CallingConv;

    let mut mb = ModuleBuilder::new_with_target_info(
        "dynamic_closure_convention_parameter",
        trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
        },
    );
    let apparent = mb.add_func_type(vec![], vec![Ty::U64]);
    let physical = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let closure_id = mb.add_closure_type(ClosureTy {
        func: apparent,
        captures: vec![Ty::U64],
    });
    let closure_ty = Ty::Closure(closure_id);
    let maker_sig = mb.add_func_type(vec![], vec![closure_ty.clone()]);
    let consumer_sig = mb.add_func_type(vec![closure_ty.clone()], vec![Ty::U64]);

    let target = {
        let mut fb = mb.function("captured_c_target", physical);
        fb.set_calling_conv(CallingConv::C);
        let entry = fb.create_block();
        let capture = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let two = fb.uconst(Ty::U64, 2);
        let answer = fb.add(Ty::U64, capture, two);
        fb.ret(vec![answer]);
        fb.build()
    };
    let maker = {
        let mut fb = mb.function("make_captured_closure", maker_sig);
        fb.set_calling_conv(CallingConv::C);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let seed = fb.const_value(
            closure_ty.clone(),
            Constant::Closure {
                func: target,
                captures: vec![Constant::Int(0)],
            },
        );
        let forty = fb.uconst(Ty::U64, 40);
        let written = fb.insert_field(closure_ty.clone(), seed, 0, forty);
        // Returning the seed instead would produce 2, not the required 42.
        fb.ret(vec![written]);
        fb.build()
    };
    let consumer = {
        let mut fb = mb.function("apply_closure_parameter", consumer_sig);
        fb.set_calling_conv(CallingConv::C);
        let entry = fb.create_block();
        let closure = fb.add_block_param(entry, closure_ty.clone());
        fb.switch_to_block(entry);
        // This callee is a typed closure SSA parameter, not a statically
        // visible closure constant or an ordinary Ty::Func pointer.
        let answer = fb.call_indirect_cc(closure, apparent, vec![], edge);
        fb.ret(vec![answer]);
        fb.build()
    };
    let program = {
        let mut fb = mb.function("program", apparent);
        fb.set_calling_conv(CallingConv::C);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let made = fb.call(maker, vec![]);
        let answer = fb.call(consumer, vec![made]);
        fb.ret(vec![answer]);
        fb.build()
    };
    let module = mb.build().expect("dynamic closure convention fixture");
    let errors = validate_module(&module);
    eprintln!(
        "[DYNAMIC_CLOSURE_CONVENTION_VALIDATION] edge={edge:?} target={target} \
         program={program} errors={errors:#?} module={module:#?}"
    );
    assert!(
        errors.is_empty(),
        "this control has not established module admission: {errors:#?}"
    );
    assert_eq!(module.closure_type(closure_id).unwrap().func, apparent);
    assert_eq!(
        module.closure_type(closure_id).unwrap().captures,
        vec![Ty::U64]
    );
    assert_eq!(module.function_by_id(target).unwrap().ty, physical);
    assert_eq!(module.func_type(physical).unwrap().params, vec![Ty::U64]);
    assert_eq!(module.func_type(physical).unwrap().returns, vec![Ty::U64]);
    assert!(
        module
            .func_types
            .iter()
            .all(|sig| sig.abi.is_none() && !sig.is_vararg)
    );
    assert!(module.functions.iter().all(|function| {
        function.calling_conv == CallingConv::C && function.body_gate.is_none()
    }));
    (module, program)
}

#[test]
fn dynamic_closure_parameter_matching_c_convention_preserves_capture_return() {
    let (module, program) =
        build_validated_dynamic_closure_convention_parameter(trust_ir::CallingConv::C);
    let result = Interpreter::with_module(&module).execute_func(program, []);
    eprintln!("[DYNAMIC_CLOSURE_CONVENTION_RESULT] edge=C result={result:#?}");
    let outcome = result.expect("matching C edge and C closure target must execute");
    assert_eq!(outcome.returns.len(), 1);
    assert_eq!(outcome.returns[0].ty, Ty::U64);
    assert_eq!(outcome.returns[0].as_int().unwrap().as_unsigned(), 42);
}

#[test]
fn dynamic_closure_parameter_rejects_rust_edge_to_c_target() {
    let (module, program) =
        build_validated_dynamic_closure_convention_parameter(trust_ir::CallingConv::Rust);
    let result = Interpreter::with_module(&module).execute_func(program, []);
    eprintln!("[DYNAMIC_CLOSURE_CONVENTION_RESULT] edge=Rust result={result:#?}");
    let error = result.expect_err(
        "a validated dynamic closure call must reject a Rust edge to its C physical target",
    );
    assert_eq!(error.code, InterpretErrorCode::SignatureMismatch);
}
