// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! One spelling of a switch case (`docs/SPEC_RATIFICATIONS.md` §3.3): a case
//! literal at an integer (or `char`) selector is a constant OF THE SELECTOR'S
//! TYPE, checked exactly as its `Inst::Const` twin is — through the one
//! constant funnel, refused as `ValidationError::ConstTypeMismatch`.
//!
//! Until 2026-09-30 the validator never typed a case literal, so `switch u8
//! [ -1: .. ]` and `switch i8 [ 255: .. ]` both validated while `const u8 -1`
//! was refused: a second spelling of every case whose selector type has a
//! sign, which the reference interpreter wrapped (`constant_to_value` at the
//! selector's type) and the Lean model compared as a residue. Both spellings
//! are now one error, and so is every other literal the `Const` twin refuses.
//!
//! A pointer-width integer (`isize` / `usize`) has the width of the module's
//! target pointer (`Module::pointer_bits`: `target_info.pointer_size * 8`, and
//! the documented 64-bit default for a target-free module), so its constants,
//! and the cases of a switch on one, are checked at THAT width. Until
//! 2026-10-01 the funnel checked them at 64 bits on every target, so on wasm32
//! `0` and `2^32` were both admitted `usize` constants and both admitted cases
//! of one switch — one selector value, which the reference interpreter (whose
//! `usize` is 32 bits there) wraps to one, so the second arm was dead.

use trust_ir::constant::Constant;
use trust_ir::inst::SwitchCase;
use trust_ir::ty::{DEFAULT_POINTER_BITS, Ty};
use trust_ir::{Endianness, Global, Linkage, Module, StructPassingPolicy, TargetInfo};
use trust_ir_build::ModuleBuilder;
use trust_ir_build::validate::ValidationError;

/// `f(x: ty) -> i32 { switch x [ case: 10 ] default: 20 }`, one function per
/// `(ty, case)`.
fn switch_module(cells: &[(Ty, Constant)]) -> Module {
    let mut mb = ModuleBuilder::new("switch_case_range");
    for (i, (ty, case)) in cells.iter().enumerate() {
        let ft = mb.add_func_type(vec![ty.clone()], vec![Ty::I32]);
        let mut fb = mb.function(format!("f{i}"), ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, ty.clone());
        let hit = fb.create_block();
        let miss = fb.create_block();
        fb.switch_to_block(entry);
        fb.switch(
            x,
            vec![SwitchCase {
                value: case.clone(),
                target: hit,
                args: vec![],
            }],
            miss,
            vec![],
        );
        for (block, value) in [(hit, 10), (miss, 20)] {
            fb.switch_to_block(block);
            let r = fb.iconst(Ty::I32, value);
            fb.ret(vec![r]);
        }
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `f() -> ty { const ty <value> }`: the `Inst::Const` twin of a case.
fn const_module(ty: &Ty, value: Constant) -> Module {
    let mut mb = ModuleBuilder::new("const_range_twin");
    let ft = mb.add_func_type(vec![], vec![ty.clone()]);
    let mut fb = mb.function("c", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let c = fb.const_value(ty.clone(), value);
    fb.ret(vec![c]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The `(expected, actual)` of every `ConstTypeMismatch` in `errors`, or a
/// panic naming the first error of any other variant: the case literal is the
/// only thing under test, so nothing else may be refused.
fn const_type_mismatches(what: &str, errors: &[ValidationError]) -> Vec<(String, String)> {
    errors
        .iter()
        .map(|e| match e {
            ValidationError::ConstTypeMismatch {
                expected, actual, ..
            } => (expected.clone(), actual.clone()),
            other => panic!("{what}: only the literal is refused, got {other:?} in {errors:?}"),
        })
        .collect()
}

/// The two spellings the validator used to accept — a negative case at an
/// unsigned selector and a case above the signed maximum — and every other
/// literal its `Inst::Const` twin refuses (out of range, a surrogate `char`,
/// a non-canonical `Constant::U128`, a non-integer) earn EXACTLY the twin's
/// refusals, located at the case.
#[test]
fn out_of_range_switch_case_literals_are_refused_like_constants() {
    let cells = [
        (Ty::U8, Constant::Int(-1)),
        (Ty::I8, Constant::Int(255)),
        (Ty::I8, Constant::Int(-129)),
        (Ty::U16, Constant::Int(1 << 16)),
        (Ty::I32, Constant::Int(1 << 31)),
        (Ty::U32, Constant::Int(1 << 32)),
        (Ty::U64, Constant::Int(-1)),
        (Ty::I64, Constant::Int(1 << 63)),
        (Ty::Usize, Constant::Int(-1)),
        (Ty::Isize, Constant::Int(1 << 63)),
        (Ty::Char, Constant::Int(0xD800)),
        (Ty::Char, Constant::Int(-1)),
        (Ty::U128, Constant::U128(5)),
        (Ty::I32, Constant::Bool(true)),
    ];
    for (ty, case) in &cells {
        let what = format!("switch {ty} [{case}]");
        let errors = trust_ir_build::validate_module(&switch_module(&[(ty.clone(), case.clone())]));
        let refusals = const_type_mismatches(&what, &errors);
        assert!(!refusals.is_empty(), "{what}: the case literal is refused");
        for e in &errors {
            let ValidationError::ConstTypeMismatch { location, .. } = e else {
                unreachable!("checked above");
            };
            assert!(
                location.contains("switch case 0"),
                "{what}: the refusal names the case: {location}"
            );
        }
        let twin = trust_ir_build::validate_module(&const_module(ty, case.clone()));
        assert_eq!(
            refusals,
            const_type_mismatches(&format!("const {ty} {case}"), &twin),
            "{what}: the case earns exactly its Inst::Const twin's refusals"
        );
    }
}

/// Every in-range spelling still validates, at both ends of every range: a
/// signed selector's case is its signed value (`switch i8 [ -1: .. ]`), an
/// unsigned selector's its unsigned value (`switch u8 [ 255: .. ]`), and a
/// `u128` case above `i128::MAX` is the canonical `Constant::U128`.
#[test]
fn in_range_switch_case_literals_validate() {
    let cells = [
        (Ty::I8, Constant::Int(-1)),
        (Ty::I8, Constant::Int(-128)),
        (Ty::I8, Constant::Int(127)),
        (Ty::U8, Constant::Int(0)),
        (Ty::U8, Constant::Int(255)),
        (Ty::I16, Constant::Int(i128::from(i16::MIN))),
        (Ty::U16, Constant::Int(i128::from(u16::MAX))),
        (Ty::I32, Constant::Int(i128::from(i32::MIN))),
        (Ty::U32, Constant::Int(i128::from(u32::MAX))),
        (Ty::I64, Constant::Int(i128::from(i64::MIN))),
        (Ty::U64, Constant::Int(i128::from(u64::MAX))),
        (Ty::I128, Constant::Int(i128::MIN)),
        (Ty::I128, Constant::Int(i128::MAX)),
        (Ty::U128, Constant::Int(i128::MAX)),
        (Ty::U128, Constant::u128(u128::MAX)),
        (Ty::Isize, Constant::Int(i128::from(i64::MIN))),
        (Ty::Usize, Constant::Int(i128::from(u64::MAX))),
        (Ty::Char, Constant::Int(i128::from(u32::from('a')))),
        (Ty::Char, Constant::Int(0x10FFFF)),
        // A bool selector is outside the rule's instance and keeps the checks
        // it had: its `Constant::Bool` cases validate as before.
        (Ty::Bool, Constant::Bool(true)),
    ];
    let errors = trust_ir_build::validate_module(&switch_module(&cells));
    assert!(
        errors.is_empty(),
        "every in-range case validates: {errors:?}"
    );
}

/// The case is checked at the selector's type wherever the selector comes
/// from: a block parameter (above), an instruction result and a call result.
#[test]
fn the_scrutinee_type_is_read_from_every_definition() {
    let mut mb = ModuleBuilder::new("switch_case_range_sources");
    let id_ft = mb.add_func_type(vec![Ty::U8], vec![Ty::U8]);
    let mut fb = mb.function("id", id_ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U8);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    let id = fb.build();
    let ft = mb.add_func_type(vec![Ty::U8], vec![Ty::I32]);
    for source in ["op_result", "call_result"] {
        let mut fb = mb.function(source, ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U8);
        let hit = fb.create_block();
        let miss = fb.create_block();
        fb.switch_to_block(entry);
        let scrutinee = if source == "op_result" {
            let one = fb.iconst(Ty::U8, 1);
            fb.add(Ty::U8, x, one)
        } else {
            fb.call(id, vec![x])
        };
        fb.switch(
            scrutinee,
            vec![SwitchCase {
                value: Constant::Int(-1),
                target: hit,
                args: vec![],
            }],
            miss,
            vec![],
        );
        for (block, value) in [(hit, 10), (miss, 20)] {
            fb.switch_to_block(block);
            let r = fb.iconst(Ty::I32, value);
            fb.ret(vec![r]);
        }
        fb.build();
    }
    let errors =
        trust_ir_build::validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
    let refusals = const_type_mismatches("u8 selector sources", &errors);
    assert_eq!(
        refusals.len(),
        2,
        "the -1 case at a u8 operation result and at a u8 call result: {errors:?}"
    );
}

/// A refinement selector has exactly its base's representation
/// (`Module::representation_ty`), so its case is a constant of the BASE type:
/// at `refine<u8, ..>` and `refine<i8, ..>` a case is refused exactly as its
/// `Inst::Const` twin at the base is (`const u8 -1`, `const u8 256`,
/// `const i8 255`), while every in-range base value validates. The twin AT the
/// refinement is refused for every value (a constant cannot carry a
/// refinement), so the base's twin is the one a refined case is held to. The
/// predicate does not narrow the case: a base value outside it is an arm the
/// refinement makes dead, not a second spelling.
#[test]
fn a_refinement_selectors_cases_are_constants_of_its_base_type() {
    for (base, lo, hi, refused, admitted) in [
        (Ty::U8, 0, 255, vec![-1, 256], vec![0, 3, 255]),
        (Ty::I8, -10, 10, vec![255, -129], vec![-1, -128, 127]),
    ] {
        let mut mb = ModuleBuilder::new("switch_case_range_refine");
        let pred = mb
            .intern_pred(trust_ir::Pred::Interval { lo, hi })
            .expect("a well-formed interval");
        let selector = mb.refine_ty(base.clone(), pred);
        let mut cells = Vec::new();
        for (i, case) in refused.iter().chain(&admitted).enumerate() {
            let ft = mb.add_func_type(vec![selector.clone()], vec![Ty::I32]);
            let mut fb = mb.function(format!("f{i}"), ft);
            let entry = fb.create_block();
            let x = fb.add_block_param(entry, selector.clone());
            let hit = fb.create_block();
            let miss = fb.create_block();
            fb.switch_to_block(entry);
            fb.switch(
                x,
                vec![SwitchCase {
                    value: Constant::Int(*case),
                    target: hit,
                    args: vec![],
                }],
                miss,
                vec![],
            );
            for (block, value) in [(hit, 10), (miss, 20)] {
                fb.switch_to_block(block);
                let r = fb.iconst(Ty::I32, value);
                fb.ret(vec![r]);
            }
            fb.build();
            cells.push((format!("function 'f{i}'"), *case));
        }
        let what = format!("switch {selector} (base {base})");
        let errors = trust_ir_build::validate_module(
            &mb.build().expect("ModuleBuilder::build: test fixture"),
        );
        // Only a literal is refused (any other variant panics here).
        const_type_mismatches(&what, &errors);
        for (function, case) in &cells {
            let at_case: Vec<&ValidationError> = errors
                .iter()
                .filter(|e| {
                    matches!(e, ValidationError::ConstTypeMismatch { location, .. }
                        if location.starts_with(function.as_str())
                            && location.contains("switch case 0"))
                })
                .collect();
            if refused.contains(case) {
                let twin =
                    trust_ir_build::validate_module(&const_module(&base, Constant::Int(*case)));
                assert_eq!(
                    at_case.len(),
                    const_type_mismatches(&format!("const {base} {case}"), &twin).len(),
                    "{what} [{case}]: refused exactly as its base twin: {errors:?}"
                );
                assert!(!at_case.is_empty(), "{what} [{case}] is refused");
            } else {
                assert!(at_case.is_empty(), "{what} [{case}] validates: {errors:?}");
            }
        }
    }
}

/// `module` on a target whose thin pointers are `pointer_size` bytes.
fn on_target(mut module: Module, target: Option<(&str, u32)>) -> Module {
    module.target_info = target.map(|(triple, pointer_size)| TargetInfo {
        triple: triple.into(),
        pointer_size,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    module
}

/// The targets a pointer-width integer is checked on, each with the width it
/// must be checked at: a 16-, a 32- and a 64-bit target, and the target-free
/// module, whose width is the documented default (`DEFAULT_POINTER_BITS`).
fn pointer_width_targets() -> [(Option<(&'static str, u32)>, u32); 4] {
    [
        (Some(("avr-unknown-gnu-atmega328", 2)), 16),
        (Some(("wasm32-unknown-unknown", 4)), 32),
        (Some(("aarch64-apple-darwin", 8)), 64),
        (None, DEFAULT_POINTER_BITS),
    ]
}

/// A pointer-width literal: its selector type and its value.
type PointerWidthCell = (Ty, i128);

/// The refused and the admitted pointer-width literals at `bits`: one past
/// each end of `usize` and `isize`, and each end itself.
fn pointer_width_cells(bits: u32) -> (Vec<PointerWidthCell>, Vec<PointerWidthCell>) {
    let half = 1i128 << (bits - 1);
    let full = 1i128 << bits;
    let refused = vec![
        (Ty::Usize, full),
        (Ty::Usize, -1),
        (Ty::Isize, half),
        (Ty::Isize, -half - 1),
    ];
    let admitted = vec![
        (Ty::Usize, 0),
        (Ty::Usize, full - 1),
        (Ty::Isize, -half),
        (Ty::Isize, half - 1),
    ];
    (refused, admitted)
}

/// A `usize` / `isize` case is a constant of its selector's type ON THE
/// MODULE'S TARGET: at a 16-, 32- and 64-bit target and at the target-free
/// default, a literal one past either end of the range is refused exactly as
/// its `Inst::Const` twin on the same target is, located at the case, and
/// both ends validate. On wasm32 this is the alias `switch usize [ 0, 2^32 ]`:
/// one selector value, two arms.
#[test]
fn pointer_width_case_literals_are_checked_at_the_target_pointer_width() {
    for (target, bits) in pointer_width_targets() {
        let (refused, admitted) = pointer_width_cells(bits);
        for (ty, value) in &refused {
            let case = Constant::Int(*value);
            let what = format!("switch {ty} [{value}] on {target:?} ({bits}-bit pointers)");
            let errors = trust_ir_build::validate_module(&on_target(
                switch_module(&[(ty.clone(), case.clone())]),
                target,
            ));
            let refusals = const_type_mismatches(&what, &errors);
            assert!(!refusals.is_empty(), "{what}: the case literal is refused");
            for e in &errors {
                let ValidationError::ConstTypeMismatch { location, .. } = e else {
                    unreachable!("checked above");
                };
                assert!(
                    location.contains("switch case 0"),
                    "{what}: the refusal names the case: {location}"
                );
            }
            let twin = trust_ir_build::validate_module(&on_target(const_module(ty, case), target));
            assert_eq!(
                refusals,
                const_type_mismatches(&format!("const {ty} {value} on {target:?}"), &twin),
                "{what}: the case earns exactly its Inst::Const twin's refusals"
            );
        }
        let cells: Vec<(Ty, Constant)> = admitted
            .iter()
            .map(|(ty, value)| (ty.clone(), Constant::Int(*value)))
            .collect();
        let errors = trust_ir_build::validate_module(&on_target(switch_module(&cells), target));
        assert!(
            errors.is_empty(),
            "every in-range pointer-width case validates on {target:?}: {errors:?}"
        );
        for (ty, value) in &cells {
            let errors = trust_ir_build::validate_module(&on_target(
                const_module(ty, value.clone()),
                target,
            ));
            assert!(
                errors.is_empty(),
                "const {ty} {value} validates on {target:?}: {errors:?}"
            );
        }
    }
}

/// The one funnel holds every constant site to the target width, not only a
/// case: an `Inst::Const`, a lane of an aggregate constant and a global
/// initializer. On wasm32 each `2^32` is refused where it stands; `2^32 - 1`
/// validates at every site.
#[test]
fn pointer_width_constants_are_checked_at_the_target_width_at_every_site() {
    let wasm32 = Some(("wasm32-unknown-unknown", 4));
    let pair = Ty::Tuple(vec![Ty::Usize, Ty::I32]);
    for (value, refused) in [(1i128 << 32, true), ((1i128 << 32) - 1, false)] {
        // An aggregate lane.
        let lane = const_module(
            &pair,
            Constant::Aggregate(vec![Constant::Int(value), Constant::Int(0)]),
        );
        let errors = trust_ir_build::validate_module(&on_target(lane, wasm32));
        let at_lane = const_type_mismatches("a usize lane", &errors);
        assert_eq!(
            at_lane.len(),
            usize::from(refused),
            "the usize lane {value} of a tuple constant on wasm32: {errors:?}"
        );
        if refused {
            assert!(
                errors.iter().all(|e| matches!(e,
                    ValidationError::ConstTypeMismatch { location, .. } if location.ends_with("[0]"))),
                "the refusal names the lane: {errors:?}"
            );
        }
        // A global initializer.
        let mut module = Module::new("usize_global");
        module.globals.push(Global {
            name: "LEN".into(),
            ty: Ty::Usize,
            mutable: false,
            initializer: Some(Constant::Int(value)),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        let errors = trust_ir_build::validate_module(&on_target(module, wasm32));
        let at_global = const_type_mismatches("a usize global", &errors);
        assert_eq!(
            at_global.len(),
            usize::from(refused),
            "the usize global initializer {value} on wasm32: {errors:?}"
        );
    }
}

/// A refinement of a pointer-width integer has its base's representation,
/// and so its base's width on the module's target: `switch refine<usize, ..>`
/// on wasm32 refuses the case `2^32` exactly as `const usize 2^32` is refused
/// there, and admits `2^32 - 1`.
#[test]
fn a_refined_pointer_width_selector_is_checked_at_the_target_width() {
    let wasm32 = Some(("wasm32-unknown-unknown", 4));
    for (case, refused) in [(1i128 << 32, true), ((1i128 << 32) - 1, false)] {
        let mut mb = ModuleBuilder::new("switch_case_range_refined_usize");
        let pred = mb
            .intern_pred(trust_ir::Pred::Interval { lo: 0, hi: 10 })
            .expect("a well-formed interval");
        let selector = mb.refine_ty(Ty::Usize, pred);
        let ft = mb.add_func_type(vec![selector.clone()], vec![Ty::I32]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, selector.clone());
        let hit = fb.create_block();
        let miss = fb.create_block();
        fb.switch_to_block(entry);
        fb.switch(
            x,
            vec![SwitchCase {
                value: Constant::Int(case),
                target: hit,
                args: vec![],
            }],
            miss,
            vec![],
        );
        for (block, value) in [(hit, 10), (miss, 20)] {
            fb.switch_to_block(block);
            let r = fb.iconst(Ty::I32, value);
            fb.ret(vec![r]);
        }
        fb.build();
        let what = format!("switch {selector} [{case}] on wasm32");
        let errors = trust_ir_build::validate_module(&on_target(
            mb.build().expect("ModuleBuilder::build: test fixture"),
            wasm32,
        ));
        let refusals = const_type_mismatches(&what, &errors);
        let twin = trust_ir_build::validate_module(&on_target(
            const_module(&Ty::Usize, Constant::Int(case)),
            wasm32,
        ));
        assert_eq!(
            refusals,
            const_type_mismatches(&format!("const usize {case} on wasm32"), &twin),
            "{what}: held to its base's twin on the same target"
        );
        assert_eq!(refusals.is_empty(), !refused, "{what}: {errors:?}");
    }
}
