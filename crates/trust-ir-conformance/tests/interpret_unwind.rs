// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Amendment D, Part 2 (`docs/SPEC_RATIFICATIONS.md` §21): unwinding is an
// exit, in the reference interpreter. Every cell of the shared unwind matrix
// (`common/unwind_matrix.rs`) runs under `PanicStrategy::Abort` (the
// default: the panic=abort projection of `docs/ub-numerics-policy.md` §4) and
// under `PanicStrategy::Unwind`, against its decided verdict; the Lean half of
// the same matrix is `lean_exec_differential.rs`
// (`unwind_paths_agree_message_for_message`).
//
// The prefix law (§21 rule 7) is held over the whole golden corpus too
// (`abort_run_is_a_prefix_of_the_unwind_run`): wherever the Abort run returns,
// is undefined behaviour, or runs out of fuel, the Unwind run does EXACTLY the
// same; only a panic or a refused pad / resume may differ.

use std::fs;
use std::path::PathBuf;

use trust_ir::interpret::{
    InterpretError, InterpretErrorCode, InterpretOptions, InterpretOutcome, InterpretValue,
    Interpreter, PanicStrategy,
};
use trust_ir::value::FuncId;
use trust_ir::{Module, Ty};

mod common;
use common::unwind_matrix::{CELLS, Cell, Expect};

fn run(
    module: &Module,
    f: FuncId,
    strategy: PanicStrategy,
) -> Result<InterpretOutcome, InterpretError> {
    Interpreter::with_module(module)
        .with_options(InterpretOptions {
            panic_strategy: strategy,
            ..InterpretOptions::default()
        })
        .execute_func(f, Vec::<InterpretValue>::new())
}

fn check(
    cell: &Cell,
    expect: Expect,
    result: &Result<InterpretOutcome, InterpretError>,
    strategy: PanicStrategy,
) {
    let what = format!("{} under {strategy:?}", cell.name);
    match (expect, result) {
        (Expect::Ok(v), Ok(outcome)) => {
            assert_eq!(
                outcome.returns[0].as_int().expect("i64").as_signed(),
                i128::from(v),
                "{what}"
            );
        }
        (Expect::Panic { sited }, Err(error)) => {
            assert_eq!(error.code, InterpretErrorCode::Panic, "{what}: {error}");
            assert_eq!(error.message, "attempt to divide by zero", "{what}");
            let panic = error.panic().expect("a structured panic");
            assert_eq!(panic.site.is_some(), sited, "{what}: {panic:?}");
        }
        (Expect::Ub, Err(error)) => {
            assert_eq!(
                error.code,
                InterpretErrorCode::UndefinedBehavior,
                "{what}: {error}"
            );
        }
        (Expect::Unsupported, Err(error)) => {
            assert_eq!(
                error.code,
                InterpretErrorCode::UnsupportedInstruction,
                "{what}: {error}"
            );
        }
        (expect, result) => panic!("{what}: expected {expect:?}, got {result:?}"),
    }
}

fn matrix() -> (Module, Vec<FuncId>) {
    let (module, ids) = common::unwind_matrix::module();
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "the matrix validates: {errors:?}");
    (module, ids)
}

fn cell(name: &str) -> (Module, FuncId, &'static Cell) {
    let (module, ids) = matrix();
    let at = CELLS
        .iter()
        .position(|c| c.name == name)
        .unwrap_or_else(|| panic!("no cell {name}"));
    (module, ids[at], &CELLS[at])
}

/// Run one cell under both strategies against its decided verdicts.
fn decided(name: &str) {
    let (module, f, cell) = cell(name);
    check(
        cell,
        cell.abort,
        &run(&module, f, PanicStrategy::Abort),
        PanicStrategy::Abort,
    );
    check(
        cell,
        cell.unwind,
        &run(&module, f, PanicStrategy::Unwind),
        PanicStrategy::Unwind,
    );
}

#[test]
fn the_default_strategy_is_abort() {
    assert_eq!(
        InterpretOptions::default().panic_strategy,
        PanicStrategy::Abort
    );
    assert_eq!(PanicStrategy::default(), PanicStrategy::Abort);
}

#[test]
fn a_plain_call_propagates_the_unwinding_out_of_its_frame() {
    decided("plain_call_unwinds");
}

#[test]
fn a_plain_drop_whose_glue_panics_unwinds_out_of_the_frame() {
    decided("plain_drop_unwinds");
}

#[test]
fn drop_invoke_takes_the_unwind_edge_and_the_cleanup_runs() {
    // The glue stored 100 before it failed; the cleanup added 1.
    decided("drop_invoke_cleanup");
}

#[test]
fn assert_invoke_failure_enters_the_pad_and_resume_reraises_the_same_panic() {
    decided("assert_invoke_resume");
}

#[test]
fn an_uncaught_unwind_reports_the_original_panic_message_after_cleanups() {
    decided("uncaught_after_cleanup");
    // The escaping error IS the Abort run's: code, message, block and the
    // structured panic (kind, operands, resolved site).
    let (module, f, _) = cell("uncaught_after_cleanup");
    let abort = run(&module, f, PanicStrategy::Abort).expect_err("abort panics");
    let unwind = run(&module, f, PanicStrategy::Unwind).expect_err("unwind panics");
    assert_eq!(abort, unwind);
}

#[test]
fn a_catch_all_pad_catches_and_binds_selector_one() {
    decided("catch_all_selector");
}

#[test]
fn a_cleanup_pad_binds_selector_zero() {
    decided("cleanup_selector");
}

#[test]
fn a_pad_with_no_action_is_skipped() {
    decided("no_action_skipped");
}

#[test]
fn a_typed_catch_clause_is_refused_unsupported() {
    decided("typed_catch_refused");
    let (module, f, _) = cell("typed_catch_refused");
    let error = run(&module, f, PanicStrategy::Unwind).expect_err("refused");
    assert!(error.message.contains("typed catch"), "{error}");
}

#[test]
fn resume_of_a_non_exception_pointer_is_undefined_behavior() {
    decided("resume_non_exception");
}

#[test]
fn the_exception_object_is_opaque_memory() {
    // A load through it is UB (a dead allocation) ...
    decided("exception_object_opaque");
    // ... while storing it as a value, reloading it and resuming it is the
    // same exception (identity by address).
    decided("exception_spilled_and_resumed");
}

#[test]
fn abort_strategy_reproduces_todays_projection() {
    // Under the default strategy every cell is the panic=abort projection:
    // no unwind edge is taken, a failed check is the terminal panic, and a
    // pad or resume is never reached.
    let (module, ids) = matrix();
    for (cell, f) in CELLS.iter().zip(&ids) {
        let default = Interpreter::with_module(&module).execute_func(*f, Vec::new());
        check(cell, cell.abort, &default, PanicStrategy::Abort);
        assert!(
            matches!(cell.abort, Expect::Ok(_) | Expect::Panic { .. }),
            "{}: the abort projection only returns or panics here",
            cell.name
        );
    }
}

#[test]
fn invoke_indirect_unwinds_like_invoke() {
    decided("invoke_indirect_catches");
    decided("invoke_indirect_normal");
    // The direct twin gives the same answer as the indirect one.
    let (module, ids) = matrix();
    let at = |name: &str| ids[CELLS.iter().position(|c| c.name == name).unwrap()];
    let direct = run(&module, at("plain_call_unwinds"), PanicStrategy::Unwind).unwrap();
    let indirect = run(
        &module,
        at("invoke_indirect_catches"),
        PanicStrategy::Unwind,
    )
    .unwrap();
    assert_eq!(direct.returns, indirect.returns);
}

#[test]
fn a_drop_order_battery_matches_declaration_order() {
    // Notes 1, 2, 3 are dropped in REVERSE declaration order (321) on the
    // normal path and on the cleanup path alike.
    decided("drop_order_normal");
    decided("drop_order_unwind");
}

#[test]
fn every_cell_is_decided() {
    // Every cell of the matrix has a test above (or the abort sweep), and
    // every function the matrix defines for a cell runs under both
    // strategies to its decided verdict.
    let (module, ids) = matrix();
    for (cell, f) in CELLS.iter().zip(&ids) {
        check(
            cell,
            cell.abort,
            &run(&module, *f, PanicStrategy::Abort),
            PanicStrategy::Abort,
        );
        check(
            cell,
            cell.unwind,
            &run(&module, *f, PanicStrategy::Unwind),
            PanicStrategy::Unwind,
        );
    }
}

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

/// The argument `n` (0 or 1) for a scalar parameter, or `None` for any
/// other type.
fn scalar_arg(ty: &Ty, n: i128) -> Option<InterpretValue> {
    match ty {
        Ty::Bool => Some(InterpretValue::bool(n != 0)),
        Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 => {
            InterpretValue::int(ty.clone(), n).ok()
        }
        _ => None,
    }
}

/// The prefix law (§21 rule 7), held by the reference interpreter over the
/// whole golden corpus: every function whose parameters are all scalars runs
/// at all-zero and at all-one arguments under both strategies. Where the Abort run returns, is
/// undefined behaviour, or runs out of fuel, the Unwind run is IDENTICAL
/// (values, steps, host calls; or code, message and block). Otherwise the
/// Abort run stopped at a panic or a refused pad / resume, where the Unwind
/// run may go on.
#[test]
fn abort_run_is_a_prefix_of_the_unwind_run() {
    let mut files: Vec<PathBuf> = fs::read_dir(fixtures_dir())
        .expect("fixture dir")
        .map(|entry| entry.expect("entry").path())
        .filter(|path| path.extension().is_some_and(|e| e == "tmbc"))
        .collect();
    files.sort();
    let mut runs = 0usize;
    let mut differing = 0usize;
    let mut modules: Vec<(String, Module)> = files
        .iter()
        .filter_map(|path| {
            trust_ir::binary::deserialize_module(&fs::read(path).ok()?)
                .ok()
                .map(|m| (path.display().to_string(), m))
        })
        .collect();
    modules.push(("unwind_matrix".into(), common::unwind_matrix::module().0));
    for (name, module) in &modules {
        for function in &module.functions {
            if function.is_declaration() {
                continue;
            }
            let Some(sig) = module.func_type(function.ty) else {
                continue;
            };
            for n in [0, 1] {
                let Some(args) = sig
                    .params
                    .iter()
                    .map(|ty| scalar_arg(ty, n))
                    .collect::<Option<Vec<_>>>()
                else {
                    continue;
                };
                let go = |strategy| {
                    Interpreter::with_module(module)
                        .with_options(InterpretOptions {
                            panic_strategy: strategy,
                            ..InterpretOptions::default()
                        })
                        .execute_func(function.id, args.clone())
                };
                let abort = go(PanicStrategy::Abort);
                let unwind = go(PanicStrategy::Unwind);
                runs += 1;
                let stops = match &abort {
                    Ok(_) => false,
                    Err(error) => match error.code {
                        InterpretErrorCode::Panic => true,
                        InterpretErrorCode::UnsupportedInstruction => {
                            error.message.contains("landingpad") || error.message.contains("resume")
                        }
                        _ => false,
                    },
                };
                if stops {
                    if abort != unwind {
                        differing += 1;
                    }
                } else {
                    assert_eq!(
                        abort, unwind,
                        "{name} @{}({n}): the Abort run is not a prefix of the Unwind run",
                        function.name
                    );
                }
            }
        }
    }
    // Measured 2026-10-02: 182 runs (91 functions at 0 and at 1).
    assert!(runs >= 150, "the corpus is not vacuous ({runs} runs)");
    assert!(differing > 0, "some run takes an unwind edge ({differing})");
}
