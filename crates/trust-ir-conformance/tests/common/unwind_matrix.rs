// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Amendment D, Part 2 (`docs/SPEC_RATIFICATIONS.md` §21): ONE module whose
// zero-argument functions are the unwinding cells, each with its decided
// verdict under `PanicStrategy::Abort` and under `PanicStrategy::Unwind`.
// `interpret_unwind.rs` runs it through the reference interpreter;
// `lean_exec_differential.rs` runs the cells the Lean model can execute
// including typed indirect calls, through both engines under both strategies.
//
// The module:
//
// * `Boom` / `Note` are i64 cells with drop glue: `drop_boom(p)` stores 100
//   at its place and then fails a `div_by_zero` check; `drop_note(p)` appends
//   the digit at its place to the mutable global `log` (`log = log * 10 +
//   digit`), so a drop ORDER is observable;
// * `fail_div() -> i64` fails a `div_by_zero` check (an unsited kinded
//   assert); `seven() -> i64` returns 7;
// * `panic_entry(ptr)` is the (bodyless) entry of every sited check, whose
//   location is the immutable global `loc`.

use trust_ir::ty::{FieldDef, StructDef};
use trust_ir::value::{FuncId, GlobalId, StructId};
use trust_ir::{AssertKind, CastOp, Constant, Endianness, Module, PanicLocation, PanicSite};
use trust_ir::{TargetInfo, Ty};
use trust_ir_build::ModuleBuilder;

/// A decided verdict of one cell under one strategy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expect {
    /// Returns this `i64`.
    Ok(i64),
    /// The `div_by_zero` panic (`attempt to divide by zero`); `sited` when
    /// the failed check carries a site (entry `panic_entry`, location `loc`).
    Panic { sited: bool },
    /// Undefined behaviour.
    Ub,
    /// Refused by name (`UnsupportedInstruction` / `unsupported.*`).
    Unsupported,
}

/// One cell: the function's name and
/// its verdict under each strategy.
#[derive(Debug, Clone, Copy)]
pub struct Cell {
    pub name: &'static str,
    pub abort: Expect,
    pub unwind: Expect,
}

const DIV: Expect = Expect::Panic { sited: false };
const SITED: Expect = Expect::Panic { sited: true };

/// Every cell, in the module's function order of definition.
pub const CELLS: &[Cell] = &[
    // A plain call propagates the unwinding out of its frame; the caller's
    // catch-all pad catches it.
    Cell {
        name: "plain_call_unwinds",
        abort: DIV,
        unwind: Expect::Ok(-1),
    },
    // A plain drop is a plain call of its glue: a panicking glue unwinds out
    // of the dropping frame.
    Cell {
        name: "plain_drop_unwinds",
        abort: DIV,
        unwind: Expect::Ok(-1),
    },
    // A `DropInvoke` takes its unwind edge: the glue stored 100, the cleanup
    // adds 1, resumes, and the caller reads 101.
    Cell {
        name: "drop_invoke_cleanup",
        abort: DIV,
        unwind: Expect::Ok(101),
    },
    // A failing `AssertInvoke` enters its own pad; the cleanup stores 7 and
    // `Resume` re-raises the same exception into the caller's catch-all.
    Cell {
        name: "assert_invoke_resume",
        abort: SITED,
        unwind: Expect::Ok(7),
    },
    // Uncaught: the run ends in the ORIGINAL sited panic, after the cleanup.
    Cell {
        name: "uncaught_after_cleanup",
        abort: SITED,
        unwind: SITED,
    },
    // The selector a pad binds: catch-all 1, cleanup 0.
    Cell {
        name: "catch_all_selector",
        abort: DIV,
        unwind: Expect::Ok(1),
    },
    Cell {
        name: "cleanup_selector",
        abort: DIV,
        unwind: Expect::Ok(0),
    },
    // A pad with no clause and no cleanup re-propagates: the frame is skipped
    // (its `ret 5` never runs) and the caller catches.
    Cell {
        name: "no_action_skipped",
        abort: DIV,
        unwind: Expect::Ok(-1),
    },
    // A typed catch clause is refused: the format has no typeinfo model.
    Cell {
        name: "typed_catch_refused",
        abort: DIV,
        unwind: Expect::Unsupported,
    },
    // `Resume` of a value no landing pad produced is undefined behaviour.
    Cell {
        name: "resume_non_exception",
        abort: DIV,
        unwind: Expect::Ub,
    },
    // The exception object is opaque, dead memory: loading through it is UB.
    Cell {
        name: "exception_object_opaque",
        abort: DIV,
        unwind: Expect::Ub,
    },
    // Spilled to a slot and reloaded, it is still the same exception.
    Cell {
        name: "exception_spilled_and_resumed",
        abort: DIV,
        unwind: Expect::Ok(-1),
    },
    // Drop order: three notes dropped in reverse declaration order, on the
    // normal path and on the cleanup path alike.
    Cell {
        name: "drop_order_normal",
        abort: Expect::Ok(321),
        unwind: Expect::Ok(321),
    },
    Cell {
        name: "drop_order_unwind",
        abort: DIV,
        unwind: Expect::Ok(321),
    },
    // `InvokeIndirect` catches exactly as `Invoke` does.
    Cell {
        name: "invoke_indirect_catches",
        abort: DIV,
        unwind: Expect::Ok(-1),
    },
    Cell {
        name: "invoke_indirect_normal",
        abort: Expect::Ok(7),
        unwind: Expect::Ok(7),
    },
    // A run that raises nothing is the same run under both strategies.
    Cell {
        name: "no_raise",
        abort: Expect::Ok(7),
        unwind: Expect::Ok(7),
    },
];

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

fn global(name: &str, mutable: bool, init: i128) -> trust_ir::Global {
    trust_ir::Global {
        name: name.into(),
        ty: if mutable { Ty::I64 } else { Ty::U64 },
        mutable,
        initializer: Some(Constant::Int(init)),
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    }
}

fn cell_struct(mb: &mut ModuleBuilder, id: u32, name: &str) -> Ty {
    Ty::Struct(mb.add_struct(StructDef {
        id: StructId::new(id),
        name: name.into(),
        fields: vec![FieldDef {
            name: "value".into(),
            ty: Ty::I64,
            offset: Some(0),
        }],
        size: Some(8),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    }))
}

/// The module and, for every cell of [`CELLS`] in order, its function id.
pub fn module() -> (Module, Vec<FuncId>) {
    let mut mb = ModuleBuilder::new_with_target_info("unwind_matrix", target());
    mb.add_global(global("loc", false, 7));
    mb.add_global(global("log", true, 0));
    let loc = GlobalId::new(0);
    let log = GlobalId::new(1);
    let boom = cell_struct(&mut mb, 0, "Boom");
    let note = cell_struct(&mut mb, 1, "Note");
    let glue_ty = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let thunk = mb.add_func_type(vec![], vec![Ty::I64]);
    let entry = mb.declare_function("panic_entry", glue_ty);
    let site = || PanicSite {
        entry,
        location: PanicLocation::Global(loc),
    };

    // drop_boom(p): *p = 100; assert false, div_by_zero
    let mut fb = mb.function("drop_boom", glue_ty);
    let b0 = fb.create_block();
    let p = fb.add_block_param(b0, Ty::Ptr);
    fb.switch_to_block(b0);
    let hundred = fb.iconst(Ty::I64, 100);
    fb.store(Ty::I64, p, hundred);
    let no = fb.const_value(Ty::Bool, Constant::Bool(false));
    fb.assert_kind(no, AssertKind::DivByZero);
    fb.ret(vec![]);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    let drop_boom = fb.build();

    // drop_note(p): log = log * 10 + *p
    let mut fb = mb.function("drop_note", glue_ty);
    let b0 = fb.create_block();
    let p = fb.add_block_param(b0, Ty::Ptr);
    fb.switch_to_block(b0);
    let digit = fb.load(Ty::I64, p);
    let g = fb.global_addr(log);
    let old = fb.load(Ty::I64, g);
    let ten = fb.iconst(Ty::I64, 10);
    let shifted = fb.mul(Ty::I64, old, ten);
    let new = fb.add(Ty::I64, shifted, digit);
    fb.store(Ty::I64, g, new);
    fb.ret(vec![]);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    let drop_note = fb.build();

    // fail_div() -> i64
    let mut fb = mb.function("fail_div", thunk);
    let b0 = fb.create_block();
    fb.switch_to_block(b0);
    let no = fb.const_value(Ty::Bool, Constant::Bool(false));
    fb.assert_kind(no, AssertKind::DivByZero);
    let zero = fb.iconst(Ty::I64, 0);
    fb.ret(vec![zero]);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    let fail_div = fb.build();

    // seven() -> i64
    let mut fb = mb.function("seven", thunk);
    let b0 = fb.create_block();
    fb.switch_to_block(b0);
    let seven = fb.iconst(Ty::I64, 7);
    fb.ret(vec![seven]);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    let seven_fn = fb.build();

    // calls_fail() -> i64: a PLAIN call of fail_div.
    let mut fb = mb.function("calls_fail", thunk);
    let b0 = fb.create_block();
    fb.switch_to_block(b0);
    let r = fb.call(fail_div, vec![]);
    fb.ret(vec![r]);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    let calls_fail = fb.build();

    // drops_boom() -> i64: a PLAIN drop of a Boom.
    let mut fb = mb.function("drops_boom", thunk);
    let b0 = fb.create_block();
    fb.switch_to_block(b0);
    let c = fb.alloca(Ty::I64);
    let zero = fb.iconst(Ty::I64, 0);
    fb.store(Ty::I64, c, zero);
    fb.drop(boom.clone(), c);
    fb.ret(vec![zero]);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    let drops_boom = fb.build();

    // drop_invoke_pad(c: ptr): drop_invoke Boom, c; cleanup: *c += 1; resume
    let mut fb = mb.function("drop_invoke_pad", glue_ty);
    let b0 = fb.create_block();
    let b1 = fb.create_block();
    let b2 = fb.create_block();
    let c = fb.add_block_param(b0, Ty::Ptr);
    fb.switch_to_block(b0);
    fb.drop_invoke(boom.clone(), c, b1, vec![], b2);
    fb.switch_to_block(b1);
    fb.ret(vec![]);
    fb.switch_to_block(b2);
    let (exn, _) = fb.landingpad(true, vec![]);
    let v = fb.load(Ty::I64, c);
    let one = fb.iconst(Ty::I64, 1);
    let v1 = fb.add(Ty::I64, v, one);
    fb.store(Ty::I64, c, v1);
    fb.resume(exn);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    let drop_invoke_pad = fb.build();

    // assert_invoke_pad(c: ptr): assert_invoke false; cleanup: *c = 7; resume
    let mut fb = mb.function("assert_invoke_pad", glue_ty);
    let b0 = fb.create_block();
    let b1 = fb.create_block();
    let b2 = fb.create_block();
    let c = fb.add_block_param(b0, Ty::Ptr);
    fb.switch_to_block(b0);
    let no = fb.const_value(Ty::Bool, Constant::Bool(false));
    fb.assert_invoke(no, AssertKind::DivByZero, site(), b1, vec![], b2);
    fb.switch_to_block(b1);
    fb.ret(vec![]);
    fb.switch_to_block(b2);
    let (exn, _) = fb.landingpad(true, vec![]);
    let seven_v = fb.iconst(Ty::I64, 7);
    fb.store(Ty::I64, c, seven_v);
    fb.resume(exn);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    let assert_invoke_pad = fb.build();

    // no_action() -> i64: invoke fail_div into a pad with no action.
    let mut fb = mb.function("no_action", thunk);
    let b0 = fb.create_block();
    let b1 = fb.create_block();
    let b2 = fb.create_block();
    fb.switch_to_block(b0);
    let r = fb.invoke(fail_div, vec![], b1, vec![], b2);
    fb.switch_to_block(b1);
    fb.ret(vec![r]);
    fb.switch_to_block(b2);
    let _ = fb.landingpad(false, vec![]);
    let five = fb.iconst(Ty::I64, 5);
    fb.ret(vec![five]);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    let no_action = fb.build();

    // spill() -> i64: invoke fail_div; cleanup: spill the exception to a
    // slot, reload it, resume the reloaded pointer.
    let mut fb = mb.function("spill", thunk);
    let b0 = fb.create_block();
    let b1 = fb.create_block();
    let b2 = fb.create_block();
    fb.switch_to_block(b0);
    let r = fb.invoke(fail_div, vec![], b1, vec![], b2);
    fb.switch_to_block(b1);
    fb.ret(vec![r]);
    fb.switch_to_block(b2);
    let (exn, _) = fb.landingpad(true, vec![]);
    let slot = fb.alloca(Ty::Ptr);
    fb.store(Ty::Ptr, slot, exn);
    let back = fb.load(Ty::Ptr, slot);
    fb.resume(back);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    let spill = fb.build();

    // drop_order_inner() -> i64: three notes 1, 2, 3; fail_div is invoked
    // while they are live; the cleanup drops them in reverse declaration
    // order and resumes.
    let mut fb = mb.function("drop_order_inner", thunk);
    let b0 = fb.create_block();
    let b1 = fb.create_block();
    let b2 = fb.create_block();
    fb.switch_to_block(b0);
    let mut notes = Vec::new();
    for digit in 1..=3 {
        let cell = fb.alloca(Ty::I64);
        let d = fb.iconst(Ty::I64, digit);
        fb.store(Ty::I64, cell, d);
        notes.push(cell);
    }
    let r = fb.invoke(fail_div, vec![], b1, vec![], b2);
    fb.switch_to_block(b1);
    for &cell in notes.iter().rev() {
        fb.drop(note.clone(), cell);
    }
    fb.ret(vec![r]);
    fb.switch_to_block(b2);
    let (exn, _) = fb.landingpad(true, vec![]);
    for &cell in notes.iter().rev() {
        fb.drop(note.clone(), cell);
    }
    fb.resume(exn);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    let drop_order_inner = fb.build();

    // A catching caller: `invoke callee(args) to bb1 unwind bb2; bb1: ret
    // <normal>; bb2: landingpad catch 0; ret <caught>`.
    let mut ids = Vec::new();
    for cell in CELLS {
        let mut fb = mb.function(cell.name, thunk);
        let b0 = fb.create_block();
        fb.switch_to_block(b0);
        match cell.name {
            "plain_call_unwinds"
            | "plain_drop_unwinds"
            | "no_action_skipped"
            | "exception_spilled_and_resumed" => {
                let callee = match cell.name {
                    "plain_call_unwinds" => calls_fail,
                    "plain_drop_unwinds" => drops_boom,
                    "no_action_skipped" => no_action,
                    _ => spill,
                };
                let b1 = fb.create_block();
                let b2 = fb.create_block();
                let r = fb.invoke(callee, vec![], b1, vec![], b2);
                fb.switch_to_block(b1);
                fb.ret(vec![r]);
                fb.switch_to_block(b2);
                let _ = fb.landingpad(false, vec![0]);
                let caught = fb.iconst(Ty::I64, -1);
                fb.ret(vec![caught]);
            }
            "drop_invoke_cleanup" | "assert_invoke_resume" => {
                let callee = if cell.name == "drop_invoke_cleanup" {
                    drop_invoke_pad
                } else {
                    assert_invoke_pad
                };
                let b1 = fb.create_block();
                let b2 = fb.create_block();
                let c = fb.alloca(Ty::I64);
                let zero = fb.iconst(Ty::I64, 0);
                fb.store(Ty::I64, c, zero);
                fb.invoke_void(callee, vec![c], b1, vec![], b2);
                fb.switch_to_block(b1);
                let v = fb.load(Ty::I64, c);
                fb.ret(vec![v]);
                fb.switch_to_block(b2);
                let _ = fb.landingpad(false, vec![0]);
                let v = fb.load(Ty::I64, c);
                fb.ret(vec![v]);
            }
            "uncaught_after_cleanup" => {
                let b1 = fb.create_block();
                let b2 = fb.create_block();
                let c = fb.alloca(Ty::I64);
                let no = fb.const_value(Ty::Bool, Constant::Bool(false));
                fb.assert_invoke(no, AssertKind::DivByZero, site(), b1, vec![], b2);
                fb.switch_to_block(b1);
                let zero = fb.iconst(Ty::I64, 0);
                fb.ret(vec![zero]);
                fb.switch_to_block(b2);
                let (exn, _) = fb.landingpad(true, vec![]);
                let one = fb.iconst(Ty::I64, 1);
                fb.store(Ty::I64, c, one);
                fb.resume(exn);
            }
            "catch_all_selector"
            | "cleanup_selector"
            | "typed_catch_refused"
            | "resume_non_exception"
            | "exception_object_opaque" => {
                let b1 = fb.create_block();
                let b2 = fb.create_block();
                let r = fb.invoke(fail_div, vec![], b1, vec![], b2);
                fb.switch_to_block(b1);
                fb.ret(vec![r]);
                fb.switch_to_block(b2);
                let (cleanup, clauses) = match cell.name {
                    "cleanup_selector" => (true, vec![]),
                    "typed_catch_refused" => (false, vec![3]),
                    _ => (false, vec![0]),
                };
                let (exn, sel) = fb.landingpad(cleanup, clauses);
                match cell.name {
                    "resume_non_exception" => {
                        let other = fb.alloca(Ty::I64);
                        fb.resume(other);
                    }
                    "exception_object_opaque" => {
                        let v = fb.load(Ty::I64, exn);
                        fb.ret(vec![v]);
                    }
                    _ => {
                        let wide = fb.cast(CastOp::SExt, Ty::I32, Ty::I64, sel);
                        fb.ret(vec![wide]);
                    }
                }
            }
            "drop_order_normal" => {
                let mut cells = Vec::new();
                for digit in 1..=3 {
                    let cell = fb.alloca(Ty::I64);
                    let d = fb.iconst(Ty::I64, digit);
                    fb.store(Ty::I64, cell, d);
                    cells.push(cell);
                }
                for &cell in cells.iter().rev() {
                    fb.drop(note.clone(), cell);
                }
                let g = fb.global_addr(log);
                let v = fb.load(Ty::I64, g);
                fb.ret(vec![v]);
            }
            "drop_order_unwind" => {
                let b1 = fb.create_block();
                let b2 = fb.create_block();
                let r = fb.invoke(drop_order_inner, vec![], b1, vec![], b2);
                fb.switch_to_block(b1);
                fb.ret(vec![r]);
                fb.switch_to_block(b2);
                let _ = fb.landingpad(false, vec![0]);
                let g = fb.global_addr(log);
                let v = fb.load(Ty::I64, g);
                fb.ret(vec![v]);
            }
            "invoke_indirect_catches" | "invoke_indirect_normal" => {
                let target_fn = if cell.name == "invoke_indirect_catches" {
                    fail_div
                } else {
                    seven_fn
                };
                let b1 = fb.create_block();
                let b2 = fb.create_block();
                let fp = fb.const_value(Ty::Func(thunk), Constant::FnDef(target_fn));
                let r = fb.invoke_indirect(fp, thunk, vec![], b1, vec![], b2);
                fb.switch_to_block(b1);
                fb.ret(vec![r]);
                fb.switch_to_block(b2);
                let _ = fb.landingpad(false, vec![0]);
                let caught = fb.iconst(Ty::I64, -1);
                fb.ret(vec![caught]);
            }
            "no_raise" => {
                let b1 = fb.create_block();
                let b2 = fb.create_block();
                let r = fb.invoke(seven_fn, vec![], b1, vec![], b2);
                fb.switch_to_block(b1);
                fb.ret(vec![r]);
                fb.switch_to_block(b2);
                let _ = fb.landingpad(false, vec![0]);
                let caught = fb.iconst(Ty::I64, -1);
                fb.ret(vec![caught]);
            }
            other => unreachable!("cell {other} has no body"),
        }
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        ids.push(fb.build());
    }

    mb.set_drop_glue(boom, drop_boom).expect("one row for Boom");
    mb.set_drop_glue(note, drop_note).expect("one row for Note");
    (mb.build().expect("ModuleBuilder::build: test fixture"), ids)
}
