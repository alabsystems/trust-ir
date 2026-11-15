// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Roadmap WS2.10 (F-034): `Undef` is POISON in the reference interpreter, as
// it already is in the Lean semantics (`Step.lean` binds `.undef ty`) and as
// ub-numerics-policy §4 has always said. Executing `undef` is not undefined
// behaviour; INSPECTING the value is, at the true use site.
//
// The poison carrier is the existing copy-propagates-poison value
// (`PartialBytes`, every byte uninitialized), so `Undef` transports exactly
// where a partially-initialized load does — `Copy`, a `Select` arm, a
// non-strict `Store`, a branch-edge block argument — and faults exactly where
// it does: arithmetic, comparison, cast, a branch/switch/select condition, a
// call argument or return, a strict (volatile/atomic) store. An unbound
// `LoadSlot` reads the same poison (Lean `initFrame` seeds `.undef`). A
// non-scalar `Undef` (struct, tuple, …) has no poison carrier and FAILS
// CLOSED with `UndefinedBehavior` — never a silently "complete" aggregate.
//
// The Lean twins are the `undef_*_stable` fixtures in
// `lean/trust_ir-semantics/TrustIr/Semantics/ExecutableFixtures.lean` and
// `undef_inspect_is_ub` in `TrustIr/Proofs/MetaTheorems.lean`. Gate 8 runs
// this file (scripts/gates/wire-format-goldens.trust-ir-conformance.tests).

use trust_ir::inst::{BindingFrameDef, BindingSlot};
use trust_ir::interpret::{InterpretError, InterpretErrorCode, Interpreter};
use trust_ir::ty::{FieldDef, StructDef, Ty};
use trust_ir::value::{BindingFrameId, FuncId, StructId, ValueId};
use trust_ir::{Inst, Module};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

/// Build `program() -> u64` whose single entry block is written by `body`
/// (which must end the block with a terminator), and return the module.
fn program(body: impl FnOnce(&mut FunctionBuilder<'_>)) -> Module {
    let mut mb = ModuleBuilder::new("undef_poison");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    body(&mut fb);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Validate (the module must be well-formed — every case here is legal IR),
/// then execute `program`.
fn run(module: &Module) -> Result<u64, InterpretError> {
    assert_eq!(
        trust_ir_build::validate_module(module),
        [],
        "every WS2.10 case is well-formed IR"
    );
    let outcome = Interpreter::with_module(module).execute_func(FuncId::new(0), [])?;
    Ok(outcome.returns[0]
        .as_int()
        .expect("integer result")
        .as_unsigned() as u64)
}

fn assert_ub(result: Result<u64, InterpretError>, reason: &str) {
    let error = result.expect_err("expected undefined behaviour");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{error}");
    assert!(
        error.to_string().contains(reason),
        "expected UB naming {reason:?}, got: {error}"
    );
}

/// `%u = undef u64; store %u, %p; ret 7`: the store only TRANSPORTS the
/// poison, so the function returns 7. Before WS2.10 this was eager UB
/// ("executing undef would read an undefined value") while Lean returned 7.
fn store_undef_then_ret_7(fb: &mut FunctionBuilder<'_>) {
    let undef = fb.undef(Ty::U64);
    let cell = fb.alloca(Ty::U64);
    fb.store(Ty::U64, cell, undef);
    let seven = fb.uconst(Ty::U64, 7);
    fb.ret(vec![seven]);
}

/// Positive: poison is transported, not inspected.
#[test]
fn ws2_10_undef_stored_then_constant_returned_is_ok() {
    assert_eq!(run(&program(store_undef_then_ret_7)), Ok(7));
}

/// Negative twin (one mutation: the poison feeds an `add` instead of a
/// store): inspecting poison is UB, reported at the `add`, as poison.
#[test]
fn ws2_10_undef_inspected_by_add_is_ub() {
    let module = program(|fb| {
        let undef = fb.undef(Ty::U64);
        let one = fb.uconst(Ty::U64, 1);
        let sum = fb.add(Ty::U64, undef, one);
        fb.ret(vec![sum]);
    });
    assert_ub(run(&module), "use of an uninitialized value");
}

/// Mutation control: an `undef` of a STRUCT type has no poison carrier and
/// stays UB at the `undef` itself — it is not silently executed as a
/// "complete" poison aggregate. A tuple is refused the same way.
#[test]
fn ws2_10_undef_of_struct_is_ub_not_a_complete_aggregate() {
    let mut mb = ModuleBuilder::new("undef_poison_struct");
    let sid = mb.add_struct(StructDef {
        id: StructId::new(0),
        name: "Pair".into(),
        fields: vec![
            FieldDef {
                name: "lo".into(),
                ty: Ty::U64,
                offset: Some(0),
            },
            FieldDef {
                name: "hi".into(),
                ty: Ty::U64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    });
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.undef(Ty::Struct(sid));
    let seven = fb.uconst(Ty::U64, 7);
    fb.ret(vec![seven]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_ub(
        run(&module),
        "undef of non-scalar type struct.0 is not executable (aggregate poison unmodelled)",
    );

    let tuple = program(|fb| {
        fb.undef(Ty::Tuple(vec![Ty::U64, Ty::Bool]));
        let seven = fb.uconst(Ty::U64, 7);
        fb.ret(vec![seven]);
    });
    assert_ub(run(&tuple), "undef of non-scalar type");
}

/// Mutation control: branching on poison is UB (policy §4, verbatim).
#[test]
fn ws2_10_condbr_on_undef_bool_is_ub() {
    let mut mb = ModuleBuilder::new("undef_poison_branch");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let entry = fb.create_block();
    let then_bb = fb.create_block();
    let else_bb = fb.create_block();
    fb.switch_to_block(entry);
    let cond = fb.undef(Ty::Bool);
    fb.condbr(cond, then_bb, vec![], else_bb, vec![]);
    fb.switch_to_block(then_bb);
    let one = fb.uconst(Ty::U64, 1);
    fb.ret(vec![one]);
    fb.switch_to_block(else_bb);
    let two = fb.uconst(Ty::U64, 2);
    fb.ret(vec![two]);
    fb.build();
    assert_ub(
        run(&mb.build().expect("ModuleBuilder::build: test fixture")),
        "cond_br: use of an uninitialized value",
    );
}

/// Transport is exactly the `PartialBytes` set: `Copy`, a `Select` ARM, and a
/// branch-edge block argument all move poison without inspecting it.
#[test]
fn ws2_10_undef_transports_through_copy_select_arm_and_block_arg() {
    let mut mb = ModuleBuilder::new("undef_poison_transport");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let entry = fb.create_block();
    let next = fb.create_block();
    let carried = fb.add_block_param(next, Ty::U64);
    fb.switch_to_block(entry);
    let undef = fb.undef(Ty::U64);
    let copied = fb.copy(Ty::U64, undef);
    let yes = fb.bool_const(true);
    let five = fb.uconst(Ty::U64, 5);
    let chosen = fb.select(Ty::U64, yes, copied, five);
    fb.br(next, vec![chosen]);
    fb.switch_to_block(next);
    let cell = fb.alloca(Ty::U64);
    fb.store(Ty::U64, cell, carried);
    let seven = fb.uconst(Ty::U64, 7);
    fb.ret(vec![seven]);
    fb.build();
    assert_eq!(
        run(&mb.build().expect("ModuleBuilder::build: test fixture")),
        Ok(7)
    );
}

/// Poison written to memory stays poison: a plain reload yields it back, and
/// inspecting the reloaded value is UB.
#[test]
fn ws2_10_undef_stored_and_reloaded_is_still_poison() {
    let module = program(|fb| {
        let undef = fb.undef(Ty::U64);
        let cell = fb.alloca(Ty::U64);
        fb.store(Ty::U64, cell, undef);
        let reloaded = fb.load(Ty::U64, cell);
        let one = fb.uconst(Ty::U64, 1);
        let sum = fb.add(Ty::U64, reloaded, one);
        fb.ret(vec![sum]);
    });
    assert_ub(run(&module), "use of an uninitialized value");
}

/// The inspection set: a `Select` CONDITION, a strict (volatile) store, a
/// call argument and a return are each UB on poison. Poison crosses a call
/// only through memory.
#[test]
fn ws2_10_undef_inspections_are_ub() {
    let select_cond = program(|fb| {
        let cond = fb.undef(Ty::Bool);
        let one = fb.uconst(Ty::U64, 1);
        let two = fb.uconst(Ty::U64, 2);
        let chosen = fb.select(Ty::U64, cond, one, two);
        fb.ret(vec![chosen]);
    });
    assert_ub(run(&select_cond), "select: use of an uninitialized value");

    let volatile = program(|fb| {
        let undef = fb.undef(Ty::U64);
        let cell = fb.alloca(Ty::U64);
        fb.store_volatile(Ty::U64, cell, undef);
        let seven = fb.uconst(Ty::U64, 7);
        fb.ret(vec![seven]);
    });
    assert_ub(
        run(&volatile),
        "Store (atomic/volatile): use of an uninitialized value",
    );

    let returned = program(|fb| {
        let undef = fb.undef(Ty::U64);
        fb.ret(vec![undef]);
    });
    assert_ub(
        run(&returned),
        "Call returns: use of an uninitialized value",
    );

    let mut mb = ModuleBuilder::new("undef_poison_call");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let id_sig = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let undef = fb.undef(Ty::U64);
    let got = fb.call(FuncId::new(1), vec![undef]);
    fb.ret(vec![got]);
    fb.build();
    let mut fb = mb.function("id", id_sig);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    fb.build();
    assert_ub(
        run(&mb.build().expect("ModuleBuilder::build: test fixture")),
        "Call arguments: use of an uninitialized value",
    );
}

/// `program()` opens a one-slot frame of `slot_ty`, never binds it, and reads
/// it back; `inspect` then adds 1 to the read (u64 only), otherwise the read
/// is dropped and 7 returned.
fn unbound_slot(slot_ty: Ty, inspect: bool) -> Module {
    program(|fb| {
        let opened = fb.open_frame(BindingFrameDef::new(
            BindingFrameId::new(0),
            "exists_i",
            vec![BindingSlot::new("i", slot_ty.clone())],
        ));
        let read: ValueId = fb.load_slot(opened, 0, slot_ty);
        fb.close_frame(opened);
        let seven = fb.uconst(Ty::U64, 7);
        if inspect {
            let sum = fb.add(Ty::U64, read, seven);
            fb.ret(vec![sum]);
        } else {
            fb.ret(vec![seven]);
        }
    })
}

/// An unbound `LoadSlot` reads the same scalar poison (Lean `initFrame`): the
/// read succeeds, inspecting it is UB, and a non-scalar unbound slot fails
/// closed at the read.
#[test]
fn ws2_10_unbound_load_slot_reads_scalar_poison() {
    assert_eq!(run(&unbound_slot(Ty::U64, false)), Ok(7));
    assert_ub(
        run(&unbound_slot(Ty::U64, true)),
        "use of an uninitialized value",
    );
    assert_ub(
        run(&unbound_slot(Ty::Tuple(vec![Ty::U64, Ty::U64]), false)),
        "LoadSlot: slot 0 read before bound: poison of non-scalar type",
    );
}

/// Ported proof-program row `b7.nondet.undef_executes_as_ub` (archived
/// `partb/tests/b7_codec_and_semantics_gaps.rs`), flipped GAP -> PASS:
/// "Undef is poison; inspection is UB". The row's module is
/// `pick() -> u64 { v = undef u64; ret and(v, 1) }`: it validates, and it is
/// STILL undefined behaviour — but now because the `and` inspects poison, not
/// because executing `undef` traps. `Undef` was never an input source and
/// still is not one: there is no value it could be observed to "choose", and
/// the verdict is identical on every run.
#[test]
fn b7_nondet_undef_executes_as_ub() {
    let pick = program(|fb| {
        let v = fb.undef(Ty::U64);
        let one = fb.uconst(Ty::U64, 1);
        let out = fb.binop(trust_ir::BinOp::And, Ty::U64, v, one);
        fb.ret(vec![out]);
    });
    let first = run(&pick);
    assert_ub(first.clone(), "use of an uninitialized value");
    assert!(
        !first
            .as_ref()
            .unwrap_err()
            .to_string()
            .contains("executing undef"),
        "the retired eager-UB reason must not come back: {first:?}"
    );
    assert_eq!(
        run(&pick).map_err(|e| e.to_string()),
        first.map_err(|e| e.to_string()),
        "the verdict is deterministic"
    );
    // The same `undef`, never inspected, executes.
    let inert = program(|fb| {
        fb.undef(Ty::U64);
        let one = fb.uconst(Ty::U64, 1);
        fb.ret(vec![one]);
    });
    assert_eq!(run(&inert), Ok(1));
    assert!(
        inert.functions[0].blocks[0]
            .body
            .iter()
            .any(|node| matches!(node.inst, Inst::Undef { ty: Ty::U64 })),
        "the inert twin really executes an undef"
    );
}

// ---------------------------------------------------------------------------
// WS2.10 adversarial review: poison may not HIDE inside a defined value, and
// every operation that looks at poison refuses it. Each case below was an
// `Ok` before the review (probed against the implementation commit).
// ---------------------------------------------------------------------------

/// Build `program() -> ret` over one entry block written by `body`, validate
/// it, and execute it (the returned values are left raw).
fn run_raw(
    ret: Ty,
    body: impl FnOnce(&mut FunctionBuilder<'_>),
) -> Result<Vec<trust_ir::interpret::InterpretValue>, InterpretError> {
    let mut mb = ModuleBuilder::new("undef_poison_review");
    let sig = mb.add_func_type(vec![], vec![ret]);
    let mut fb = mb.function("program", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    body(&mut fb);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(
        trust_ir_build::validate_module(&module),
        [],
        "every WS2.10 review case is well-formed IR"
    );
    Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .map(|outcome| outcome.returns)
}

fn assert_raw_ub<T: std::fmt::Debug>(result: Result<T, InterpretError>, reason: &str) {
    let error = result.expect_err("expected undefined behaviour");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{error}");
    assert!(
        error.to_string().contains(reason),
        "expected UB naming {reason:?}, got: {error}"
    );
}

/// `program() -> [u64; 2] { ret insert_element([1, 2], 0, <elem>) }`.
fn array_insert(undef_elem: bool) -> Module {
    let mut mb = ModuleBuilder::new("undef_poison_array");
    let elem = mb.add_type(Ty::U64);
    let arr = Ty::Array(elem, 2);
    let sig = mb.add_func_type(vec![], vec![arr.clone()]);
    let mut fb = mb.function("program", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let base = fb.const_value(
        arr.clone(),
        trust_ir::Constant::Array(vec![trust_ir::Constant::Int(1), trust_ir::Constant::Int(2)]),
    );
    let value = if undef_elem {
        fb.undef(Ty::U64)
    } else {
        fb.uconst(Ty::U64, 9)
    };
    let zero = fb.uconst(Ty::U64, 0);
    let inserted = fb.insert_element(arr, base, zero, value);
    fb.ret(vec![inserted]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Adversarial 1 (a false accept): `insert_element` of an `undef` into a
/// defined array USED to succeed, and the array — poison lane and all — was
/// returned from the entry `Ok`, because the call-boundary check only looks
/// at top-level values. Embedding is an inspection, as `insert_field` already
/// was (Lean `semInsertElement` mirrors it:
/// `undef_insert_element_into_array_is_ub_stable`).
#[test]
fn ws2_10_review_undef_inserted_into_array_is_ub() {
    let run_module = |module: &Module| {
        assert_eq!(trust_ir_build::validate_module(module), []);
        Interpreter::with_module(module)
            .execute_func(FuncId::new(0), [])
            .map(|outcome| outcome.returns)
    };
    assert_raw_ub(
        run_module(&array_insert(true)),
        "insert_element value: use of an uninitialized value",
    );
    // Mutation control: a defined element inserts and returns normally.
    let returns = run_module(&array_insert(false)).expect("defined insert runs");
    assert_eq!(
        format!("{:?}", returns[0].kind).matches("raw: 9").count(),
        1,
        "the inserted lane is 9: {returns:?}"
    );
}

/// Adversarial 2: the same escape through a SIMD vector — `insert_element`
/// and the `vector.insert_lane` / `vector.pack_lanes` dialect ops each used
/// to place a poison lane in a vector that was then returned `Ok`. (Lean's
/// `setVectorElement` refuses a non-lane value as a type error; the engines
/// agree the module is refused and differ only in the error class, as for a
/// poison pointer operand — ub-numerics-policy §4.)
#[test]
fn ws2_10_review_undef_lane_in_vector_is_ub() {
    use trust_ir::dialect::vector as vd;
    assert_raw_ub(
        run_raw(Ty::v2_i64(), |fb| {
            let base = fb.const_value(
                Ty::v2_i64(),
                trust_ir::Constant::Vector(vec![
                    trust_ir::Constant::Int(1),
                    trust_ir::Constant::Int(2),
                ]),
            );
            let lane = fb.undef(Ty::I64);
            let zero = fb.uconst(Ty::U32, 0);
            let inserted = fb.insert_element(Ty::v2_i64(), base, zero, lane);
            fb.ret(vec![inserted]);
        }),
        "insert_element value: use of an uninitialized value",
    );
    assert_raw_ub(
        run_raw(Ty::v2_i64(), |fb| {
            let base = fb.const_value(
                Ty::v2_i64(),
                trust_ir::Constant::Vector(vec![
                    trust_ir::Constant::Int(1),
                    trust_ir::Constant::Int(2),
                ]),
            );
            let lane = fb.undef(Ty::I64);
            let out = fb.dialect_op(vd::insert_lane(Ty::v2_i64(), base, 1, lane));
            fb.ret(out);
        }),
        "vector.insert_lane: use of an uninitialized value",
    );
    assert_raw_ub(
        run_raw(Ty::v2_i64(), |fb| {
            let lane = fb.undef(Ty::I64);
            let one = fb.iconst(Ty::I64, 1);
            let out = fb.dialect_op(vd::pack_lanes(Ty::v2_i64(), [one, lane]));
            fb.ret(out);
        }),
        "vector.pack_lanes: use of an uninitialized value",
    );
    // Mutation control: defined lanes pack and return.
    run_raw(Ty::v2_i64(), |fb| {
        let a = fb.iconst(Ty::I64, 1);
        let b = fb.iconst(Ty::I64, 2);
        let out = fb.dialect_op(vd::pack_lanes(Ty::v2_i64(), [a, b]));
        fb.ret(out);
    })
    .expect("defined lanes pack");
}

/// `cmpxchg` of a cell holding 5 against `expected`, desired 9; returns the
/// old value.
fn cmpxchg_program(undef_expected: bool) -> Module {
    program(|fb| {
        let cell = fb.alloca(Ty::U64);
        let five = fb.uconst(Ty::U64, 5);
        fb.store(Ty::U64, cell, five);
        let expected = if undef_expected {
            fb.undef(Ty::U64)
        } else {
            fb.uconst(Ty::U64, 4)
        };
        let nine = fb.uconst(Ty::U64, 9);
        let (old, _swapped) = fb.cmpxchg(
            Ty::U64,
            cell,
            expected,
            nine,
            trust_ir::inst::Ordering::SeqCst,
            trust_ir::inst::Ordering::SeqCst,
        );
        fb.ret(vec![old]);
    })
}

/// Adversarial 3 (a silent verdict): `cmpxchg` COMPARES `expected`, which is
/// an inspection like `icmp`. A poison `expected` used to compare "unequal"
/// deterministically and the program returned `Ok(5)`; it is UB in both
/// engines now (Lean `undef_cmpxchg_expected_is_ub_stable`).
#[test]
fn ws2_10_review_cmpxchg_with_undef_expected_is_ub() {
    assert_ub(
        run(&cmpxchg_program(true)),
        "cmpxchg expected: use of an uninitialized value",
    );
    // Mutation control: a defined, unequal `expected` leaves 5 in place.
    assert_eq!(run(&cmpxchg_program(false)), Ok(5));
}

/// Adversarial 4 (an engine divergence): `ptr_from_parts` / `ptr_data` /
/// `ptr_metadata` over a poison THIN pointer used to relabel the poison as a
/// pointer result and run on (`store` it, `ret 7` → `Ok(7)`), while Lean's
/// pointer matches refuse a `.undef` operand. Both engines refuse it now.
#[test]
fn ws2_10_review_pointer_parts_of_undef_are_refused() {
    fn with(op: impl FnOnce(&mut FunctionBuilder<'_>, ValueId) -> ValueId, store_ty: Ty) -> Module {
        program(|fb| {
            let poison = fb.undef(Ty::Ptr);
            let out = op(fb, poison);
            let cell = fb.alloca(store_ty.clone());
            fb.store(store_ty, cell, out);
            let seven = fb.uconst(Ty::U64, 7);
            fb.ret(vec![seven]);
        })
    }
    let unit =
        |fb: &mut FunctionBuilder<'_>| fb.const_value(Ty::Unit, trust_ir::Constant::PhantomData);
    assert_ub(
        run(&with(
            |fb, p| {
                let meta = unit(fb);
                fb.ptr_from_parts(Ty::Ptr, Ty::Unit, p, meta)
            },
            Ty::Ptr,
        )),
        "PtrFromParts data: use of an uninitialized value",
    );
    assert_ub(
        run(&with(|fb, p| fb.ptr_data(Ty::Ptr, p), Ty::Ptr)),
        "PtrData: use of an uninitialized value",
    );
    assert_ub(
        run(&with(
            |fb, p| fb.ptr_metadata(Ty::Ptr, Ty::Unit, p),
            Ty::Unit,
        )),
        "PtrMetadata: use of an uninitialized value",
    );
    // Mutation control: the same shape over a real pointer runs.
    let real = program(|fb| {
        let target = fb.alloca(Ty::U64);
        let meta = fb.const_value(Ty::Unit, trust_ir::Constant::PhantomData);
        let rebuilt = fb.ptr_from_parts(Ty::Ptr, Ty::Unit, target, meta);
        let cell = fb.alloca(Ty::Ptr);
        fb.store(Ty::Ptr, cell, rebuilt);
        let seven = fb.uconst(Ty::U64, 7);
        fb.ret(vec![seven]);
    });
    assert_eq!(run(&real), Ok(7));
}

/// Pinned residue (documented in ub-numerics-policy §4): `assume` of poison
/// is UB in the reference interpreter, which checks every `assume` condition
/// (a FALSE one is refused too, but since WS2.11 under its own name
/// `AssumeViolated` — the poison one here stays `UndefinedBehavior`); Lean's
/// `Assume` is a no-op in execution (`assume_always_succeeds`), for a false
/// condition as much as a poison one.
#[test]
fn ws2_10_review_assume_of_undef_is_ub_in_the_interpreter() {
    assert_ub(
        run(&program(|fb| {
            let cond = fb.undef(Ty::Bool);
            fb.assume(cond);
            let seven = fb.uconst(Ty::U64, 7);
            fb.ret(vec![seven]);
        })),
        "assume: use of an uninitialized value",
    );
}
