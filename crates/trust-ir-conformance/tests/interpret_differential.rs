// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Validator <-> reference-interpreter differential property test.
//
// `crates/trust-ir/src/interpret.rs` is a 5000+ line reference interpreter
// for the bounded core subset, but it had only inline unit tests and no
// integration coverage. This file is the W5a "differential oracle" payoff
// that does not need a Lean-extracted oracle (W5b): a seeded generator emits
// a wide space of VALID scalar/control-flow modules and asserts three
// properties that tie the interpreter to the validator without a second
// reference implementation:
//
//   1. DETERMINISM. Executing the same function with the same arguments
//      twice yields byte-identical results (Ok outcome or Err code). The
//      interpreter is `Copy` and rebuilds fresh state per call, so any
//      observable nondeterminism (e.g. a HashMap creeping into value or
//      memory state, or address randomization) is a regression this catches.
//
//   2. NO STRUCTURAL ERROR ON VALIDATED IR. A module the validator accepts
//      must never make the interpreter report a structural-integrity code
//      (`MalformedInstruction` / `MissingValue` / `MissingBlock`). If it
//      does, the validator and interpreter disagree about well-formedness —
//      exactly the cross-checking a differential oracle exists to surface.
//      Runtime/capability codes (`UndefinedBehavior` from div-by-zero,
//      `Unsupported*`, `OutOfFuel`, `Panic`) are legitimate outcomes.
//
//   3. RETURN SHAPE. When a function returns `Ok`, the produced value count
//      matches the declared return arity and the value's type matches the
//      declared return type.
//
// The generator is intentionally focused on the interpreter's robust core
// (integer/bool arithmetic, comparisons, select, copy, and diamond control
// flow). Memory, atomics, casts, and aggregates are exercised against the
// codec by `module_roundtrip_fuzz.rs`; here they would mostly surface as
// `Unsupported*` and dilute the execution signal. Floats are excluded (the
// generator never mints them) so results stay structurally comparable.

use trust_ir::Module;
use trust_ir::inst::{BinOp, ICmpOp, UnOp};
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

mod common;
use common::{Rng, int_ty};

/// What the test needs to call a generated function and check its result.
struct FnSpec {
    id: FuncId,
    params: Vec<Ty>,
    ret: Option<Ty>,
}

/// Argument/return palette: integers plus `Bool`. No `Ptr` — passing a null
/// pointer into a body that dereferences it produces `UndefinedBehavior`,
/// which is a legitimate but noisy outcome that would obscure clean
/// execution coverage.
fn arg_ty(rng: &mut Rng) -> Ty {
    if rng.bounded(4) == 0 {
        Ty::Bool
    } else {
        int_ty(rng)
    }
}

/// Draw an in-scope value of the wanted type, minting a fresh constant if the
/// pool has none. Every entry is an already-defined SSA value, so any operand
/// is guaranteed in-scope and well-typed.
fn get_or_mint(
    fb: &mut FunctionBuilder<'_>,
    rng: &mut Rng,
    pool: &mut Vec<(ValueId, Ty)>,
    want: &Ty,
) -> ValueId {
    let matches: Vec<ValueId> = pool
        .iter()
        .filter(|(_, t)| t == want)
        .map(|(v, _)| *v)
        .collect();
    if !matches.is_empty() {
        return matches[rng.bounded(matches.len() as u32) as usize];
    }
    let minted = match want {
        Ty::Bool => fb.bool_const(rng.bool()),
        other => fb.iconst(other.clone(), rng.small()),
    };
    pool.push((minted, want.clone()));
    minted
}

fn gen_inst(fb: &mut FunctionBuilder<'_>, rng: &mut Rng, pool: &mut Vec<(ValueId, Ty)>) {
    match rng.bounded(6) {
        0 => {
            let t = int_ty(rng);
            let v = fb.iconst(t.clone(), rng.small());
            pool.push((v, t));
        }
        1 => {
            // Integer binary op. Div/rem may divide by a zero constant; the
            // interpreter reports that as `UndefinedBehavior`, an accepted
            // outcome (it does not panic).
            let t = int_ty(rng);
            let op = rng.one_of(&[
                BinOp::Add,
                BinOp::Sub,
                BinOp::Mul,
                BinOp::UDiv,
                BinOp::SDiv,
                BinOp::URem,
                BinOp::SRem,
                BinOp::And,
                BinOp::Or,
                BinOp::Xor,
            ]);
            let a = get_or_mint(fb, rng, pool, &t);
            let b = get_or_mint(fb, rng, pool, &t);
            let v = fb.binop(op, t.clone(), a, b);
            pool.push((v, t));
        }
        2 => {
            let t = int_ty(rng);
            let op = rng.one_of(&[UnOp::Neg, UnOp::Not]);
            let a = get_or_mint(fb, rng, pool, &t);
            let v = fb.unop(op, t.clone(), a);
            pool.push((v, t));
        }
        3 => {
            let t = int_ty(rng);
            let op = rng.one_of(&[
                ICmpOp::Eq,
                ICmpOp::Ne,
                ICmpOp::Ult,
                ICmpOp::Ule,
                ICmpOp::Ugt,
                ICmpOp::Uge,
                ICmpOp::Slt,
                ICmpOp::Sle,
                ICmpOp::Sgt,
                ICmpOp::Sge,
            ]);
            let a = get_or_mint(fb, rng, pool, &t);
            let b = get_or_mint(fb, rng, pool, &t);
            let v = fb.icmp(op, t, a, b);
            pool.push((v, Ty::Bool));
        }
        4 => {
            let t = int_ty(rng);
            let c = get_or_mint(fb, rng, pool, &Ty::Bool);
            let a = get_or_mint(fb, rng, pool, &t);
            let b = get_or_mint(fb, rng, pool, &t);
            let v = fb.select(t.clone(), c, a, b);
            pool.push((v, t));
        }
        _ => {
            let t = int_ty(rng);
            let a = get_or_mint(fb, rng, pool, &t);
            let v = fb.copy(t.clone(), a);
            pool.push((v, t));
        }
    }
}

fn gen_signature(rng: &mut Rng) -> (Vec<Ty>, Option<Ty>) {
    let n_params = rng.bounded(4);
    let params: Vec<Ty> = (0..n_params).map(|_| arg_ty(rng)).collect();
    let ret = if rng.bounded(4) == 0 {
        None
    } else {
        Some(arg_ty(rng))
    };
    (params, ret)
}

fn gen_function_linear(mb: &mut ModuleBuilder, rng: &mut Rng, idx: u32) -> FnSpec {
    let (params, ret) = gen_signature(rng);
    let returns = ret.iter().cloned().collect::<Vec<_>>();
    let ft = mb.add_func_type(params.clone(), returns);
    let mut fb = mb.function(format!("f{idx}"), ft);

    let entry = fb.create_block();
    let mut pool: Vec<(ValueId, Ty)> = Vec::new();
    for p in &params {
        let v = fb.add_block_param(entry, p.clone());
        pool.push((v, p.clone()));
    }
    fb.switch_to_block(entry);
    for _ in 0..(4 + rng.bounded(16)) {
        gen_inst(&mut fb, rng, &mut pool);
    }
    match &ret {
        None => fb.ret(vec![]),
        Some(t) => {
            let v = get_or_mint(&mut fb, rng, &mut pool, t);
            fb.ret(vec![v]);
        }
    }
    let id = fb.build();
    FnSpec { id, params, ret }
}

/// Diamond CFG: entry conditionally branches to then/else, both branch to a
/// merge block carrying a block parameter. Dominance is respected exactly as
/// in the codec generator: entry-defined values seed the successor pools;
/// then/else locals do not dominate merge.
fn gen_function_cfg(mb: &mut ModuleBuilder, rng: &mut Rng, idx: u32) -> FnSpec {
    let (params, ret) = gen_signature(rng);
    let returns = ret.iter().cloned().collect::<Vec<_>>();
    let ft = mb.add_func_type(params.clone(), returns);
    let mut fb = mb.function(format!("f{idx}"), ft);

    let entry = fb.create_block();
    let then_bb = fb.create_block();
    let else_bb = fb.create_block();
    let merge_bb = fb.create_block();

    let merge_ty = int_ty(rng);
    let merge_param = fb.add_block_param(merge_bb, merge_ty.clone());

    let mut entry_pool: Vec<(ValueId, Ty)> = Vec::new();
    for p in &params {
        let v = fb.add_block_param(entry, p.clone());
        entry_pool.push((v, p.clone()));
    }
    fb.switch_to_block(entry);
    for _ in 0..(2 + rng.bounded(6)) {
        gen_inst(&mut fb, rng, &mut entry_pool);
    }
    let cond = get_or_mint(&mut fb, rng, &mut entry_pool, &Ty::Bool);
    fb.condbr(cond, then_bb, vec![], else_bb, vec![]);

    fb.switch_to_block(then_bb);
    let mut then_pool = entry_pool.clone();
    for _ in 0..(1 + rng.bounded(4)) {
        gen_inst(&mut fb, rng, &mut then_pool);
    }
    let then_arg = get_or_mint(&mut fb, rng, &mut then_pool, &merge_ty);
    fb.br(merge_bb, vec![then_arg]);

    fb.switch_to_block(else_bb);
    let mut else_pool = entry_pool.clone();
    for _ in 0..(1 + rng.bounded(4)) {
        gen_inst(&mut fb, rng, &mut else_pool);
    }
    let else_arg = get_or_mint(&mut fb, rng, &mut else_pool, &merge_ty);
    fb.br(merge_bb, vec![else_arg]);

    fb.switch_to_block(merge_bb);
    let mut merge_pool = entry_pool.clone();
    merge_pool.push((merge_param, merge_ty));
    for _ in 0..(1 + rng.bounded(4)) {
        gen_inst(&mut fb, rng, &mut merge_pool);
    }
    match &ret {
        None => fb.ret(vec![]),
        Some(t) => {
            let v = get_or_mint(&mut fb, rng, &mut merge_pool, t);
            fb.ret(vec![v]);
        }
    }
    let id = fb.build();
    FnSpec { id, params, ret }
}

fn gen_module_exec(seed: u64) -> (Module, Vec<FnSpec>) {
    let mut rng = Rng::new(seed);
    let mut mb = ModuleBuilder::new(format!("exec_mod_{seed}"));
    let n_funcs = 1 + rng.bounded(3);
    let mut specs = Vec::new();
    for i in 0..n_funcs {
        let spec = if rng.bool() {
            gen_function_cfg(&mut mb, &mut rng, i)
        } else {
            gen_function_linear(&mut mb, &mut rng, i)
        };
        specs.push(spec);
    }
    (mb.build(), specs)
}

/// Build deterministic arguments for a function from its parameter types.
fn build_args(params: &[Ty], rng: &mut Rng) -> Vec<InterpretValue> {
    params
        .iter()
        .map(|p| match p {
            Ty::Bool => InterpretValue::bool(rng.bool()),
            other => InterpretValue::int(other.clone(), rng.small())
                .expect("integer palette type is always constructible"),
        })
        .collect()
}

/// Structural-integrity codes that a validator-accepted module must never
/// trigger. The generator emits no calls, so the call-related structural
/// codes cannot arise; the three below are the ones the scalar/CFG core can
/// reach if (and only if) the interpreter and validator disagree about IR
/// well-formedness.
fn is_structural(code: InterpretErrorCode) -> bool {
    matches!(
        code,
        InterpretErrorCode::MalformedInstruction
            | InterpretErrorCode::MissingValue
            | InterpretErrorCode::MissingBlock
    )
}

/// Returns the number of functions that executed to a successful `Ok`
/// outcome, so the caller can assert the suite exercises real execution and
/// has not silently degraded into all-error paths.
fn check_exec(seed: u64) -> u32 {
    let mut ok_count = 0u32;
    let (module, specs) = gen_module_exec(seed);

    // Tie the differential to validation: the generator must only emit IR the
    // validator accepts, otherwise property 2 is vacuous.
    let errs = trust_ir_build::validate_module(&module);
    assert!(
        errs.is_empty(),
        "seed {seed}: generated module failed validation: {errs:?}"
    );

    let interp = Interpreter::with_module(&module);
    // A dedicated, fixed-seed RNG for argument values so the two executions
    // of a given function receive identical inputs.
    let mut arg_rng = Rng::new(seed ^ 0xA5A5_A5A5_A5A5_A5A5);

    for spec in &specs {
        let args = build_args(&spec.params, &mut arg_rng);

        let r1 = interp.execute_func(spec.id, args.clone());
        let r2 = interp.execute_func(spec.id, args.clone());
        assert_eq!(
            r1, r2,
            "seed {seed} fn {:?}: interpreter is nondeterministic across two identical calls",
            spec.id
        );

        match &r1 {
            Ok(outcome) => {
                ok_count += 1;
                let expected_arity = usize::from(spec.ret.is_some());
                assert_eq!(
                    outcome.returns.len(),
                    expected_arity,
                    "seed {seed} fn {:?}: return arity {} != declared {expected_arity}",
                    spec.id,
                    outcome.returns.len()
                );
                if let Some(ret_ty) = &spec.ret {
                    assert_eq!(
                        &outcome.returns[0].ty, ret_ty,
                        "seed {seed} fn {:?}: returned value type {} != declared {ret_ty}",
                        spec.id, outcome.returns[0].ty
                    );
                }
            }
            Err(e) => {
                assert!(
                    !is_structural(e.code),
                    "seed {seed} fn {:?}: validator accepted the module but the \
                     interpreter reported a structural error {:?}: {}",
                    spec.id,
                    e.code,
                    e.message
                );
            }
        }
    }
    ok_count
}

/// Build `fn() -> i32 { binop(op, i32, a, b) }`, execute it, and return the
/// i32 bit-pattern of the result (the interpreter's computed value).
fn run_i32_binop(op: BinOp, a: i32, b: i32) -> u32 {
    let mut mb = ModuleBuilder::new("oracle");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let va = fb.iconst(Ty::I32, a as i128);
    let vb = fb.iconst(Ty::I32, b as i128);
    let r = fb.binop(op, Ty::I32, va, vb);
    fb.ret(vec![r]);
    fb.build();
    let module = mb.build();
    let out = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .expect("oracle binop executes");
    out.returns[0].as_int().expect("int result").as_unsigned() as u32
}

/// SEMANTIC ORACLE (closes #83): the prior differential checked determinism,
/// no-structural-error, and return-shape but NEVER a single arithmetic VALUE,
/// and excluded shifts. Here plain Rust i32/u32 arithmetic is an INDEPENDENT
/// second reference implementation; every case (incl. shifts and negative
/// operands) cross-checks the interpreter's computed value against it.
#[test]
fn interpreter_arithmetic_matches_independent_rust_oracle() {
    // (op, a, b, expected-as-i32). Expected computed by hand/Rust as the oracle.
    let cases: &[(BinOp, i32, i32, i32)] = &[
        (BinOp::Add, 2147483647, 1, i32::MIN), // wraps
        (BinOp::Add, -5, 8, 3),
        (BinOp::Sub, i32::MIN, 1, i32::MAX), // wraps
        (BinOp::Mul, 65536, 65536, 0),       // overflow wraps to 0
        (BinOp::Mul, -3, 7, -21),
        (BinOp::SDiv, -7, 2, -3), // truncates toward zero
        (BinOp::SDiv, 7, -2, -3),
        (BinOp::SRem, -7, 3, -1), // sign of dividend
        (BinOp::SRem, 7, -3, 1),
        (BinOp::UDiv, -1, 2, (u32::MAX / 2) as i32), // -1 == u32::MAX
        (BinOp::URem, -1, 3, (u32::MAX % 3) as i32),
        (BinOp::And, -1, 0x0F0F0F0F, 0x0F0F0F0F),
        (BinOp::Or, 0x00FF00FF, 0xFF00FF00u32 as i32, -1),
        (BinOp::Xor, -1, -1, 0),
        (BinOp::Shl, 1, 31, i32::MIN),  // 1<<31
        (BinOp::LShr, -1, 1, i32::MAX), // logical: 0x7FFFFFFF
        (BinOp::AShr, -8, 1, -4),       // arithmetic: floor
        (BinOp::AShr, -1, 31, -1),      // sign-extends
    ];
    for &(op, a, b, expected) in cases {
        let got = run_i32_binop(op, a, b);
        assert_eq!(
            got, expected as u32,
            "interpreter {op:?}({a}, {b}) = {} (i32 {}), oracle expected {expected}",
            got, got as i32
        );
    }
}

#[test]
fn interpret_differential() {
    // Fixed seed range -> deterministic, never flakes.
    let mut total_ok = 0u32;
    for seed in 1..=1024u64 {
        total_ok += check_exec(seed);
    }
    // Guard the test's own value: if a future generator change degraded into
    // all-error paths, the Ok-branch assertions (return arity/type) would
    // never run and the differential would be vacuous. The vast majority of
    // generated functions execute cleanly, so this floor is very loose.
    assert!(
        total_ok > 500,
        "only {total_ok} functions executed to Ok; the generator is no longer \
         exercising real interpreter execution"
    );
}
