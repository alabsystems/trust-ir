// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Randomized module-level codec round-trip + idempotency property test.
//
// The fixed-corpus harness in `conformance.rs` proves that *known* modules
// survive every serialization format byte-for-byte against checked-in
// goldens. This file is its complement: a seeded generator emits a wide,
// novel space of VALID modules (functions, the scalar instruction set,
// memory ops, atomics, tuple aggregates, pointer arithmetic, multi-block
// diamond control flow with block parameters and branch arguments, and
// scalar globals) and asserts the format-agnostic invariants no
// module-specific golden can capture:
//
//   * validate_module(m)               is empty            (generator is sound)
//   * deserialize(serialize(m))        == m                (binary is lossless)
//   * serialize(deserialize(serialize(m))) == serialize(m) (binary is idempotent)
//   * from_json(to_json(m))            == m                (serde JSON lossless)
//   * from_msgpack(to_msgpack(m))      == m                (MessagePack lossless)
//   * canonical(parse(canonical(m)))   == canonical(m)     (text is idempotent)
//
// The binary idempotency check directly guards the bug class fixed in
// commit 94bcc1e ("v4 binary round-trip desync and idempotency"): a desync
// between the string-interning write pass and the read pass only manifests
// on structurally diverse modules, which the fixed corpus enumerates by
// hand but cannot exhaustively cover.
//
// Why handwritten (seeded xorshift64) instead of proptest / cargo-fuzz:
// the `trust-ir` crate is zero-required-dep by policy (CLAUDE.md feature
// table). A seeded generator is deterministic across platforms and never
// flakes — the core property of a useful regression test. We deliberately
// exclude floating-point values: NaN breaks structural `==`, and float
// round-trip is already covered by `aggregate_constant_fuzz.rs` and the
// fixed float-instruction fixtures.

use trust_ir::constant::Constant;
use trust_ir::inst::{AtomicRMWOp, BinOp, CastOp, ICmpOp, Ordering, UnOp};
use trust_ir::ty::Ty;
use trust_ir::value::ValueId;
use trust_ir::{Global, Linkage, Module};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

mod common;
use common::{Rng, int_ty};

// ---------------------------------------------------------------------------
// Type palette. Floats are excluded on purpose (see header).
// ---------------------------------------------------------------------------

/// Parameter / return type palette: integers plus the always-mintable
/// scalar non-aggregates `Bool` and `Ptr`.
fn scalar_ty(rng: &mut Rng) -> Ty {
    match rng.bounded(12) {
        10 => Ty::Bool,
        11 => Ty::Ptr,
        _ => int_ty(rng),
    }
}

/// Validation-safe integer cast triples `(op, src, dst)`. Width/sign
/// relationships mirror the hand-checked pairs in `build_inst_arithmetic`.
fn cast_triple(rng: &mut Rng) -> (CastOp, Ty, Ty) {
    match rng.bounded(12) {
        0 => (CastOp::Trunc, Ty::I64, Ty::I32),
        1 => (CastOp::Trunc, Ty::I32, Ty::I16),
        2 => (CastOp::Trunc, Ty::I16, Ty::I8),
        3 => (CastOp::Trunc, Ty::U64, Ty::U32),
        4 => (CastOp::ZExt, Ty::I8, Ty::I32),
        5 => (CastOp::ZExt, Ty::I32, Ty::I64),
        6 => (CastOp::ZExt, Ty::U8, Ty::U32),
        7 => (CastOp::ZExt, Ty::U32, Ty::U64),
        8 => (CastOp::SExt, Ty::I8, Ty::I32),
        9 => (CastOp::SExt, Ty::I16, Ty::I64),
        10 => (CastOp::Bitcast, Ty::I32, Ty::U32),
        _ => (CastOp::Bitcast, Ty::I64, Ty::U64),
    }
}

// Memory-ordering palettes. We restrict to the orderings each op is
// semantically permitted to carry (LLVM rules) rather than the full set the
// validator structurally accepts, so the generated IR stays meaningful and not
// merely well-formed: loads cannot be `Release`/`AcqRel`, stores cannot be
// `Acquire`/`AcqRel`, fences cannot be `Relaxed`. RMW accepts all five.
fn load_ordering(rng: &mut Rng) -> Ordering {
    rng.one_of(&[Ordering::Relaxed, Ordering::Acquire, Ordering::SeqCst])
}

fn store_ordering(rng: &mut Rng) -> Ordering {
    rng.one_of(&[Ordering::Relaxed, Ordering::Release, Ordering::SeqCst])
}

fn rmw_ordering(rng: &mut Rng) -> Ordering {
    rng.one_of(&[
        Ordering::Relaxed,
        Ordering::Acquire,
        Ordering::Release,
        Ordering::AcqRel,
        Ordering::SeqCst,
    ])
}

fn fence_ordering(rng: &mut Rng) -> Ordering {
    rng.one_of(&[
        Ordering::Acquire,
        Ordering::Release,
        Ordering::AcqRel,
        Ordering::SeqCst,
    ])
}

// ---------------------------------------------------------------------------
// Typed value pool: every entry is an already-defined SSA value of a known
// type, so any operand drawn from it is guaranteed in-scope and well-typed.
// ---------------------------------------------------------------------------

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
        Ty::Ptr => fb.null_ptr(),
        other => fb.iconst(other.clone(), rng.small()),
    };
    pool.push((minted, want.clone()));
    minted
}

fn gen_inst(fb: &mut FunctionBuilder<'_>, rng: &mut Rng, pool: &mut Vec<(ValueId, Ty)>) {
    match rng.bounded(12) {
        0 => {
            // Fresh integer constant.
            let t = int_ty(rng);
            let v = fb.iconst(t.clone(), rng.small());
            pool.push((v, t));
        }
        1 => {
            // Integer binary op (both operands share the result type).
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
                BinOp::Shl,
                BinOp::LShr,
                BinOp::AShr,
            ]);
            let a = get_or_mint(fb, rng, pool, &t);
            let b = get_or_mint(fb, rng, pool, &t);
            let v = fb.binop(op, t.clone(), a, b);
            pool.push((v, t));
        }
        2 => {
            // Unary op.
            let t = int_ty(rng);
            let op = rng.one_of(&[UnOp::Neg, UnOp::Not]);
            let a = get_or_mint(fb, rng, pool, &t);
            let v = fb.unop(op, t.clone(), a);
            pool.push((v, t));
        }
        3 => {
            // Integer comparison -> Bool.
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
            // Conditional select.
            let t = int_ty(rng);
            let c = get_or_mint(fb, rng, pool, &Ty::Bool);
            let a = get_or_mint(fb, rng, pool, &t);
            let b = get_or_mint(fb, rng, pool, &t);
            let v = fb.select(t.clone(), c, a, b);
            pool.push((v, t));
        }
        5 => {
            // Value copy.
            let t = int_ty(rng);
            let a = get_or_mint(fb, rng, pool, &t);
            let v = fb.copy(t.clone(), a);
            pool.push((v, t));
        }
        6 => {
            // Width/sign-safe integer cast.
            let (op, src, dst) = cast_triple(rng);
            let a = get_or_mint(fb, rng, pool, &src);
            let v = fb.cast(op, src, dst.clone(), a);
            pool.push((v, dst));
        }
        7 => {
            // Atomic stack-slot round-trip: alloca, atomic_store, fence,
            // atomic_load.
            let t = int_ty(rng);
            let slot = fb.alloca(t.clone());
            let init = get_or_mint(fb, rng, pool, &t);
            fb.atomic_store(t.clone(), slot, init, store_ordering(rng));
            fb.fence(fence_ordering(rng));
            let loaded = fb.atomic_load(t.clone(), slot, load_ordering(rng));
            pool.push((slot, Ty::Ptr));
            pool.push((loaded, t));
        }
        8 => {
            // Atomic read-modify-write returning the prior value.
            let t = int_ty(rng);
            let slot = fb.alloca(t.clone());
            let init = get_or_mint(fb, rng, pool, &t);
            fb.atomic_store(t.clone(), slot, init, Ordering::Relaxed);
            let op = rng.one_of(&[
                AtomicRMWOp::Xchg,
                AtomicRMWOp::Add,
                AtomicRMWOp::Sub,
                AtomicRMWOp::And,
                AtomicRMWOp::Or,
                AtomicRMWOp::Xor,
                AtomicRMWOp::Max,
                AtomicRMWOp::Min,
                AtomicRMWOp::UMax,
                AtomicRMWOp::UMin,
            ]);
            let operand = get_or_mint(fb, rng, pool, &t);
            let old = fb.atomic_rmw(op, t.clone(), slot, operand, rmw_ordering(rng));
            pool.push((slot, Ty::Ptr));
            pool.push((old, t));
        }
        9 => {
            // Stack slot round-trip: alloca, store, load.
            let t = int_ty(rng);
            let slot = fb.alloca(t.clone());
            let x = get_or_mint(fb, rng, pool, &t);
            fb.store(t.clone(), slot, x);
            let loaded = fb.load(t.clone(), slot);
            pool.push((slot, Ty::Ptr));
            pool.push((loaded, t));
        }
        10 => {
            // Tuple aggregate: undef -> insert_field -> extract_field. Tuple
            // types are structural (`Ty::Tuple(Vec<Ty>)`) and need no
            // module-level type-table interning, unlike `Ty::Array`.
            let arity = 2 + rng.bounded(2);
            let field_tys: Vec<Ty> = (0..arity).map(|_| int_ty(rng)).collect();
            let tup = Ty::Tuple(field_tys.clone());
            let agg0 = fb.undef(tup.clone());
            let field = rng.bounded(arity);
            let ftype = field_tys[field as usize].clone();
            let x = get_or_mint(fb, rng, pool, &ftype);
            let agg1 = fb.insert_field(tup.clone(), agg0, field, x);
            let got = fb.extract_field(ftype.clone(), agg1, field);
            pool.push((got, ftype));
        }
        _ => {
            // Pointer arithmetic: GEP off a fresh stack slot.
            let t = int_ty(rng);
            let slot = fb.alloca(t.clone());
            let idx = fb.iconst(Ty::I64, (rng.next_u64() % 8) as i128);
            let p = fb.gep(t, slot, vec![idx]);
            pool.push((slot, Ty::Ptr));
            pool.push((p, Ty::Ptr));
        }
    }
}

/// v23 producer provenance: ~2-in-3 functions carry a tag, cycling through
/// the full vocabulary — including the `Other` escape (with a non-trivial
/// string) — so every wire tag rides the randomized round-trip.
fn gen_producer(rng: &mut Rng) -> Option<trust_ir::Producer> {
    use trust_ir::Producer;
    match rng.bounded(9) {
        0 => Some(Producer::TRust),
        1 => Some(Producer::Clean),
        2 => Some(Producer::TrustIr),
        3 => Some(Producer::TSwift),
        4 => Some(Producer::TC),
        5 => Some(Producer::Other(format!(
            "fuzz frontend #{} \"quoted\"",
            rng.bounded(1000)
        ))),
        _ => None,
    }
}

fn gen_function(mb: &mut ModuleBuilder, rng: &mut Rng, idx: u32) {
    let n_params = rng.bounded(4);
    let params: Vec<Ty> = (0..n_params).map(|_| scalar_ty(rng)).collect();
    // 1-in-4 functions return Unit (empty return list).
    let ret_ty = if rng.bounded(4) == 0 {
        None
    } else {
        Some(scalar_ty(rng))
    };
    let returns = ret_ty.iter().cloned().collect::<Vec<_>>();

    let ft = mb.add_func_type(params.clone(), returns);
    let mut fb = mb.function(format!("f{idx}"), ft);
    if let Some(producer) = gen_producer(rng) {
        fb.set_producer(producer);
    }
    let entry = fb.create_block();
    let mut pool: Vec<(ValueId, Ty)> = Vec::new();
    for p in &params {
        let v = fb.add_block_param(entry, p.clone());
        pool.push((v, p.clone()));
    }
    fb.switch_to_block(entry);

    let n_insts = 4 + rng.bounded(16);
    for _ in 0..n_insts {
        gen_inst(&mut fb, rng, &mut pool);
    }

    match &ret_ty {
        None => fb.ret(vec![]),
        Some(t) => {
            let v = get_or_mint(&mut fb, rng, &mut pool, t);
            fb.ret(vec![v]);
        }
    }
    fb.build();
}

/// A diamond control-flow function: `entry` conditionally branches to `then` /
/// `else`, both of which branch to a `merge` block that carries a block
/// parameter (the SSA-form replacement for a phi node). This exercises codec
/// paths the linear shape never reaches — multiple blocks, `CondBr`/`Br`
/// terminators, block parameters, and branch arguments — while respecting SSA
/// dominance: `entry` dominates every block, so its values seed the successor
/// pools, but `then`/`else` locals do NOT dominate `merge` and are excluded
/// from the merge pool.
fn gen_function_cfg(mb: &mut ModuleBuilder, rng: &mut Rng, idx: u32) {
    let n_params = rng.bounded(4);
    let params: Vec<Ty> = (0..n_params).map(|_| scalar_ty(rng)).collect();
    let ret_ty = if rng.bounded(4) == 0 {
        None
    } else {
        Some(scalar_ty(rng))
    };
    let returns = ret_ty.iter().cloned().collect::<Vec<_>>();

    let ft = mb.add_func_type(params.clone(), returns);
    let mut fb = mb.function(format!("f{idx}"), ft);
    if let Some(producer) = gen_producer(rng) {
        fb.set_producer(producer);
    }

    let entry = fb.create_block();
    let then_bb = fb.create_block();
    let else_bb = fb.create_block();
    let merge_bb = fb.create_block();

    // The merge block carries one int-typed parameter that both predecessors
    // supply as a branch argument.
    let merge_ty = int_ty(rng);
    let merge_param = fb.add_block_param(merge_bb, merge_ty.clone());

    // Entry dominates all blocks, so values defined here form the shared base
    // pool for every successor.
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

    // `then` / `else` each clone the entry pool, may add locals that dominate
    // only themselves, and pass a `merge_ty` value as the branch argument.
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

    // `merge`: entry-dominating values plus the merge block parameter are in
    // scope; `then`/`else` locals are not.
    fb.switch_to_block(merge_bb);
    let mut merge_pool = entry_pool.clone();
    merge_pool.push((merge_param, merge_ty));
    for _ in 0..(1 + rng.bounded(4)) {
        gen_inst(&mut fb, rng, &mut merge_pool);
    }
    match &ret_ty {
        None => fb.ret(vec![]),
        Some(t) => {
            let v = get_or_mint(&mut fb, rng, &mut merge_pool, t);
            fb.ret(vec![v]);
        }
    }
    fb.build();
}

fn gen_module(seed: u64) -> Module {
    let mut rng = Rng::new(seed);
    let mut mb = ModuleBuilder::new(format!("fuzz_mod_{seed}"));

    let n_funcs = 1 + rng.bounded(3);
    for i in 0..n_funcs {
        // Mix linear and diamond-CFG function shapes.
        if rng.bool() {
            gen_function_cfg(&mut mb, &mut rng, i);
        } else {
            gen_function(&mut mb, &mut rng, i);
        }
    }

    let mut m = mb.build();

    // A few scalar globals exercise the global + constant-pool codec paths.
    let n_globals = rng.bounded(3);
    for g in 0..n_globals {
        let t = int_ty(&mut rng);
        m.globals.push(Global {
            name: format!("G{g}"),
            ty: t,
            mutable: rng.bool(),
            initializer: Some(Constant::Int(rng.small())),
            linkage: rng.one_of(&[Linkage::Internal, Linkage::External, Linkage::Private]),
            tls: None,
            align: None,
        });
    }

    m
}

fn check_module(seed: u64) {
    let m = gen_module(seed);

    // The generator must only ever emit well-formed IR.
    let errs = trust_ir_build::validate_module(&m);
    assert!(
        errs.is_empty(),
        "seed {seed}: generated module failed validation: {errs:?}"
    );

    // Binary: lossless AND idempotent (the 94bcc1e regression target).
    let b1 = trust_ir::binary::serialize_module(&m);
    let m2 = trust_ir::binary::deserialize_module(&b1)
        .unwrap_or_else(|e| panic!("seed {seed}: binary deserialize failed: {e:?}"));
    assert_eq!(m, m2, "seed {seed}: binary round-trip changed the module");
    let b2 = trust_ir::binary::serialize_module(&m2);
    assert_eq!(
        b1, b2,
        "seed {seed}: binary serialize is not idempotent across a round-trip"
    );

    // serde JSON.
    let json = serde_json::to_string(&m).expect("json serialize");
    let mj: Module = serde_json::from_str(&json).expect("json deserialize");
    assert_eq!(m, mj, "seed {seed}: JSON round-trip lost information");

    // serde MessagePack.
    let mp = rmp_serde::to_vec(&m).expect("msgpack serialize");
    let mm: Module = rmp_serde::from_slice(&mp).expect("msgpack deserialize");
    assert_eq!(
        m, mm,
        "seed {seed}: MessagePack round-trip lost information"
    );

    // Canonical text: format / parse / format is idempotent.
    let t1 = trust_ir::format::canonical(&m);
    let mt = trust_ir::parser::parse_module(&t1)
        .unwrap_or_else(|e| panic!("seed {seed}: text parse failed: {e:?}"));
    let t2 = trust_ir::format::canonical(&mt);
    assert_eq!(
        t1, t2,
        "seed {seed}: canonical text is not idempotent across a round-trip"
    );
}

#[test]
fn module_roundtrip_fuzz() {
    // Fixed seed range → deterministic, never flakes. Sized to densely
    // cover the expanded instruction/CFG space while staying sub-second.
    for seed in 1..=1024u64 {
        check_module(seed);
    }
}
