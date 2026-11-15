// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The ONE bit-vector statement of `ICmp` (`trust_ir::bv_meaning`), held to
//! the reference interpreter over every x86-64 vector-compare cell's lane type.
//!
//! The governed shapes are the `chc_x86` descriptors (16 x 8, 8 x 16, 4 x 32
//! and 2 x 64 bits). A cell is keyed by lane width and count alone, so each
//! shape runs at EVERY integer lane type of its width the validator admits,
//! signed and unsigned (`common::x86_cell_lane_tys`: `<16 x i8>` and
//! `<16 x u8>`, …, `<2 x i64>` and `<2 x u64>`; `<2 x isize>` / `<2 x usize>`
//! are refused as vector types). For each such vector type and every
//! `ICmpOp`, the interpreter runs three functions built from scalar lane
//! parameters:
//!
//! * `image(l…) -> u128` — the vector stored to an `Alloca` and loaded back as
//!   `u128`: the interpreter's BYTE IMAGE of the vector, the layout the
//!   statement's lane extraction (`vector_lane`, lane 0 least significant)
//!   claims;
//! * `cell(l…, r…) -> <n x bool>` — the `icmp` itself;
//! * `bits(l…, r…) -> i32` — `vector.mask_to_bits` of the `icmp`.
//!
//! and the statement is evaluated over [`Concrete`] on the two images. The
//! interpreter's lanes must be the statement's lanes; the spec side of the
//! cell (`chc_x86_vector_icmp_spec`) must carry each true lane as the all-ones
//! lane and each false lane as zero; and the lane-MSB compaction of that
//! physical mask must be the interpreter's `mask_to_bits`.
//!
//! Inputs: the 8-bit lane types cover EVERY byte pair, each pair at a lane that
//! rotates with the run; the wider shapes run the square of an edge set
//! (0, ±1, ±2, MIN, MIN+1, MAX, MAX-1) plus 512 seeded pairs. Evidence class:
//! test — exhaustive at 8 bits, sampled above.

mod common;

use trust_ir::Module;
use trust_ir::bv_meaning::{BvVector, Concrete, all_ones, vector_icmp};
use trust_ir::dialect::vector as vector_dialect;
use trust_ir::inst::ICmpOp;
use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, ValueId};
use trust_ir::{chc_x86_hardware_vector_contract_descriptors, chc_x86_vector_icmp_spec};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

const ALL_OPS: [ICmpOp; 10] = [
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
];

/// Wildcard-free: a new `ICmpOp` fails to compile here until it is listed.
fn listed(op: ICmpOp) -> bool {
    match op {
        ICmpOp::Eq
        | ICmpOp::Ne
        | ICmpOp::Ult
        | ICmpOp::Ule
        | ICmpOp::Ugt
        | ICmpOp::Uge
        | ICmpOp::Slt
        | ICmpOp::Sle
        | ICmpOp::Sgt
        | ICmpOp::Sge => ALL_OPS.contains(&op),
    }
}

/// One governed shape's functions, at one of its lane types.
struct Shape {
    elem: Ty,
    bits: u32,
    count: u32,
    module: Module,
    image: FuncId,
    /// `(op, cell, bits)` per `ICmpOp`.
    ops: Vec<(ICmpOp, FuncId, FuncId)>,
}

/// `v = zeroinitializer; v = insertelement v, lane_i, i` for each parameter.
fn build_vector(fb: &mut FunctionBuilder<'_>, vty: &Ty, lanes: &[ValueId]) -> ValueId {
    let zero = fb.const_value(
        vty.clone(),
        trust_ir::constant::Constant::Vector(
            (0..lanes.len())
                .map(|_| trust_ir::constant::Constant::Int(0))
                .collect(),
        ),
    );
    let mut v = zero;
    for (i, lane) in lanes.iter().enumerate() {
        let idx = fb.iconst(Ty::I64, i as i128);
        v = fb.insert_element(vty.clone(), v, idx, *lane);
    }
    v
}

fn shape(elem: Ty, bits: u32, count: u32) -> Shape {
    let vty = Ty::Vector(Box::new(elem.clone()), count);
    let mask_ty = Ty::Vector(Box::new(Ty::Bool), count);
    let mut mb = ModuleBuilder::new(format!("icmp_meaning_v{count}_{elem}"));
    let lanes = |n: u32| vec![elem.clone(); n as usize];

    let image_ft = mb.add_func_type(lanes(count), vec![Ty::U128]);
    let mut fb = mb.function("image", image_ft);
    let entry = fb.create_block();
    let params: Vec<ValueId> = (0..count)
        .map(|_| fb.add_block_param(entry, elem.clone()))
        .collect();
    fb.switch_to_block(entry);
    let v = build_vector(&mut fb, &vty, &params);
    let slot = fb.alloca(vty.clone());
    fb.store(vty.clone(), slot, v);
    let bits_image = fb.load(Ty::U128, slot);
    fb.ret(vec![bits_image]);
    let image = fb.build();

    let cell_ft = mb.add_func_type(lanes(2 * count), vec![mask_ty.clone()]);
    let bits_ft = mb.add_func_type(lanes(2 * count), vec![Ty::I32]);
    let mut ops = Vec::new();
    for op in ALL_OPS {
        assert!(listed(op));
        let mut ids = Vec::new();
        for (name, ft, compact) in [("cell", cell_ft, false), ("bits", bits_ft, true)] {
            let mut fb = mb.function(format!("{name}_{op}"), ft);
            let entry = fb.create_block();
            let params: Vec<ValueId> = (0..2 * count)
                .map(|_| fb.add_block_param(entry, elem.clone()))
                .collect();
            fb.switch_to_block(entry);
            let (l, r) = params.split_at(count as usize);
            let lv = build_vector(&mut fb, &vty, l);
            let rv = build_vector(&mut fb, &vty, r);
            let mask = fb.icmp(op, vty.clone(), lv, rv);
            let out = if compact {
                let results =
                    fb.dialect_op(vector_dialect::mask_to_bits(mask_ty.clone(), mask, Ty::I32));
                assert_eq!(results.len(), 1, "mask_to_bits has one result");
                results[0]
            } else {
                mask
            };
            fb.ret(vec![out]);
            ids.push(fb.build());
        }
        ops.push((op, ids[0], ids[1]));
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errs = trust_ir_build::validate_module(&module);
    assert!(errs.is_empty(), "<{count} x {elem}>: {errs:?}");
    Shape {
        elem,
        bits,
        count,
        module,
        image,
        ops,
    }
}

/// The interpreter's argument for a lane pattern at the lane type `elem`.
fn lane_arg(elem: &Ty, bits: u32, pattern: u128) -> InterpretValue {
    InterpretValue::int(
        elem.clone(),
        common::x86_cell_lane_value(elem, bits, pattern),
    )
    .expect("a lane value")
}

fn run(module: &Module, f: FuncId, args: Vec<InterpretValue>) -> InterpretValue {
    let outcome = Interpreter::with_module(module)
        .execute_func(f, args)
        .unwrap_or_else(|e| panic!("{f:?} must execute: {e:?}"));
    assert_eq!(outcome.returns.len(), 1);
    outcome.returns.into_iter().next().unwrap()
}

fn int_bits(v: &InterpretValue) -> u128 {
    match &v.kind {
        InterpretValueKind::Int(i) => i.raw,
        other => panic!("expected an integer, got {other:?}"),
    }
}

fn bool_lanes(v: &InterpretValue) -> Vec<bool> {
    let lanes = v.as_vector().expect("a vector result");
    lanes
        .iter()
        .map(|lane| lane.as_bool().expect("a bool lane"))
        .collect()
}

/// The lane-pair batches a shape runs: each batch is `(lhs lanes, rhs lanes)`.
fn batches(bits: u32, count: u32) -> Vec<(Vec<u128>, Vec<u128>)> {
    let mask = all_ones(bits);
    let mut pairs: Vec<(u128, u128)> = Vec::new();
    if bits == 8 {
        for a in 0..=255u128 {
            for b in 0..=255u128 {
                pairs.push((a, b));
            }
        }
        assert_eq!(
            pairs.len() % count as usize,
            0,
            "every byte pair, in full batches"
        );
    } else {
        let min = 1u128 << (bits - 1);
        let edges = [0, 1, 2, mask, mask - 1, min, min + 1, min - 1, min - 2];
        for a in edges {
            for b in edges {
                pairs.push((a, b));
            }
        }
        let mut state = 0x1CE5_0000_0000_0001u64 ^ u64::from(bits);
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            u128::from(state) | (u128::from(state.rotate_left(29)) << 64)
        };
        for _ in 0..512 {
            pairs.push((next() & mask, next() & mask));
        }
    }
    // Pair `p` of batch `k` sits at lane `(slot + k) % count`, so every lane
    // position sees pairs from every part of the space.
    let count = count as usize;
    pairs
        .chunks(count)
        .enumerate()
        .map(|(k, chunk)| {
            let mut lhs = vec![0u128; count];
            let mut rhs = vec![0u128; count];
            for (slot, (a, b)) in chunk.iter().enumerate() {
                let lane = (slot + k) % count;
                lhs[lane] = *a;
                rhs[lane] = *b;
            }
            (lhs, rhs)
        })
        .collect()
}

/// Every governed shape at every lane type of its width (a cell is keyed by
/// lane width and count alone; `common::x86_cell_lane_tys`).
fn governed_shapes() -> Vec<Shape> {
    let descriptors = chc_x86_hardware_vector_contract_descriptors();
    assert!(!descriptors.is_empty(), "the chc_x86 descriptors");
    descriptors
        .iter()
        .flat_map(|d| {
            common::x86_cell_lane_tys(d.element_bits, d.lane_count)
                .into_iter()
                .map(|elem| shape(elem, d.element_bits, d.lane_count))
        })
        .collect()
}

/// The statement IS the interpreter's `icmp`, lane by lane, on the
/// interpreter's own byte image; and the cell's spec side carries a true lane
/// as all-ones and a false lane as zero. Mutations, each red: swap `Ult`/`Ugt`
/// in `icmp_holds`; read lane `n-1-i` in `vector_lane`; make `Concrete::slt`
/// unsigned; make `physical_mask_lane`'s false lane all-ones.
#[test]
fn chc_x86_vector_icmp_spec_is_the_interpreters_icmp() {
    let mut checked = 0usize;
    for s in governed_shapes() {
        let (bits, count) = (s.bits, s.count);
        let total = bits * count;
        for (lhs, rhs) in batches(bits, count) {
            let args = |lanes: &[u128]| lanes.iter().map(|l| lane_arg(&s.elem, bits, *l)).collect();
            let li = int_bits(&run(&s.module, s.image, args(&lhs)));
            let ri = int_bits(&run(&s.module, s.image, args(&rhs)));
            let mut cell_args: Vec<InterpretValue> = args(&lhs);
            cell_args.extend(args(&rhs));
            for (op, cell, _) in &s.ops {
                let interp = bool_lanes(&run(&s.module, *cell, cell_args.clone()));
                let mut c = Concrete;
                let lb = c.bv_const(li, total);
                let rb = c.bv_const(ri, total);
                let stated = vector_icmp(&mut c, *op, bits, count, &lb, &rb);
                assert_eq!(
                    interp, stated,
                    "<{count} x {}> icmp {op}: lhs {lhs:?} rhs {rhs:?}",
                    s.elem
                );
                let spec = chc_x86_vector_icmp_spec(&mut c, bits, count, *op, &lb, &rb)
                    .expect("a governed cell has a spec");
                assert_eq!(spec.1, total);
                for (i, held) in interp.iter().enumerate() {
                    let lane = (spec.0 >> (i as u32 * bits)) & all_ones(bits);
                    assert_eq!(
                        lane,
                        if *held { all_ones(bits) } else { 0 },
                        "<{count} x {}> icmp {op} lane {i}",
                        s.elem
                    );
                }
                checked += count as usize;
            }
        }
    }
    // Every byte pair of `<16 x i8>` and of `<16 x u8>`, at least, for each of
    // the ten ops.
    assert!(
        checked >= 2 * 10 * 65536,
        "only {checked} lanes were compared"
    );
}

/// The physical mask's lane-MSB compaction is the interpreter's
/// `vector.mask_to_bits` of the logical mask: the published carrier and the
/// mask's one bit-level consumer agree. Mutation: carry a true lane as `1`
/// instead of all-ones (its most significant bit is then clear).
#[test]
fn physical_mask_compacts_to_the_interpreters_mask_to_bits() {
    for s in governed_shapes() {
        let (bits, count) = (s.bits, s.count);
        let total = bits * count;
        // Every 16th batch of the A-T1 inputs: the compaction is per lane, so
        // a sample over every lane position suffices.
        for (lhs, rhs) in batches(bits, count).into_iter().step_by(16) {
            let args = |lanes: &[u128]| lanes.iter().map(|l| lane_arg(&s.elem, bits, *l)).collect();
            let li = int_bits(&run(&s.module, s.image, args(&lhs)));
            let ri = int_bits(&run(&s.module, s.image, args(&rhs)));
            let mut cell_args: Vec<InterpretValue> = args(&lhs);
            cell_args.extend(args(&rhs));
            for (op, _, compact) in &s.ops {
                let interp = int_bits(&run(&s.module, *compact, cell_args.clone()));
                let mut c = Concrete;
                let lb = c.bv_const(li, total);
                let rb = c.bv_const(ri, total);
                let spec = chc_x86_vector_icmp_spec(&mut c, bits, count, *op, &lb, &rb)
                    .expect("a governed cell has a spec");
                let msb = (0..count).fold(0u128, |acc, i| {
                    acc | (((spec.0 >> (i * bits + bits - 1)) & 1) << i)
                });
                assert_eq!(
                    interp, msb,
                    "<{count} x {}> icmp {op}: lhs {lhs:?} rhs {rhs:?}",
                    s.elem
                );
            }
        }
    }
}
