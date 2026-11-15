// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// The W5a execution-corpus generator (`interpret_differential.rs`), shared
// with the W5b Lean-execution oracle (`lean_exec_differential.rs`, roadmap
// WS2.19) so both differentials measure ONE corpus: a seeded generator of
// VALID scalar/control-flow modules — integer/bool arithmetic (shifts and
// the checked `Overflow` trio included), comparisons, select, copy, diamond
// control flow, binding frames (WS2.8) and enum lane projections (WS2.2).
// Floats are excluded (the generator never mints them) so results stay
// structurally comparable; memory, atomics and casts are exercised against
// the codec by `module_roundtrip_fuzz.rs`.

use trust_ir::Module;
use trust_ir::constant::Constant;
use trust_ir::inst::{BinOp, BindingFrameDef, BindingSlot, ICmpOp, OverflowOp, UnOp};
use trust_ir::interpret::InterpretValue;
use trust_ir::ty::{EnumDef, EnumVariant, Ty};
use trust_ir::value::{BindingFrameId, EnumId, FuncId, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

use super::{Rng, int_ty};

/// What the test needs to call a generated function and check its result.
pub struct FnSpec {
    pub id: FuncId,
    pub params: Vec<Ty>,
    pub ret: Option<Ty>,
    /// The body contains a binding frame (WS2.8 coverage accounting).
    pub frames: bool,
}

/// Argument/return palette: integers plus `Bool`. No `Ptr` — passing a null
/// pointer into a body that dereferences it produces `UndefinedBehavior`,
/// which is a legitimate but noisy outcome that would obscure clean
/// execution coverage.
pub fn arg_ty(rng: &mut Rng) -> Ty {
    if rng.bounded(4) == 0 {
        Ty::Bool
    } else {
        int_ty(rng)
    }
}

/// Draw an in-scope value of the wanted type, minting a fresh constant if the
/// pool has none. Every entry is an already-defined SSA value, so any operand
/// is guaranteed in-scope and well-typed.
pub fn get_or_mint(
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

/// `enum GenE { a(i32, bool), b(u64), c }` — discriminants 0, 1, 2, so the
/// canonical tag repr is `u8`. Lane 1 is `i32` (a) or `u64` (b); lane 2 is
/// `bool` (a only); lane 0 is the `u8` tag.
pub fn gen_enum_def() -> EnumDef {
    EnumDef::new(
        EnumId::new(0),
        "GenE",
        vec![
            EnumVariant {
                name: "a".into(),
                fields: vec![Ty::I32, Ty::Bool],
                field_names: vec![],
            },
            EnumVariant {
                name: "b".into(),
                fields: vec![Ty::U64],
                field_names: vec![],
            },
            EnumVariant {
                name: "c".into(),
                fields: vec![],
                field_names: vec![],
            },
        ],
    )
}

pub fn gen_enum_ty() -> Ty {
    Ty::Enum(EnumId::new(0))
}

/// A `(lane, lane type)` pair of `GenE`.
pub type EnumLane = (u32, fn() -> Ty);

/// Every `(lane, type)` pair SOME variant of `GenE` carries — exactly the
/// set the validator admits for a projection.
pub const GEN_ENUM_LANES: &[EnumLane] = &[
    (0, || Ty::U8),
    (1, || Ty::I32),
    (1, || Ty::U64),
    (2, || Ty::Bool),
];

/// Construct a `GenE` variant with `Const`, then run one or two lane
/// projections over it. Three in four pick a lane of the ACTIVE variant (or
/// the tag); the rest pick any admitted pair, which may belong to another
/// variant — statically valid, dynamically undefined behaviour.
pub fn gen_enum_projection(
    fb: &mut FunctionBuilder<'_>,
    rng: &mut Rng,
    pool: &mut Vec<(ValueId, Ty)>,
) {
    let def = gen_enum_def();
    let variant = rng.bounded(3) as usize;
    let mut payload = vec![Constant::Int(variant as i128)];
    for field_ty in &def.variants[variant].fields {
        payload.push(match field_ty {
            Ty::Bool => Constant::Bool(rng.bool()),
            _ => Constant::Int(rng.small()),
        });
    }
    let mut e = fb.const_value(gen_enum_ty(), Constant::Aggregate(payload));
    for _ in 0..(1 + rng.bounded(2)) {
        let (lane, lane_ty) = if rng.bounded(4) != 0 {
            let fields = &def.variants[variant].fields;
            let lane = rng.bounded(fields.len() as u32 + 1);
            let ty = if lane == 0 {
                Ty::U8
            } else {
                fields[lane as usize - 1].clone()
            };
            (lane, ty)
        } else {
            let (lane, ty) = GEN_ENUM_LANES[rng.bounded(GEN_ENUM_LANES.len() as u32) as usize];
            (lane, ty())
        };
        // The tag lane is read-only (a variant is constructed whole).
        if lane >= 1 && rng.bounded(4) == 0 {
            let value = get_or_mint(fb, rng, pool, &lane_ty);
            e = fb.insert_field(gen_enum_ty(), e, lane, value);
        } else {
            let v = fb.extract_field(lane_ty.clone(), e, lane);
            pool.push((v, lane_ty));
        }
    }
}

pub fn gen_inst(fb: &mut FunctionBuilder<'_>, rng: &mut Rng, pool: &mut Vec<(ValueId, Ty)>) {
    match rng.bounded(8) {
        6 => gen_enum_projection(fb, rng, pool),
        7 => {
            // Checked arithmetic (WS2.19): the (result, overflowed) pair binds
            // two destinations positionally in both engines (WS2.24); the
            // flag joins the Bool pool so it steers later selects/branches.
            let t = int_ty(rng);
            let op = rng.one_of(&[
                OverflowOp::AddOverflow,
                OverflowOp::SubOverflow,
                OverflowOp::MulOverflow,
            ]);
            let a = get_or_mint(fb, rng, pool, &t);
            let b = get_or_mint(fb, rng, pool, &t);
            let (v, flag) = fb.overflow(op, t.clone(), a, b);
            pool.push((v, t));
            pool.push((flag, Ty::Bool));
        }
        0 => {
            let t = int_ty(rng);
            let v = fb.iconst(t.clone(), rng.small());
            pool.push((v, t));
        }
        1 => {
            // Integer binary op. Div/rem may divide by a zero constant and a
            // shift amount may reach the width; the interpreter reports both
            // as `UndefinedBehavior`, an accepted outcome (it does not panic).
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

/// Emit one binding-frame lifetime into the current block: open a frame of
/// 1..=3 integer slots, then a random mix of functional `bind_slot`s (from ANY
/// live handle of the lineage, so both chains and siblings occur) and
/// `load_slot`s (only of a slot bound ON THAT HANDLE, so the run stays on the
/// executing path), then close the lineage through a random handle. Loaded
/// values join the pool, so frame results feed later arithmetic.
pub fn gen_frame_group(
    fb: &mut FunctionBuilder<'_>,
    rng: &mut Rng,
    pool: &mut Vec<(ValueId, Ty)>,
    frame_idx: u32,
) {
    let n = 1 + rng.bounded(3);
    let slot_tys: Vec<Ty> = (0..n).map(|_| int_ty(rng)).collect();
    let opened = fb.open_frame(BindingFrameDef::new(
        BindingFrameId::new(frame_idx),
        format!("q{frame_idx}"),
        slot_tys
            .iter()
            .enumerate()
            .map(|(k, t)| BindingSlot::new(format!("s{k}"), t.clone()))
            .collect(),
    ));
    // Every live handle with the slots bound ON IT.
    let mut handles: Vec<(ValueId, Vec<bool>)> = vec![(opened, vec![false; n as usize])];
    for _ in 0..(1 + rng.bounded(6)) {
        if rng.bounded(3) < 2 {
            let (h, mut mask) = handles[rng.bounded(handles.len() as u32) as usize].clone();
            let k = rng.bounded(n);
            let v = get_or_mint(fb, rng, pool, &slot_tys[k as usize]);
            let bound = fb.bind_slot(h, k, v);
            mask[k as usize] = true;
            handles.push((bound, mask));
        } else {
            let readable: Vec<(ValueId, u32)> = handles
                .iter()
                .flat_map(|(h, mask)| {
                    mask.iter()
                        .enumerate()
                        .filter(|(_, b)| **b)
                        .map(move |(k, _)| (*h, k as u32))
                })
                .collect();
            if readable.is_empty() {
                continue;
            }
            let (h, k) = readable[rng.bounded(readable.len() as u32) as usize];
            let ty = slot_tys[k as usize].clone();
            let loaded = fb.load_slot(h, k, ty.clone());
            pool.push((loaded, ty));
        }
    }
    let (close_via, _) = handles[rng.bounded(handles.len() as u32) as usize];
    fb.close_frame(close_via);
}

pub fn gen_signature(rng: &mut Rng) -> (Vec<Ty>, Option<Ty>) {
    let n_params = rng.bounded(4);
    let params: Vec<Ty> = (0..n_params).map(|_| arg_ty(rng)).collect();
    let ret = if rng.bounded(4) == 0 {
        None
    } else {
        Some(arg_ty(rng))
    };
    (params, ret)
}

pub fn gen_function_linear(mb: &mut ModuleBuilder, rng: &mut Rng, idx: u32) -> FnSpec {
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
    let frames = rng.bounded(3) == 0;
    if frames {
        for frame_idx in 0..(1 + rng.bounded(2)) {
            gen_frame_group(&mut fb, rng, &mut pool, frame_idx);
            gen_inst(&mut fb, rng, &mut pool);
        }
    }
    match &ret {
        None => fb.ret(vec![]),
        Some(t) => {
            let v = get_or_mint(&mut fb, rng, &mut pool, t);
            fb.ret(vec![v]);
        }
    }
    let id = fb.build();
    FnSpec {
        id,
        params,
        ret,
        frames,
    }
}

/// Diamond CFG: entry conditionally branches to then/else, both branch to a
/// merge block carrying a block parameter. Dominance is respected exactly as
/// in the codec generator: entry-defined values seed the successor pools;
/// then/else locals do not dominate merge.
pub fn gen_function_cfg(mb: &mut ModuleBuilder, rng: &mut Rng, idx: u32) -> FnSpec {
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
    // WS2.8: optionally carry a binding-frame handle across the diamond. The
    // entry binds slot 0; each arm may rebind a slot and passes ITS handle to
    // a `Ptr` merge parameter; the merge reads slot 0 (bound on every path)
    // and closes the lineage through the parameter.
    let frames = rng.bounded(3) == 0;
    let frame_slot_tys: Vec<Ty> = if frames {
        (0..(1 + rng.bounded(3))).map(|_| int_ty(rng)).collect()
    } else {
        Vec::new()
    };
    let merge_frame = frames.then(|| fb.add_block_param(merge_bb, Ty::Ptr));

    let mut entry_pool: Vec<(ValueId, Ty)> = Vec::new();
    for p in &params {
        let v = fb.add_block_param(entry, p.clone());
        entry_pool.push((v, p.clone()));
    }
    fb.switch_to_block(entry);
    for _ in 0..(2 + rng.bounded(6)) {
        gen_inst(&mut fb, rng, &mut entry_pool);
    }
    let entry_frame = frames.then(|| {
        let opened = fb.open_frame(BindingFrameDef::new(
            BindingFrameId::new(0),
            "diamond",
            frame_slot_tys
                .iter()
                .enumerate()
                .map(|(k, t)| BindingSlot::new(format!("s{k}"), t.clone()))
                .collect(),
        ));
        let v = get_or_mint(&mut fb, rng, &mut entry_pool, &frame_slot_tys[0]);
        fb.bind_slot(opened, 0, v)
    });
    let cond = get_or_mint(&mut fb, rng, &mut entry_pool, &Ty::Bool);
    fb.condbr(cond, then_bb, vec![], else_bb, vec![]);

    for arm_bb in [then_bb, else_bb] {
        fb.switch_to_block(arm_bb);
        let mut arm_pool = entry_pool.clone();
        for _ in 0..(1 + rng.bounded(4)) {
            gen_inst(&mut fb, rng, &mut arm_pool);
        }
        let mut args = vec![get_or_mint(&mut fb, rng, &mut arm_pool, &merge_ty)];
        if let Some(handle) = entry_frame {
            // Rebind a random slot on this arm (or pass the entry handle on).
            let carried = if rng.bool() {
                let k = rng.bounded(frame_slot_tys.len() as u32);
                let v = get_or_mint(&mut fb, rng, &mut arm_pool, &frame_slot_tys[k as usize]);
                fb.bind_slot(handle, k, v)
            } else {
                handle
            };
            args.push(carried);
        }
        fb.br(merge_bb, args);
    }

    fb.switch_to_block(merge_bb);
    let mut merge_pool = entry_pool.clone();
    merge_pool.push((merge_param, merge_ty));
    if let Some(handle) = merge_frame {
        let ty = frame_slot_tys[0].clone();
        let loaded = fb.load_slot(handle, 0, ty.clone());
        merge_pool.push((loaded, ty));
        fb.close_frame(handle);
    }
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
    FnSpec {
        id,
        params,
        ret,
        frames,
    }
}

pub fn gen_module_exec(seed: u64) -> (Module, Vec<FnSpec>) {
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
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.add_enum(gen_enum_def());
    (module, specs)
}

/// An integer argument: usually a small magnitude, one time in four an edge
/// of the type's range (`0`, `1`, all-ones / `-1`, the sign bit / `MIN`,
/// `MAX`), so signed `MIN / -1`, `MIN - 1`, shift-by-width and the overflow
/// flags are reached (the W5b test idea's named cases). `InterpretValue::int`
/// masks the literal to the type's width, so the same `i128` spells the edge
/// of every width and signedness.
pub fn int_arg(ty: &Ty, rng: &mut Rng) -> InterpretValue {
    let bits = ty.bit_width().expect("integer palette type has a width");
    let value = if rng.bounded(4) == 0 {
        let sign_bit = 1i128 << (bits - 1);
        match rng.bounded(5) {
            0 => 0,
            1 => 1,
            2 => -1,
            3 => sign_bit.wrapping_neg(),
            _ => sign_bit.wrapping_sub(1),
        }
    } else {
        rng.small()
    };
    InterpretValue::int(ty.clone(), value).expect("integer palette type is always constructible")
}

/// Build deterministic arguments for a function from its parameter types.
pub fn build_args(params: &[Ty], rng: &mut Rng) -> Vec<InterpretValue> {
    params
        .iter()
        .map(|p| match p {
            Ty::Bool => InterpretValue::bool(rng.bool()),
            other => int_arg(other, rng),
        })
        .collect()
}
