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
//   * parse(text_checked(m))           == m                (text is EXACT:
//     the module's own SSA value ids and block order survive print -> parse)
//
// That last leg is the id-preservation property. Every other text leg
// canonicalizes BOTH sides, so a printer that renumbers SSA values passes
// them all while silently handing a consumer a module the producer never
// built (a `bin -> text -> bin` transport that is not the identity, with an
// EMPTY `text_losses` — the false-clean direction). `non_canonical_seeds`
// below fails the run if the generated corpus ever stops containing modules
// that are not already canonical, which is what would make it vacuous.
//
// The `parse_never_panics` leg (roadmap WS4.1, finding F-066) adds the text
// parser's totality over UTF-8: for every corpus `.trust_ir` fixture and the
// canonical text of every seed, a multi-byte character inserted at every line
// start, before every newline and after every `;` yields `Ok` or a
// `ParseError` — never a panic, never the fallible cursor's `internal:
// cursor split` refusal — and one inserted inside a comment changes nothing.
// Its unit twins live in the `text_parser_utf8` module (tests/text_parser_utf8/).
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

mod text_parser_utf8;

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

    // WS4.5: a switch carrying the producer's `exhaustive_enum_unreachable`
    // hint, on ~half the seeds. The validator admits it on a plain integer
    // switch whose default is a dead `[unreachable]` arm with distinct cases;
    // the builder never sets the flag, so it is patched in after `build`.
    let exhaustive_switch = rng.bool().then(|| {
        let name = format!("fsw{n_funcs}");
        let ft = mb.add_func_type(vec![Ty::U8], vec![]);
        let mut fb = mb.function(name.clone(), ft);
        let entry = fb.create_block();
        let (a, b, dead) = (fb.create_block(), fb.create_block(), fb.create_block());
        let tag = fb.add_block_param(entry, Ty::U8);
        fb.switch_to_block(entry);
        let case = |value: i128, target| trust_ir::inst::SwitchCase {
            value: Constant::Int(value),
            target,
            args: vec![],
        };
        fb.switch(tag, vec![case(0, a), case(1, b)], dead, vec![]);
        for bb in [a, b] {
            fb.switch_to_block(bb);
            fb.ret(vec![]);
        }
        fb.switch_to_block(dead);
        fb.unreachable();
        fb.build();
        name
    });

    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    if let Some(name) = exhaustive_switch {
        let f = m.functions.iter_mut().find(|f| f.name == name).unwrap();
        for node in f.blocks.iter_mut().flat_map(|b| &mut b.body) {
            if let trust_ir::inst::Inst::Switch {
                exhaustive_enum_unreachable,
                ..
            } = &mut node.inst
            {
                *exhaustive_enum_unreachable = true;
            }
        }
    }

    // v45 (WS3.10): function symbol attributes on ~1-in-3 functions. The
    // section pool carries every character the text grammar must escape —
    // `"`, `\`, `;`, a newline, and a forged directive — so the quoted
    // spelling rides the randomized round-trip laws. The builder's functions
    // are `External`, so every visibility is admissible.
    for f in &mut m.functions {
        if rng.bounded(3) == 0 {
            f.visibility = rng.one_of(&[
                trust_ir::Visibility::Default,
                trust_ir::Visibility::Hidden,
                trust_ir::Visibility::Protected,
            ]);
            f.section = match rng.bounded(6) {
                0 => Some("__TEXT,\"q\"".to_string()),
                1 => Some("back\\slash".to_string()),
                2 => Some(".text;#visibility: hidden".to_string()),
                3 => Some("line\nbreak ; #retained".to_string()),
                4 => Some(".text.hot".to_string()),
                _ => None,
            };
            f.retained = rng.bool();
        }
    }

    // v45 (WS3.11): per-slot ABI facts on ~1-in-3 functions. Every fact is
    // placed where the validator admits it — an extension only on a
    // sub-64-bit integer / `Bool` slot, `direct` anywhere, `cast` lanes that
    // cover a scalar slot — so `validate_module` stays empty and the flag
    // bits, the pass-mode record and the `#ret_attrs:` line all ride the
    // round-trip laws. A fact lands on the return slot only when the
    // signature returns exactly one value.
    let sigs: Vec<Option<trust_ir::ty::FuncTy>> = m
        .functions
        .iter()
        .map(|f| m.func_type(f.ty).cloned())
        .collect();
    for (f, sig) in m.functions.iter_mut().zip(sigs) {
        let Some(sig) = sig else { continue };
        if rng.bounded(3) != 0 {
            continue;
        }
        let narrow = |ty: &Ty| {
            matches!(
                ty,
                Ty::I8 | Ty::I16 | Ty::I32 | Ty::U8 | Ty::U16 | Ty::U32 | Ty::Bool | Ty::Char
            )
        };
        let decorate = |ty: &Ty, rng: &mut Rng| {
            let mut pa = trust_ir::ParamAttrs::default();
            if narrow(ty) {
                pa.ext = rng.one_of(&[
                    trust_ir::ArgExt::None,
                    trust_ir::ArgExt::ZeroExt,
                    trust_ir::ArgExt::SignExt,
                ]);
            }
            pa.pass = match rng.bounded(4) {
                0 => Some(trust_ir::PassMode::Direct),
                // Lanes sized to the slot: two `u64` lanes for a 128-bit
                // slot, one for anything narrower (`Ptr` included).
                1 => Some(trust_ir::PassMode::Cast {
                    pieces: if matches!(ty, Ty::I128 | Ty::U128) {
                        vec![Ty::U64, Ty::U64]
                    } else {
                        vec![Ty::U64]
                    },
                }),
                _ => None,
            };
            pa
        };
        f.attrs.params = sig.params.iter().map(|ty| decorate(ty, &mut rng)).collect();
        if let [ret] = sig.returns.as_slice() {
            f.attrs.ret = decorate(ret, &mut rng);
        }
    }

    // v43: on half the seeds, an UNUSED pinned handle in the type table. It
    // is the one handle occurrence the generator can emit while keeping
    // `validate_module` empty (no declaration, no body touches it), and it
    // flips the writer to header 43 so the tag-38 path, its two pooled
    // strings and the quoted text spelling all ride the round-trip laws.
    if rng.bool() {
        m.types.push(Ty::handle("Nat", "trust_bignum::Nat"));
    }

    // v31 / WS4.5 (enum half): producer-supplied enum LAYOUT DESCRIPTORS, one
    // per tag encoding, on ~half the seeds each. The descriptor is normative
    // where present, so it is exactly the kind of field a text grammar must
    // either carry or refuse — and the laws above are what make a silent drop
    // fail: `canonical_checked` must be `Ok` (so the field is not a loss) AND
    // the parsed module must equal `canonicalize(m)` field for field (so it is
    // not dropped). A new field on `EnumLayoutDescriptor` /
    // `EnumTagEncoding` without a text spelling fails here on every seed that
    // emits one.
    //
    // Every shape below is one the validator admits on a target-free module
    // (`target_has_canonical_scalar_layout` is true without target_info):
    // aligned lanes inside the declared size, no tag/payload overlap, and for
    // the niche encoding an interval that covers every inhabited variant with
    // the untagged variant's payload covering the lane.
    {
        use trust_ir::ty::{
            EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant,
        };
        // WS4.5: per-field source names on ~half the seeds, parallel to the
        // fields (the only shape the validator admits), drawn from a pool that
        // includes the EMPTY name (`: ty`) and a name that must be quoted.
        let names = rng.bool();
        let name_pool = ["value", "", "needs quoting", "0"];
        let first_name = rng.bounded(4) as usize;
        let mut drawn = 0usize;
        let mut variant = |name: &str, fields: Vec<Ty>| EnumVariant {
            name: name.to_string(),
            field_names: if names {
                fields
                    .iter()
                    .map(|_| {
                        drawn += 1;
                        name_pool[(first_name + drawn) % name_pool.len()].to_string()
                    })
                    .collect()
            } else {
                Vec::new()
            },
            fields,
        };
        if rng.bool() {
            // DIRECT, with the tag lane placed either before or after the
            // 8-byte payload so the printed offsets are not all zero — a
            // parser that invented them positionally would disagree.
            let repr = rng.one_of(&[EnumTagRepr::U8, EnumTagRepr::U32, EnumTagRepr::U64]);
            let tag_last = rng.bool();
            let (tag_offset, payload_offset) = if tag_last { (8, 0) } else { (0, 8) };
            let id = trust_ir::value::EnumId::new(u32::try_from(m.enums.len()).unwrap());
            m.add_enum(EnumDef {
                id,
                name: format!("FuzzDirect{}", id.index()),
                variants: vec![variant("payload", vec![Ty::U64]), variant("empty", vec![])],
                discriminants: Vec::new(),
                repr: Some(repr),
                layout: Some(EnumLayoutDescriptor {
                    encoding: EnumTagEncoding::Direct { tag_offset },
                    size: 16,
                    align: 8,
                    variant_field_offsets: vec![vec![payload_offset], vec![]],
                }),
                origin: None,
            });
        }
        if rng.bool() {
            // NICHE: `none` is a reserved value of the 4-byte payload lane.
            let niche_start = 0xFFFF_FF00u128 + u128::from(rng.bounded(16));
            let id = trust_ir::value::EnumId::new(u32::try_from(m.enums.len()).unwrap());
            m.add_enum(EnumDef {
                id,
                name: format!("FuzzNiche{}", id.index()),
                variants: vec![variant("some", vec![Ty::U32]), variant("none", vec![])],
                discriminants: Vec::new(),
                repr: None,
                layout: Some(EnumLayoutDescriptor {
                    encoding: EnumTagEncoding::Niche {
                        untagged_variant: 0,
                        niche_variants_start: 1,
                        niche_variants_end: 1,
                        niche_start,
                        niche_offset: 0,
                        niche_ty: EnumTagRepr::U32,
                    },
                    size: 4,
                    align: 4,
                    variant_field_offsets: vec![vec![0], vec![]],
                }),
                origin: None,
            });
        }
        if rng.bool() {
            // v37 UNTAGGED: no tag lane at all; the image IS the payload.
            let id = trust_ir::value::EnumId::new(u32::try_from(m.enums.len()).unwrap());
            m.add_enum(EnumDef {
                id,
                name: format!("FuzzUntagged{}", id.index()),
                variants: vec![variant("only", vec![Ty::U64])],
                discriminants: Vec::new(),
                repr: None,
                layout: Some(EnumLayoutDescriptor {
                    encoding: EnumTagEncoding::Untagged,
                    size: 8,
                    align: 8,
                    variant_field_offsets: vec![vec![0]],
                }),
                origin: None,
            });
        }
    }

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
            section: None,
            visibility: Default::default(),
            retained: false,
        });
    }

    // WS4.5 (F-065): module-level `global_asm!` blocks, 0..=2 per seed, with
    // the characters the text escape set must invert (newline, tab, quote,
    // backslash, a control character, non-ASCII). Order is identity.
    let asm_pool = [
        ".globl _x\n_x:\n\tret",
        "  .section \"__TEXT,__text\"",
        "\\ \u{1} \r\0 é",
        "",
    ];
    for _ in 0..rng.bounded(3) {
        m.global_asm
            .push(asm_pool[rng.bounded(4) as usize].to_string());
    }

    m
}

/// Check one seed. Returns whether the generated module was NOT already in
/// canonical form — the caller uses it to prove the exact-text leg below is
/// not vacuous.
fn check_module(seed: u64) -> bool {
    let m = gen_module(seed);

    // The generator must only ever emit well-formed IR.
    let errs = trust_ir_build::validate_module(&m);
    assert!(
        errs.is_empty(),
        "seed {seed}: generated module failed validation: {errs:?}"
    );

    // Binary: lossless AND idempotent (the 94bcc1e regression target).
    let b1 = trust_ir::binary::serialize_module(&m).expect("serialize_module: test fixture");
    let m2 = trust_ir::binary::deserialize_module(&b1)
        .unwrap_or_else(|e| panic!("seed {seed}: binary deserialize failed: {e:?}"));
    assert_eq!(m, m2, "seed {seed}: binary round-trip changed the module");
    let b2 = trust_ir::binary::serialize_module(&m2).expect("serialize_module: test fixture");
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

    // Canonical text: format / parse / format is idempotent — and, since
    // roadmap WS4.2, EXACT: the generator emits nothing the text grammar
    // cannot carry, so `canonical_checked` must be `Ok` and the parsed module
    // must equal `canonicalize(m)` field for field. A field the grammar drops
    // without a `TextLoss` arm fails here, on any seed that reaches it.
    let t1 = trust_ir::format::canonical_checked(&m)
        .unwrap_or_else(|e| panic!("seed {seed}: generated module is text-lossy: {e}"));
    let mt = trust_ir::parser::parse_module(&t1)
        .unwrap_or_else(|e| panic!("seed {seed}: text parse failed: {e:?}"));
    let t2 = trust_ir::format::canonical(&mt);
    assert_eq!(
        t1, t2,
        "seed {seed}: canonical text is not idempotent across a round-trip"
    );
    assert_eq!(
        mt,
        trust_ir::format::canonicalize(&m),
        "seed {seed}: text round-trip lost module structure although text_losses is empty"
    );
    // v45: the text round trip is INJECTIVE on the function symbol
    // attributes — idempotency alone would pass a printer that dropped them.
    let symbols = |m: &Module| {
        let mut rows: Vec<_> = m
            .functions
            .iter()
            .map(|f| {
                (
                    f.name.clone(),
                    f.section.clone(),
                    f.visibility,
                    f.retained,
                    // v45 (WS3.11): the slot facts must survive too. The
                    // Canonicalization explicitly trims the default tail.
                    // Raw transport below instead retains the exact table.
                    f.attrs.ret.clone(),
                    {
                        let mut params = f.attrs.params.clone();
                        while params.last().is_some_and(trust_ir::ParamAttrs::is_empty) {
                            params.pop();
                        }
                        params
                    },
                )
            })
            .collect();
        // Function names are unique per module, so the name orders the rows
        // (`ParamAttrs` is not `Ord`: `PassMode::Cast` carries types).
        rows.sort_by(|a, b| a.0.cmp(&b.0));
        rows
    };
    assert_eq!(
        symbols(&m),
        symbols(&mt),
        "seed {seed}: text lost a symbol attribute or a slot ABI fact"
    );

    // Exact text (the TRANSPORT spelling): `text_checked` prints the module's
    // OWN value ids, block order and param-attr table, so the round trip is
    // the identity — no `canonicalize` on either side.
    //
    // This is the only text leg that can see a renumbering printer. The
    // canonical legs above compare `canonicalize`d modules, so a printer that
    // allocates fresh dense ids passes them while `bin -> text -> bin` stops
    // being byte-identical and `text_losses` reports nothing: a consumer
    // validates a module the producer never emitted. Sparse and out-of-order
    // ids are legal here — `validate_ssa` requires unique definitions and
    // dominance, not density, and the binary codec writes every id verbatim.
    //
    // The final #param_attrs row now carries the exact table length, even
    // for a default tail. Test the ORIGINAL owner without any preprocessing.
    let exact = trust_ir::format::text_checked(&m)
        .unwrap_or_else(|e| panic!("seed {seed}: generated raw module is text-lossy: {e}"));
    let twin_back = trust_ir::parser::parse_module(&exact)
        .unwrap_or_else(|e| panic!("seed {seed}: exact text parse failed: {e:?}"));
    assert_eq!(
        twin_back, m,
        "seed {seed}: the text round trip RENUMBERED the module — its own SSA \
         value ids or block order did not survive print -> parse, and \
         text_losses reported nothing"
    );
    assert_eq!(
        trust_ir::binary::serialize_module(&twin_back).expect("serialize_module: test fixture"),
        b1,
        "seed {seed}: bin -> raw text -> bin changed actual artifact bytes"
    );
    // Exact text is a fixed point through a parse, too.
    let exact2 = trust_ir::format::text_checked(&twin_back).expect("loss-free");
    assert_eq!(
        exact, exact2,
        "seed {seed}: exact text is not idempotent across a round-trip"
    );

    // Attribute-length canonicalization alone must not satisfy the SSA
    // anti-vacuity guard. Observe actual block/definition IDs independently.
    let canonical = trust_ir::format::canonicalize(&m);
    m.functions.iter().any(|original| {
        let normalized = canonical
            .functions
            .iter()
            .find(|function| function.name == original.name)
            .expect("canonicalization retains the unique source function");
        original
            .blocks
            .iter()
            .zip(&normalized.blocks)
            .any(|(left, right)| {
                left.id != right.id
                    || left.params != right.params
                    || left
                        .body
                        .iter()
                        .zip(&right.body)
                        .any(|(left, right)| left.results != right.results)
            })
    })
}

#[test]
fn module_roundtrip_fuzz() {
    // Fixed seed range → deterministic, never flakes. Sized to densely
    // cover the expanded instruction/CFG space while staying sub-second.
    let mut non_canonical_seeds = 0_u32;
    for seed in 1..=1024u64 {
        if check_module(seed) {
            non_canonical_seeds += 1;
        }
    }
    // Anti-vacuity guard for the exact-text leg: on a corpus of already-dense
    // modules, `canonicalize` is the identity and a renumbering printer would
    // pass unnoticed. The generator's multi-block functions interleave block
    // parameters with instruction results, which canonical form does not, so
    // this count is large; the assert only has to catch the day it becomes 0.
    assert!(
        non_canonical_seeds > 0,
        "no generated module was non-canonical: the exact-text round-trip leg \
         would be vacuous against a renumbering printer"
    );
}

// ---------------------------------------------------------------------------
// parse_never_panics — roadmap WS4.1 (F-066, audit row
// `a.format.text_parser_utf8`, skeptic c09).
// ---------------------------------------------------------------------------

/// The inserted characters the roadmap names: 2-byte `é`, 3-byte `→`,
/// 4-byte `𝕏`, and the combining mark U+0301.
const UTF8_INSERTS: [char; 4] = ['\u{e9}', '\u{2192}', '\u{1d54f}', '\u{301}'];

/// Every line start, every position before a newline (and the end of a text
/// with no final newline), and every position right after a `;`.
fn utf8_insertion_points(text: &str) -> Vec<usize> {
    let mut points = vec![0, text.len()];
    for (i, b) in text.bytes().enumerate() {
        match b {
            b'\n' => {
                points.push(i);
                points.push(i + 1);
            }
            b';' => points.push(i + 1),
            _ => {}
        }
    }
    points.sort_unstable();
    points.dedup();
    points
}

fn insert_at(text: &str, pos: usize, ch: char) -> String {
    let mut out = String::with_capacity(text.len() + 4);
    out.push_str(&text[..pos]);
    out.push(ch);
    out.push_str(&text[pos..]);
    out
}

#[derive(Default)]
struct Utf8SweepStats {
    ok: usize,
    err: usize,
    in_comment: usize,
}

impl Utf8SweepStats {
    fn merge(&mut self, other: Utf8SweepStats) {
        self.ok += other.ok;
        self.err += other.err;
        self.in_comment += other.in_comment;
    }
}

/// Run `sweep` over `items` on every available core. The work is ~10^6
/// debug-build parses, so the wall time stays proportionate; the partition
/// is fixed and every item is swept, so the result is deterministic. A
/// failing assertion in any worker fails the test when the scope joins.
fn sweep_in_parallel<T: Sync>(
    items: &[T],
    sweep: impl Fn(&T, &mut Utf8SweepStats) + Sync,
) -> Utf8SweepStats {
    let workers = std::thread::available_parallelism().map_or(1, |n| n.get());
    let chunk = items.len().div_ceil(workers).max(1);
    let mut total = Utf8SweepStats::default();
    std::thread::scope(|scope| {
        let handles: Vec<_> = items
            .chunks(chunk)
            .map(|part| {
                let sweep = &sweep;
                scope.spawn(move || {
                    let mut stats = Utf8SweepStats::default();
                    for item in part {
                        sweep(item, &mut stats);
                    }
                    stats
                })
            })
            .collect();
        for handle in handles {
            match handle.join() {
                Ok(stats) => total.merge(stats),
                Err(payload) => std::panic::resume_unwind(payload),
            }
        }
    });
    total
}

/// Run the leg's two assertions over one text.
///
/// 1. PANIC LEG: every insertion yields `Ok(_)` or `Err(ParseError)` under
///    `catch_unwind`, never an unwind.
/// 2. MUTATION CONTROL: `advance` is fallible, so a scanner reverted to a
///    byte step yields `Err(internal: cursor split …)`, which leg 1 cannot
///    see. So (a) that refusal fails the leg wherever it appears, and (b)
///    every insertion that lands inside a `;` comment — after a `;` on its
///    line, where the ASCII twin (`x` at the same point) parses to the
///    unmodified baseline — must parse to a module structurally EQUAL to
///    that baseline.
fn sweep_utf8_insertions(label: &str, text: &str, stats: &mut Utf8SweepStats) {
    use text_parser_utf8::{CURSOR_SPLIT, parse_caught};

    let baseline = match parse_caught(text) {
        Ok(Ok(m)) => m,
        other => panic!("{label}: the unmodified text must parse: {other:?}"),
    };
    let line_of = |pos: usize| text[..pos].matches('\n').count() + 1;
    for pos in utf8_insertion_points(text) {
        let line_start = text[..pos].rfind('\n').map_or(0, |i| i + 1);
        let in_comment = text[line_start..pos].contains(';')
            && matches!(
                parse_caught(&insert_at(text, pos, 'x')),
                Ok(Ok(ref m)) if *m == baseline
            );
        if in_comment {
            stats.in_comment += 1;
        }
        for ch in UTF8_INSERTS {
            match parse_caught(&insert_at(text, pos, ch)) {
                Err(msg) => panic!(
                    "{label}: parser PANICKED with {ch:?} inserted at byte {pos} (line {}): {msg}",
                    line_of(pos)
                ),
                Ok(Err(e)) if e.message.contains(CURSOR_SPLIT) => panic!(
                    "{label}: a scanner split a UTF-8 scalar with {ch:?} inserted at byte \
                     {pos} (line {}): {e}",
                    line_of(pos)
                ),
                Ok(Err(e)) => {
                    assert!(
                        !in_comment,
                        "{label}: {ch:?} inside a `;` comment at byte {pos} (line {}) was \
                         refused, but its ASCII twin parses: {e}",
                        line_of(pos)
                    );
                    stats.err += 1;
                }
                Ok(Ok(m)) => {
                    assert!(
                        !in_comment || m == baseline,
                        "{label}: {ch:?} inside a `;` comment at byte {pos} (line {}) changed \
                         the parsed module",
                        line_of(pos)
                    );
                    stats.ok += 1;
                }
            }
        }
    }
}

fn corpus_text_fixtures() -> Vec<(String, String)> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures");
    let mut out: Vec<(String, String)> = std::fs::read_dir(&dir)
        .expect("fixtures dir")
        .map(|entry| entry.expect("dir entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "trust_ir"))
        .map(|path| {
            // A lossy golden carries a `; #lossy:` marker the parser refuses
            // (roadmap WS4.2). This sweep measures the GRAMMAR's panic
            // freedom, not the loss verdict (the conformance ratchet pins
            // that), so it strips the marker line — exactly the edit a human
            // could make — and keeps the fixture's grammar coverage.
            let text: String = std::fs::read_to_string(&path)
                .expect("read fixture")
                .lines()
                .filter(|line| !line.starts_with("; #lossy:"))
                .map(|line| format!("{line}\n"))
                .collect();
            let name = path
                .file_name()
                .expect("file name")
                .to_string_lossy()
                .into_owned();
            (name, text)
        })
        .collect();
    out.sort();
    assert!(
        out.len() >= 20,
        "the text corpus shrank to {} fixtures; the sweep would lose coverage",
        out.len()
    );
    out
}

#[test]
fn parse_never_panics() {
    let corpus = sweep_in_parallel(&corpus_text_fixtures(), |(name, text), stats| {
        sweep_utf8_insertions(name, text, stats);
    });
    let seeds: Vec<u64> = (1..=1024).collect();
    let fuzz = sweep_in_parallel(&seeds, |&seed, stats| {
        let text = trust_ir::format::canonical(&gen_module(seed));
        sweep_utf8_insertions(&format!("seed {seed}"), &text, stats);
    });
    // Non-vacuity, per population: each saw accepted insertions, refused
    // insertions and in-comment insertions (the mutation control's equality
    // half), so neither half of the leg can pass on an empty set.
    for (population, stats) in [("corpus", &corpus), ("seeds", &fuzz)] {
        assert!(
            stats.ok > 0 && stats.err > 0 && stats.in_comment >= 50,
            "{population} sweep too narrow: ok={} err={} in_comment={}",
            stats.ok,
            stats.err,
            stats.in_comment
        );
    }
}

/// The wider corpus sweep: a 2- and a 4-byte character at EVERY character
/// boundary of every corpus fixture, so every scanner position the corpus
/// reaches (numbers, types, attrs, quoted strings, keyword boundaries — not
/// only comment and line edges) is handed a multi-byte character.
#[test]
fn parse_never_panics_at_every_char_boundary() {
    use text_parser_utf8::{CURSOR_SPLIT, parse_caught};

    let stats = sweep_in_parallel(&corpus_text_fixtures(), |(name, text), stats| {
        for pos in (0..=text.len()).filter(|&i| text.is_char_boundary(i)) {
            for ch in ['\u{e9}', '\u{1f600}'] {
                match parse_caught(&insert_at(text, pos, ch)) {
                    Ok(Ok(_)) => stats.ok += 1,
                    Ok(Err(e)) => {
                        assert!(
                            !e.message.contains(CURSOR_SPLIT),
                            "{name}: {ch:?} at byte {pos}: {e}"
                        );
                        stats.err += 1;
                    }
                    Err(msg) => panic!("{name}: parser PANICKED with {ch:?} at byte {pos}: {msg}"),
                }
            }
        }
    });
    assert!(
        stats.ok > 0 && stats.err > 0,
        "sweep saw only one outcome (ok={}, err={})",
        stats.ok,
        stats.err
    );
}

/// Review adversary (WS4.1 review, 2026-10-01). The every-boundary sweep
/// above reaches only the checked-in corpus, with a 2- and a 4-byte
/// character; `parse_never_panics` reaches the fuzzer's seeds only at line
/// edges and after `;`. This sweep hands EVERY character boundary of a
/// sample of seed texts (the canonical printer's output for generated
/// modules: every instruction family the fuzzer emits) a 3-byte character,
/// the combining mark, and a no-break space, and holds two properties:
///
/// 1. never a panic, never the fallible cursor's `internal: cursor split`;
/// 2. none of them is ignorable to the grammar — the no-break space is not
///    whitespace, the combining mark does not vanish: wherever an insertion
///    leaves the module unchanged, an ASCII letter at the same byte must
///    leave it unchanged too (i.e. the position is a comment). A lookahead that
///    skipped Unicode whitespace into a branch that accepted it would make
///    the NBSP a second spelling of an ASCII space, and fail here.
#[test]
fn parse_never_panics_at_every_char_boundary_of_seed_texts() {
    use text_parser_utf8::{CURSOR_SPLIT, parse_caught};

    let seeds: Vec<u64> = (1..=24).collect();
    let stats = sweep_in_parallel(&seeds, |&seed, stats| {
        let text = trust_ir::format::canonical(&gen_module(seed));
        let baseline = match parse_caught(&text) {
            Ok(Ok(m)) => m,
            other => panic!("seed {seed}: the canonical text must parse: {other:?}"),
        };
        for pos in (0..=text.len()).filter(|&i| text.is_char_boundary(i)) {
            for ch in ['\u{2192}', '\u{301}', '\u{a0}'] {
                match parse_caught(&insert_at(&text, pos, ch)) {
                    Err(msg) => {
                        panic!("seed {seed}: parser PANICKED with {ch:?} at byte {pos}: {msg}")
                    }
                    Ok(Err(e)) => {
                        assert!(
                            !e.message.contains(CURSOR_SPLIT),
                            "seed {seed}: {ch:?} at byte {pos}: {e}"
                        );
                        stats.err += 1;
                    }
                    Ok(Ok(m)) => {
                        if m == baseline {
                            let ascii_twin = parse_caught(&insert_at(&text, pos, 'x'));
                            assert!(
                                matches!(&ascii_twin, Ok(Ok(t)) if *t == baseline),
                                "seed {seed}: {ch:?} at byte {pos} was accepted with the \
                                 module unchanged where an ASCII letter is not a comment: \
                                 {ascii_twin:?}\n--- context ---\n{}",
                                &text[text[..pos].rfind('\n').map_or(0, |i| i + 1)..pos]
                            );
                            stats.in_comment += 1;
                        }
                        stats.ok += 1;
                    }
                }
            }
        }
    });
    assert!(
        stats.ok > 0 && stats.err > 0,
        "sweep saw only one outcome (ok={}, err={})",
        stats.ok,
        stats.err
    );
}
