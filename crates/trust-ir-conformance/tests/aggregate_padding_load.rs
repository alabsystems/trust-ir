// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Roadmap WS2.14 (F-030): whole-aggregate `Load` and never-written padding.
//
// Rule. A whole-aggregate `Load` (struct, tuple, enum, array; strict or not)
// requires exactly the bytes a LIVE field of the decoded value covers to be
// initialized — struct/tuple fields, array elements, and for an enum the tag
// lane plus the ACTIVE variant's fields. Padding and the inactive-variant tail
// are don't-care: the decode never reads them. An uninitialized covered byte
// stays undefined behaviour, reported at its exact offset.
//
// Store side, same change. A typed aggregate value carries no byte image
// beyond its live fields, so a typed aggregate `Store` writes every uncovered
// byte as UNINITIALIZED, never as the zeros the encoder fills it with.
// Otherwise `load %agg` of never-written padding followed by `store %agg`
// would launder uninitialized padding into defined zeros.
//
// Lean has no aggregate memory path (`encodeValue`/`decodeValue` give `none`
// for every aggregate), so this is interpreter-only; the B3 depth ledger
// carries the row "whole-aggregate memory images unmodelled in Lean".

use trust_ir::constant::Constant;
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::ty::{EnumDef, EnumVariant, FieldDef, StructDef, Ty};
use trust_ir::value::{EnumId, StructId};
use trust_ir::{BodyGate, Module};
use trust_ir_build::{FunctionBuilder, ModuleBuilder, validate_module};

/// Run the module's single nullary function `program`. `Err` carries the
/// interpreter's `code: message`.
fn run(module: &Module) -> Result<Vec<InterpretValue>, String> {
    let func = module.function_by_name("program").expect("program");
    Interpreter::with_module(module)
        .execute_func(func.id, [])
        .map(|outcome| outcome.returns)
        .map_err(|e| format!("{:?}: {e}", e.code))
}

fn run_u(module: &Module) -> Result<u128, String> {
    let values = run(module)?;
    let [value] = values.as_slice() else {
        return Err(format!("expected one return value, got {values:?}"));
    };
    value
        .as_int()
        .map(|i| i.as_unsigned())
        .ok_or_else(|| format!("non-integer return {value:?}"))
}

fn assert_valid(module: &Module) {
    let errors = validate_module(module);
    assert!(errors.is_empty(), "fixture must validate: {errors:?}");
}

/// `Err` must be the uninitialized-covered-byte fault at exactly `offset`.
fn assert_uninit_at(out: &Result<u128, String>, offset: u64) {
    let expected = format!("Load: reading uninitialized byte at offset {offset}");
    assert!(
        matches!(out, Err(e) if e.starts_with("UndefinedBehavior") && e.contains(&expected)),
        "expected UndefinedBehavior `{expected}`, got {out:?}"
    );
}

/// `Err` must be the poison-inspection fault (a `PartialBytes` value used),
/// never `Ok(0)` from a fabricated zero.
fn assert_poison(out: &Result<u128, String>) {
    assert!(
        matches!(out, Err(e) if e.starts_with("UndefinedBehavior")
            && e.contains("use of an uninitialized value")),
        "expected the poison-use UndefinedBehavior, got {out:?}"
    );
}

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

/// `struct S { x: u64, y: u8 }` — canonical layout: `x` @0, `y` @8, size 16,
/// seven tail-padding bytes 9..16.
fn struct_s() -> StructDef {
    StructDef {
        id: StructId::new(0),
        name: "S".into(),
        fields: vec![
            FieldDef {
                name: "x".into(),
                ty: Ty::U64,
                offset: None,
            },
            FieldDef {
                name: "y".into(),
                ty: Ty::U8,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    }
}

fn s_ty() -> Ty {
    Ty::Struct(StructId::new(0))
}

/// A module with `struct S` and one nullary `program() -> ret`.
fn struct_module(ret: Ty, body: impl FnOnce(&mut FunctionBuilder<'_>)) -> Module {
    let mut mb = ModuleBuilder::new("ws2_14_struct");
    mb.add_struct(struct_s());
    let sig = mb.add_func_type(vec![], vec![ret]);
    let mut fb = mb.function("program", sig);
    fb.set_body_gate(BodyGate::Gated {
        authority: "ws2.14".into(),
        evidence: None,
    });
    let bb = fb.create_block();
    fb.switch_to_block(bb);
    body(&mut fb);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Field-wise initialization of an `S` slot: `x = 42` (unless `skip_x`), and
/// `y = 1` (unless `skip_y`). Padding 9..16 is never written.
fn init_fieldwise(fb: &mut FunctionBuilder<'_>, skip_x: bool, skip_y: bool) -> trust_ir::ValueId {
    let p = fb.alloca(s_ty());
    if !skip_x {
        let x = fb.uconst(Ty::U64, 42);
        fb.store(Ty::U64, p, x);
    }
    if !skip_y {
        let p8 = fb.gep_byte_offset(p, 8);
        let y = fb.uconst(Ty::U8, 1);
        fb.store(Ty::U8, p8, y);
    }
    p
}

/// `enum R { None, Some(&i64) }` with no descriptor — the canonical tagged
/// union: `u8` tag @0, payload @8, size 16. Bytes 1..8 are padding in every
/// variant; bytes 8..16 are the inactive-variant tail of `None`.
fn r_enum(refty: &Ty) -> EnumDef {
    EnumDef::new(
        EnumId::new(0),
        "R",
        vec![
            EnumVariant {
                name: "None".into(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "Some".into(),
                fields: vec![refty.clone()],
                field_names: vec![],
            },
        ],
    )
}

/// c06 p3: `R` built field-wise (tag store + payload store, padding never
/// written), then loaded WHOLE and projected. `write_payload = false` leaves the
/// ACTIVE variant's field unwritten (the negative twin).
fn enum_fieldwise_module(write_payload: bool) -> Module {
    let refty = Ty::Ref(Box::new(Ty::I64));
    let r = Ty::Enum(EnumId::new(0));
    let mut mb = ModuleBuilder::new("ws2_14_enum");
    mb.add_enum(r_enum(&refty));
    let sig = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("program", sig);
    fb.set_body_gate(BodyGate::Gated {
        authority: "ws2.14".into(),
        evidence: None,
    });
    let bb = fb.create_block();
    fb.switch_to_block(bb);
    let p = fb.alloca(r.clone());
    let slot = fb.alloca(Ty::I64);
    let v42 = fb.iconst(Ty::I64, 42);
    fb.store(Ty::I64, slot, v42);
    let reff = fb.cast(
        trust_ir::inst::CastOp::PtrToPtr,
        Ty::Ptr,
        refty.clone(),
        slot,
    );
    let one = fb.uconst(Ty::U8, 1);
    fb.store(Ty::U8, p, one);
    if write_payload {
        let q = fb.gep_byte_offset(p, 8);
        fb.store(refty.clone(), q, reff);
    }
    let e = fb.load(r, p);
    let x = fb.extract_field(refty.clone(), e, 1);
    let y = fb.cast(trust_ir::inst::CastOp::PtrToPtr, refty, Ty::Ptr, x);
    let z = fb.load(Ty::I64, y);
    fb.ret(vec![z]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

// ---------------------------------------------------------------------------
// Positive
// ---------------------------------------------------------------------------

/// c06 h: field-wise init, whole `Load`, return field 0. Before WS2.14 this was
/// `UndefinedBehavior "offset 9"` (the first never-written padding byte).
#[test]
fn ws2_14_struct_fieldwise_init_whole_load_is_defined() {
    let m = struct_module(Ty::U64, |fb| {
        let p = init_fieldwise(fb, false, false);
        let v = fb.load(s_ty(), p);
        let x = fb.extract_field(Ty::U64, v, 0);
        fb.ret(vec![x]);
    });
    assert_valid(&m);
    assert_eq!(run_u(&m), Ok(42));
}

/// c06 p3 / partb b6 enum field-wise: tag + active payload written, padding and
/// nothing else; the whole-enum `Load` is defined.
#[test]
fn ws2_14_enum_fieldwise_init_whole_load_is_defined() {
    let m = enum_fieldwise_module(true);
    assert_valid(&m);
    assert_eq!(run_u(&m), Ok(42));
}

/// A `None` value written field-wise is just its tag: the whole `None` image's
/// payload region is the inactive-variant tail, never read.
#[test]
fn ws2_14_enum_inactive_variant_tail_is_dont_care() {
    let refty = Ty::Ref(Box::new(Ty::I64));
    let r = Ty::Enum(EnumId::new(0));
    let mut mb = ModuleBuilder::new("ws2_14_enum_none");
    mb.add_enum(r_enum(&refty));
    let sig = mb.add_func_type(vec![], vec![Ty::U8]);
    let mut fb = mb.function("program", sig);
    let bb = fb.create_block();
    fb.switch_to_block(bb);
    let p = fb.alloca(r.clone());
    let zero = fb.uconst(Ty::U8, 0);
    fb.store(Ty::U8, p, zero);
    let e = fb.load(r, p);
    let tag = fb.extract_field(Ty::U8, e, 0);
    fb.ret(vec![tag]);
    fb.build();
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_valid(&m);
    assert_eq!(run_u(&m), Ok(0));
}

/// Strictness is "every COVERED byte initialized" for a volatile whole load too
/// (Rust's `read_volatile::<S>` is defined over never-written padding).
#[test]
fn ws2_14_volatile_whole_load_ignores_padding() {
    let m = struct_module(Ty::U64, |fb| {
        let p = init_fieldwise(fb, false, false);
        let v = fb.load_volatile(s_ty(), p);
        let x = fb.extract_field(Ty::U64, v, 0);
        fb.ret(vec![x]);
    });
    assert_valid(&m);
    assert_eq!(run_u(&m), Ok(42));
}

// ---------------------------------------------------------------------------
// Negative twins: a covered byte never written stays UB, at its offset
// ---------------------------------------------------------------------------

/// Field 1 (`y` @8) never written, then a whole `Load`: UB "offset 8".
#[test]
fn ws2_14_struct_field_never_written_is_ub_at_its_offset() {
    let m = struct_module(Ty::U64, |fb| {
        let p = init_fieldwise(fb, false, true);
        let v = fb.load(s_ty(), p);
        let x = fb.extract_field(Ty::U64, v, 0);
        fb.ret(vec![x]);
    });
    assert_valid(&m);
    assert_uninit_at(&run_u(&m), 8);
}

/// The active variant's payload never written: UB at the payload offset 8.
#[test]
fn ws2_14_enum_active_payload_never_written_is_ub() {
    let m = enum_fieldwise_module(false);
    assert_valid(&m);
    assert_uninit_at(&run_u(&m), 8);
}

/// A tag lane never written: the active variant is unknowable, so the load
/// reports the tag byte.
#[test]
fn ws2_14_enum_tag_never_written_is_ub_at_the_tag() {
    let refty = Ty::Ref(Box::new(Ty::I64));
    let r = Ty::Enum(EnumId::new(0));
    let mut mb = ModuleBuilder::new("ws2_14_enum_no_tag");
    mb.add_enum(r_enum(&refty));
    let sig = mb.add_func_type(vec![], vec![Ty::U8]);
    let mut fb = mb.function("program", sig);
    let bb = fb.create_block();
    fb.switch_to_block(bb);
    let p = fb.alloca(r.clone());
    let e = fb.load(r, p);
    let tag = fb.extract_field(Ty::U8, e, 0);
    fb.ret(vec![tag]);
    fb.build();
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_valid(&m);
    assert_uninit_at(&run_u(&m), 0);
}

// ---------------------------------------------------------------------------
// Mutation controls
// ---------------------------------------------------------------------------

/// A strict (volatile) whole `Load` with an uninitialized COVERED byte stays UB:
/// the relaxation is padding-only, never a covered byte.
#[test]
fn ws2_14_volatile_whole_load_uninit_covered_byte_stays_ub() {
    let m = struct_module(Ty::U64, |fb| {
        let p = init_fieldwise(fb, true, false);
        let v = fb.load_volatile(s_ty(), p);
        let y = fb.extract_field(Ty::U8, v, 1);
        let y = fb.cast(trust_ir::inst::CastOp::ZExt, Ty::U8, Ty::U64, y);
        fb.ret(vec![y]);
    });
    assert_valid(&m);
    assert_uninit_at(&run_u(&m), 0);
}

/// c07 t8: the `Array(U8, 8)` union carrier is NOT covered by the padding rule —
/// every byte is an element, so a by-value move of a partially initialized
/// carrier stays UB (F-050 is a separate owner decision).
#[test]
fn ws2_14_array_u8_partial_carrier_move_stays_ub() {
    let mut mb = ModuleBuilder::new("ws2_14_carrier");
    let u8t = mb.add_type(Ty::U8);
    let carrier = Ty::Array(u8t, 8);
    let sig = mb.add_func_type(vec![], vec![Ty::U8]);
    let mut fb = mb.function("program", sig);
    let bb = fb.create_block();
    fb.switch_to_block(bb);
    let src = fb.alloca_aligned(carrier.clone(), 8);
    let nine = fb.uconst(Ty::U8, 9);
    fb.store(Ty::U8, src, nine); // u.small = 9 (bytes 1..8 stay uninit)
    let whole = fb.load(carrier.clone(), src); // let v = u; (a MOVE)
    let dst = fb.alloca_aligned(carrier.clone(), 8);
    fb.store(carrier, dst, whole);
    let small = fb.load(Ty::U8, dst);
    fb.ret(vec![small]);
    fb.build();
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_valid(&m);
    assert_uninit_at(&run_u(&m), 1);
}

/// Laundering control: field-wise init, whole `Load`, whole `Store` to a fresh
/// `Alloca`, then a `u8` load of a padding byte. The byte is poison
/// (`PartialBytes`), and returning it is UB — never `Ok(0)`. An implementation
/// that kept the zero-filling aggregate store would return 0 here.
#[test]
fn ws2_14_padding_is_not_laundered_through_a_typed_store() {
    let m = struct_module(Ty::U8, |fb| {
        let p = init_fieldwise(fb, false, false);
        let v = fb.load(s_ty(), p);
        let fresh = fb.alloca(s_ty());
        fb.store(s_ty(), fresh, v);
        let pad = fb.gep_byte_offset(fresh, 9);
        let byte = fb.load(Ty::U8, pad);
        fb.ret(vec![byte]);
    });
    assert_valid(&m);
    // Returning the poison byte crosses the return boundary: that is an
    // inspection, so it is the poison-use UB.
    assert_poison(&run_u(&m));
    // The covered byte next to it round-trips.
    let m = struct_module(Ty::U8, |fb| {
        let p = init_fieldwise(fb, false, false);
        let v = fb.load(s_ty(), p);
        let fresh = fb.alloca(s_ty());
        fb.store(s_ty(), fresh, v);
        let field = fb.gep_byte_offset(fresh, 8);
        let byte = fb.load(Ty::U8, field);
        fb.ret(vec![byte]);
    });
    assert_eq!(run_u(&m), Ok(1));
}

/// Store-side rule on its own: a full-image memset of 0xAA, then a typed store
/// of a register-built `S`. The padding byte now reads as poison, not 0xAA and
/// not 0 — the typed store owns every byte of its image.
#[test]
fn ws2_14_typed_store_writes_padding_as_uninit_after_memset() {
    let m = struct_module(Ty::U8, |fb| {
        let p = fb.alloca(s_ty());
        // memset: the whole 16-byte image, as a [u8; 16] store (the type is
        // added through the builder's own table below).
        let image = fb.const_value(Ty::U128, Constant::U128(u128::from_le_bytes([0xAA; 16])));
        fb.store(Ty::U128, p, image);
        let s = fb.const_value(
            s_ty(),
            Constant::Aggregate(vec![Constant::Int(7), Constant::Int(1)]),
        );
        fb.store(s_ty(), p, s);
        let pad = fb.gep_byte_offset(p, 12);
        let byte = fb.load(Ty::U8, pad);
        let zero = fb.uconst(Ty::U8, 0);
        let sum = fb.add(Ty::U8, byte, zero);
        fb.ret(vec![sum]);
    });
    assert_valid(&m);
    assert_poison(&run_u(&m));
    // Control: the memset byte IS readable before the typed store.
    let m = struct_module(Ty::U8, |fb| {
        let p = fb.alloca(s_ty());
        let image = fb.const_value(Ty::U128, Constant::U128(u128::from_le_bytes([0xAA; 16])));
        fb.store(Ty::U128, p, image);
        let pad = fb.gep_byte_offset(p, 12);
        let byte = fb.load(Ty::U8, pad);
        fb.ret(vec![byte]);
    });
    assert_eq!(run_u(&m), Ok(0xAA));
}

/// Store-side rule for enums: storing `None` leaves its inactive-variant tail
/// uninitialized — a byte-level read of the payload region is poison, even
/// after a memset.
#[test]
fn ws2_14_enum_store_writes_inactive_tail_as_uninit() {
    let refty = Ty::Ref(Box::new(Ty::I64));
    let r = Ty::Enum(EnumId::new(0));
    let mut mb = ModuleBuilder::new("ws2_14_enum_store");
    mb.add_enum(r_enum(&refty));
    let sig = mb.add_func_type(vec![], vec![Ty::U8]);
    let mut fb = mb.function("program", sig);
    let bb = fb.create_block();
    fb.switch_to_block(bb);
    let p = fb.alloca(r.clone());
    let image = fb.const_value(Ty::U128, Constant::U128(u128::from_le_bytes([0xAA; 16])));
    fb.store(Ty::U128, p, image);
    let none = fb.const_value(r.clone(), Constant::Aggregate(vec![Constant::Int(0)]));
    fb.store(r, p, none);
    let tail = fb.gep_byte_offset(p, 8);
    let byte = fb.load(Ty::U8, tail);
    let zero = fb.uconst(Ty::U8, 0);
    let sum = fb.add(Ty::U8, byte, zero);
    fb.ret(vec![sum]);
    fb.build();
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_valid(&m);
    assert_poison(&run_u(&m));
}

// ---------------------------------------------------------------------------
// Adversarial review: shapes the first cut's tests did not reach
// ---------------------------------------------------------------------------

/// `[S; 2]` built element-by-element, field-wise (padding 9..16 and 25..32 never
/// written): the whole-array `Load` is defined — each element's padding is
/// don't-care. The twin leaves element 1's `y` (@24) unwritten: a covered byte
/// of the SECOND element, reported at its exact offset.
#[test]
fn ws2_14_review_array_of_padded_structs_fieldwise() {
    let build = |skip_second_y: bool| {
        let mut mb = ModuleBuilder::new("ws2_14_array_of_s");
        mb.add_struct(struct_s());
        let s_id = mb.add_type(s_ty());
        let arr = Ty::Array(s_id, 2);
        let sig = mb.add_func_type(vec![], vec![Ty::U64]);
        let mut fb = mb.function("program", sig);
        let bb = fb.create_block();
        fb.switch_to_block(bb);
        let p = fb.alloca(arr.clone());
        for (base, x) in [(0u64, 40u128), (16, 2)] {
            let px = fb.gep_byte_offset(p, base);
            let xv = fb.uconst(Ty::U64, x);
            fb.store(Ty::U64, px, xv);
            if !(skip_second_y && base == 16) {
                let py = fb.gep_byte_offset(p, base + 8);
                let yv = fb.uconst(Ty::U8, 1);
                fb.store(Ty::U8, py, yv);
            }
        }
        let whole = fb.load(arr, p);
        let i0 = fb.uconst(Ty::U64, 0);
        let i1 = fb.uconst(Ty::U64, 1);
        let e0 = fb.extract_element(s_ty(), whole, i0);
        let e1 = fb.extract_element(s_ty(), whole, i1);
        let x0 = fb.extract_field(Ty::U64, e0, 0);
        let x1 = fb.extract_field(Ty::U64, e1, 0);
        let sum = fb.add(Ty::U64, x0, x1);
        fb.ret(vec![sum]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let m = build(false);
    assert_valid(&m);
    assert_eq!(run_u(&m), Ok(42));
    let twin = build(true);
    assert_valid(&twin);
    assert_uninit_at(&run_u(&twin), 24);
}

/// `struct W { e: R, k: u8 }` (R @0 size 16, k @16, size 24) with `e = None`
/// written as its tag byte only and `k` written: the whole-`W` load is defined
/// although R's padding 1..8, R's inactive tail 8..16 and W's padding 17..24
/// were never written. The twin skips `k` (@16). The store-side half: moving
/// the loaded `W` into a fresh slot leaves the NESTED inactive tail (byte 8)
/// uninitialized — the covered-byte recursion reaches into the inner enum.
#[test]
fn ws2_14_review_enum_nested_in_struct() {
    let refty = Ty::Ref(Box::new(Ty::I64));
    let r = Ty::Enum(EnumId::new(0));
    let w = Ty::Struct(StructId::new(0));
    let build = |skip_k: bool, read_moved_tail: bool| {
        let mut mb = ModuleBuilder::new("ws2_14_nested");
        mb.add_enum(r_enum(&refty));
        mb.add_struct(StructDef {
            id: StructId::new(0),
            name: "W".into(),
            fields: vec![
                FieldDef {
                    name: "e".into(),
                    ty: r.clone(),
                    offset: None,
                },
                FieldDef {
                    name: "k".into(),
                    ty: Ty::U8,
                    offset: None,
                },
            ],
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        });
        let sig = mb.add_func_type(vec![], vec![Ty::U8]);
        let mut fb = mb.function("program", sig);
        let bb = fb.create_block();
        fb.switch_to_block(bb);
        let p = fb.alloca(w.clone());
        let tag = fb.uconst(Ty::U8, 0);
        fb.store(Ty::U8, p, tag);
        if !skip_k {
            let pk = fb.gep_byte_offset(p, 16);
            let k = fb.uconst(Ty::U8, 7);
            fb.store(Ty::U8, pk, k);
        }
        let whole = fb.load(w.clone(), p);
        if read_moved_tail {
            // 16-aligned so the 16-byte `u128` pre-fill store is aligned.
            let fresh = fb.alloca_aligned(w.clone(), 16);
            let image = fb.const_value(Ty::U128, Constant::U128(u128::from_le_bytes([0xAA; 16])));
            fb.store(Ty::U128, fresh, image);
            fb.store(w.clone(), fresh, whole);
            let tail = fb.gep_byte_offset(fresh, 8);
            let byte = fb.load(Ty::U8, tail);
            let zero = fb.uconst(Ty::U8, 0);
            let sum = fb.add(Ty::U8, byte, zero);
            fb.ret(vec![sum]);
        } else {
            let k = fb.extract_field(Ty::U8, whole, 1);
            fb.ret(vec![k]);
        }
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let m = build(false, false);
    assert_valid(&m);
    assert_eq!(run_u(&m), Ok(7));
    let twin = build(true, false);
    assert_valid(&twin);
    assert_uninit_at(&run_u(&twin), 16);
    let moved = build(false, true);
    assert_valid(&moved);
    assert_poison(&run_u(&moved));
}

/// A NICHE-encoded enum (`enum N { Some(&i64, u8), None }`, rustc's layout:
/// `&i64` @0 carrying the null niche, `u8` @8, size 16): the tag lane IS the
/// dataful variant's pointer field, so the covered set is variant-dependent.
///
/// - `Some` written field-wise (pointer + `u8`, padding 9..16 never written)
///   loads whole and dereferences to 42.
/// - The twin writes only the pointer: the `u8` @8 is covered by the active
///   `Some` and is reported.
/// - `None` written as its niche value alone (lane 0..8 = 0) loads whole even
///   though byte 8 — `Some`'s `u8` — was never written: for `None` it is the
///   inactive tail. Moving it over a 0xAA image keeps the lane (reads 0) and
///   leaves byte 8 poison.
#[test]
fn ws2_14_review_niche_enum_covered_set_follows_the_active_variant() {
    use trust_ir::ty::{EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr};
    let refty = Ty::Ref(Box::new(Ty::I64));
    let n = Ty::Enum(EnumId::new(0));
    let module = |body: &dyn Fn(&mut FunctionBuilder<'_>), ret: Ty| {
        let mut mb = ModuleBuilder::new("ws2_14_niche");
        let mut def = EnumDef::new(
            EnumId::new(0),
            "N",
            vec![
                EnumVariant {
                    name: "Some".into(),
                    fields: vec![refty.clone(), Ty::U8],
                    field_names: vec![],
                },
                EnumVariant {
                    name: "None".into(),
                    fields: vec![],
                    field_names: vec![],
                },
            ],
        );
        def.layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Niche {
                untagged_variant: 0,
                niche_variants_start: 1,
                niche_variants_end: 1,
                niche_start: 0,
                niche_offset: 0,
                niche_ty: EnumTagRepr::U64,
            },
            size: 16,
            align: 8,
            variant_field_offsets: vec![vec![0, 8], vec![]],
        });
        mb.add_enum(def);
        let sig = mb.add_func_type(vec![], vec![ret]);
        let mut fb = mb.function("program", sig);
        let bb = fb.create_block();
        fb.switch_to_block(bb);
        body(&mut fb);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let some = |write_u8: bool| {
        let refty = refty.clone();
        let n = n.clone();
        move |fb: &mut FunctionBuilder<'_>| {
            let slot = fb.alloca(Ty::I64);
            let v42 = fb.iconst(Ty::I64, 42);
            fb.store(Ty::I64, slot, v42);
            let reff = fb.cast(
                trust_ir::inst::CastOp::PtrToPtr,
                Ty::Ptr,
                refty.clone(),
                slot,
            );
            let p = fb.alloca(n.clone());
            fb.store(refty.clone(), p, reff);
            if write_u8 {
                let p8 = fb.gep_byte_offset(p, 8);
                let one = fb.uconst(Ty::U8, 1);
                fb.store(Ty::U8, p8, one);
            }
            let e = fb.load(n.clone(), p);
            let x = fb.extract_field(refty.clone(), e, 1);
            let y = fb.cast(trust_ir::inst::CastOp::PtrToPtr, refty.clone(), Ty::Ptr, x);
            let z = fb.load(Ty::I64, y);
            fb.ret(vec![z]);
        }
    };
    let m = module(&some(true), Ty::I64);
    assert_valid(&m);
    assert_eq!(run_u(&m), Ok(42));
    let twin = module(&some(false), Ty::I64);
    assert_valid(&twin);
    assert_uninit_at(&run_u(&twin), 8);

    // `None`: niche lane only, then move over a 0xAA image.
    let none = |read_at: u64, ty: Ty| {
        let n = n.clone();
        move |fb: &mut FunctionBuilder<'_>| {
            let p = fb.alloca(n.clone());
            let lane = fb.uconst(Ty::U64, 0);
            fb.store(Ty::U64, p, lane);
            let whole = fb.load(n.clone(), p);
            let fresh = fb.alloca_aligned(n.clone(), 16);
            let image = fb.const_value(Ty::U128, Constant::U128(u128::from_le_bytes([0xAA; 16])));
            fb.store(Ty::U128, fresh, image);
            fb.store(n.clone(), fresh, whole);
            let q = fb.gep_byte_offset(fresh, read_at);
            let v = fb.load(ty.clone(), q);
            let zero = fb.uconst(ty.clone(), 0);
            let sum = fb.add(ty.clone(), v, zero);
            fb.ret(vec![sum]);
        }
    };
    let lane = module(&none(0, Ty::U64), Ty::U64);
    assert_valid(&lane);
    assert_eq!(
        run_u(&lane),
        Ok(0),
        "the niche lane is covered: stored defined"
    );
    let tail = module(&none(8, Ty::U8), Ty::U8);
    assert_valid(&tail);
    assert_poison(&run_u(&tail));
}

/// A VOLATILE typed store is a typed aggregate store too: it writes padding as
/// uninitialized, so a volatile (strict) `u8` load of a padding byte faults at
/// that byte's offset — where the zero-filling store gave `Ok(0)`.
#[test]
fn ws2_14_review_volatile_store_writes_padding_uninit() {
    let m = struct_module(Ty::U8, |fb| {
        let p = fb.alloca(s_ty());
        let image = fb.const_value(Ty::U128, Constant::U128(u128::from_le_bytes([0xAA; 16])));
        fb.store(Ty::U128, p, image);
        let s = fb.const_value(
            s_ty(),
            Constant::Aggregate(vec![Constant::Int(7), Constant::Int(1)]),
        );
        fb.store_volatile(s_ty(), p, s);
        let pad = fb.gep_byte_offset(p, 9);
        let byte = fb.load_volatile(Ty::U8, pad);
        fb.ret(vec![byte]);
    });
    assert_valid(&m);
    assert_uninit_at(&run_u(&m), 9);
    // Control: the covered byte next to it reads back through the same path.
    let m = struct_module(Ty::U8, |fb| {
        let p = fb.alloca(s_ty());
        let s = fb.const_value(
            s_ty(),
            Constant::Aggregate(vec![Constant::Int(7), Constant::Int(1)]),
        );
        fb.store_volatile(s_ty(), p, s);
        let field = fb.gep_byte_offset(p, 8);
        let byte = fb.load_volatile(Ty::U8, field);
        fb.ret(vec![byte]);
    });
    assert_eq!(run_u(&m), Ok(1));
}

/// Tuples share the struct rule: `(u8, u32)` (u8 @0, u32 @4, padding 1..4)
/// written field-wise loads whole; the twin skips the `u32` and reports @4.
#[test]
fn ws2_14_review_tuple_fieldwise() {
    let tup = Ty::Tuple(vec![Ty::U8, Ty::U32]);
    let build = |write_u32: bool| {
        let mut mb = ModuleBuilder::new("ws2_14_tuple");
        let sig = mb.add_func_type(vec![], vec![Ty::U32]);
        let mut fb = mb.function("program", sig);
        let bb = fb.create_block();
        fb.switch_to_block(bb);
        let p = fb.alloca(tup.clone());
        let a = fb.uconst(Ty::U8, 2);
        fb.store(Ty::U8, p, a);
        if write_u32 {
            let p4 = fb.gep_byte_offset(p, 4);
            let b = fb.uconst(Ty::U32, 40);
            fb.store(Ty::U32, p4, b);
        }
        let whole = fb.load(tup.clone(), p);
        let b = fb.extract_field(Ty::U32, whole, 1);
        let a = fb.extract_field(Ty::U8, whole, 0);
        let a = fb.cast(trust_ir::inst::CastOp::ZExt, Ty::U8, Ty::U32, a);
        let sum = fb.add(Ty::U32, a, b);
        fb.ret(vec![sum]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let m = build(true);
    assert_valid(&m);
    assert_eq!(run_u(&m), Ok(42));
    let twin = build(false);
    assert_valid(&twin);
    assert_uninit_at(&run_u(&twin), 4);
}
