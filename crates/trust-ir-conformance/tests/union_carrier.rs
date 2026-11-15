// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Roadmap WS3.18 (F-050; F-030 companion): unions on the ratified
// byte-overlap carrier (G18-3). This file pins the producer guidance in
// `lowering-target-subset.md` ("Unions", "Producer guidance: carrier, access,
// moves and call edges"), one rule per section below:
//
//   1-2. a union value lives in an `[u8; N]` carrier and a field access is a
//        typed `Load`/`Store` at the carrier base (`bits(x: f32) -> u32`);
//   3.   a by-value move is `MemCopy` between carriers, which keeps
//        uninitialised bytes uninitialised; a whole `Load` of the carrier is
//        the forbidden spelling, and it faults;
//   4.   a union crosses a call edge by address (`byval` / `sret`, pass
//        `indirect`); a register lane cannot carry an uninitialised byte.
//        The move of rules 3-4 has a wire identity since `MemCopy`'s binary
//        tag landed (Inst tag 61, the v51 INST wire batch), like rules 1-2
//        ("Wire identity of the move");
//   5.   padding stays padding (WS2.14), field bytes stay strict;
//   6.   the struct spelling of a union is refused by name, and the rendered
//        refusal points at the carrier.
//
// Roadmap rows ported here, named after them:
//   * `goal-g1-g8/g1-unions` (field projection, `MaybeUninit` by-value move,
//     by-value passing, FFI register classification): `goal_g1_g8_g1_unions_*`;
//   * `producer-rust-thir/union-type`, FORMAT half only (the producer half is
//     WS5.17): `producer_rust_thir_union_type_*`.
// The ratchet `b6.union.overlapping_struct_fields_rejected` flips GAP -> PASS
// in `two_language/b6_data_carriers.rs`, and the positive `build_rc_tree(3)`
// fixture is the WS2.14 row `b6.enum.fieldwise_init_uninit_padding_is_ub_on_load`
// there.
//
// Every fixture that is meant to validate is also run, and a validated module
// may only end in `Ok` or `UndefinedBehavior`. Any other interpreter code
// would mean the validator and the interpreter disagree about the module
// (the `interpret_differential` property, stated per fixture here).

use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::{
    BodyGate, Endianness, EnumDef, EnumId, EnumLayoutDescriptor, EnumTagEncoding, EnumVariant,
    FieldDef, FuncAttrs, FuncId, Module, ParamAttrs, PassMode, StructDef, StructId, StructRepr,
    TargetInfo, TupleLayoutDescriptor, Ty, ValueId,
};
use trust_ir_build::validate::{STRUCT_FIELDS_OVERLAP_CARRIER_HINT, STRUCT_FIELDS_OVERLAP_REASON};
use trust_ir_build::{
    FunctionBuilder, ModuleBuilder, ValidationError, validate_module, validate_module_for_codegen,
};
use trust_ir_conformance::subset::module_subset_violations;

// ---------------------------------------------------------------------------
// Harness
// ---------------------------------------------------------------------------

/// Run `entry` (nullary). `Err` carries the interpreter's `code: message`.
fn run(module: &Module, entry: &str) -> Result<Vec<InterpretValue>, (InterpretErrorCode, String)> {
    let func = module
        .function_by_name(entry)
        .unwrap_or_else(|| panic!("no function @{entry}"));
    Interpreter::with_module(module)
        .execute_func(func.id, [])
        .map(|outcome| outcome.returns)
        .map_err(|e| (e.code, format!("{:?}: {e}", e.code)))
}

/// The fixture validates, and running it ends in `Ok` or in
/// `UndefinedBehavior` only (never a code that means the two disagree).
fn run_validated(module: &Module, entry: &str) -> Result<Vec<u128>, String> {
    let errors = validate_module(module);
    assert!(errors.is_empty(), "fixture must validate: {errors:?}");
    match run(module, entry) {
        Ok(values) => Ok(values
            .iter()
            .map(|v| {
                v.as_int()
                    .unwrap_or_else(|| panic!("non-integer return {v:?}"))
                    .as_unsigned()
            })
            .collect()),
        Err((InterpretErrorCode::UndefinedBehavior, message)) => Err(message),
        Err((code, message)) => {
            panic!(
                "a validated module must end in Ok or UndefinedBehavior, got {code:?}: {message}"
            )
        }
    }
}

fn assert_ub(out: &Result<Vec<u128>, String>, needle: &str) {
    assert!(
        matches!(out, Err(e) if e.starts_with("UndefinedBehavior") && e.contains(needle)),
        "expected UndefinedBehavior containing `{needle}`, got {out:?}"
    );
}

/// The poison-use refusal: an uninitialised byte was INSPECTED (returned,
/// passed, computed on), never answered with a fabricated value.
const POISON_USE: &str = "use of an uninitialized value";

fn gated(fb: &mut FunctionBuilder<'_>) {
    fb.set_body_gate(BodyGate::Gated {
        authority: "ws3.18".into(),
        evidence: None,
    });
}

/// One nullary `program() -> returns` over a fresh module whose type table
/// holds `u8` (for `[u8; N]` carriers). `setup` runs first on the builder, so a
/// fixture can add callees and structs.
fn program_module(
    name: &str,
    returns: Vec<Ty>,
    setup: impl FnOnce(&mut ModuleBuilder, trust_ir::TyId) -> Vec<FuncId>,
    body: impl FnOnce(&mut FunctionBuilder<'_>, trust_ir::TyId, &[FuncId]),
) -> Module {
    let mut mb = ModuleBuilder::new(name);
    let u8_ty = mb.add_type(Ty::U8);
    let callees = setup(&mut mb, u8_ty);
    let sig = mb.add_func_type(vec![], returns);
    let mut fb = mb.function("program", sig);
    gated(&mut fb);
    let bb = fb.create_block();
    fb.switch_to_block(bb);
    body(&mut fb, u8_ty, &callees);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A union carrier of `n` bytes at alignment `align` (rule 1).
fn carrier(fb: &mut FunctionBuilder<'_>, u8_ty: trust_ir::TyId, n: u64, align: u64) -> ValueId {
    fb.alloca_aligned(Ty::Array(u8_ty, n), align)
}

fn memcopy(fb: &mut FunctionBuilder<'_>, dst: ValueId, src: ValueId, n: u64) {
    // Target-free module: the byte count is exactly `u64` (WS3.20).
    let bytes = fb.uconst(Ty::U64, u128::from(n));
    fb.memcopy(dst, src, bytes, false);
}

/// `MaybeUninit<[u8; 8]>` with only its first two bytes written (`0xBEEF`,
/// little-endian at [0..2)); bytes [2..8) are NEVER written.
fn partial_union(fb: &mut FunctionBuilder<'_>, u8_ty: trust_ir::TyId) -> ValueId {
    let src = carrier(fb, u8_ty, 8, 8);
    let head = fb.uconst(Ty::U16, 0xBEEF);
    fb.store(Ty::U16, src, head);
    src
}

/// `struct {name}` with id 0 and the given `(name, type, offset)` fields. This
/// is the file's one `StructDef` literal, so a field added to `StructDef`
/// is a one-line change here and nowhere else.
fn struct_def(
    name: &str,
    fields: Vec<(&str, Ty, Option<u64>)>,
    size: Option<u64>,
    align: Option<u64>,
    repr: StructRepr,
) -> StructDef {
    StructDef {
        id: StructId::new(0),
        name: name.into(),
        fields: fields
            .into_iter()
            .map(|(name, ty, offset)| FieldDef {
                name: name.into(),
                ty,
                offset,
            })
            .collect(),
        size,
        align,
        repr,
        origin: None,
    }
}

// ---------------------------------------------------------------------------
// Rules 1-2: the carrier and a typed access at its base
// ---------------------------------------------------------------------------

/// `#[repr(C)] union U { i: u32, f: f32 }` and
/// `fn bits(x: f32) -> u32 { unsafe { U { f: x }.i } }`: write field `f`, read
/// field `i`, both at the carrier base. The whole body is inside the subset.
fn bits_module(x: f64) -> Module {
    program_module(
        "ws3_18_bits",
        vec![Ty::U32],
        |mb, u8_ty| {
            let sig = mb.add_func_type(vec![Ty::F32], vec![Ty::U32]);
            let mut fb = mb.function("bits", sig);
            gated(&mut fb);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let x = fb.add_block_param(entry, Ty::F32);
            // size 4 (largest field), align 4 (strictest field): both on the carrier.
            let u = fb.alloca_aligned(Ty::Array(u8_ty, 4), 4);
            fb.store_aligned(Ty::F32, u, x, 4);
            let i = fb.load_aligned(Ty::U32, u, 4);
            fb.ret(vec![i]);
            vec![fb.build()]
        },
        |fb, _u8, callees| {
            let x = fb.fconst(Ty::F32, x);
            let i = fb.call(callees[0], vec![x]);
            fb.ret(vec![i]);
        },
    )
}

/// REVIEW (rule 1, the alignment clause): the carrier's alignment is stated
/// on the `Alloca`, and that statement is load-bearing. `[u8; 8]` alone is
/// 1-aligned, so a carrier that omits `align` can land on an odd address
/// (here, right after a 1-byte slot), and the first 8-aligned typed access
/// faults there. The same body with `align 8` on the carrier runs.
#[test]
fn an_under_aligned_carrier_faults_on_its_first_wide_access() {
    let module = |align: Option<u64>| {
        program_module(
            "ws3_18_align",
            vec![Ty::U64],
            |_, _| vec![],
            move |fb, u8_ty, _| {
                let _flag = fb.alloca(Ty::U8);
                let u = match align {
                    Some(align) => carrier(fb, u8_ty, 8, align),
                    None => fb.alloca(Ty::Array(u8_ty, 8)),
                };
                let n = fb.uconst(Ty::U64, 5);
                fb.store(Ty::U64, u, n);
                let n = fb.load(Ty::U64, u);
                fb.ret(vec![n]);
            },
        )
    };
    assert_ub(
        &run_validated(&module(None), "program"),
        "is not aligned to 8",
    );
    assert_eq!(run_validated(&module(Some(8)), "program"), Ok(vec![5]));
}

#[test]
fn goal_g1_g8_g1_unions_field_projection_puns_through_the_carrier() {
    for (x, bits) in [
        (1.0_f32, 0x3F80_0000_u32),
        (-2.5, 0xC020_0000),
        (-0.0, 0x8000_0000),
    ] {
        let module = bits_module(f64::from(x));
        assert_eq!(
            run_validated(&module, "program"),
            Ok(vec![u128::from(bits)]),
            "bits({x})"
        );
        assert_eq!(x.to_bits(), bits, "the oracle is Rust's own f32::to_bits");
    }
    // Rules 1-2 use only subset constructs, and the carrier spelling is
    // admitted for codegen as it stands.
    let module = bits_module(1.0);
    assert_eq!(module_subset_violations(&module), Vec::<String>::new());
    assert_eq!(validate_module_for_codegen(&module), vec![]);
}

// ---------------------------------------------------------------------------
// Rule 3: a by-value move is MemCopy, and uninitialised bytes survive it
// ---------------------------------------------------------------------------

/// `let dst = src;` for the partial `MaybeUninit<[u8; 8]>` above, spelled as
/// `MemCopy` between two carriers; `probe` then reads the destination.
fn memcopy_move(
    returns: Vec<Ty>,
    probe: impl FnOnce(&mut FunctionBuilder<'_>, ValueId, ValueId),
) -> Module {
    program_module(
        "ws3_18_move",
        returns,
        |_, _| vec![],
        |fb, u8_ty, _| {
            let src = partial_union(fb, u8_ty);
            let dst = carrier(fb, u8_ty, 8, 8);
            memcopy(fb, dst, src, 8);
            probe(fb, dst, src);
        },
    )
}

#[test]
fn goal_g1_g8_g1_unions_maybe_uninit_moves_by_memcopy() {
    // POSITIVE: the move itself is defined, and the written field arrives.
    let module = memcopy_move(vec![Ty::U16], |fb, dst, _| {
        let head = fb.load(Ty::U16, dst);
        fb.ret(vec![head]);
    });
    assert_eq!(run_validated(&module, "program"), Ok(vec![0xBEEF]));

    // The never-written bytes are STILL uninitialised at the destination:
    // a strict (volatile) read of the wide field faults at the load ...
    let module = memcopy_move(vec![Ty::U64], |fb, dst, _| {
        let wide = fb.load_volatile(Ty::U64, dst);
        fb.ret(vec![wide]);
    });
    assert_ub(&run_validated(&module, "program"), "uninitialized");

    // ... and a plain read transports poison that faults once inspected. A
    // move that zero-filled bytes [2..8) would return 0xBEEF here instead.
    let module = memcopy_move(vec![Ty::U64], |fb, dst, _| {
        let wide = fb.load(Ty::U64, dst);
        fb.ret(vec![wide]);
    });
    assert_ub(&run_validated(&module, "program"), POISON_USE);
}

/// NEGATIVE TWIN: the forbidden spelling of the same move, a whole typed
/// `Load` of the `[u8; 8]` carrier into an SSA value. An array's elements
/// cover every byte (no byte of a carrier is padding), so the load faults at
/// the first never-written byte. The control shows the refusal is about the
/// uninitialised bytes, not about array loads: a FULLY written carrier moves
/// through an SSA `[u8; 8]` value without a fault.
#[test]
fn a_whole_carrier_load_is_not_a_union_move() {
    let typed_move = |fully_written: bool| {
        program_module(
            "ws3_18_typed_move",
            vec![Ty::U64],
            |_, _| vec![],
            move |fb, u8_ty, _| {
                let src = partial_union(fb, u8_ty);
                if fully_written {
                    let all = fb.uconst(Ty::U64, 0x0102_0304_0506_BEEF);
                    fb.store(Ty::U64, src, all);
                }
                let dst = carrier(fb, u8_ty, 8, 8);
                let value = fb.load(Ty::Array(u8_ty, 8), src);
                fb.store(Ty::Array(u8_ty, 8), dst, value);
                let wide = fb.load(Ty::U64, dst);
                fb.ret(vec![wide]);
            },
        )
    };
    assert_ub(
        &run_validated(&typed_move(false), "program"),
        "Load: reading uninitialized byte at offset 2",
    );
    assert_eq!(
        run_validated(&typed_move(true), "program"),
        Ok(vec![0x0102_0304_0506_BEEF])
    );
}

/// NEGATIVE TWIN kept from the ratification: a scalar read of carrier bytes
/// that were never written faults, with or without a move in between
/// (`union_byte_overlap_model.rs` pins the no-move half in `trust-ir`).
#[test]
fn a_scalar_read_of_never_written_carrier_bytes_still_faults() {
    let module = program_module(
        "ws3_18_unwritten",
        vec![Ty::U64],
        |_, _| vec![],
        |fb, u8_ty, _| {
            let src = carrier(fb, u8_ty, 8, 8);
            let dst = carrier(fb, u8_ty, 8, 8);
            memcopy(fb, dst, src, 8);
            let wide = fb.load_volatile(Ty::U64, dst);
            fb.ret(vec![wide]);
        },
    );
    assert_ub(&run_validated(&module, "program"), "uninitialized");
}

/// `union { p: *const u64, n: usize }`: a pointer stored through the union
/// and moved by `MemCopy` still dereferences at the destination. Provenance
/// travels with the bytes, so the move needs no pointer-typed special case.
#[test]
fn a_union_holding_a_pointer_moves_with_its_provenance() {
    let module = program_module(
        "ws3_18_ptr",
        vec![Ty::U64],
        |_, _| vec![],
        |fb, u8_ty, _| {
            let target = fb.alloca(Ty::U64);
            let seven = fb.uconst(Ty::U64, 7);
            fb.store(Ty::U64, target, seven);
            let src = carrier(fb, u8_ty, 8, 8);
            fb.store(Ty::Ptr, src, target);
            let dst = carrier(fb, u8_ty, 8, 8);
            memcopy(fb, dst, src, 8);
            let p = fb.load(Ty::Ptr, dst);
            let value = fb.load(Ty::U64, p);
            fb.ret(vec![value]);
        },
    );
    assert_eq!(run_validated(&module, "program"), Ok(vec![7]));
}

/// Rule 3's second half: a struct that CONTAINS a carrier field. The carrier's
/// bytes are field bytes, so a whole-struct `Load` of a struct holding a
/// partially written union faults inside the carrier. `MemCopy` of the whole
/// struct is the move that works. The struct's own padding (bytes [4..8)) is
/// still padding: with the carrier fully written, the whole load succeeds
/// although those four bytes were never written.
#[test]
fn a_struct_holding_a_union_moves_by_memcopy_too() {
    // `struct W { tag: u32 @0, u: [u8; 8] @8 }`, size 16, align 8.
    fn w_module(write_whole_union: bool, whole_load: bool) -> Module {
        program_module(
            "ws3_18_contained",
            vec![Ty::U32, Ty::U16],
            |mb, u8_ty| {
                mb.add_struct(struct_def(
                    "W",
                    vec![
                        ("tag", Ty::U32, Some(0)),
                        ("u", Ty::Array(u8_ty, 8), Some(8)),
                    ],
                    Some(16),
                    Some(8),
                    StructRepr::C,
                ));
                vec![]
            },
            move |fb, _u8, _| {
                let w_ty = Ty::Struct(StructId::new(0));
                let w = fb.alloca_aligned(w_ty.clone(), 8);
                let tag = fb.uconst(Ty::U32, 3);
                fb.store(Ty::U32, w, tag);
                let u = fb.gep_byte_offset(w, 8);
                if write_whole_union {
                    let all = fb.uconst(Ty::U64, 0xBEEF);
                    fb.store(Ty::U64, u, all);
                } else {
                    let head = fb.uconst(Ty::U16, 0xBEEF);
                    fb.store(Ty::U16, u, head);
                }
                let copy = fb.alloca_aligned(w_ty.clone(), 8);
                if whole_load {
                    let value = fb.load(w_ty.clone(), w);
                    fb.store(w_ty, copy, value);
                } else {
                    memcopy(fb, copy, w, 16);
                }
                let tag = fb.load(Ty::U32, copy);
                let cu = fb.gep_byte_offset(copy, 8);
                let head = fb.load(Ty::U16, cu);
                fb.ret(vec![tag, head]);
            },
        )
    }
    // The partial union makes the whole-struct load fault INSIDE the carrier.
    assert_ub(
        &run_validated(&w_module(false, true), "program"),
        "Load: reading uninitialized byte at offset 10",
    );
    // MemCopy moves the same struct.
    assert_eq!(
        run_validated(&w_module(false, false), "program"),
        Ok(vec![3, 0xBEEF])
    );
    // Control: a fully written union, never-written struct padding [4..8), and
    // the whole-struct load is defined (WS2.14: padding is not read).
    assert_eq!(
        run_validated(&w_module(true, true), "program"),
        Ok(vec![3, 0xBEEF])
    );
}

// ---------------------------------------------------------------------------
// Rule 4: call edges, by address
// ---------------------------------------------------------------------------

fn byval_indirect() -> ParamAttrs {
    ParamAttrs {
        byval: true,
        pass: Some(PassMode::Indirect { on_stack: false }),
        ..ParamAttrs::default()
    }
}

fn sret_indirect() -> ParamAttrs {
    ParamAttrs {
        sret: true,
        pass: Some(PassMode::Indirect { on_stack: false }),
        ..ParamAttrs::default()
    }
}

/// `extern "C" fn take(u: U) -> u16` with `U` classified MEMORY: the callee
/// receives the address of the caller's copy (`byval`, pass `indirect`), reads
/// field `head: u16`, optionally reads the wide field strictly, then scribbles
/// over its own copy (by value: the caller must not see it).
fn byval_module(callee_reads_wide: bool) -> Module {
    program_module(
        "ws3_18_byval",
        vec![Ty::U16, Ty::U16],
        |mb, _u8| {
            let sig = mb.add_func_type(vec![Ty::Ptr], vec![Ty::U16]);
            let mut fb = mb.function("take", sig);
            gated(&mut fb);
            fb.set_attrs(FuncAttrs {
                params: vec![byval_indirect()],
                ..FuncAttrs::default()
            });
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let u = fb.add_block_param(entry, Ty::Ptr);
            let head = fb.load(Ty::U16, u);
            if callee_reads_wide {
                let _wide = fb.load_volatile(Ty::U64, u);
            }
            let zero = fb.uconst(Ty::U16, 0);
            fb.store(Ty::U16, u, zero);
            fb.ret(vec![head]);
            vec![fb.build()]
        },
        |fb, u8_ty, callees| {
            let src = partial_union(fb, u8_ty);
            // The by-value copy, made explicit (rule 4).
            let arg = carrier(fb, u8_ty, 8, 8);
            memcopy(fb, arg, src, 8);
            let got = fb.call(callees[0], vec![arg]);
            let after = fb.load(Ty::U16, src);
            fb.ret(vec![got, after]);
        },
    )
}

/// `extern "C" fn make() -> U` with `U` classified MEMORY: the caller passes
/// the result carrier as the single `sret` pointer (pass `indirect`) and the
/// signature returns nothing. The callee writes only field `head: u16`.
fn sret_module(caller_reads_wide: bool) -> Module {
    program_module(
        "ws3_18_sret",
        vec![if caller_reads_wide { Ty::U64 } else { Ty::U16 }],
        |mb, _u8| {
            let sig = mb.add_func_type(vec![Ty::Ptr], vec![]);
            let mut fb = mb.function("make", sig);
            gated(&mut fb);
            fb.set_attrs(FuncAttrs {
                params: vec![sret_indirect()],
                ..FuncAttrs::default()
            });
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let out = fb.add_block_param(entry, Ty::Ptr);
            let head = fb.uconst(Ty::U16, 0xCAFE);
            fb.store(Ty::U16, out, head);
            fb.ret(vec![]);
            vec![fb.build()]
        },
        move |fb, u8_ty, callees| {
            let out = carrier(fb, u8_ty, 8, 8);
            fb.call_void(callees[0], vec![out]);
            let value = if caller_reads_wide {
                fb.load_volatile(Ty::U64, out)
            } else {
                fb.load(Ty::U16, out)
            };
            fb.ret(vec![value]);
        },
    )
}

#[test]
fn goal_g1_g8_g1_unions_by_value_passing_is_byval_and_sret() {
    // byval: the field arrives, and the callee's write to its copy never
    // reaches the caller's union.
    assert_eq!(
        run_validated(&byval_module(false), "program"),
        Ok(vec![0xBEEF, 0xBEEF])
    );
    // The never-written bytes crossed the edge UNINITIALISED: a strict read
    // of the wide field in the callee faults (a zero-filling copy would not).
    assert_ub(
        &run_validated(&byval_module(true), "program"),
        "uninitialized",
    );
    // sret: the written field comes back, the unwritten ones stay unwritten.
    assert_eq!(
        run_validated(&sret_module(false), "program"),
        Ok(vec![0xCAFE])
    );
    assert_ub(
        &run_validated(&sret_module(true), "program"),
        "uninitialized",
    );
}

/// MUTATION: the same `byval` fact on a slot that is not a pointer is refused
/// by name, so the by-address spelling is the one the validator admits, not
/// a fact it ignores.
#[test]
fn byval_on_a_non_pointer_slot_is_refused() {
    let mut module = byval_module(false);
    let take = module
        .functions
        .iter()
        .position(|f| f.name == "take")
        .expect("take");
    let sig = module
        .add_func_type(trust_ir::FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U16],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module.functions[take].ty = sig;
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::ParamAbiAttrInvalid { func_name, reason, .. }
                if func_name == "take" && *reason == "byval/sret require a pointer-typed parameter"
        )),
        "expected the named byval refusal, got {errors:?}"
    );
}

/// Where the target classifies a union into REGISTERS (`direct`), the lane is
/// a scalar loaded from the carrier. A FULLY written union crosses that way.
/// A partially written one cannot: the lane value is poison, and the
/// interpreter refuses poison across a call boundary. That is why rule 4
/// sends every possibly-uninitialised union through memory, and why a
/// producer must refuse such a register-classified call site by name.
#[test]
fn goal_g1_g8_g1_unions_register_lane_cannot_carry_uninit_bytes() {
    let lane_module = |fully_written: bool| {
        program_module(
            "ws3_18_lane",
            vec![Ty::U64],
            |mb, _u8| {
                let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
                let mut fb = mb.function("take_lane", sig);
                gated(&mut fb);
                fb.set_attrs(FuncAttrs {
                    params: vec![ParamAttrs {
                        pass: Some(PassMode::Direct),
                        ..ParamAttrs::default()
                    }],
                    ..FuncAttrs::default()
                });
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                let lane = fb.add_block_param(entry, Ty::U64);
                fb.ret(vec![lane]);
                vec![fb.build()]
            },
            move |fb, u8_ty, callees| {
                let src = partial_union(fb, u8_ty);
                if fully_written {
                    let all = fb.uconst(Ty::U64, 0xBEEF);
                    fb.store(Ty::U64, src, all);
                }
                let lane = fb.load(Ty::U64, src);
                let got = fb.call(callees[0], vec![lane]);
                fb.ret(vec![got]);
            },
        )
    };
    assert_eq!(
        run_validated(&lane_module(true), "program"),
        Ok(vec![0xBEEF])
    );
    let out = run_validated(&lane_module(false), "program");
    assert_ub(&out, "Call arguments");
    assert_ub(&out, POISON_USE);
}

// ---------------------------------------------------------------------------
// Wire identity of the move (REVIEW): MemCopy has a wire tag since v51
// ---------------------------------------------------------------------------

/// JSON, positional MessagePack and canonical text, each compared exactly.
/// Binary is checked separately below, with the header it selects.
fn lossless_without_binary(module: &Module) -> [(&'static str, bool); 3] {
    let json = serde_json::to_string(module).expect("json");
    let json_ok = serde_json::from_str::<Module>(&json).is_ok_and(|back| &back == module);
    let mp = rmp_serde::to_vec(module).expect("msgpack");
    let mp_ok = rmp_serde::from_slice::<Module>(&mp).is_ok_and(|back| &back == module);
    let text = trust_ir::format::canonical(module);
    let text_ok = trust_ir::parser::parse_module(&text)
        .is_ok_and(|back| back == trust_ir::format::canonicalize(module));
    [("json", json_ok), ("msgpack", mp_ok), ("text", text_ok)]
}

/// Rules 3 and 4 spell the move as `MemCopy`. Before the INST wire batch
/// (v51) it had no binary tag, so a module carrying one had NO wire identity
/// and the review pinned the named refusal here. Since v51 `MemCopy` is Inst
/// tag 61, so both rules' fixtures have a wire identity: no blocker, a binary
/// encoding at the batch version that decodes to the same module, and the
/// same digest either way. Every codec is RUN after its round trip, so each
/// keeps the move's meaning (the uninitialised bytes stay uninitialised).
/// CONTROL: rules 1-2 alone do not raise the header to the batch version.
#[test]
fn a_union_move_has_a_wire_identity_since_the_inst_wire_batch() {
    let head = memcopy_move(vec![Ty::U16], |fb, dst, _| {
        let head = fb.load(Ty::U16, dst);
        fb.ret(vec![head]);
    });
    let wide = memcopy_move(vec![Ty::U64], |fb, dst, _| {
        let wide = fb.load_volatile(Ty::U64, dst);
        fb.ret(vec![wide]);
    });
    for (label, module) in [
        ("rule 3 move", &head),
        ("rule 3 move, wide read", &wide),
        ("rule 4 byval copy", &byval_module(false)),
    ] {
        assert_eq!(
            trust_ir_build::wire_identity_blocker(module),
            None,
            "{label}: MemCopy has a wire tag"
        );
        let bytes =
            trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture");
        let (back, version) = trust_ir::binary::deserialize_module_with_wire_version(&bytes)
            .unwrap_or_else(|e| panic!("{label}: {e:?}"));
        assert_eq!(
            version.get(),
            trust_ir::binary::INST_WIRE_BATCH_FORMAT_VERSION,
            "{label}: the move selects the batch version"
        );
        assert_eq!(&back, module, "{label}: binary is lossless");
        assert_eq!(back.stable_digest(), module.stable_digest(), "{label}");
        let verdicts = lossless_without_binary(module);
        assert!(
            verdicts.iter().all(|(_, ok)| *ok),
            "{label}: lossy codec(s) {verdicts:?}"
        );
    }
    // The text- and binary-decoded moves still mean the same thing.
    let reparse = |module: &Module| {
        trust_ir::parser::parse_module(&trust_ir::format::canonical(module)).expect("parse")
    };
    let rebinary = |module: &Module| {
        trust_ir::binary::deserialize_module(
            &trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture"),
        )
        .expect("decode")
    };
    for decode in [&reparse as &dyn Fn(&Module) -> Module, &rebinary] {
        assert_eq!(run_validated(&decode(&head), "program"), Ok(vec![0xBEEF]));
        assert_ub(&run_validated(&decode(&wide), "program"), "uninitialized");
    }

    // CONTROL: the carrier and a typed access (rules 1-2) keep their older
    // header, and the binary round trip runs to the same bits.
    let bits = bits_module(-2.5);
    assert_eq!(trust_ir_build::wire_identity_blocker(&bits), None);
    let bytes = trust_ir::binary::serialize_module(&bits).expect("serialize_module: test fixture");
    let (back, version) =
        trust_ir::binary::deserialize_module_with_wire_version(&bytes).expect("decode");
    assert!(version.get() < trust_ir::binary::INST_WIRE_BATCH_FORMAT_VERSION);
    assert_eq!(back, bits);
    assert_eq!(run_validated(&back, "program"), Ok(vec![0xC020_0000]));
}

// ---------------------------------------------------------------------------
// Rule 5: padding stays padding, field bytes stay strict (WS2.14)
// ---------------------------------------------------------------------------

/// `struct S { x: u64, y: u8 }`, canonical layout: `x` @0, `y` @8, size 16,
/// padding [9..16). Field-wise init writes `x` (unless `skip_x`) and `y`.
fn s_module(
    returns: Vec<Ty>,
    skip_x: bool,
    tail: impl FnOnce(&mut FunctionBuilder<'_>, ValueId),
) -> Module {
    program_module(
        "ws3_18_padding",
        returns,
        |mb, _| {
            mb.add_struct(struct_def(
                "S",
                vec![("x", Ty::U64, None), ("y", Ty::U8, None)],
                None,
                None,
                StructRepr::default(),
            ));
            vec![]
        },
        move |fb, _u8, _| {
            let s = fb.alloca(Ty::Struct(StructId::new(0)));
            if !skip_x {
                let x = fb.uconst(Ty::U64, 42);
                fb.store(Ty::U64, s, x);
            }
            let py = fb.gep_byte_offset(s, 8);
            let y = fb.uconst(Ty::U8, 1);
            fb.store(Ty::U8, py, y);
            tail(fb, s);
        },
    )
}

#[test]
fn padding_is_not_read_but_field_bytes_stay_strict() {
    let s_ty = Ty::Struct(StructId::new(0));
    // POSITIVE: field-wise init, whole load, project field 0.
    let whole = |skip_x: bool| {
        let s_ty = s_ty.clone();
        s_module(vec![Ty::U64], skip_x, move |fb, s| {
            let value = fb.load(s_ty, s);
            let x = fb.extract_field(Ty::U64, value, 0);
            fb.ret(vec![x]);
        })
    };
    assert_eq!(run_validated(&whole(false), "program"), Ok(vec![42]));
    // MUTATION: a FIELD byte never written still faults, at its offset. A
    // relaxation that also skipped field bytes would return here.
    assert_ub(
        &run_validated(&whole(true), "program"),
        "Load: reading uninitialized byte at offset 0",
    );
}

/// REVIEW (padding round trip): load a struct with never-written padding,
/// store it into a fresh slot, then read a padding byte. The whole-aggregate
/// `Store` writes padding UNINITIALISED, so the byte is poison and returning
/// it faults. An implementation that zero-fills padding returns `Ok(0)` and
/// fails here. Control: the same read of a FIELD byte of the copy is defined.
#[test]
fn a_stored_padding_byte_is_poison_never_zero() {
    let s_ty = Ty::Struct(StructId::new(0));
    let round_trip = |offset: u64| {
        let s_ty = s_ty.clone();
        s_module(vec![Ty::U8], false, move |fb, s| {
            let value = fb.load(s_ty.clone(), s);
            let fresh = fb.alloca(s_ty.clone());
            fb.store(s_ty, fresh, value);
            let p = fb.gep_byte_offset(fresh, offset);
            let byte = fb.load(Ty::U8, p);
            fb.ret(vec![byte]);
        })
    };
    assert_ub(&run_validated(&round_trip(9), "program"), POISON_USE);
    assert_eq!(run_validated(&round_trip(8), "program"), Ok(vec![1]));
}

// ---------------------------------------------------------------------------
// Rule 6: the struct spelling of a union is refused, toward the carrier
// ---------------------------------------------------------------------------

/// `union U { i: u32, f: f32 }` spelled the way `producer-rust-thir/union-type`
/// asked for it: a `StructDef` whose two fields share offset 0 (size 4,
/// align 4). `f_offset = 4` (size 8) is the disjoint twin.
fn struct_spelled_union(f_offset: u64, size: u64, pin: bool) -> Module {
    let mut mb = if pin {
        ModuleBuilder::new_with_target_info(
            "ws3_18_struct_union",
            TargetInfo {
                triple: "x86_64-unknown-linux-gnu".into(),
                pointer_size: 8,
                endianness: Endianness::Little,
                abi: None,
                struct_passing: trust_ir::StructPassingPolicy::Unclassified,
            },
        )
    } else {
        ModuleBuilder::new("ws3_18_struct_union")
    };
    mb.add_struct(struct_def(
        "U",
        vec![("i", Ty::U32, Some(0)), ("f", Ty::F32, Some(f_offset))],
        Some(size),
        Some(4),
        StructRepr::C,
    ));
    let u_ty = Ty::Struct(StructId::new(0));
    let sig = mb.add_func_type(vec![], vec![Ty::U32]);
    let mut fb = mb.function("program", sig);
    gated(&mut fb);
    let bb = fb.create_block();
    fb.switch_to_block(bb);
    let u = fb.alloca(u_ty.clone());
    let one = fb.fconst(Ty::F32, 1.0);
    let pf = fb.gep_byte_offset(u, f_offset);
    fb.store(Ty::F32, pf, one);
    let i = fb.uconst(Ty::U32, 7);
    fb.store(Ty::U32, u, i);
    let whole = fb.load(u_ty, u);
    let field = fb.extract_field(Ty::U32, whole, 0);
    fb.ret(vec![field]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn overlap_refusal() -> ValidationError {
    ValidationError::StructLayoutInconsistent {
        struct_id: 0,
        reason: STRUCT_FIELDS_OVERLAP_REASON,
    }
}

#[test]
fn producer_rust_thir_union_type_struct_spelling_is_refused_toward_the_carrier() {
    for pin in [false, true] {
        let module = struct_spelled_union(0, 4, pin);
        // Exactly ONE named refusal, on both entry points.
        assert_eq!(
            validate_module(&module),
            vec![overlap_refusal()],
            "pin={pin}"
        );
        assert_eq!(
            validate_module_for_codegen(&module),
            vec![overlap_refusal()],
            "pin={pin}"
        );
    }
    // The machine-readable reason is the WS2.3 one, unchanged ...
    assert_eq!(STRUCT_FIELDS_OVERLAP_REASON, "fields overlap");
    // ... and the RENDERED refusal names the carrier and where it is ratified.
    let rendered = overlap_refusal().to_string();
    assert_eq!(
        rendered,
        format!(
            "struct #0: declared layout is inconsistent: fields overlap{STRUCT_FIELDS_OVERLAP_CARRIER_HINT}"
        )
    );
    for needle in [
        "a union is not a struct",
        "byte-overlap carrier",
        "[u8; N]",
        "typed Load/Store per access",
        "lowering-target-subset.md \"Unions\"",
        "G18-3",
    ] {
        assert!(
            rendered.contains(needle),
            "`{needle}` missing from: {rendered}"
        );
    }

    // The interpreter, handed the same module unvalidated, refuses the layout
    // and points at the carrier too.
    let ran = run(&struct_spelled_union(0, 4, false), "program");
    assert!(
        matches!(&ran, Err((InterpretErrorCode::TypeError, e))
            if e.contains("overlapping fields 0 and 1") && e.contains("byte-overlap carrier")),
        "{ran:?}"
    );
}

/// MUTATION CONTROLS for rule 6. (a) The disjoint twin validates and runs, so
/// the refusal is about the overlap, not the declared offsets. (b) Another
/// layout reason renders WITHOUT the carrier hint, so the hint is attached to
/// the overlap reason only. (c) The same union on the carrier validates (the
/// `bits` fixture above), so the refusal never blocks the ratified spelling.
#[test]
fn the_carrier_hint_rides_on_the_overlap_reason_only() {
    // (a)
    let disjoint = struct_spelled_union(4, 8, false);
    assert_eq!(run_validated(&disjoint, "program"), Ok(vec![7]));
    // (b)
    let other = ValidationError::StructLayoutInconsistent {
        struct_id: 0,
        reason: "field offset is outside the declared struct size",
    };
    assert_eq!(
        other.to_string(),
        "struct #0: declared layout is inconsistent: field offset is outside the declared struct size"
    );
    assert!(!other.to_string().contains("carrier"));
    // (c)
    assert_eq!(validate_module(&bits_module(1.0)), vec![]);
}

/// REVIEW (rule 6, the other doors): the struct is not the only aggregate
/// that declares field offsets. A producer turned away from the struct
/// spelling could try the other two: a declared TUPLE layout (v42), or a
/// one-variant UNTAGGED enum (v37), each with both fields at offset 0. Both
/// are refused as well. Each has a disjoint twin that validates, so each
/// refusal is about the overlap.
#[test]
fn no_other_overlapping_aggregate_spells_a_union() {
    let pinned = || TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    };
    // `(u32, f32)` with a declared layout. Tuple layouts need a pinned target.
    let tuple = |f_offset: u64, size: u64| {
        let mut mb = ModuleBuilder::new_with_target_info("ws3_18_tuple_union", pinned());
        let tuple_ty = mb.add_type(Ty::Tuple(vec![Ty::U32, Ty::F32]));
        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
        module.tuple_layouts.push(TupleLayoutDescriptor {
            tuple_type: tuple_ty,
            size,
            align: 4,
            field_offsets: vec![0, f_offset],
        });
        module
    };
    let refused = validate_module(&tuple(0, 4));
    assert!(
        matches!(refused.as_slice(), [ValidationError::TupleLayoutInconsistent { reason }]
            if reason.contains("incoherent")),
        "overlapping tuple layout: {refused:?}"
    );
    assert_eq!(validate_module(&tuple(4, 8)), vec![], "disjoint tuple twin");

    // `enum U { V(u32, f32) }` with an untagged descriptor.
    let untagged = |f_offset: u64, size: u64| {
        let mut mb = ModuleBuilder::new("ws3_18_enum_union");
        let mut def = EnumDef::new(
            EnumId::new(0),
            "U",
            vec![EnumVariant {
                name: "V".into(),
                fields: vec![Ty::U32, Ty::F32],
                field_names: vec![],
            }],
        );
        def.layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Untagged,
            size,
            align: 4,
            variant_field_offsets: vec![vec![0, f_offset]],
        });
        mb.add_enum(def);
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let refused = validate_module(&untagged(0, 4));
    assert!(
        matches!(refused.as_slice(), [ValidationError::ConstTypeMismatch { actual, .. }]
            if actual.contains("fields 0 and 1 overlap")),
        "overlapping untagged enum: {refused:?}"
    );
    assert_eq!(
        validate_module(&untagged(4, 8)),
        vec![],
        "disjoint enum twin"
    );
}

/// The hint cites `lowering-target-subset.md` "Unions"; the section and the
/// producer guidance it points to must exist (a conformance test reads the
/// root doc at run time, as `lowering_subset.rs` does).
#[test]
fn the_cited_section_exists() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let doc = std::fs::read_to_string(root.join("lowering-target-subset.md"))
        .expect("read lowering-target-subset.md");
    assert!(doc.contains("### Unions — the byte-overlap model is RATIFIED (G18-3"));
    assert!(doc.contains("#### Producer guidance: carrier, access, moves and call edges"));
    assert!(doc.contains("crates/trust-ir-conformance/tests/union_carrier.rs"));
    // The move's wire-identity consequence is stated, not left implicit.
    assert!(doc.contains("**Wire identity of the move.**"));
    assert!(doc.contains("`ModuleHasNoWireIdentity`"));
}
