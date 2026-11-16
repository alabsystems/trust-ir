// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Target-indexed scalar decisions and the actual lowering helpers, exercised
//! without requiring a cross-target sysroot or executing native code.

use super::*;
use trust_ir::interpret::Interpreter;

fn builder(bits: u32) -> ModuleBuilder {
    ModuleBuilder::new_with_target_info(
        "pointer-width",
        trust_ir::TargetInfo {
            triple: if bits == 32 {
                "wasm32-unknown-unknown"
            } else {
                "x86_64-unknown-linux-gnu"
            }
            .into(),
            pointer_size: bits / 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        },
    )
}

fn run(
    bits: u32,
    emit: impl FnOnce(&mut trust_ir_build::FunctionBuilder<'_>) -> trust_ir::ValueId,
) -> i128 {
    let mut mb = builder(bits);
    let sig = mb.add_func_type(vec![], vec![TIRTy::I128]);
    let mut fb = mb.function("boundary", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let value = emit(&mut fb);
    fb.ret(vec![value]);
    fb.build();
    let module = mb.build().expect("build target-width fixture");
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    Interpreter::with_module(&module)
        .execute_func(module.functions[0].id, vec![])
        .expect("execute target-width fixture")
        .returns[0]
        .as_int()
        .expect("integer result")
        .as_signed()
}

#[test]
fn source_pointer_scalar_width_matches_target_and_memory_abi() {
    for (bits, signed, unsigned, bytes) in [
        (32, TIRTy::I32, TIRTy::U32, 4),
        (64, TIRTy::I64, TIRTy::U64, 8),
    ] {
        assert_eq!(pointer_sized_int_ty(bits, true), Some(signed.clone()));
        assert_eq!(pointer_sized_int_ty(bits, false), Some(unsigned.clone()));
        assert_eq!(int_bit_width(&signed), Some(bits));
        assert_eq!(int_lane_size(&unsigned), bytes);
        assert_eq!(
            switch_int_case_value(&signed, bits, bits, (1_u128 << bits) - 1),
            Ok(Constant::Int(-1))
        );
    }
    for unsupported in [0, 16, 48, 128] {
        assert_eq!(pointer_sized_int_ty(unsupported, false), None);
        assert_eq!(pointer_sized_int_ty(unsupported, true), None);
    }
}

#[test]
fn pointer_scalar_wrap_and_integer_casts_have_source_width_semantics() {
    for bits in [32, 64] {
        let unsigned = pointer_sized_int_ty(bits, false).unwrap();
        let signed = pointer_sized_int_ty(bits, true).unwrap();
        assert_eq!(
            run(bits, |fb| {
                let max = fb.iconst(unsigned.clone(), ((1_u128 << bits) - 1) as i128);
                let one = fb.iconst(unsigned.clone(), 1);
                let wrapped = fb.binop(BinOp::Add, unsigned.clone(), max, one);
                int_cast(fb, wrapped, &unsigned, &TIRTy::I128)
            }),
            0
        );
        assert_eq!(
            run(bits, |fb| {
                let wide = fb.iconst(TIRTy::U64, (1_i128 << 32) + 7);
                let narrow = int_cast(fb, wide, &TIRTy::U64, &unsigned);
                int_cast(fb, narrow, &unsigned, &TIRTy::I128)
            }),
            if bits == 32 { 7 } else { (1_i128 << 32) + 7 }
        );
        assert_eq!(
            run(bits, |fb| {
                let min = fb.iconst(signed.clone(), -(1_i128 << (bits - 1)));
                int_cast(fb, min, &signed, &TIRTy::I128)
            }),
            -(1_i128 << (bits - 1))
        );
    }
}

#[test]
fn pointer_scalar_memory_access_and_element_stride_agree() {
    for bits in [32, 64] {
        let lane = pointer_sized_int_ty(bits, false).unwrap();
        assert_eq!(
            run(bits, |fb| {
                let bytes = u64::from(bits / 8);
                let slot = fb.alloca(slot_lane_ty(2 * bytes, bytes).unwrap());
                fb.note_alloc_extent(slot, 2 * bytes);
                let index = fb.iconst(TIRTy::I32, 1);
                let next = fb.gep(lane.clone(), slot, vec![index]);
                let first = ptr_int_cast(fb, slot, &TIRTy::Ptr, &lane, bits).unwrap();
                let second = ptr_int_cast(fb, next, &TIRTy::Ptr, &lane, bits).unwrap();
                let stride = fb.binop(BinOp::Sub, lane.clone(), second, first);
                let max = fb.iconst(lane.clone(), ((1_u128 << bits) - 1) as i128);
                fb.store(lane.clone(), next, max);
                let loaded = fb.load(lane.clone(), next);
                let one = fb.iconst(lane.clone(), 1);
                let wrapped = fb.binop(BinOp::Add, lane.clone(), loaded, one);
                let sum = fb.binop(BinOp::Add, lane.clone(), stride, wrapped);
                int_cast(fb, sum, &lane, &TIRTy::I128)
            }),
            i128::from(bits / 8)
        );
    }
}

#[test]
fn pointer_casts_and_signed_offsets_use_the_target_address_lane() {
    for bits in [32, 64] {
        let lane = pointer_sized_int_ty(bits, false).unwrap();
        assert_eq!(
            run(bits, |fb| {
                let wide = fb.iconst(TIRTy::U64, (1_i128 << 32) + 12);
                let ptr = ptr_int_cast(fb, wide, &TIRTy::U64, &TIRTy::Ptr, bits).unwrap();
                let back = ptr_int_cast(fb, ptr, &TIRTy::Ptr, &TIRTy::U64, bits).unwrap();
                int_cast(fb, back, &TIRTy::U64, &TIRTy::I128)
            }),
            if bits == 32 { 12 } else { (1_i128 << 32) + 12 }
        );
        assert_eq!(
            run(bits, |fb| {
                let address = fb.iconst(lane.clone(), 100);
                let ptr = ptr_int_cast(fb, address, &lane, &TIRTy::Ptr, bits).unwrap();
                let minus_one = fb.iconst(TIRTy::I32, -1);
                let moved =
                    pointer_offset_value(fb, ptr, minus_one, &TIRTy::I32, 4, bits, true).unwrap();
                let back = ptr_int_cast(fb, moved, &TIRTy::Ptr, &lane, bits).unwrap();
                int_cast(fb, back, &lane, &TIRTy::I128)
            }),
            96
        );
    }
}

#[test]
fn mismatched_pointer_transmute_remains_refused() {
    let mut mb = builder(32);
    let sig = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("refused", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let ptr = fb.null_ptr();
    assert!(transmute_cast(&mut fb, ptr, &TIRTy::Ptr, &TIRTy::U64, 32).is_err());
    assert!(ptr_int_cast(&mut fb, ptr, &TIRTy::Ptr, &TIRTy::U32, 16).is_err());
}
