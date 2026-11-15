// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! The real switch literal helper, with explicit target widths, not host
//! `isize::BITS`. These are representation tests, not an ABI/source theorem.

use super::switch_int_case_value;
use trust_ir::{Constant, Ty};

#[test]
fn pointer_sized_switch_literals_use_the_requested_target_width() {
    for width in [32_u32, 64] {
        let sign = 1_u128 << (width - 1);
        let max = (1_u128 << width) - 1;
        for (bits, expected) in [
            (0, 0),
            (sign - 1, (sign - 1) as i128),
            (sign, -(sign as i128)),
            (max, -1),
        ] {
            assert_eq!(
                switch_int_case_value(&Ty::Isize, width, width, bits),
                Ok(Constant::Int(expected))
            );
        }
        assert_eq!(
            switch_int_case_value(&Ty::Usize, width, width, max),
            Ok(Constant::Int(max as i128))
        );
    }
    // The same zero-extended MIR pattern has different signed readings on
    // the two targets. A hard-coded/host width must not make these identical.
    assert_eq!(
        switch_int_case_value(&Ty::Isize, 32, 32, u32::MAX as u128),
        Ok(Constant::Int(-1))
    );
    assert_eq!(
        switch_int_case_value(&Ty::Isize, 64, 64, u32::MAX as u128),
        Ok(Constant::Int(i128::from(u32::MAX)))
    );
}

#[test]
fn widened_pointer_selector_mismatches_refuse_instead_of_masking_the_abi_gap() {
    for selector in [Ty::I64, Ty::U64] {
        for bits in [0, 1, u32::MAX as u128] {
            let error = switch_int_case_value(&selector, 32, 32, bits).unwrap_err();
            assert_eq!(error, format!(
                "switch selector source width 32 differs from emitted {selector} width 64 on a 32-bit pointer target"));
        }
    }
    assert_eq!(
        switch_int_case_value(&Ty::I32, 32, 64, u32::MAX as u128),
        Ok(Constant::Int(-1))
    );
    assert_eq!(
        switch_int_case_value(&Ty::I64, 64, 32, u64::MAX as u128),
        Ok(Constant::Int(-1))
    );
    // The target is consulted only for pointer-sized lanes. Fixed-width
    // signed integers remain fixed-width on every pointer target.
}

#[test]
fn integer_case_spelling_keeps_signed_values_and_canonical_unsigned_magnitudes() {
    for (selector, width, bits, expected) in [
        (Ty::I8, 8, 255, Constant::Int(-1)),
        (Ty::I16, 16, 32768, Constant::Int(i128::from(i16::MIN))),
        (
            Ty::I32,
            32,
            1_u128 << 31,
            Constant::Int(i128::from(i32::MIN)),
        ),
        (
            Ty::I64,
            64,
            1_u128 << 63,
            Constant::Int(i128::from(i64::MIN)),
        ),
        (Ty::I128, 128, 1_u128 << 127, Constant::Int(i128::MIN)),
        (Ty::I128, 128, u128::MAX, Constant::Int(-1)),
        (Ty::U128, 128, i128::MAX as u128, Constant::Int(i128::MAX)),
        (Ty::U128, 128, 1_u128 << 127, Constant::U128(1_u128 << 127)),
        (Ty::U128, 128, u128::MAX, Constant::U128(u128::MAX)),
    ] {
        assert_eq!(
            switch_int_case_value(&selector, width, 64, bits),
            Ok(expected)
        );
    }
    // U128's actual lowering still uses the existing uconst/Eq/CondBr chain.
    // These helper controls are not a claim that this patch repairs that path.
    assert_eq!(
        switch_int_case_value(&Ty::Char, 32, 64, 65),
        Ok(Constant::Int(65))
    );
}

#[test]
fn malformed_case_patterns_and_noninteger_selectors_remain_refused() {
    for (selector, width, bits) in [(Ty::I8, 8, 256), (Ty::U32, 32, 1_u128 << 32)] {
        assert!(switch_int_case_value(&selector, width, 64, bits)
            .unwrap_err()
            .contains("does not fit its source width"));
    }
    for selector in [Ty::Bool, Ty::Ptr] {
        assert!(switch_int_case_value(&selector, 64, 64, 0)
            .unwrap_err()
            .contains("has no integer representation"));
    }
}
