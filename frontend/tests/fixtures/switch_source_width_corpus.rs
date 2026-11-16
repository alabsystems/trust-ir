// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

#![feature(core_intrinsics, custom_mir)]
#![allow(internal_features)]

use std::intrinsics::mir::*;

pub fn signed_pointer_match(x: isize) -> i32 {
    match x {
        -1 => 10,
        isize::MIN => 20,
        5 => 30,
        _ => 0,
    }
}

const HIGH_U128: u128 = 1_u128 << 127;

pub fn unsigned_wide_match(x: u128) -> i32 {
    match x {
        u128::MAX => 10,
        HIGH_U128 => 20,
        5 => 30,
        _ => 0,
    }
}

#[inline(never)]
fn advance_aggregate_index_slot(index: &mut usize) {
    *index = (*index + 1) % 3;
}

// Optimized-dialect custom MIR prevents Rust's normal index temporary from
// hiding the address-taken projection that the frontend explicitly supports.
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn memory_backed_aggregate_index(mut index: usize) -> u64 {
    mir! {
        let row0: (u64, u64);
        let row1: (u64, u64);
        let row2: (u64, u64);
        let values: [(u64, u64); 3];
        let slot: &mut usize;
        let unit: ();
        let left: u64;
        let right: u64;

        {
            row0 = (101_u64, 1001_u64);
            row1 = (202_u64, 2002_u64);
            row2 = (303_u64, 3003_u64);
            values = [row0, row1, row2];
            slot = &mut index;
            Call(unit = advance_aggregate_index_slot(slot), ReturnTo(project), UnwindContinue())
        }
        project = {
            left = values[index].0;
            right = values[index].1;
            RET = left + right;
            Return()
        }
    }
}
