// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

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
