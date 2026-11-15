#![allow(dead_code)]

// Integer `match`es lowered through MIR `SwitchInt`, whose targets carry each
// arm as the selector's bit pattern zero-extended to `u128` (the `-1` arm of an
// `i8` match is `255`). A TrustIR switch case is the selector's VALUE in its
// type's one spelling (SPEC_RATIFICATIONS §3.3), so the signed selectors must
// come out sign-extended and the unsigned one unchanged.

pub fn signed_byte_match(x: i8) -> i32 {
    match x {
        -1 => 10,
        -128 => 20,
        5 => 30,
        _ => 0,
    }
}

pub fn signed_word_match(x: i64) -> i32 {
    match x {
        -1 => 10,
        i64::MIN => 20,
        _ => 0,
    }
}

pub fn unsigned_byte_match(x: u8) -> i32 {
    match x {
        255 => 10,
        0 => 20,
        _ => 0,
    }
}

// Pointer-width selectors. The driver maps `isize` / `usize` to the
// fixed-width `i64` / `u64` (its host-only type map), so the `-1` arm of the
// `isize` match arrives as `2^64 - 1` and must be sign-extended at `i64`.

pub fn signed_pointer_match(x: isize) -> i32 {
    match x {
        -1 => 10,
        isize::MIN => 20,
        _ => 0,
    }
}

pub fn unsigned_pointer_match(x: usize) -> i32 {
    match x {
        usize::MAX => 10,
        0 => 20,
        _ => 0,
    }
}
