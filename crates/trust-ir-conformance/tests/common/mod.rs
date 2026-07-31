// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Shared deterministic test infrastructure for the conformance property
// tests. Lives in `tests/common/mod.rs` (the subdirectory form) so Cargo
// treats it as a shared module rather than a standalone test binary.

#![allow(dead_code)] // Each test binary uses only the subset it needs.

use trust_ir::ty::Ty;

/// Integer-type palette shared by the property-test generators. Floats are
/// deliberately excluded everywhere: NaN breaks structural `==` (codec test)
/// and is covered by dedicated float fixtures.
pub const INT_TYPES: &[fn() -> Ty] = &[
    || Ty::I8,
    || Ty::I16,
    || Ty::I32,
    || Ty::I64,
    || Ty::I128,
    || Ty::U8,
    || Ty::U16,
    || Ty::U32,
    || Ty::U64,
    || Ty::U128,
];

pub fn int_ty(rng: &mut Rng) -> Ty {
    INT_TYPES[rng.bounded(INT_TYPES.len() as u32) as usize]()
}

/// Deterministic xorshift64 generator (no external `rand` dependency — the
/// `trust-ir` crate is zero-required-dep by policy, and a seeded generator is
/// reproducible across platforms so the property tests never flake).
pub struct Rng {
    state: u64,
}

impl Rng {
    pub fn new(seed: u64) -> Self {
        // Avoid the zero fixed-point of xorshift.
        Self {
            state: if seed == 0 {
                0x9E37_79B9_7F4A_7C15
            } else {
                seed
            },
        }
    }

    pub fn next_u64(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    pub fn bounded(&mut self, n: u32) -> u32 {
        if n == 0 {
            0
        } else {
            (self.next_u64() as u32) % n
        }
    }

    pub fn bool(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }

    pub fn one_of<T: Copy>(&mut self, xs: &[T]) -> T {
        xs[self.bounded(xs.len() as u32) as usize]
    }

    /// A small, type-range-safe constant magnitude (keeps integer operands
    /// well inside every width we generate).
    pub fn small(&mut self) -> i128 {
        (self.next_u64() % 64) as i128
    }
}
