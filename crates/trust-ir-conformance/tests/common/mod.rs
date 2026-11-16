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

/// Wildcard-free: a new `Ty` variant fails to compile here until it is
/// classified, so [`x86_cell_lane_tys`] cannot silently miss an integer type.
/// `true` exactly for the types `Ty::is_integer` admits.
fn is_integer_variant(ty: &Ty) -> bool {
    match ty {
        Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::Isize
        | Ty::U8
        | Ty::U16
        | Ty::U32
        | Ty::U64
        | Ty::U128
        | Ty::Usize => true,
        Ty::Char
        | Ty::Error
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Ptr
        | Ty::FatPtr(_)
        | Ty::Vector(_, _)
        | Ty::Unit
        | Ty::Never
        | Ty::Array(_, _)
        | Ty::Tuple(_)
        | Ty::Struct(_)
        | Ty::Enum(_)
        | Ty::Func(_)
        | Ty::FnItem(_)
        | Ty::Sequence(_)
        | Ty::Set(_, _)
        | Ty::Record(_)
        | Ty::Closure(_)
        | Ty::Refine(_, _)
        | Ty::Dialect(_)
        | Ty::Handle(_)
        | Ty::Storage(_)
        | Ty::Tensor(_, _)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Rc(_) => false,
        Ty::Ext(e) => e.unreachable(),
    }
}

/// The lane types of the x86-64 vector-compare cell shape `<count x
/// (bits-bit integer)>`: every integer `Ty` whose width at the 64-bit pointer
/// pin is `bits` and that the validator admits as a vector lane.
///
/// A cell is keyed by lane width and lane count alone: the
/// `chc_x86_vector_icmp_cell_status` reader ignores element signedness,
/// because the predicate carries it, and trust-cg's module-entry gate admits
/// any `Ty::is_integer` element by `Ty::bit_width_with(64)`. So `<4 x u32>` is
/// a lane type of the same cells as `<4 x i32>`, and a test of "every cell's
/// lane type" runs both. The set is read from the validator, not restated:
/// each candidate's vector type is validated, the admitted ones are returned,
/// and every other one must be refused as a vector type (today the
/// pointer-width and 128-bit lanes, `<2 x isize>` / `<2 x usize>`), so a
/// validator that starts admitting one puts it under these tests.
pub fn x86_cell_lane_tys(bits: u32, count: u32) -> Vec<Ty> {
    use trust_ir_build::validate::ValidationError;
    let mut admitted = Vec::new();
    for ty in [
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::Isize,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::U128,
        Ty::Usize,
    ] {
        assert!(
            is_integer_variant(&ty) && ty.is_integer(),
            "{ty} is an integer type"
        );
        if ty.bit_width_with(64) != Some(bits) {
            continue;
        }
        let vty = Ty::Vector(Box::new(ty.clone()), count);
        let mut mb = trust_ir_build::ModuleBuilder::new("x86_cell_lane_probe");
        let ft = mb.add_func_type(vec![vty.clone()], vec![vty.clone()]);
        let mut fb = mb.function("id", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, vty.clone());
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();
        let errors = trust_ir_build::validate_module(
            &mb.build().expect("ModuleBuilder::build: test fixture"),
        );
        if errors.is_empty() {
            admitted.push(ty);
        } else {
            assert!(
                errors.iter().all(|e| matches!(
                    e,
                    ValidationError::InvalidVectorType { .. }
                        | ValidationError::InvalidModuleVectorType { .. }
                )),
                "{vty} is either a well-formed vector or refused as a vector type: {errors:?}"
            );
        }
    }
    assert!(
        admitted.iter().any(Ty::is_signed) && admitted.iter().any(Ty::is_unsigned),
        "a {count} x {bits}-bit cell has a signed and an unsigned lane type: {admitted:?}"
    );
    admitted
}

/// The low `bits` of `pattern` as an integer VALUE of the lane type `ty`:
/// sign-extended for a signed type, as is for an unsigned one.
pub fn x86_cell_lane_value(ty: &Ty, bits: u32, pattern: u128) -> i128 {
    if ty.is_signed() {
        let shift = 128 - bits;
        ((pattern << shift) as i128) >> shift
    } else {
        pattern as i128
    }
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

pub mod exec_gen;
pub mod unwind_matrix;

pub mod target_model;
