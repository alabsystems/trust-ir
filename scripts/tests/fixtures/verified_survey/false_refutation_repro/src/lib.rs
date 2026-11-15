//! One function per false-refutation shape of the installed Trust seal
//! (scripts/verified_survey.py, SHAPES). Each comment says why the refuted
//! operation cannot fail.

/// Shape (a): an index walk bounded by a slice length, so `i += 1` cannot
/// overflow. The L0 `arithmetic_overflow_add` row PROVES; its
/// `hardened_panic_boundary` twin is refuted with `slice_len = 2^64`.
pub fn count_args(args: &[String]) -> usize {
    let mut i = 0;
    while i < args.len() {
        i += 1;
    }
    i
}

/// Shape (c), control: `Box::new` never yields null (allocation failure
/// aborts). This isolated call PROVES; that check refutes only inside larger
/// bodies, so its ledger rows are their own evidence.
pub fn boxed(x: u64) -> Box<u64> {
    Box::new(x)
}

/// Shape (c), refuted in isolation: a nest of boxed elements, the shape of
/// trust-ir's `Ty::Vector(Box<Ty>, u32)`.
pub enum Nest {
    Leaf(u32),
    Boxed(Box<Nest>, u32),
}

impl Nest {
    /// `elem.width()` reads through the `Box<Nest>`, and MIR asserts that the
    /// reference it builds there is not null. A Box's pointer is never null,
    /// yet the native CHC/PDR runner refutes that `assertion` row and its
    /// `hardened_panic_boundary` twin, both at `elem` (published demoted to
    /// unknown, naming `refuted obligation`). This is `Ty::bit_width`'s vector
    /// arm (crates/trust-ir/src/ty.rs), reduced; measured 2026-10-01.
    pub fn width(&self) -> Option<u32> {
        match self {
            Nest::Leaf(bits) => Some(*bits),
            Nest::Boxed(elem, lanes) => elem.width().and_then(|bits| bits.checked_mul(*lanes)),
        }
    }
}

/// Shape (b): `digits[i] -= 1` runs only when `digits[i] > 0`, and `i` stays
/// below `digits.len()`; the guard is lost to slice-length symbol
/// proliferation, and the subtraction, the slice check and `i += 1` refute.
pub fn dec_first_nonzero(digits: &mut [u8]) {
    let mut i = 0;
    while i < digits.len() {
        if digits[i] > 0 {
            digits[i] -= 1;
            break;
        }
        digits[i] = 9;
        i += 1;
    }
}

/// Shape (d): `i128::from(x)` is at most `u64::MAX`, so `+ 1` cannot
/// overflow an i128; the counterexample takes the widened value as
/// `i128::MAX` while `x = 0`.
pub fn widen_past_u64(x: u64) -> i128 {
    i128::from(x) + 1
}

/// Shape (d), a constant: `u64::from(u32::MAX) + 1` is 2^32.
pub fn past_u32() -> u64 {
    u64::from(u32::MAX) + 1
}

/// Shape (b), a range: `width - 1 - i` runs only inside `for i in 0..width`,
/// so `width >= 1` and `i < width`; the range guard is lost and both
/// subtractions are refuted (the ctlz encoding of trust-ir-ay has this shape).
pub fn reverse_indices(width: u32) -> u32 {
    let mut acc = 0;
    for i in 0..width {
        acc ^= width - 1 - i;
    }
    acc
}

/// Shape (e): `u32::try_from(n).expect(..)` returns only when `n <= u32::MAX`,
/// so `n + 1` cannot overflow a u64; the fact the call establishes is lost.
pub fn next_after_checked(n: u64) -> u64 {
    let _ = u32::try_from(n).expect("fits");
    n + 1
}

/// Shape (e): after `push`, `len() >= 1`, so `len() - 1` cannot underflow.
pub fn last_index(v: &mut Vec<u8>) -> usize {
    v.push(0);
    v.len() - 1
}
