#![allow(dead_code)]

// Keep this as a direct scalar return so the MIR frontend must materialize the
// upper half of the unsigned 128-bit constant domain in TrustIR.
pub fn u128_max_const() -> u128 {
    u128::MAX
}
