//! Wrapping signed pointer-offset coverage for the TrustIR integer-pointer lane.
//!
//! TrustIR GEP rejects negative indices and models allocation-relative
//! addition; Rust's `arith_offset` / `wrapping_offset` accept negative counts
//! and wrap the address. Both forms must lower as `ptrtoint + count * stride`
//! followed by `inttoptr`, never as GEP or a stride-erased extern call.

#![feature(core_intrinsics)]
#![allow(internal_features)]

#[inline(never)]
pub unsafe fn wrapping_wide_offset(ptr: *mut u64, count: isize) -> *mut u64 {
    core::intrinsics::arith_offset(ptr, count) as *mut u64
}

#[inline(never)]
pub fn stable_wrapping_wide_offset(ptr: *mut u64, count: isize) -> *mut u64 {
    ptr.wrapping_offset(count)
}

fn main() {
    let mut values = [1_u64, 2, 3];
    unsafe {
        let end = values.as_mut_ptr().add(values.len());
        let _ = wrapping_wide_offset(end, -1);
        let _ = stable_wrapping_wide_offset(end, -1);
    }
}
