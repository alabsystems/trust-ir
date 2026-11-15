//! Panic-abort MIR fixture for the emit-closure EXTERN TABLE.
//!
//! Two closure members each reach the same extern callee (`memmove`, via the
//! size-scaled `copy` intrinsic). Before the closure-wide extern table, each
//! member declared its own 0-block `memmove`, so the emitted module carried two
//! functions with one link-time symbol — which trust-ir's own validator refuses
//! since v41 (`DuplicateFunctionSymbol`).

#![feature(core_intrinsics)]
#![allow(dead_code)]
#![allow(internal_features)]

#[inline(never)]
pub unsafe fn copy_a(dst: *mut u64, src: *const u64, count: usize) {
    core::intrinsics::copy(src, dst, count);
}

#[inline(never)]
pub unsafe fn copy_b(dst: *mut u64, src: *const u64, count: usize) {
    core::intrinsics::copy(src, dst, count);
}

#[inline(never)]
pub unsafe fn shared_extern_root(dst: *mut u64, src: *const u64, count: usize) {
    copy_a(dst, src, count);
    copy_b(dst, src, count);
}
