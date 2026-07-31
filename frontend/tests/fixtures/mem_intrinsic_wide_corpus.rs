//! Panic-abort MIR fixture for size-scaled raw-memory intrinsics.
//!
//! Each helper uses `u64` elements so an element count and a byte count differ
//! by a visible stride of eight. Direct intrinsic calls keep the regression on
//! the exact MIR shape the frontend recognizes.

#![feature(core_intrinsics)]
#![allow(dead_code)]
#![allow(internal_features)]

#[inline(never)]
pub unsafe fn wide_copy(dst: *mut u64, src: *const u64, count: usize) {
    core::intrinsics::copy(src, dst, count);
}

#[inline(never)]
pub unsafe fn wide_write(dst: *mut u64, count: usize) {
    core::intrinsics::write_bytes(dst, 0xa5, count);
}

#[inline(never)]
pub unsafe fn mem_intrinsic_wide(dst: *mut u64, src: *const u64, count: usize) {
    wide_copy(dst, src, count);
    wide_write(dst, count);
}

#[derive(Clone, Copy)]
pub struct Zst;

#[inline(never)]
pub unsafe fn zst_copy(dst: *mut Zst, src: *const Zst, count: usize) {
    core::intrinsics::copy(src, dst, count);
}

#[inline(never)]
pub unsafe fn zst_write(dst: *mut Zst, count: usize) {
    core::intrinsics::write_bytes(dst, 0xa5, count);
}

#[inline(never)]
pub unsafe fn mem_intrinsic_zst(dst: *mut Zst, src: *const Zst, count: usize) {
    zst_copy(dst, src, count);
    zst_write(dst, count);
}

#[inline(never)]
pub unsafe fn stable_free_copy(dst: *mut u64, src: *const u64, count: usize) {
    std::ptr::copy(src, dst, count);
}

#[inline(never)]
pub unsafe fn stable_free_copy_nonoverlapping(
    dst: *mut u64,
    src: *const u64,
    count: usize,
) {
    std::ptr::copy_nonoverlapping(src, dst, count);
}

#[inline(never)]
pub unsafe fn stable_copy_to(dst: *mut u64, src: *const u64, count: usize) {
    src.copy_to(dst, count);
}

#[inline(never)]
pub unsafe fn stable_copy_to_nonoverlapping(
    dst: *mut u64,
    src: *const u64,
    count: usize,
) {
    src.copy_to_nonoverlapping(dst, count);
}

#[inline(never)]
pub unsafe fn stable_copy_from(dst: *mut u64, src: *const u64, count: usize) {
    dst.copy_from(src, count);
}

#[inline(never)]
pub unsafe fn stable_copy_from_nonoverlapping(
    dst: *mut u64,
    src: *const u64,
    count: usize,
) {
    dst.copy_from_nonoverlapping(src, count);
}

#[inline(never)]
pub unsafe fn stable_free_write(dst: *mut u64, count: usize) {
    std::ptr::write_bytes(dst, 0xa5, count);
}

#[inline(never)]
pub unsafe fn stable_method_write(dst: *mut u64, count: usize) {
    dst.write_bytes(0xa5, count);
}

#[inline(never)]
pub unsafe fn stable_mem_wrappers_wide(dst: *mut u64, src: *const u64, count: usize) {
    stable_free_copy(dst, src, count);
    stable_free_copy_nonoverlapping(dst, src, count);
    stable_copy_to(dst, src, count);
    stable_copy_to_nonoverlapping(dst, src, count);
    stable_copy_from(dst, src, count);
    stable_copy_from_nonoverlapping(dst, src, count);
    stable_free_write(dst, count);
    stable_method_write(dst, count);
}

#[inline(never)]
pub unsafe fn stable_mem_wrappers_zst(dst: *mut Zst, src: *const Zst, count: usize) {
    core::ptr::copy(src, dst, count);
    core::ptr::copy_nonoverlapping(src, dst, count);
    src.copy_to(dst, count);
    src.copy_to_nonoverlapping(dst, count);
    dst.copy_from(src, count);
    dst.copy_from_nonoverlapping(src, count);
    core::ptr::write_bytes(dst, 0xa5, count);
    dst.write_bytes(0xa5, count);
}

fn main() {
    let mut dst = [0_u64; 4];
    let src = [1_u64, 2, 3, 4];
    unsafe {
        mem_intrinsic_wide(dst.as_mut_ptr(), src.as_ptr(), src.len());
        let mut zst_dst = [Zst, Zst, Zst, Zst];
        let zst_src = [Zst, Zst, Zst, Zst];
        mem_intrinsic_zst(zst_dst.as_mut_ptr(), zst_src.as_ptr(), zst_src.len());
        stable_mem_wrappers_wide(dst.as_mut_ptr(), src.as_ptr(), src.len());
        stable_mem_wrappers_zst(zst_dst.as_mut_ptr(), zst_src.as_ptr(), zst_src.len());
    }
}
