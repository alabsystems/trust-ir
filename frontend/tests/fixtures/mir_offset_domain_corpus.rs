//! MIR `BinOp::Offset` semantic-domain fixture.
//!
//! Rust's raw-pointer `offset` takes a signed element count and permits a
//! negative step when the result stays within the same allocation. TrustIR GEP
//! cannot represent that negative-index behavior. The frontend retains GEP for
//! the proven-forward case and uses integer-pointer arithmetic for a dynamic
//! signed count, preserving the exact element stride in both lanes.

#![feature(core_intrinsics)]
#![allow(dead_code)]
#![allow(internal_features)]

#[inline(never)]
pub unsafe fn forward_wide_offset(ptr: *const u64) -> *const u64 {
    core::intrinsics::offset(ptr, 1_isize)
}

#[inline(never)]
pub unsafe fn dynamic_wide_offset(ptr: *const u64, count: isize) -> *const u64 {
    core::intrinsics::offset(ptr, count)
}

// Cross-crate MIR can retain the stable always-inline wrapper as a real call
// instead of exposing the intrinsic BinOp above. Keep that separate escape
// path under the same semantic-domain regression: it must inline, not become a
// bodyless core declaration.
#[inline(never)]
pub unsafe fn wrapper_forward_wide_offset(ptr: *const u64) -> *const u64 {
    ptr.offset(1)
}

#[inline(never)]
pub unsafe fn wrapper_dynamic_wide_offset(ptr: *const u64, count: isize) -> *const u64 {
    ptr.offset(count)
}

#[derive(Clone, Copy)]
pub struct Zst;

#[inline(never)]
pub unsafe fn dynamic_zst_offset(ptr: *const Zst, count: isize) -> *const Zst {
    core::intrinsics::offset(ptr, count)
}

#[inline(never)]
pub unsafe fn wrapper_dynamic_zst_offset(ptr: *const Zst, count: isize) -> *const Zst {
    ptr.offset(count)
}

fn main() {
    let values = [1_u64, 2, 3];
    unsafe {
        let _ = forward_wide_offset(values.as_ptr());
        let end = values.as_ptr().add(values.len());
        let _ = dynamic_wide_offset(end, -1);
        let _ = wrapper_forward_wide_offset(values.as_ptr());
        let _ = wrapper_dynamic_wide_offset(end, -1);
        let zst = Zst;
        let _ = dynamic_zst_offset(&zst, -1);
        let _ = wrapper_dynamic_zst_offset(&zst, -1);
    }
}
