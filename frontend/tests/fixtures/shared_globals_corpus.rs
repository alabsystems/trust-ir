//! Each member contributes literals; repeated bytes must share module identity.
#![allow(dead_code)]

#[inline(never)]
pub fn byte_at(s: &str) -> u8 {
    s.as_bytes()[0]
}
#[inline(never)]
pub fn first() -> u8 {
    byte_at("u")
}
#[inline(never)]
pub fn second() -> u8 {
    byte_at("v")
}
#[inline(never)]
pub fn repeated() -> u8 {
    byte_at("u")
}
#[inline(never)]
pub fn shared_globals_root() -> u32 {
    ((byte_at("A") as u32) << 24)
        | ((first() as u32) << 16)
        | ((second() as u32) << 8)
        | repeated() as u32
}

pub trait Value {
    fn get(&self) -> u64;
}
impl Value for u64 {
    fn get(&self) -> u64 {
        *self
    }
}
impl Value for u32 {
    fn get(&self) -> u64 {
        *self as u64
    }
}
#[inline(never)]
pub fn vtable_u64(value: &u64) -> &dyn Value {
    value
}
#[inline(never)]
pub fn vtable_u64_repeat(value: &u64) -> &dyn Value {
    value
}
#[inline(never)]
pub fn vtable_u32(value: &u32) -> &dyn Value {
    value
}
#[inline(never)]
pub fn shared_vtables_root(a: &u64, b: &u32) -> u64 {
    byte_at("A") as u64 + vtable_u64(a).get() + vtable_u64_repeat(a).get() + vtable_u32(b).get()
}
