// Fixture for the MIR-path CONSTANT-AGGREGATE call-arg (R1) and FAT-POINTER
// Cast/Transmute (R2) lowering gates
// (`real_lowering_acceptance.rs::mir_const_aggregate_arg_lowers_and_interprets`).
//
// R1 — `take_cfg` / `const_agg_trip`: a `const` STRUCT value (`CFG`, a 3×u64
//   Memory-repr aggregate) is passed BY VALUE as a call argument. The scalar-only
//   const path rejects it; the R1 lowering materializes its byte image into a
//   fresh stack slot (`materialize_const_aggregate`) and passes it by ref, exactly
//   the by-ref-aggregate convention the in-module callee `take_cfg` models its
//   `Cfg` param with. The callee XORs the three fields; the caller XORs the result
//   with its argument — so the trust-ir Interpreter differential (against the same
//   source compiled by the host rustc) exercises materialize -> pass-by-ref ->
//   field-load end to end.
//
// R2 — `fat_cast_probe`: builds a slice (`&arr` — an array->slice Unsize into a
//   fat slot), then casts the fat `&[u64]` to a thin `*const u64` (the fat-source
//   Cast the R2 fix extracts lane 0 for) and reads the slice length (fat metadata).
//   This is the EMIT+VALIDATE leg (a fat-pointer deref's runtime address has no
//   Interpreter provenance model, so it is checked for valid, re-parseable IR, not
//   run) — the same bar the MIR span-threading gate uses.
//
// The arithmetic is deliberately BITWISE-ONLY (`^` / `&` / int casts — no
// `+`/`-`/`*` that would emit a debug `Assert` edge the trust-ir Interpreter
// cannot execute yet; a pre-existing limitation orthogonal to what is under test).
//
// Compiled by the driver with `--crate-type=lib` (a reachable `pub fn` in a lib
// crate is a mono-collection root; no `main` needed). The acceptance test also
// `include!`s this file as the NATIVE ORACLE.

pub struct Cfg {
    pub a: u64,
    pub b: u64,
    pub c: u64,
}

// A `const` item: used directly as a call argument, it lowers to an
// `Operand::Constant` whose const-eval'd value is a 24-byte in-memory aggregate
// (`ConstValue::Indirect`) — the R1 materialization target.
pub const CFG: Cfg = Cfg {
    a: 0x0123_4567_89ab_cdef,
    b: 0x5a5a_5a5a_5a5a_5a5a,
    c: 0xffff_0000_ffff_0000,
};

// The in-module callee: a by-ref aggregate `Cfg` param, read field by field.
pub fn take_cfg(k: Cfg) -> u64 {
    k.a ^ k.b ^ k.c
}

// The caller: passes the CONST AGGREGATE `CFG` by value (R1), then folds the
// callee's result with its own argument.
pub fn const_agg_trip(x: u64) -> u64 {
    take_cfg(CFG) ^ x
}

// R2: a fat `&[u64]` -> thin `*const u64` cast (data-pointer extraction) plus a
// slice-length metadata read. Self-contained (no fat-pointer argument), so the
// driver's whole-closure emit exercises the fat-source cast + the array->slice
// Unsize fat-store on one function.
pub fn fat_cast_probe(n: u64) -> u64 {
    let arr: [u64; 4] = [n, n, n, n];
    let s: &[u64] = &arr;
    // A DIRECT fat -> thin reinterpret chain, lowered INLINE (not via a pulled-in
    // std `as_ptr`): `&[u64]` -> `*const [u64]` (fat -> fat reinterpret, the R2
    // fat-dst path) -> `*const u64` (fat -> thin, the R2 lane-0 data-pointer
    // extraction). The address is folded with the slice length (fat metadata).
    let fat: *const [u64] = s as *const [u64];
    let p: *const u64 = fat as *const u64;
    (p as usize as u64) & (s.len() as u64)
}
