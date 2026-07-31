// Fixture for the MIR-path BY-VALUE SMALL-PAIR PARAM ABI gate (RUNG 11, the DUAL
// of the RUNG 10 by-value pair RETURN), driven by
// `real_lowering_acceptance.rs::mir_pair_by_value_param_lowers_and_interprets`
// under `--mir-pair-ret-by-value`, and the default-off by-ref pin
// `mir_pair_param_defaults_to_byref_without_flag`.
//
// Each CONSUMER below takes a 2-int-lane `BackendRepr::ScalarPair` struct/tuple BY
// VALUE, which the MIR lowering under the opt-in flag must accept as a single SSA
// 2-tuple PARAM (`functy ((..., ...)) -> ...`, NO by-ref leading `Ptr` param), then
// spill into the param's entry slot so the body's layout-faithful field reads work:
//
//   * `sum_pair`  — a named 2-field struct param `Pair { hi: u64, lo: u32 }`
//                   (u64@0, u32@8: declaration order == memory order).
//   * `sum_tuple` — a homogeneous `(u64, u64)` tuple param (no inter-lane padding).
//   * `take_rev`  — a `Rev { tag: u8, val: u32 }` param rustc REORDERS (val@0,
//                   tag@4). Pins the OFFSET-ORDERED lane contract for PARAMS: the
//                   accepted param type is `(u32, u8)` while `.tag`/`.val` reads go
//                   through the slot at the faithful `layout_of` offsets.
//
// The PRODUCERS (`mk_pair`/`mk_tuple`/`mk_rev`) return the same pairs BY VALUE
// (RUNG 10), so in the whole-program closure `param_trip` every by-value pair ARG
// originates from a by-value RETURN whose spill Store zero-fills inter-lane padding
// — the caller-side whole-aggregate Load of the pair arg then reads a fully-defined
// byte image (the exact dual of RUNG 10's `_0` entry zero-fill). `param_trip`
// exercises BOTH the caller side (by-value arg Load) and the callee side (SSA-tuple
// param + entry spill) of the by-value pair PARAM ABI end-to-end.
//
// The acceptance test ALSO `include!`s this file as the NATIVE ORACLE, so the
// trust-ir Interpreter differential runs against the same source compiled by the
// host rustc. The arithmetic is deliberately BITWISE-ONLY (`^` / `&` and int casts,
// no +/-/*/ that would emit a debug `Assert` edge the interpreter cannot execute).
//
// Compiled by the driver with `--crate-type=lib` (a reachable `pub fn` in a lib
// crate is a mono-collection root; no `main` needed).

pub struct Pair {
    pub hi: u64,
    pub lo: u32,
}

pub struct Rev {
    pub tag: u8,
    pub val: u32,
}

// A 24-byte aggregate: too wide for the ScalarPair register band, so it stays a
// by-ref (`Ptr`) param / sret return. Exercises the RUNG 11 `byval`/`sret`
// ParamAttrs pins on the aggregates that KEEP crossing through memory.
pub struct Big {
    pub a: u64,
    pub b: u64,
    pub c: u64,
}

// ---- producers (RUNG 10 by-value returns) --------------------------------------

pub fn mk_pair(x: u64, y: u32) -> Pair {
    Pair {
        hi: x ^ 0x0123_4567_89ab_cdef,
        lo: y ^ 0x5a5a,
    }
}

pub fn mk_tuple(x: u64, y: u64) -> (u64, u64) {
    (x & y, x ^ y)
}

pub fn mk_rev(t: u8, v: u32) -> Rev {
    Rev {
        tag: t ^ 0x2a,
        val: v ^ 0x00ff_00ff,
    }
}

// A >16-byte aggregate RETURN: keeps the sret hidden pointer (RUNG 11 pins `sret`).
pub fn mk_big(x: u64) -> Big {
    Big {
        a: x,
        b: x ^ 0x00ff,
        c: x ^ 0xff00,
    }
}

// ---- consumers (RUNG 11 by-value params) ---------------------------------------

pub fn sum_pair(p: Pair) -> u64 {
    p.hi ^ (p.lo as u64)
}

pub fn sum_tuple(t: (u64, u64)) -> u64 {
    t.0 ^ t.1
}

pub fn take_rev(r: Rev) -> u64 {
    (r.val as u64) ^ (r.tag as u64)
}

// A >16-byte aggregate PARAM: keeps the by-ref `Ptr` (RUNG 11 pins `byval`).
pub fn big_first(g: Big) -> u64 {
    g.a ^ g.b ^ g.c
}

// ---- whole-program trip (caller by-value arg + callee spill) --------------------

pub fn param_trip(x: u64, y: u32) -> u64 {
    let p = mk_pair(x, y);
    let a = sum_pair(p);
    let t = mk_tuple(x, y as u64);
    let b = sum_tuple(t);
    let r = mk_rev(y as u8, (x as u32) ^ y);
    let c = take_rev(r);
    let g = mk_big(x);
    let d = big_first(g);
    a ^ b ^ c ^ d
}
