// Fixture for the MIR-path BY-VALUE SMALL-PAIR RETURN ABI gate (RUNG 10,
// `real_lowering_acceptance.rs::mir_pair_by_value_return_lowers_and_interprets`
// under `--mir-pair-ret-by-value`, and the default-off sret pin
// `mir_pair_return_defaults_to_sret_without_flag`).
//
// Each producer below returns a 2-int-lane `BackendRepr::ScalarPair`
// struct/tuple, which the MIR lowering under the opt-in flag must return BY
// VALUE as a single SSA 2-tuple (`functy ... -> ((..., ...))`, NO leading sret
// pointer param):
//
//   * `mk_pair`   — a named 2-field struct (u64@0, u32@8: declaration order ==
//                   memory order).
//   * `mk_tuple`  — a homogeneous `(u64, u64)` tuple.
//   * `swap_wide` — a mixed-width `(u32, u64)` tuple (rustc keeps 2-tuples in
//                   source order: u32@0, u64@8).
//   * `mk_rev`    — a `struct Rev { tag: u8, val: u32 }` rustc REORDERS
//                   (val@0, tag@4). Pins the OFFSET-ORDERED lane contract: the
//                   emitted return type is `(u32, u8)` while `.tag`/`.val`
//                   reads keep going through the destination slot at the
//                   faithful `layout_of` offsets.
//   * `pair_trip` — the caller shape: consumes all four by-value results via
//                   field reads, so the emitted closure module exercises BOTH
//                   the callee `ret` side and the caller spill side.
//
// The acceptance test ALSO `include!`s this file as the NATIVE ORACLE, so the
// trust-ir Interpreter differential runs against the same source compiled by
// the host rustc. The arithmetic is deliberately BITWISE-ONLY (`^` / `&` / `|`
// and int casts — no +/-/*//` that would emit a debug `Assert` edge): unoptimized
// MIR guards those with an `Assert` whose lowering compares bools (`icmp eq
// bool cond, false`), a shape the trust-ir Interpreter cannot execute yet (a
// pre-existing interpreter limitation, orthogonal to the pair-return ABI under
// test here; the trust-cg JIT path executes it fine).
//
// Compiled by the driver with `--crate-type=lib` (a reachable `pub fn` in a lib
// crate is a mono-collection root; no `main` needed).

pub struct Pair {
    pub hi: u64,
    pub lo: u32,
}

pub fn mk_pair(x: u64, y: u32) -> Pair {
    Pair {
        hi: x ^ 0x0123_4567_89ab_cdef,
        lo: y ^ 0x5a5a,
    }
}

pub fn mk_tuple(x: u64, y: u64) -> (u64, u64) {
    (x & y, x ^ y)
}

pub fn swap_wide(a: u32, b: u64) -> (u32, u64) {
    ((b & 0xffff) as u32, (a as u64) ^ b)
}

pub struct Rev {
    pub tag: u8,
    pub val: u32,
}

pub fn mk_rev(t: u8, v: u32) -> Rev {
    Rev {
        tag: t ^ 0x2a,
        val: v ^ 0x00ff_00ff,
    }
}

pub fn pair_trip(x: u64, y: u32) -> u64 {
    let p = mk_pair(x, y);
    let t = mk_tuple(p.hi, p.lo as u64);
    let s = swap_wide(y, t.0);
    let r = mk_rev(y as u8, s.0);
    t.1 ^ s.1 ^ (s.0 as u64) ^ (r.tag as u64) ^ (r.val as u64)
}
