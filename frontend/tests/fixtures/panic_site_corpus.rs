// Fixture for the PANIC-SITE gate (trust-ir amendment P, wire v53):
// `real_lowering_acceptance.rs::mir_asserts_lower_to_sited_asserts_in_both_lanes`
// and its siblings.
//
// Each probe forces rustc to insert a `TerminatorKind::Assert`, which the
// frontend must lower to ONE sited trust-ir check — a sited `assert` (or an
// `assert_invoke` when the check's unwind action enters cleanup) naming the
// check's kind, its `core::panicking` entry and its `Location` — never a
// branch into an `unreachable` trap and never a branch into a call:
//
//   * `probe_site_bounds`    -> `AssertKind::BoundsCheck`  (no cleanup)
//   * `probe_site_overflow`  -> `AssertKind::Overflow(Add)` (no cleanup)
//   * `probe_site_tracked`   -> a `#[track_caller]` body: under panic=unwind
//                               its location is the caller's (a forwarded
//                               parameter), under panic=abort its own
//   * `probe_site_cleanup`   -> a bounds check while a `String` is live, so
//                               under panic=unwind the check's unwind action
//                               is `Cleanup` (the `String` must be dropped)
//
// The overflow assert only exists with debug assertions ON, so the gate
// compiles this corpus with `-Cdebug-assertions=yes`. `main` calls each probe
// (`--mir-emit` lowers only reachable mono-items); `#[inline(never)]` keeps
// each a distinct mono-item.

#[inline(never)]
pub fn probe_site_bounds(xs: &[i64], i: usize) -> i64 {
    xs[i]
}

#[inline(never)]
pub fn probe_site_overflow(a: i64, b: i64) -> i64 {
    a + b
}

#[track_caller]
#[inline(never)]
pub fn probe_site_tracked(xs: &[i64], i: usize) -> i64 {
    xs[i]
}

#[inline(never)]
pub fn probe_site_cleanup(xs: &[i64], i: usize) -> i64 {
    let label = String::from("live across the check");
    let value = xs[i];
    value + label.len() as i64
}

fn main() {
    let xs = [1i64, 2, 3];
    let mut acc = probe_site_bounds(&xs, 1);
    acc = probe_site_overflow(acc, 3);
    acc += probe_site_tracked(&xs, 2);
    acc += probe_site_cleanup(&xs, 0);
    assert!(acc > 0);
}
