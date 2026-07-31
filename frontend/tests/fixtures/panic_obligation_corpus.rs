// Fixture for the PANIC-CLASS OBLIGATION gate
// (`real_lowering_acceptance.rs::mir_emit_records_panic_class_obligations`).
//
// Each function below forces rustc to insert a specific
// `TerminatorKind::Assert` into MIR, which the frontend must record as one
// `Pending` `ProofObligation` scoped to the function that carries the check:
//
//   * `probe_bounds`   -> `AssertKind::BoundsCheck`      -> ObligationKind::BoundsCheck
//   * `probe_overflow` -> `AssertKind::Overflow(Add)`    -> ObligationKind::ArithmeticSafety
//   * `probe_div_zero` -> `AssertKind::DivisionByZero`   -> ObligationKind::ArithmeticSafety
//                       (+ `AssertKind::Overflow(Div)` — signed MIN / -1)
//
// The overflow/div asserts only exist with debug assertions ON, so the gate
// compiles this corpus with `-Cdebug-assertions=yes` (rustc's default at -O0,
// stated explicitly here so the fixture does not silently stop testing anything
// if the driver's default flags change).
//
// `main` must CALL each probe: `--mir-emit` walks
// `collect_and_partition_mono_items`, which only collects REACHABLE mono-items.
// `#[inline(never)]` keeps each probe a distinct mono-item so `--mir-emit
// <substring>` can select exactly one.

// A slice index: rustc inserts `Assert(BoundsCheck { len, index })`.
#[inline(never)]
pub fn probe_bounds(xs: &[i64], i: usize) -> i64 {
    xs[i]
}

// A checked add: rustc inserts `Assert(Overflow(Add, ..))`.
#[inline(never)]
pub fn probe_overflow(a: i64, b: i64) -> i64 {
    a + b
}

// A signed division: rustc inserts BOTH `Assert(DivisionByZero)` and
// `Assert(Overflow(Div, ..))` (the `i64::MIN / -1` case).
#[inline(never)]
pub fn probe_div_zero(a: i64, b: i64) -> i64 {
    a / b
}

fn main() {
    let xs = [1i64, 2, 3];
    let mut acc = probe_bounds(&xs, 1);
    acc = probe_overflow(acc, 3);
    acc = probe_div_zero(acc, 2);
    assert!(acc == 2);
}
