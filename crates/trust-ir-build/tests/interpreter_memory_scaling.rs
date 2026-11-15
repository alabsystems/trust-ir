// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// ══════════════════════════════════════════════════════════════════════════
// The reference interpreter's host memory does not grow with VALUES.
// ══════════════════════════════════════════════════════════════════════════
//
// The owner's principle: memory and time scale with the program TEXT (and
// the instructions a run executes), never with values in it — array lengths,
// copy counts, lane counts. Every scenario below is a program of a few
// dozen instructions whose byte counts or lengths are 2^30..2^40. The
// assertion is a SCALING one, not a threshold: each scenario's peak heap
// at a large `N` is compared with the same program's peak at a small `N`.
//
// A counting `#[global_allocator]` measures the peak. It also makes a
// regression fail FAST: while the large run executes, any allocation that
// would take the heap past the scaled small-run peak aborts the test binary
// ("memory allocation of … failed"), so a regression to an O(N)
// representation costs megabytes, never the host (the huge-`N` tests in
// `array_splat.rs` would otherwise find it only by exhausting memory).
//
// The scenarios are the review findings of 2026-09-23 on the first version
// of this branch, each of which grew ~5–140 bytes of host memory per byte of
// the value:
//
//   * the doubling `MemCopy` of `<[T]>::repeat` (copy `[0, k)` to `[k, 2k)`);
//   * the same doubling with a distinct byte written between copies, loaded
//     back as ONE array value (a DAG of memory, decoded structurally);
//   * a stored `[u16; N]` splat loaded as `[u8; 2N]`, and a stored
//     `[[u8; 3]; N]` splat loaded as `[u8; 3N]` (type punning at a stride the
//     stored period does not divide — the transmute-fail shape);
//   * an `alloca <N x i64>` filled by `MemSet`, loaded as a vector and added
//     to itself (a vector value is a structural array value too).
//
// Plus the `InsertElement` chain: filling an array element by element keeps
// O(height) new nodes per insert (O(n log n) in total), where the pre-v50
// interpreter cloned the array on every insert (O(n^2)).

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use trust_ir::constant::Constant;
use trust_ir::interpret::{InterpretOptions, Interpreter};
use trust_ir::{CastOp, Module, Ty};
use trust_ir_build::{ModuleBuilder, validate_module};

struct Counting;

static CURRENT: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
/// Allocations that would take `CURRENT` above this fail (and so abort).
static CEILING: AtomicUsize = AtomicUsize::new(usize::MAX);

// SAFETY: every method forwards to `System` with the caller's layout and only
// adds bookkeeping; a refused allocation returns null, which is the
// `GlobalAlloc` contract for failure.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let now = CURRENT.fetch_add(layout.size(), Ordering::SeqCst) + layout.size();
        if now > CEILING.load(Ordering::SeqCst) {
            CURRENT.fetch_sub(layout.size(), Ordering::SeqCst);
            return core::ptr::null_mut();
        }
        PEAK.fetch_max(now, Ordering::SeqCst);
        // SAFETY: forwarded unchanged.
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        CURRENT.fetch_sub(layout.size(), Ordering::SeqCst);
        // SAFETY: forwarded unchanged.
        unsafe { System.dealloc(ptr, layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let grow = new_size.saturating_sub(layout.size());
        let now = CURRENT.fetch_add(grow, Ordering::SeqCst) + grow;
        if now > CEILING.load(Ordering::SeqCst) {
            CURRENT.fetch_sub(grow, Ordering::SeqCst);
            return core::ptr::null_mut();
        }
        PEAK.fetch_max(now, Ordering::SeqCst);
        // SAFETY: forwarded unchanged.
        let moved = unsafe { System.realloc(ptr, layout, new_size) };
        if !moved.is_null() {
            CURRENT.fetch_sub(layout.size().saturating_sub(new_size), Ordering::SeqCst);
        }
        moved
    }
}

#[global_allocator]
static ALLOCATOR: Counting = Counting;

/// The counters are process-wide: scenarios run one at a time.
static SERIAL: Mutex<()> = Mutex::new(());

/// Run `@probe` of `module` and return (its result, the peak heap growth
/// while it ran). `ceiling` bounds that growth eagerly.
fn measure(module: &Module, ceiling: Option<usize>) -> (i128, usize) {
    let func = module.function_by_name("probe").expect("@probe");
    let interpreter = Interpreter::with_module(module).with_options(InterpretOptions {
        fuel: 1_000_000,
        max_call_depth: 64,
        ..InterpretOptions::default()
    });
    let base = CURRENT.load(Ordering::SeqCst);
    PEAK.store(base, Ordering::SeqCst);
    if let Some(ceiling) = ceiling {
        CEILING.store(base + ceiling, Ordering::SeqCst);
    }
    let outcome = interpreter.execute_func(func.id, vec![]);
    CEILING.store(usize::MAX, Ordering::SeqCst);
    let peak = PEAK.load(Ordering::SeqCst) - base;
    let returns = outcome.expect("@probe executes").returns;
    let value = returns[0].as_int().expect("an integer result").as_signed();
    (value, peak)
}

/// The same program at `2^small` and `2^large`: the large run's peak heap may
/// be at most `factor` times the small run's (plus 64 KiB of slack). The
/// scaled bound is enforced WHILE the large run executes. `factor` allows the
/// program's own growth (its instruction count and the O(log N) height of
/// the structures grow with `log2 N`); an O(N) regression is `2^(large -
/// small)` times the small peak, a factor of a million or more here.
fn assert_value_independent(
    scenario: &str,
    build: impl Fn(u32) -> Module,
    (small, large): (u32, u32),
    factor: usize,
    expected: impl Fn(u32) -> i128,
) {
    let _serial = SERIAL
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let slack = 64 << 10;
    let small_module = build(small);
    assert_eq!(validate_module(&small_module), [], "{scenario} validates");
    let (value, small_peak) = measure(&small_module, None);
    assert_eq!(value, expected(small), "{scenario} at 2^{small}");
    let large_module = build(large);
    let bound = factor * small_peak + slack;
    let (value, large_peak) = measure(&large_module, Some(bound));
    assert_eq!(value, expected(large), "{scenario} at 2^{large}");
    assert!(
        large_peak <= bound,
        "{scenario}: peak heap {large_peak} B at 2^{large} vs {small_peak} B at 2^{small}"
    );
}

fn zext_to_i64(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    byte: trust_ir::ValueId,
) -> trust_ir::ValueId {
    fb.cast(CastOp::ZExt, Ty::U8, Ty::I64, byte)
}

/// `alloca [u8 x n]`, two byte stores, doubling copies; then read the last
/// byte (`whole == false`) or load the whole region as one array value and
/// extract it.
fn doubling_copy(log2: u32, whole: bool) -> Module {
    let n = 1u64 << log2;
    let mut mb = ModuleBuilder::new("doubling_copy");
    let u8_id = mb.add_type(Ty::U8);
    let bytes = Ty::Array(u8_id, n);
    let ft = mb.add_func_type(vec![], vec![Ty::I64]);
    {
        let mut fb = mb.function("probe", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let a = fb.alloca(bytes.clone());
        let zero = fb.iconst(Ty::U64, 0);
        let one = fb.iconst(Ty::U64, 1);
        let p0 = fb.gep(Ty::U8, a, vec![zero]);
        let p1 = fb.gep(Ty::U8, a, vec![one]);
        let v1 = fb.iconst(Ty::U8, 1);
        let v2 = fb.iconst(Ty::U8, 2);
        fb.store(Ty::U8, p0, v1);
        fb.store(Ty::U8, p1, v2);
        let mut k = 2u64;
        while k < n {
            let off = fb.iconst(Ty::U64, i128::from(k));
            let dst = fb.gep(Ty::U8, a, vec![off]);
            let count = fb.iconst(Ty::U64, i128::from(k));
            fb.memcopy(dst, a, count, false);
            k *= 2;
        }
        let last = fb.iconst(Ty::U64, i128::from(n - 1));
        let byte = if whole {
            let value = fb.load(bytes, a);
            fb.extract_element(Ty::U8, value, last)
        } else {
            let at = fb.gep(Ty::U8, a, vec![last]);
            fb.load(Ty::U8, at)
        };
        let result = zext_to_i64(&mut fb, byte);
        fb.ret(vec![result]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Doubling copies with a distinct separator byte between them, the rest of
/// the region `MemSet`, and the whole region loaded as one array value.
fn interleaved_copy(log2: u32) -> Module {
    let n = 1u64 << log2;
    let mut mb = ModuleBuilder::new("interleaved_copy");
    let u8_id = mb.add_type(Ty::U8);
    let bytes = Ty::Array(u8_id, n);
    let ft = mb.add_func_type(vec![], vec![Ty::I64]);
    {
        let mut fb = mb.function("probe", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let a = fb.alloca(bytes.clone());
        let zero = fb.iconst(Ty::U64, 0);
        let first = fb.iconst(Ty::U8, 0);
        let p0 = fb.gep(Ty::U8, a, vec![zero]);
        fb.store(Ty::U8, p0, first);
        let mut filled = 1u64;
        let mut step = 1i128;
        while 2 * filled < n {
            let at = fb.iconst(Ty::U64, i128::from(filled));
            let separator = fb.gep(Ty::U8, a, vec![at]);
            let value = fb.iconst(Ty::U8, step);
            fb.store(Ty::U8, separator, value);
            let off = fb.iconst(Ty::U64, i128::from(filled + 1));
            let dst = fb.gep(Ty::U8, a, vec![off]);
            let count = fb.iconst(Ty::U64, i128::from(filled));
            fb.memcopy(dst, a, count, false);
            filled = 2 * filled + 1;
            step += 1;
        }
        let fill = fb.iconst(Ty::U8, 7);
        let off = fb.iconst(Ty::U64, i128::from(filled));
        let rest = fb.gep(Ty::U8, a, vec![off]);
        let count = fb.iconst(Ty::U64, i128::from(n - filled));
        fb.memset(rest, fill, count);
        let value = fb.load(bytes, a);
        // The middle byte of the copied region: the last separator written.
        let middle = fb.iconst(Ty::U64, i128::from(filled / 2));
        let byte = fb.extract_element(Ty::U8, value, middle);
        let result = zext_to_i64(&mut fb, byte);
        fb.ret(vec![result]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The separator the interleaved copy writes last, for `n = 2^log2`.
fn last_separator(log2: u32) -> i128 {
    let n = 1u64 << log2;
    let (mut filled, mut step) = (1u64, 0i128);
    while 2 * filled < n {
        filled = 2 * filled + 1;
        step += 1;
    }
    step
}

/// A stored `[u16; n]` splat of `0x0102` loaded as `[u8; 2n]`; the last byte.
fn pun_u16_as_u8(log2: u32) -> Module {
    let n = 1u64 << log2;
    let mut mb = ModuleBuilder::new("pun_u16_as_u8");
    let u8_id = mb.add_type(Ty::U8);
    let u16_id = mb.add_type(Ty::U16);
    let wide = Ty::Array(u16_id, n);
    let narrow = Ty::Array(u8_id, 2 * n);
    let ft = mb.add_func_type(vec![], vec![Ty::I64]);
    {
        let mut fb = mb.function("probe", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let a = fb.alloca(wide.clone());
        let splat = fb.const_value(wide.clone(), Constant::splat(Constant::Int(0x0102), n));
        fb.store(wide, a, splat);
        let value = fb.load(narrow, a);
        let last = fb.iconst(Ty::U64, i128::from(2 * n - 1));
        let byte = fb.extract_element(Ty::U8, value, last);
        let result = zext_to_i64(&mut fb, byte);
        fb.ret(vec![result]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A stored `[[u8; 3]; n]` splat of `[1, 2, 3]` loaded as `[u8; 3n]`; byte
/// `3n - 2`.
fn pun_rows_as_bytes(log2: u32) -> Module {
    let n = 1u64 << log2;
    let mut mb = ModuleBuilder::new("pun_rows_as_bytes");
    let u8_id = mb.add_type(Ty::U8);
    let row = Ty::Array(u8_id, 3);
    let row_id = mb.add_type(row.clone());
    let grid = Ty::Array(row_id, n);
    let flat = Ty::Array(u8_id, 3 * n);
    let ft = mb.add_func_type(vec![], vec![Ty::I64]);
    {
        let mut fb = mb.function("probe", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let a = fb.alloca(grid.clone());
        let x = fb.iconst(Ty::U8, 1);
        let y = fb.iconst(Ty::U8, 2);
        let z = fb.iconst(Ty::U8, 3);
        let one_row = fb.make_aggregate(row, vec![x, y, z]);
        let rows = fb.uniform_array(grid.clone(), one_row);
        fb.store(grid, a, rows);
        let value = fb.load(flat, a);
        let at = fb.iconst(Ty::U64, i128::from(3 * n - 2));
        let byte = fb.extract_element(Ty::U8, value, at);
        let result = zext_to_i64(&mut fb, byte);
        fb.ret(vec![result]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `alloca <n x i64>`, `MemSet` 7 over it, load it, add it to itself; the
/// last lane.
fn vector_memset_add(log2: u32) -> Module {
    let lanes = 1u32 << log2;
    let mut mb = ModuleBuilder::new("vector_memset_add");
    let vector = Ty::Vector(Box::new(Ty::I64), lanes);
    let ft = mb.add_func_type(vec![], vec![Ty::I64]);
    {
        let mut fb = mb.function("probe", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let a = fb.alloca(vector.clone());
        let seven = fb.iconst(Ty::U8, 7);
        let count = fb.iconst(Ty::U64, 8 * i128::from(lanes));
        fb.memset(a, seven, count);
        let value = fb.load(vector.clone(), a);
        let doubled = fb.add(vector, value, value);
        let last = fb.iconst(Ty::U64, i128::from(lanes - 1));
        let lane = fb.extract_element(Ty::I64, doubled, last);
        fb.ret(vec![lane]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn a_doubling_copy_costs_nodes_not_bytes() {
    assert_value_independent(
        "doubling copy",
        |log2| doubling_copy(log2, false),
        (16, 40),
        4,
        |_| 2,
    );
    assert_value_independent(
        "doubling copy, whole load",
        |log2| doubling_copy(log2, true),
        (16, 40),
        4,
        |_| 2,
    );
}

#[test]
fn an_interleaved_copy_loads_back_as_a_dag() {
    // A DAG of 2^40 bytes built by ~40 copies. Its size follows the COPIES:
    // copy `k` reads the ~2k runs the earlier copies left and joins them,
    // and each one-byte separator descends an O(k)-high spine, so the DAG has
    // O(k^3) = O(log^3 N) nodes (~8.5K at 2^40): from 2^20 (19 copies) to
    // 2^40 (39 copies) that is ~9x, measured ~11x with hash-table growth.
    assert_value_independent(
        "interleaved copy",
        interleaved_copy,
        (20, 40),
        32,
        last_separator,
    );
}

#[test]
fn a_punned_load_decodes_one_period() {
    assert_value_independent("[u16; n] as [u8; 2n]", pun_u16_as_u8, (16, 40), 4, |_| 1);
    assert_value_independent(
        "[[u8; 3]; n] as [u8; 3n]",
        pun_rows_as_bytes,
        (16, 40),
        4,
        |_| 2,
    );
}

#[test]
fn a_memset_vector_is_one_node_through_arithmetic() {
    assert_value_independent(
        "<n x i64> memset + add",
        vector_memset_add,
        (10, 31),
        4,
        |_| 2 * 0x0707_0707_0707_0707,
    );
}

/// `n` `InsertElement`s filling `[i64 x n]` element by element, then a read
/// of element `n - 1`. Each insert copies one path, so the heap (every SSA
/// version stays live) grows as n log n; the pre-v50 whole-array clone per
/// insert grew as n^2.
fn insert_chain(n: u64) -> Module {
    let mut mb = ModuleBuilder::new("insert_chain");
    let i64_id = mb.add_type(Ty::I64);
    let array = Ty::Array(i64_id, n);
    let ft = mb.add_func_type(vec![], vec![Ty::I64]);
    {
        let mut fb = mb.function("probe", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::I64, 0);
        let mut current = fb.uniform_array(array.clone(), zero);
        for index in 0..n {
            let at = fb.iconst(Ty::U64, i128::from(index));
            let value = fb.iconst(Ty::I64, i128::from(index) + 1);
            current = fb.insert_element(array.clone(), current, at, value);
        }
        let last = fb.iconst(Ty::U64, i128::from(n - 1));
        let element = fb.extract_element(Ty::I64, current, last);
        fb.ret(vec![element]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn an_insert_chain_grows_as_n_log_n_not_n_squared() {
    let _serial = SERIAL
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let small = insert_chain(1024);
    let large = insert_chain(4096);
    let (value, small_peak) = measure(&small, None);
    assert_eq!(value, 1024);
    // Four times the inserts: n log n is ~4.8x the heap, n^2 is 16x. The
    // bound between them is enforced while the large chain runs.
    let bound = 8 * small_peak;
    let (value, large_peak) = measure(&large, Some(bound));
    assert_eq!(value, 4096);
    assert!(
        large_peak <= bound,
        "insert chain: {large_peak} B for 4096 inserts vs {small_peak} B for 1024"
    );
}
