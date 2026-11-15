// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// ══════════════════════════════════════════════════════════════════════════
// A `trust-ir.Pred@1` citation costs the one-text check no more than the
// rendering it is compared with.
// ══════════════════════════════════════════════════════════════════════════
//
// Both validators (`validate_module` and `NativeVerificationBundle::validate`)
// refuse a formula whose `smtlib` rendering is not its payload's one text; for
// a `pred.N` citation that text is `PredTable::smtlib_of(N)`. The predicate
// DAG's rendering is not shared: the validator-legal table
// `pred.k = Conj([k-2, k-1])` renders `pred.k` to fib(k) leaves, and the check
// rendered it whole before comparing. Measured before the fix: 41.8 MB and
// ~1 s per validator at 31 entries, so the 65-entry table below (`pred.64`,
// the depth cap, ~5*10^14 bytes) beside `smtlib = "true"` exhausts the host.
// The check now renders no further than the rendering in hand
// (`PredTable::smtlib_of_within`): a longer text is not it.
//
// A counting `#[global_allocator]` holds each validator call to a heap
// ceiling WHILE it runs: an allocation past it fails, which aborts this test
// binary ("memory allocation of … failed"), so an unbounded render fails here
// within megabytes instead of taking the host (the pattern of
// `interpreter_memory_scaling.rs`).

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::pred::PRED_FORMULA_SCHEMA;
use trust_ir::proof::{ProofDigest, ProofFormula, ProofLineageManifest};
use trust_ir::request::{
    NativeAdapterInput, NativeBundleProducer, NativeVerificationBundle,
    NativeVerificationBundleError,
};
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, PredId};
use trust_ir::{Block, Function, FunctionSummary, Module, Pred, Producer};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::validate_module;

struct Counting;

static CURRENT: AtomicUsize = AtomicUsize::new(0);
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

/// The counters are process-wide: measurements run one at a time.
static SERIAL: Mutex<()> = Mutex::new(());

/// Run `operation` with the heap allowed to grow at most `ceiling` bytes
/// while it runs.
fn within<T>(ceiling: usize, operation: impl FnOnce() -> T) -> T {
    let _serial = SERIAL
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    CEILING.store(CURRENT.load(Ordering::SeqCst) + ceiling, Ordering::SeqCst);
    let result = operation();
    CEILING.store(usize::MAX, Ordering::SeqCst);
    result
}

/// One empty function `f` and the predicate table `pred.0 = NonZero`,
/// `pred.1 = Interval [0, 5]`, `pred.k = Conj([k-2, k-1])` for `2 <= k <= n`.
fn fibonacci_table_module(n: u32) -> Module {
    let mut module = Module::new("pred_citation_rendering_budget");
    let ft = module
        .add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function =
        Function::new(FuncId::new(0), "f", ft, BlockId::new(0)).with_producer(Producer::TRust);
    function.blocks.push(Block {
        id: BlockId::new(0),
        params: Vec::new(),
        body: vec![InstrNode::new(Inst::Return { values: Vec::new() })],
    });
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module.predicates = vec![Pred::NonZero, Pred::Interval { lo: 0, hi: 5 }];
    for k in 2..=n {
        module
            .predicates
            .push(Pred::Conj(vec![PredId::new(k - 2), PredId::new(k - 1)]));
    }
    module
}

/// `module` with `f` ensuring the citation `pred.n` beside `rendering`.
fn citing(mut module: Module, n: u32, rendering: String) -> Module {
    let mut formula = ProofFormula::new(PRED_FORMULA_SCHEMA, format!("pred.{n}"));
    formula.smtlib = Some(rendering);
    module.functions[0].summary = Some(FunctionSummary::new().ensuring(formula));
    module
}

fn bundle(module: Module) -> NativeVerificationBundle {
    let digest = module.stable_digest();
    NativeVerificationBundle::new(
        NativeBundleProducer::TRust,
        NativeAdapterInput::RustMir {
            body_digest: ProofDigest::sha256_domain("pred_citation_rendering_budget", b"f"),
        },
        digest,
        module,
        ProofLineageManifest {
            schema_version: ProofLineageManifest::SCHEMA_VERSION,
            nodes: Vec::new(),
            roots: Vec::new(),
        },
    )
}

/// How many `FormulaTextsDisagree` each validator reports for `module`, each
/// run under `ceiling` bytes of heap growth.
fn two_text_refusals(module: &Module, ceiling: usize) -> (usize, usize) {
    let module_errors = within(ceiling, || validate_module(module));
    let bundle = bundle(module.clone());
    let bundle_errors = within(ceiling, || bundle.validate().err().unwrap_or_default());
    (
        module_errors
            .iter()
            .filter(|error| matches!(error, ValidationError::FormulaTextsDisagree { .. }))
            .count(),
        bundle_errors
            .iter()
            .filter(|error| {
                matches!(
                    error,
                    NativeVerificationBundleError::FormulaTextsDisagree { .. }
                )
            })
            .count(),
    )
}

/// The depth cap's table: `pred.64` renders to fib(64) leaves. Beside the
/// four-byte rendering `true` both validators refuse the formula within 8 MiB
/// of heap growth (the check renders at most five bytes of it).
#[test]
fn a_deep_citation_beside_a_short_rendering_is_refused_within_its_budget() {
    let n = 64;
    let table = fibonacci_table_module(n);
    // The table itself is legal: only the rendering beside the citation is
    // refused.
    assert_eq!(validate_module(&table), []);
    let module = citing(table, n, "true".to_string());
    assert_eq!(two_text_refusals(&module, 8 << 20), (1, 1));
}

/// The budget is the rendering's own length, not a constant: an honest
/// rendering of `pred.20` (339,696 bytes) still states one text, and a
/// one-byte-short or one-byte-long one does not.
#[test]
fn an_honest_long_rendering_still_states_one_text() {
    let n = 20;
    let table = fibonacci_table_module(n);
    let honest = table
        .pred_table()
        .smtlib_of(PredId::new(n))
        .expect("pred.20 renders");
    assert_eq!(honest.len(), 339_696);
    let ceiling = 16 * honest.len() + (8 << 20);
    for (rendering, refusals) in [
        (honest.clone(), (0, 0)),
        (honest[..honest.len() - 1].to_string(), (1, 1)),
        (format!("{honest} "), (1, 1)),
    ] {
        let module = citing(table.clone(), n, rendering);
        assert_eq!(two_text_refusals(&module, ceiling), refusals);
    }
}
