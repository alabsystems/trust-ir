// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// GPU eligibility integration test harness.
//
// Part of TrustIr#35. Exercises the end-to-end path from `FunctionBuilder`
// through built `Module` → `Function::is_safe_for_gpu()` /
// `Function::is_gpu_eligible()` / `gpu_proofs()`, across the combinatorial
// space of parallel / purity / memory-role annotations. The harness is
// deliberately black-box: it pokes only the public API, so it doubles as a
// regression gate if the annotation vocabulary or predicate semantics shift
// underneath TrustIr (issue #26, TrustIr#390).
//
// ## Two-gate contract (per designs/2026-04-18-ty-supremacy-trust-ir-scope.md §3.2
// and TrustIr#39)
//
// - `Function::is_safe_for_gpu()` is **frozen** at `Pure + NoPanic +
//   Deterministic`. It does NOT reject DivergenceClass(High); pre-existing
//   downstream consumers (tRust, TrustIr CPU/SIMD paths) rely on this exact
//   three-annotation check.
// - `Function::is_gpu_eligible()` is the stricter gate TrustIr `KernelExtract`
//   queries. It composes `is_safe_for_gpu() && ParallelMap && DivergenceClass
//   ∈ {Uniform, Low}`. Absent or `High` divergence disqualifies.
//
// This harness covers both gates against the full Cartesian space.
//
// ## Determinism
//
// All tests construct modules from literals and call pure predicates. There
// is no filesystem, network, time, randomness, or parallel execution — the
// suite is deterministic and not timing-sensitive.

use trust_ir::Function;
use trust_ir::proof::{Divergence, ProofAnnotation};
use trust_ir::ty::Ty;
use trust_ir_build::ModuleBuilder;

// --- Helpers ---------------------------------------------------------------

/// Build a one-block function `fn f(i64) -> i64 { ret %0 }` stamped with the
/// given function-level proof annotations. Returns the built `Function` by
/// value so callers can query its predicates without borrowing the module.
///
/// The body is the same across the matrix so variation is isolated to the
/// proof set under test — no hidden per-instruction proofs contaminate the
/// signal.
fn build_func_with_proofs(proofs: &[ProofAnnotation]) -> Function {
    let mut mb = ModuleBuilder::new("gpu_eligibility_test");
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    for p in proofs {
        fb.add_proof(p.clone());
    }
    fb.ret(vec![x]);
    fb.build();
    let module = mb.build();
    assert_eq!(module.functions.len(), 1);
    module.functions[0].clone()
}

// Note: earlier drafts wrapped the §3.2 policy in a local `rich_gpu_gate`
// helper because `Function::is_gpu_eligible()` had not yet landed on main.
// TL5's TrustIr#39 has since merged the upstream predicate; this harness now
// calls `f.is_gpu_eligible()` directly.

// --- Baseline: is_safe_for_gpu is frozen at the three-annotation check -----

#[test]
fn safe_for_gpu_minimal_triple_true() {
    // (Pure, NoPanic, Deterministic) with no other annotations: the
    // canonical "safe for GPU" baseline. This is the pre-supremacy contract
    // and MUST remain true regardless of what memory-role / parallel
    // attributes ship later.
    let f = build_func_with_proofs(&[
        ProofAnnotation::Pure,
        ProofAnnotation::NoPanic,
        ProofAnnotation::Deterministic,
    ]);
    assert!(f.is_safe_for_gpu());
}

#[test]
fn safe_for_gpu_missing_pure_false() {
    let f = build_func_with_proofs(&[ProofAnnotation::NoPanic, ProofAnnotation::Deterministic]);
    assert!(!f.is_safe_for_gpu());
}

#[test]
fn safe_for_gpu_missing_nopanic_false() {
    let f = build_func_with_proofs(&[ProofAnnotation::Pure, ProofAnnotation::Deterministic]);
    assert!(!f.is_safe_for_gpu());
}

#[test]
fn safe_for_gpu_missing_deterministic_false() {
    let f = build_func_with_proofs(&[ProofAnnotation::Pure, ProofAnnotation::NoPanic]);
    assert!(!f.is_safe_for_gpu());
}

#[test]
fn safe_for_gpu_empty_proofs_false() {
    let f = build_func_with_proofs(&[]);
    assert!(!f.is_safe_for_gpu());
}

// --- Divergence and the two-gate split -------------------------------------

#[test]
fn safe_for_gpu_not_tightened_by_high_divergence() {
    // Post-TrustIr#39 contract: `is_safe_for_gpu()` is FROZEN at
    // `Pure + NoPanic + Deterministic`. It does NOT reject
    // `DivergenceClass(High)` — pre-existing downstream consumers (tRust,
    // TrustIr CPU/SIMD paths) rely on this exact three-annotation check.
    // Divergence gating lives in the stricter `is_gpu_eligible` gate below.
    let f = build_func_with_proofs(&[
        ProofAnnotation::Pure,
        ProofAnnotation::NoPanic,
        ProofAnnotation::Deterministic,
        ProofAnnotation::DivergenceClass(Divergence::High),
    ]);
    assert!(
        f.is_safe_for_gpu(),
        "is_safe_for_gpu must remain true when the triple is present, \
         regardless of DivergenceClass"
    );
    assert!(
        !f.is_gpu_eligible(),
        "is_gpu_eligible must reject DivergenceClass(High)"
    );
}

#[test]
fn safe_for_gpu_allowed_with_uniform_divergence() {
    let f = build_func_with_proofs(&[
        ProofAnnotation::Pure,
        ProofAnnotation::NoPanic,
        ProofAnnotation::Deterministic,
        ProofAnnotation::DivergenceClass(Divergence::Uniform),
    ]);
    assert!(f.is_safe_for_gpu());
}

#[test]
fn safe_for_gpu_allowed_with_low_divergence() {
    let f = build_func_with_proofs(&[
        ProofAnnotation::Pure,
        ProofAnnotation::NoPanic,
        ProofAnnotation::Deterministic,
        ProofAnnotation::DivergenceClass(Divergence::Low),
    ]);
    assert!(f.is_safe_for_gpu());
}

// --- Rich gate matrix (mirrors TrustIr#35 Acceptance Criteria table) ----------
//
// Columns: Pure | NoPanic | Deterministic | ParallelMap | DivergenceClass
// Each row asserts `f.is_gpu_eligible()` matches the expected eligibility
// per §3.2 and TrustIr#39.

fn matrix_row(
    pure_: bool,
    no_panic: bool,
    deterministic: bool,
    parallel: bool,
    div: Option<Divergence>,
) -> Function {
    let mut proofs = Vec::new();
    if pure_ {
        proofs.push(ProofAnnotation::Pure);
    }
    if no_panic {
        proofs.push(ProofAnnotation::NoPanic);
    }
    if deterministic {
        proofs.push(ProofAnnotation::Deterministic);
    }
    if parallel {
        proofs.push(ProofAnnotation::ParallelMap);
    }
    if let Some(d) = div {
        proofs.push(ProofAnnotation::DivergenceClass(d));
    }
    build_func_with_proofs(&proofs)
}

#[test]
fn matrix_all_true_uniform_is_eligible() {
    let f = matrix_row(true, true, true, true, Some(Divergence::Uniform));
    assert!(f.is_gpu_eligible());
    // Sanity: the conservative baseline remains true too.
    assert!(f.is_safe_for_gpu());
}

#[test]
fn matrix_all_true_low_is_eligible() {
    let f = matrix_row(true, true, true, true, Some(Divergence::Low));
    assert!(f.is_gpu_eligible());
    assert!(f.is_safe_for_gpu());
}

#[test]
fn matrix_all_true_high_is_not_eligible() {
    // High divergence disqualifies the rich gate but does NOT tighten the
    // frozen conservative baseline (post-TrustIr#39 contract). This row pins
    // the two-gate split: `is_safe_for_gpu` = yes, `is_gpu_eligible` = no.
    let f = matrix_row(true, true, true, true, Some(Divergence::High));
    assert!(!f.is_gpu_eligible());
    assert!(f.is_safe_for_gpu());
}

#[test]
fn matrix_parallel_missing_is_not_eligible() {
    // Even with the triple and low divergence, ParallelMap is required for
    // the rich gate. The conservative gate still accepts this row — this
    // asserts the two gates are meaningfully distinct.
    let f = matrix_row(true, true, true, false, Some(Divergence::Low));
    assert!(!f.is_gpu_eligible());
    assert!(f.is_safe_for_gpu());
}

#[test]
fn matrix_deterministic_missing_is_not_eligible() {
    let f = matrix_row(true, true, false, true, Some(Divergence::Low));
    assert!(!f.is_gpu_eligible());
    assert!(!f.is_safe_for_gpu());
}

#[test]
fn matrix_no_panic_missing_is_not_eligible() {
    let f = matrix_row(true, false, true, true, Some(Divergence::Low));
    assert!(!f.is_gpu_eligible());
    assert!(!f.is_safe_for_gpu());
}

#[test]
fn matrix_pure_missing_is_not_eligible() {
    let f = matrix_row(false, true, true, true, Some(Divergence::Low));
    assert!(!f.is_gpu_eligible());
    assert!(!f.is_safe_for_gpu());
}

#[test]
fn matrix_divergence_absent_is_not_eligible() {
    // No DivergenceClass annotation at all: the rich gate rejects because
    // the backend needs a definite divergence answer. The conservative gate
    // still accepts because divergence is not part of the frozen
    // `is_safe_for_gpu` contract at all.
    let f = matrix_row(true, true, true, true, None);
    assert!(!f.is_gpu_eligible());
    assert!(f.is_safe_for_gpu());
}

// --- Cross-check: append-only buffer + parallel-map loop is eligible -------

#[test]
fn append_only_buffer_parallel_map_uniform_is_eligible() {
    // Canonical shape of a GPU-offloadable reduce-into-buffer kernel:
    // `Pure + NoPanic + Deterministic + ParallelMap + Uniform divergence`
    // with a memory-role hint (`AppendOnlyBuffer`) for address-space
    // lowering. The memory-role is informative (TrustIr picks the address
    // space) but not required for eligibility.
    let f = build_func_with_proofs(&[
        ProofAnnotation::Pure,
        ProofAnnotation::NoPanic,
        ProofAnnotation::Deterministic,
        ProofAnnotation::ParallelMap,
        ProofAnnotation::AppendOnlyBuffer,
        ProofAnnotation::BoundedLoop(1024),
        ProofAnnotation::DivergenceClass(Divergence::Uniform),
    ]);
    assert!(f.is_safe_for_gpu());
    assert!(f.is_gpu_eligible());
    // All the GPU-relevant proofs on the function should surface via
    // gpu_proofs(), so TrustIr can pick the address space and unroll hint.
    let gpu = f.gpu_proofs();
    assert!(gpu.contains(&&ProofAnnotation::Pure));
    assert!(gpu.contains(&&ProofAnnotation::NoPanic));
    assert!(gpu.contains(&&ProofAnnotation::Deterministic));
    assert!(gpu.contains(&&ProofAnnotation::ParallelMap));
    assert!(gpu.contains(&&ProofAnnotation::AppendOnlyBuffer));
    assert!(gpu.contains(&&ProofAnnotation::BoundedLoop(1024)));
    assert!(gpu.contains(&&ProofAnnotation::DivergenceClass(Divergence::Uniform)));
}

// --- gpu_proofs behaviour on full annotation vocabulary --------------------

#[test]
fn gpu_proofs_includes_new_annotations_excludes_high_divergence() {
    // A kitchen-sink function: every new annotation plus all three
    // divergence classes. gpu_proofs() must surface the GPU-relevant ones
    // and drop DivergenceClass(High). This is the filter TrustIr consults.
    let f = build_func_with_proofs(&[
        ProofAnnotation::Pure,
        ProofAnnotation::ReadonlyTable,
        ProofAnnotation::AppendOnlyBuffer,
        ProofAnnotation::AtomicSetInsert,
        ProofAnnotation::ParallelMap,
        ProofAnnotation::BoundedLoop(256),
        ProofAnnotation::DivergenceClass(Divergence::Uniform),
        ProofAnnotation::DivergenceClass(Divergence::Low),
        ProofAnnotation::DivergenceClass(Divergence::High), // excluded
    ]);
    let gpu = f.gpu_proofs();
    assert!(gpu.contains(&&ProofAnnotation::Pure));
    assert!(gpu.contains(&&ProofAnnotation::ReadonlyTable));
    assert!(gpu.contains(&&ProofAnnotation::AppendOnlyBuffer));
    assert!(gpu.contains(&&ProofAnnotation::AtomicSetInsert));
    assert!(gpu.contains(&&ProofAnnotation::ParallelMap));
    assert!(gpu.contains(&&ProofAnnotation::BoundedLoop(256)));
    assert!(gpu.contains(&&ProofAnnotation::DivergenceClass(Divergence::Uniform)));
    assert!(gpu.contains(&&ProofAnnotation::DivergenceClass(Divergence::Low)));
    assert!(!gpu.contains(&&ProofAnnotation::DivergenceClass(Divergence::High)));
}

#[test]
fn gpu_proofs_excludes_unrelated_annotations() {
    // Annotations that are correct but not GPU-synthesis signals should
    // NOT appear in gpu_proofs(). Keeping the filter tight lets the TrustIr
    // backend trust that every entry in gpu_proofs() is actionable.
    let f = build_func_with_proofs(&[
        ProofAnnotation::Pure,                                // kept (GPU-relevant)
        ProofAnnotation::Monotonic,                           // dropped (NN-only)
        ProofAnnotation::DataRaceFree,                        // dropped (concurrency, not GPU)
        ProofAnnotation::BoundedOutput { lo: -1.0, hi: 1.0 }, // dropped
    ]);
    let gpu = f.gpu_proofs();
    assert_eq!(gpu.len(), 1);
    assert!(gpu.contains(&&ProofAnnotation::Pure));
}

// --- Contract across the whole matrix: is_gpu_eligible ≤ is_safe_for_gpu --

#[test]
fn is_gpu_eligible_implies_safe_for_gpu_across_full_matrix() {
    // Cartesian product of (Pure, NoPanic, Deterministic, ParallelMap) ×
    // {None, Some(Uniform), Some(Low), Some(High)}. 2^4 × 4 = 64 rows.
    // For every row, `is_gpu_eligible(f)` must imply `is_safe_for_gpu(f)`.
    // This is the monotonicity property §3.2 relies on: the richer gate
    // only ever further restricts the conservative one; it must not admit
    // functions the conservative one rejects.
    let divs: [Option<Divergence>; 4] = [
        None,
        Some(Divergence::Uniform),
        Some(Divergence::Low),
        Some(Divergence::High),
    ];
    let bools = [false, true];
    let mut cases = 0usize;
    for &pure_ in &bools {
        for &np in &bools {
            for &det in &bools {
                for &par in &bools {
                    for div in &divs {
                        let f = matrix_row(pure_, np, det, par, *div);
                        if f.is_gpu_eligible() {
                            assert!(
                                f.is_safe_for_gpu(),
                                "rich gate accepted a function the conservative gate rejected: \
                                 pure={pure_} no_panic={np} det={det} par={par} div={div:?}"
                            );
                        }
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 64, "expected full Cartesian coverage");
}
