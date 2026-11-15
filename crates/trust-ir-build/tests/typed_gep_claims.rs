// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! External consumer of the public, non-authoritative expected-claim view.
//! These structural controls do not claim kernel replay or execution; the
//! library's fetched-instruction controls qualify those separate boundaries.

#![cfg(feature = "clean-tv-anchor")]

use trust_ir_build::clean_kernel::Expr;
use trust_ir_build::core_execution::{ByteGepSingleton, ByteGepSingletonChecks};

fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_str(name), args)
}

fn input() -> ByteGepSingleton {
    // Opaque actual expressions remain opaque; this API proves nothing about
    // them and may not replace them with convenient literals or allocations.
    ByteGepSingleton {
        pointee: app("IRTy.uint_", [Expr::nat_lit(32)]),
        layout: Expr::const_str("actual_layout"),
        stride: Expr::nat_lit(4),
        pointer: Expr::const_str("actual_pointer_read"),
        indices: Expr::const_str("actual_ordered_resolved_indices"),
        base: Expr::const_str("actual_base"),
        index: Expr::const_str("actual_index"),
        memory: Expr::const_str("actual_current_memory"),
    }
}

#[test]
fn public_typed_gep_checks_name_actual_operands_bounds_and_scaled_address() {
    let input = input();
    let context = Expr::const_str("actual_context");
    let checks: ByteGepSingletonChecks = input.checks(&context);
    assert_eq!(
        checks.layout,
        (
            app("IROption", [Expr::const_str("IRByteLayoutV1")]),
            app("ir_byte_layout_v1", [context, input.pointee.clone()]),
            app(
                "IROption.some",
                [Expr::const_str("IRByteLayoutV1"), input.layout.clone()],
            ),
        )
    );
    assert_eq!(checks.layout_size.2, input.stride);
    assert_eq!(checks.indices.1, input.indices);
    assert_eq!(
        checks.index_bound,
        app("Nat.lt", [input.index.clone(), Expr::nat_lit(1_u64 << 63)],)
    );
    let delta = app("Nat.mul", [input.stride.clone(), input.index.clone()]);
    let address = app("Nat.add", [input.base.clone(), delta.clone()]);
    let limit = Expr::const_str("ir_byte_limit_v1");
    assert_eq!(checks.delta_bound, app("Nat.lt", [delta, limit.clone()]));
    assert_eq!(checks.result_bound, app("Nat.lt", [address.clone(), limit]));
    assert_eq!(
        checks.inbounds_membership,
        (
            Expr::const_str("Bool"),
            app(
                "ir_byte_same_allocation_v1",
                [
                    app("ir_byte_mem_allocs_v1", [input.memory]),
                    input.base,
                    address,
                ],
            ),
            Expr::const_str("Bool.true"),
        )
    );
}

#[test]
fn public_typed_gep_checks_do_not_reuse_foreign_context_layout_or_memory() {
    let original = input();
    let context = Expr::const_str("actual_context");
    let checks = original.checks(&context);
    assert_ne!(
        checks.layout,
        original.checks(&Expr::const_str("foreign_context")).layout
    );
    let mut changed = original.clone();
    changed.layout = Expr::const_str("foreign_layout");
    assert_ne!(checks.layout, changed.checks(&context).layout);
    changed = original.clone();
    changed.memory = Expr::const_str("stale_memory");
    let foreign = changed.checks(&context);
    assert_ne!(checks.inbounds_membership, foreign.inbounds_membership);
    assert_eq!(checks.result_bound, foreign.result_bound);
    assert_eq!(checks.index_bound, foreign.index_bound);
}
