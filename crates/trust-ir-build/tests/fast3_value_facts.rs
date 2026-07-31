// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// fast-3: value-fact annotations (`ProofAnnotation::ValueRange` / `KnownBits`).
//
// Claim-style optimization hints TrustCg consumes (range strength-reduction,
// switch-table layout, known-bit folding). Additive — like fast-1 ProofRef they
// are new binary tags with NO VERSION bump. The validator rejects internally
// INCONSISTENT claims (an empty range `lo > hi`, or a bit claimed both 0 and 1),
// which are always producer bugs. See docs/roadmap/specs/perf-fast-3-5-decisions.md.

use trust_ir::Module;
use trust_ir::proof::ProofAnnotation;
use trust_ir::ty::Ty;
use trust_ir_build::{ModuleBuilder, validate_module};

fn one_fn() -> Module {
    let mut mb = ModuleBuilder::new("fast3");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("f", ft);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let z = fb.iconst(Ty::I32, 0);
    fb.ret(vec![z]);
    fb.build();
    mb.build()
}

#[test]
fn well_formed_value_facts_validate() {
    let mut m = one_fn();
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ValueRange { lo: -8, hi: 8 });
    m.functions[0].proofs.push(ProofAnnotation::KnownBits {
        zeros: 0xff00,
        ones: 0x00ff,
    });
    // Degenerate-but-valid single-point range.
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ValueRange { lo: 5, hi: 5 });
    assert!(
        validate_module(&m).is_empty(),
        "well-formed value facts must validate: {:?}",
        validate_module(&m)
    );
}

#[test]
fn inverted_value_range_is_rejected() {
    let mut m = one_fn();
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ValueRange { lo: 10, hi: 1 });
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::ValueRangeInverted { .. }
        )),
        "an inverted value_range (lo > hi) must be rejected: {errs:?}"
    );
}

#[test]
fn contradictory_known_bits_is_rejected() {
    let mut m = one_fn();
    // bit 1 (0b10) claimed both 0 and 1.
    m.functions[0].proofs.push(ProofAnnotation::KnownBits {
        zeros: 0b110,
        ones: 0b010,
    });
    let errs = validate_module(&m);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            trust_ir_build::validate::ValidationError::KnownBitsContradiction { .. }
        )),
        "known_bits claiming a bit is both 0 and 1 must be rejected: {errs:?}"
    );
}

#[test]
fn is_value_fact_classifier() {
    assert!(ProofAnnotation::ValueRange { lo: 0, hi: 1 }.is_value_fact());
    assert!(ProofAnnotation::KnownBits { zeros: 0, ones: 0 }.is_value_fact());
    assert!(!ProofAnnotation::NoOverflow.is_value_fact());
}
