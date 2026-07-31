// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TrustIr serialization conformance corpus (tests) and the
//! lowering-target subset checker (library).
//!
//! See `tests/conformance.rs` for the corpus entry point and
//! `docs/release-checklist.md` for how this corpus is used during a
//! TrustIr release.
//!
//! The [`subset`] module carries the machine-readable lowering-target
//! conformance subset (`lowering-target-subset.md`, repo root): the pinned
//! `Inst`/`Ty`/`ProofAnnotation` surface a frontend may emit on the
//! "perfectly proven" path, plus the checker the
//! `tests/lowering_subset.rs` gate runs over every fixture.
//!
//! Producers may consume that checker directly to SELF-GATE their
//! emission (`subset::module_subset_violations`; Clean's `emit_trust_ir`
//! does — see the spec doc's "Producer notes"). Depend with
//! `default-features = false`: the library target requires no features
//! (the defaults only feed the byte-golden test corpus).

/// Canonical modules used by the serialization conformance corpus.
///
/// Downstream internal repositories should depend on this crate and build the
/// canonical modules here instead of copying (vendoring) TrustIr fixture files.
#[cfg(feature = "all")]
#[path = "../tests/generate.rs"]
pub mod fixtures;

pub mod subset;
