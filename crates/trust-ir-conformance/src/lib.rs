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

/// The must-refuse corpus builders (KIND 4): every `build_refuse_*` artifact
/// of `tests/fixtures/refuse/`, byte-pinned and run by
/// `tests/refuse_corpus.rs`. A module of its own, not part of [`fixtures`]:
/// `trust-ir-build/tests/builder_doors.rs` includes `generate.rs` without the
/// `binary` feature the byte-string builders need, and the test targets that
/// include `generate.rs` directly use none of these.
#[cfg(feature = "all")]
#[path = "../tests/generate/refuse.rs"]
pub mod refuse_fixtures;

/// The level-S golden templates and their scripted hosts (amendment S):
/// `tests/fixtures/templates/`, and the instances `trust-ir-build`'s
/// instantiation tests run (that crate includes this file by path: it cannot
/// depend on this one).
#[cfg(feature = "all")]
#[path = "../tests/generate/templates.rs"]
pub mod template_fixtures;

/// The level-S must-refuse builders: every artifact of
/// `tests/fixtures/refuse_templates/`, byte-pinned and run by
/// `tests/template_refuse_corpus.rs`.
#[cfg(feature = "all")]
#[path = "../tests/generate/refuse_templates.rs"]
pub mod refuse_template_fixtures;

pub mod subset;

/// The must-refuse corpus runner (KIND 4): every row under
/// `tests/fixtures/refuse/` is a wire artifact a conforming consumer must
/// REFUSE, and this module hands a consumer the rows plus a verdict report so
/// it never re-implements the corpus. `must-refuse` feature (forwards only
/// `trust-ir/binary`).
#[cfg(feature = "must-refuse")]
pub mod refuse;
