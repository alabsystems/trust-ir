// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Names, not numbers.
//
// A wire version number is a CONTENDED resource (see `wire-allocations.toml`
// at the repo root): until a feature's number has been pushed to `main`, it
// can still lose a race and be renumbered. That happened three times in one
// quarter, and each renumber cost hours — not because a constant changed, but
// because the NUMBER had been spelled into file names (`body_gate_v41.*`,
// `ty_handle_v43.*`, `v41_*.rs`), so a one-line renumber became a multi-file
// `git mv` plus every reference to those files, across two lines of work.
//
// So test and fixture FILE NAMES name the feature, never the version. A
// renumber is then a one-line change to a constant and a registry row.
//
// What this lint does NOT touch: the existing numbered names listed below.
// They belong to work that is already pushed (so their numbers can no longer
// move) and renaming another line's in-flight files is itself a conflict
// generator. The list is CLOSED to contended numbers mechanically (the freeze
// below); that nobody adds an old number to it is left to review, and said so.

use std::path::{Path, PathBuf};

/// The wire version that was current when the grandfather list was FROZEN
/// (2026-09-18). NEVER raise it: every number above it was allocated after the
/// names-not-numbers rule, so nothing numbered above it can be grandfathered.
/// This is what makes the list closed to the case the lint exists for — a
/// `foo_v44.tmbc` whose author answers the lint by listing it here.
const GRANDFATHER_FREEZE: u32 = 43;

// The freeze names a LANDED version: it can never be raised past one. Checked
// when this file COMPILES, so it cannot be skipped by a test filter.
const _: () = assert!(GRANDFATHER_FREEZE <= trust_ir::binary::FORMAT_VERSION);

/// Existing numbered names, relative to the repo root, extension-less for
/// fixture families. NEVER add to this list — name the feature instead.
const GRANDFATHERED: &[&str] = &[
    "crates/trust-ir-conformance/tests/fixtures/compat/v22_composition",
    "crates/trust-ir-conformance/tests/fixtures/compat/v22_frontend_emission_subset",
    "crates/trust-ir-conformance/tests/fixtures/compat/v30_ty_composite",
    "crates/trust-ir-conformance/tests/fixtures/compat/v32_debug_metadata",
    "crates/trust-ir-conformance/tests/fixtures/debug_metadata_v33",
    "crates/trust-ir-conformance/tests/fixtures/declared_tuple_v42",
    "crates/trust-ir-conformance/tests/fixtures/ty_dialect_v39",
    // A frozen snapshot directory with recorded SHA-256s (ORIGIN.json): its
    // own name and every file in it keep their historical spelling.
    "crates/trust-ir-conformance/tests/fixtures/v41-reader-compat",
];

/// The `N` of a `vN` token in `name`: a `v` at a word start, then digits, then
/// a word end. `v41_body_gate.rs`, `ty_handle_v43.tmbc` and
/// `v41-reader-compat` have one; `inst_vector.json`, `u128_constants.tmbc`
/// and `sha256.rs` do not.
fn version_token(name: &str) -> Option<u32> {
    let bytes = name.as_bytes();
    for start in 0..bytes.len() {
        if bytes[start] != b'v' || (start > 0 && bytes[start - 1].is_ascii_alphanumeric()) {
            continue;
        }
        let digits = bytes[start + 1..]
            .iter()
            .take_while(|byte| byte.is_ascii_digit())
            .count();
        let end = start + 1 + digits;
        if digits > 0
            && bytes
                .get(end)
                .is_none_or(|byte| !byte.is_ascii_alphanumeric())
        {
            return name[start + 1..end].parse().ok();
        }
    }
    None
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Every file and directory under a `tests/` or `benches/` tree of the
/// workspace crates, the excluded `frontend/` crate, and `benchmarks/`.
fn test_and_fixture_paths() -> Vec<PathBuf> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        let mut entries: Vec<PathBuf> = entries.map(|entry| entry.expect("entry").path()).collect();
        entries.sort();
        for path in entries {
            out.push(path.clone());
            if path.is_dir() {
                walk(&path, out);
            }
        }
    }
    let root = repo_root();
    let mut roots = vec![root.join("benchmarks"), root.join("frontend/tests")];
    let mut crates: Vec<PathBuf> = std::fs::read_dir(root.join("crates"))
        .expect("read crates/")
        .map(|entry| entry.expect("entry").path())
        .collect();
    crates.sort();
    for member in crates {
        roots.push(member.join("tests"));
        roots.push(member.join("benches"));
    }
    let mut out = Vec::new();
    for dir in roots {
        walk(&dir, &mut out);
    }
    out
}

#[test]
fn no_new_test_or_fixture_name_spells_a_version_number() {
    let root = repo_root().canonicalize().expect("repo root");
    let mut offenders = Vec::new();
    for path in test_and_fixture_paths() {
        let relative = path
            .canonicalize()
            .expect("canonical path")
            .strip_prefix(&root)
            .expect("under the repo root")
            .to_string_lossy()
            .replace('\\', "/");
        let name = path.file_name().expect("file name").to_string_lossy();
        let Some(number) = version_token(&name) else {
            continue;
        };
        let grandfathered = GRANDFATHERED.iter().any(|allowed| {
            relative == *allowed
                || relative.starts_with(&format!("{allowed}."))
                || relative.starts_with(&format!("{allowed}/"))
        });
        // A pinned back-compat blob names the version of FROZEN bytes: that
        // number is history and cannot be renumbered — but only once it has
        // landed, so a number above the current format version is refused.
        let pinned_history = relative.contains("/tests/fixtures/compat/")
            && number <= trust_ir::binary::FORMAT_VERSION;
        if !grandfathered && !pinned_history {
            offenders.push(relative);
        }
    }
    assert!(
        offenders.is_empty(),
        "test/fixture names must name the FEATURE, not the wire version (a version number is \
         contended until it is pushed, and a renumber must stay a one-line change — see \
         wire-allocations.toml):\n  {}",
        offenders.join("\n  ")
    );
}

/// Why `allowed` may NOT be grandfathered, if it may not.
fn grandfather_refusal(allowed: &str) -> Option<String> {
    let name = allowed.rsplit('/').next().unwrap_or(allowed);
    match version_token(name) {
        None => Some(format!(
            "`{allowed}` spells no version: it needs no grandfathering"
        )),
        Some(number) if number > GRANDFATHER_FREEZE => Some(format!(
            "`{allowed}` names v{number}, above the freeze (v{GRANDFATHER_FREEZE}): a number \
             allocated after the names-not-numbers rule cannot be grandfathered — name the \
             feature instead"
        )),
        Some(_) => None,
    }
}

/// What is checked, and what is not. CHECKED: every entry still exists (a
/// stale row is deleted, so the list shrinks as history is cleaned up), and
/// no entry names a version above the freeze (so a CONTENDED number — the
/// only kind a renumber can hit — can never be grandfathered in). NOT checked:
/// that nobody adds an entry for an already-landed number; such a name cannot
/// be renumbered, so it costs nothing this lint protects, and review owns it.
/// This test was once called `the_grandfather_list_only_shrinks`, which its
/// body never established: a claim dressed as a check.
#[test]
fn every_grandfathered_name_exists_and_predates_the_freeze() {
    let root = repo_root();
    for allowed in GRANDFATHERED {
        assert_eq!(grandfather_refusal(allowed), None);
        let path = root.join(allowed);
        let family_exists = path.exists()
            || ["json", "msgpack", "tmbc", "trust_ir"]
                .iter()
                .any(|extension| path.with_extension(extension).exists());
        assert!(
            family_exists,
            "`{allowed}` no longer exists: delete its GRANDFATHERED row (the list only shrinks)"
        );
    }
}

/// The freeze bites: the reviewer's scenario, run against the same predicate.
#[test]
fn a_contended_number_cannot_be_grandfathered() {
    // Derived, never spelled: the next number is whatever follows today's.
    let next = trust_ir::binary::FORMAT_VERSION + 1;
    let sneaked = format!("crates/trust-ir-conformance/tests/fixtures/foo_v{next}");
    let refusal = grandfather_refusal(&sneaked).expect("a contended number is refused");
    assert!(refusal.contains("above the freeze"), "{refusal}");
    assert!(
        grandfather_refusal("crates/trust-ir-conformance/tests/fixtures/ty_handle").is_some(),
        "a name with no version needs no grandfathering"
    );
}

#[test]
fn the_token_detector_sees_versions_and_nothing_else() {
    for (name, expected) in [
        ("v41_body_gate.rs", Some(41)),
        ("ty_handle_v43.tmbc", Some(43)),
        ("v41-reader-compat", Some(41)),
        ("debug_metadata_v33.trust_ir", Some(33)),
        ("v7", Some(7)),
        ("inst_vector.json", None),
        ("u128_constants.tmbc", None),
        ("b1_scalars.json", None),
        ("sha256.rs", None),
        ("conv2d.rs", None),
        ("v.rs", None),
        ("v41x.rs", None),
        ("names_not_numbers.rs", None),
    ] {
        assert_eq!(version_token(name), expected, "{name}");
    }
}
