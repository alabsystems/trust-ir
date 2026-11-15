// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `docs/binary-format.md`'s per-enum tag-range HEADINGS must equal the tag
//! space the codec actually writes.
//!
//! WHY THIS EXISTS. The headings are hand-maintained hex ranges, and on
//! 2026-09-20 three of the seven were STALE — measured against
//! `wire-allocations.toml`, which is derived from the writers themselves:
//!
//! | heading | said | codec writes |
//! |---|---|---|
//! | `ProofAnnotation` | `0x00..=0x25` | `0x26` |
//! | `ProofEvidence`   | `0x00..=0x07` | `0x08` |
//! | `ObligationKind`  | `0x00..=0x09` | `0x0F` |
//!
//! `ObligationKind` had been wrong since v41 added `Termination` (13),
//! `Ownership` (14) and `Custom` (15) — six tags of drift in a document whose
//! own opening calls itself "the normative specification for the TrustIr
//! binary format". Nothing caught it, because the ONE mechanised doc check
//! (`back_compat.rs`) pins the `TRUST_IR_BINARY_FORMAT_VERSION` marker and
//! nothing else, and a stale range is invisible to every byte-level test: the
//! goldens exercise the tags, not the prose about them.
//!
//! So this is a claim-to-mechanism conversion, not a style gate. The heading
//! is a NORMATIVE CLAIM about the tag space a consumer must handle; a consumer
//! that implemented `ObligationKind` from the heading would have refused three
//! kinds the codec emits. The number is now DERIVED and the prose merely
//! carries it.
//!
//! Scope, stated so the next reader does not over-read it: this checks the
//! RANGE END against the registry maximum. It does not check that every tag in
//! the range has a table row, nor that the row's prose describes the variant
//! correctly — see `wire_census` in `trust-ir` for the code-derived half, and
//! `scripts/check_enforcement_links.py` for citation resolution.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// Repository root, from this crate's manifest directory.
fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The highest tag each registered wire enum carries, read from the
/// allocation registry (whose own rows the `wire_census` tests re-derive from
/// the real writers, so this file never parses `binary.rs` itself).
fn registry_maxima(registry: &str) -> BTreeMap<String, u16> {
    let mut maxima: BTreeMap<String, u16> = BTreeMap::new();
    for line in registry.lines() {
        let line = line.trim();
        if !line.starts_with('{') || !line.contains("enum = \"") {
            continue;
        }
        let name = match field(line, "enum = \"") {
            Some(name) => name,
            None => continue,
        };
        // A row whose status is not `landed` names a tag no writer emits yet;
        // a heading must describe what the codec DOES write, so reservations
        // are excluded rather than silently widening the documented range.
        if let Some(status) = field(line, "status = \"")
            && status != "landed"
        {
            continue;
        }
        let Some(tag) = numeric_field(line, "tag = ") else {
            continue;
        };
        let slot = maxima.entry(name).or_insert(tag);
        *slot = (*slot).max(tag);
    }
    maxima
}

/// The text between `key` and the next `"`.
fn field(line: &str, key: &str) -> Option<String> {
    let rest = line.split_once(key)?.1;
    let value = rest.split_once('"')?.0;
    Some(value.to_string())
}

/// The integer immediately after `key`.
fn numeric_field(line: &str, key: &str) -> Option<u16> {
    let rest = line.split_once(key)?.1;
    let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
    digits.parse().ok()
}

/// Every `## \`Name\` tags — 0xAA..=0xBB` heading, as (name, range end).
///
/// The heading spelling is matched exactly as the document writes it, em dash
/// included: a heading that drifts from that shape is reported as unparsed
/// rather than skipped, so a reformat cannot silently retire the check.
fn documented_ranges(doc: &str) -> (BTreeMap<String, u16>, Vec<String>) {
    let mut ranges: BTreeMap<String, u16> = BTreeMap::new();
    let mut unparsed: Vec<String> = Vec::new();
    for line in doc.lines() {
        let line = line.trim_end();
        if !line.starts_with("## `") || !line.contains(" tags ") {
            continue;
        }
        let parsed = (|| {
            let name = line.strip_prefix("## `")?.split_once('`')?.0.to_string();
            let range = line.split_once("0x")?.1;
            let end = range.split_once("..=0x")?.1.trim();
            let end = u16::from_str_radix(end, 16).ok()?;
            Some((name, end))
        })();
        match parsed {
            Some((name, end)) => {
                ranges.insert(name, end);
            }
            None => unparsed.push(line.to_string()),
        }
    }
    (ranges, unparsed)
}

/// Every documented tag range ends at the highest tag the codec writes.
#[test]
fn documented_tag_ranges_match_the_registry() {
    let root = repo_root();
    let doc_path = root.join("docs/binary-format.md");
    // `docs/` is denied from every public export, exactly as `back_compat.rs`
    // records for the format-version marker, so this half is dev-tree-only.
    if !doc_path.exists() {
        eprintln!(
            "skipping tag-range check: docs/binary-format.md not present in \
             this checkout (docs/ never ships)"
        );
        return;
    }
    let doc = std::fs::read_to_string(&doc_path).expect("read docs/binary-format.md");
    let registry = std::fs::read_to_string(root.join("wire-allocations.toml"))
        .expect("read wire-allocations.toml");

    let maxima = registry_maxima(&registry);
    assert!(
        !maxima.is_empty(),
        "parsed no landed enum_tag rows from wire-allocations.toml — the \
         registry's row shape changed and this gate went vacuous"
    );
    let (ranges, unparsed) = documented_ranges(&doc);
    assert!(
        unparsed.is_empty(),
        "these look like tag-range headings but did not parse, so they are \
         unchecked: {unparsed:?}"
    );
    assert!(
        !ranges.is_empty(),
        "parsed no tag-range headings from docs/binary-format.md — the \
         heading shape changed and this gate went vacuous"
    );

    let mut drift: Vec<String> = Vec::new();
    for (name, documented_end) in &ranges {
        let Some(actual_end) = maxima.get(name) else {
            // A heading for something the registry does not carry: either the
            // enum is unregistered (a real registry gap) or the heading names
            // a construct that is not a wire enum at all. Both need a human.
            drift.push(format!(
                "`{name}` has a documented range ending 0x{documented_end:02X} but no \
                 landed enum_tag rows in wire-allocations.toml"
            ));
            continue;
        };
        if documented_end != actual_end {
            drift.push(format!(
                "`{name}`: docs/binary-format.md says 0x00..=0x{documented_end:02X}, the \
                 codec writes up to 0x{actual_end:02X}"
            ));
        }
    }
    assert!(
        drift.is_empty(),
        "docs/binary-format.md is the NORMATIVE tag-byte specification, and a \
         consumer implemented from a stale range refuses tags the codec emits \
         (measured 2026-09-20: ObligationKind had drifted six tags since v41). \
         Fix the heading, not this test:\n  {}",
        drift.join("\n  ")
    );
}

/// The gate fails on the exact drift it was written for.
///
/// Without this, a refactor that broke the heading parser would leave the test
/// green over an empty comparison — the failure mode the two vacuity
/// assertions above cover for absence, and this covers for mismatch.
#[test]
fn the_gate_catches_a_stale_heading() {
    let registry = std::fs::read_to_string(repo_root().join("wire-allocations.toml"))
        .expect("read wire-allocations.toml");
    let maxima = registry_maxima(&registry);
    let obligation_kind = *maxima
        .get("ObligationKind")
        .expect("ObligationKind is a registered wire enum");
    assert_eq!(
        obligation_kind, 15,
        "v41 put `Custom` at tag 15; if this moved, the doc heading and this \
         control both need the new value"
    );

    // The document as it read before 2026-09-20, verbatim in the heading shape.
    let stale = "## `ObligationKind` tags — 0x00..=0x09\n";
    let (ranges, unparsed) = documented_ranges(stale);
    assert!(unparsed.is_empty(), "the control heading must parse");
    assert_eq!(
        ranges.get("ObligationKind"),
        Some(&9),
        "the parser must read the stale range it is meant to catch"
    );
    assert_ne!(
        ranges.get("ObligationKind").copied(),
        Some(obligation_kind),
        "the stale heading must NOT compare equal to the registry maximum, or \
         the gate above proves nothing"
    );
}
