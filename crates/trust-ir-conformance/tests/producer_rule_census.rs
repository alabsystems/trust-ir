// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The v41 producer conformance rule, measured over the binary golden corpus.
//!
//! `trust_ir_build::validate_module_as_decoded` refuses a bodied function with
//! no `body_gate` claim in a blob whose header declares v41 or later
//! (`ProducerOmittedBodyGate`), reading the rule against the `WireVersion` the
//! decoder returns beside the module. The goldens are byte-frozen — they are
//! the cross-repo wire contract — and when the rule first became checkable
//! (2026-09-24) it found that 8 of the goldens written at v41 or later carry
//! such a function, so `trust-ir validate` refuses those eight blobs. Their
//! producer is the fixture harness (`generate.rs`): a codec-fixture generator,
//! not a conforming producer — it stamps no claim, `body_gate.tmbc`'s
//! `no_claim` DELIBERATELY (that golden pins that the three-valued tag can
//! spell `None` at v41 at all), the others incidentally. Those bytes cannot
//! move, so the finding lives here as an exact census instead of as a
//! sentence:
//!
//! * a golden LEAVING the set is a regeneration that stamped the claim — drop
//!   the row;
//! * a golden JOINING it is a NEW bodied tag-0 at v41+ — this test fails,
//!   and the fix is at the producer (stamp the claim), never here;
//! * a pre-v41 golden can never appear: `None` is the grandfather state, and
//!   `decoded_provenance_errors` reports nothing below v41 by construction.
//!
//! Every `.tmbc` under `tests/fixtures` is a module blob this build reads;
//! one that does not decode fails this test too, so a golden cannot fall out
//! of the census by becoming unreadable. Every count here is DERIVED from the
//! directory and the set below — no literal spells "the number of v41+
//! goldens", because that is a line every parallel golden addition would
//! have to edit (CLAUDE.md, "No test may spell the next number").

use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;

use trust_ir::binary::{CONTRACT_SURFACE_FORMAT_VERSION, deserialize_module_with_wire_version};
use trust_ir_build::validate::{ValidationError, decoded_provenance_errors};

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

/// The goldens known to carry a bodied tag-0 function at v41+, with the
/// number of such functions in each. Measured 2026-09-24 with
/// `trust-ir validate` over every `.tmbc` whose header is >= 41.
const KNOWN_BODIED_TAG0_GOLDENS: &[(&str, usize)] = &[
    ("abi_calling_conv.tmbc", 1),
    ("abi_enum_tag_repr.tmbc", 1),
    ("abi_function_symbol.tmbc", 2),
    ("body_gate.tmbc", 1),
    ("composition.tmbc", 1),
    ("import_scheme.tmbc", 1),
    ("spec_carrier.tmbc", 1),
    ("text_directives.tmbc", 2),
];

#[test]
fn the_producer_rule_census_over_the_binary_goldens_is_exact() {
    let mut entries: Vec<PathBuf> = fs::read_dir(fixtures_dir())
        .expect("read fixtures dir")
        .map(|entry| entry.expect("dir entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "tmbc"))
        .collect();
    entries.sort();
    assert!(
        entries.len() >= 40,
        "the golden corpus is not where this test expects it"
    );

    let mut offenders = BTreeMap::new();
    let mut at_or_above_v41 = 0usize;
    for path in &entries {
        let name = path
            .file_name()
            .and_then(|n| n.to_str())
            .expect("utf-8 golden name")
            .to_string();
        let bytes = fs::read(path).expect("read golden");
        let (module, wire_version) = deserialize_module_with_wire_version(&bytes)
            .unwrap_or_else(|error| panic!("{name}: this build must read every golden: {error}"));
        // Only the provenance layer is measured here: each golden's
        // structural verdict is `conformance.rs`'s business and is unchanged
        // by the wire version, which this layer is the ONLY reader of.
        let errors = decoded_provenance_errors(&module, wire_version);
        if wire_version.claims_contract_surface() {
            assert!(wire_version.get() >= CONTRACT_SURFACE_FORMAT_VERSION);
            at_or_above_v41 += 1;
        } else {
            assert!(
                wire_version.get() < CONTRACT_SURFACE_FORMAT_VERSION,
                "{name}: claims_contract_surface is exactly `>= 41`"
            );
            assert_eq!(
                errors,
                Vec::new(),
                "{name}: a pre-v41 golden is grandfathered"
            );
        }
        for error in &errors {
            assert!(
                matches!(error, ValidationError::ProducerOmittedBodyGate { wire_version: v, .. } if *v == wire_version.get()),
                "{name}: the layer reports only the producer-side variant, naming the declared version: {error:?}"
            );
        }
        if !errors.is_empty() {
            offenders.insert(name, errors.len());
        }
    }

    let pinned: BTreeMap<String, usize> = KNOWN_BODIED_TAG0_GOLDENS
        .iter()
        .map(|(name, count)| ((*name).to_string(), *count))
        .collect();
    assert_eq!(
        offenders, pinned,
        "the set of v41+ goldens carrying a bodied function with no `body_gate` claim moved: \
         a NEW entry is a new bodied tag-0 at v41+ (stamp the claim at the producer, do not \
         grow this list); a MISSING entry is a regenerated golden that now conforms (drop \
         its row)"
    );
    // Non-vacuity, derived rather than spelled: both branches of the layer
    // ran (some golden is pre-v41, so the grandfather branch was exercised),
    // and some v41+ golden CONFORMS, so the refusal is not "everything at
    // v41+" — the layer distinguishes a stamped claim from an absent one.
    assert!(
        at_or_above_v41 < entries.len(),
        "no pre-v41 golden was walked; the grandfather branch never ran"
    );
    assert!(
        offenders.len() < at_or_above_v41,
        "every v41+ golden ({at_or_above_v41}) is a bodied tag-0 blob; the census cannot tell \
         the rule from a blanket refusal of v41+"
    );
}
