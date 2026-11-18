// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn all_270_current_variant_shapes_retire_every_owned_header_separately() {
    let cases = witnesses::all();
    assert_eq!(cases.len(), 270);
    for (error, count) in cases {
        one(error, count);
    }
}

#[test]
fn complete_mixed_variant_vector_consumes_each_element_and_the_final_buffer() {
    let cases = witnesses::all();
    let expected = cases.iter().map(|(_, n)| n).sum::<usize>() + 1;
    let errors = cases.into_iter().map(|(e, _)| e).collect();
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    retire_validation_errors_observed(errors, &mut session, site()).unwrap();
    assert_eq!(headers(&observer), expected);
    assert!(
        observer.events[..observer.events.len() - 1]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn all_22_spec_violation_payload_shapes_are_consumed_without_flat_nested_drop() {
    let cases = nested_cases::specs();
    assert_eq!(cases.len(), 22);
    for (error, count) in cases {
        one(error, count);
    }
}

#[test]
fn all_15_pointer_refusal_payload_shapes_are_consumed_without_flat_nested_drop() {
    let cases = nested_cases::pointers();
    assert_eq!(cases.len(), 15);
    for (error, count) in cases {
        one(error, count);
    }
}

#[test]
fn every_formula_site_consumes_only_its_owned_labels_and_fixed_ids() {
    let cases = nested_cases::formulas();
    assert_eq!(cases.len(), 4);
    for (error, count) in cases {
        one(error, count);
    }
}

#[test]
fn every_producer_variant_and_optional_owned_display_path_is_retired() {
    for producer in [
        trust_ir::Producer::TRust,
        trust_ir::Producer::Clean,
        trust_ir::Producer::TrustIr,
        trust_ir::Producer::TSwift,
        trust_ir::Producer::TC,
        trust_ir::Producer::Other("other".into()),
    ] {
        let owned = usize::from(matches!(&producer, trust_ir::Producer::Other(_)));
        one(
            ValidationError::DuplicateFunctionSymbol {
                name: "name".into(),
                first: 1,
                second: 2,
                first_producer: Some(producer),
                second_producer: Some(trust_ir::Producer::Other("other2".into())),
                first_display_path: Some(String::with_capacity(64)),
                second_display_path: None,
            },
            3 + owned,
        );
    }
    one(
        ValidationError::DuplicateFunctionSymbol {
            name: "name".into(),
            first: 1,
            second: 2,
            first_producer: None,
            second_producer: None,
            first_display_path: None,
            second_display_path: None,
        },
        1,
    );
}

#[test]
fn empty_allocated_options_and_list_buffers_are_not_silently_overwritten_or_skipped() {
    one(
        ValidationError::TypeOriginConflict {
            origin: String::with_capacity(8),
            first_module: Some(String::with_capacity(16)),
            first_table: "static",
            first: String::new(),
            second_module: None,
            second_table: "static",
            second: String::new(),
        },
        4,
    );
    one(
        ValidationError::ImportCycle {
            import: 0,
            path: Vec::with_capacity(16),
        },
        1,
    );
    one(
        ValidationError::AmbiguousImportedSymbol {
            symbol: String::new(),
            imports: Vec::with_capacity(16),
        },
        2,
    );
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    retire_validation_errors_observed(Vec::with_capacity(16), &mut session, site()).unwrap();
    assert_eq!(headers(&observer), 1);
}

#[test]
fn long_flat_string_drop_does_not_invent_a_byte_traversal_or_new_storage_charge() {
    let short = one(
        ValidationError::InvalidFunctionSummary {
            function: 0,
            detail: "short".into(),
        },
        1,
    );
    let long = one(
        ValidationError::InvalidFunctionSummary {
            function: 0,
            detail: "λ".repeat(100_000),
        },
        1,
    );
    assert_eq!(short.events, long.events);
    // Only a flat String header and pre/post allocator observations are
    // claimed; actual allocator/deallocator latency remains outside the model.
}
