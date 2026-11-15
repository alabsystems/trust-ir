// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn unicode_trim_blank_module_check_matches_the_original_whitespace_contract() {
    let mut m = fixture();
    for name in [
        "",
        " ",
        "\n\t\r",
        "\u{a0}\u{3000}\n",
        "\u{200b}",
        " x ",
        "λ",
    ] {
        m.name = name.into();
        assert_eq!(
            run(&m, Stage::Name).0.len(),
            usize::from(name.trim().is_empty())
        );
    }
}
#[test]
fn each_exact_closed_name_is_allowed_but_case_and_outer_whitespace_claims_are_refused() {
    let mut m = fixture();
    for name in RESERVED_TRUST_INTERNAL_SPEC_MODULES {
        m.spec_modules[0].name = (*name).into();
        assert!(run(&m, Stage::Reserved).0.is_empty());
        m.spec_modules[0].name = name.to_uppercase();
        assert_eq!(run(&m, Stage::Reserved).0.len(), 1);
        m.spec_modules[0].name = format!(" \u{3000}{name}\n");
        assert_eq!(run(&m, Stage::Reserved).0.len(), 1);
    }
}
#[test]
fn unrelated_and_utf8_boundary_names_do_not_claim_the_ascii_namespace() {
    let mut m = fixture();
    for name in [
        "M",
        "@trust-interné::x",
        "λtrust-internal::x",
        "@trust-internal:",
        "@trust-internal中::x",
    ] {
        m.spec_modules[0].name = name.into();
        assert!(run(&m, Stage::Reserved).0.is_empty());
    }
}
#[test]
fn unknown_reserved_name_preserves_the_complete_raw_name_and_ignores_shape_after_refusal() {
    let mut m = offenders();
    m.spec_modules[0].name = TRUST_INTERNAL_SPEC_PREFIX.to_owned() + &"λ'\n".repeat(2000) + "TAIL";
    let out = run(&m, Stage::Reserved).0;
    assert_eq!(out.len(), 1);
    assert!(
        matches!(&out[0],ValidationError::ReservedSpecModuleName {name,..} if name==&m.spec_modules[0].name)
    );
}
#[test]
fn offender_labels_enforcement_and_external_origin_keep_exact_original_order() {
    let m = offenders();
    let out = run(&m, Stage::Reserved).0;
    assert_eq!(out.len(), 3);
    assert!(detail(&out[0]).contains("vars, actions, anchors, waivers, proofs"));
    assert!(detail(&out[1]).ends_with("enforcement `linked`"));
    assert!(detail(&out[2]).ends_with("origin `external(λ'\norigin)`"));
}
#[test]
fn descriptive_content_and_temporal_payload_remain_outside_this_original_reservation_rule() {
    let mut m = fixture();
    m.spec_modules[0]
        .invariants
        .push(trust_ir::SpecInvariant::new(
            "general:opaque",
            "not parsed".repeat(10000),
        ));
    let (_, before) = run(&m, Stage::Reserved);
    m.spec_modules[0].temporal.push(trust_ir::SpecTemporal::new(
        "opaque",
        trust_ir::TemporalForm::WeakFair {
            action: "not-declared".repeat(10000),
            relation: None,
        },
    ));
    let (_, after) = run(&m, Stage::Reserved);
    assert_eq!(before.events, after.events);
}
#[test]
fn canonical_decimal_zero_maximum_and_every_malformed_key_keep_exact_refusals() {
    let mut m = fixture();
    m.functions = vec![function(0, true), function(u32::MAX, true)];
    rows(
        &mut m,
        &[
            "fn:0",
            "fn:4294967295",
            "fn:",
            "fn:+1",
            "fn:-1",
            "fn:01",
            "fn:4294967296",
            "fn:١",
            "fn: 1",
        ],
    );
    let out = run(&m, Stage::Reserved).0;
    assert_eq!(out.len(), 7);
    assert!(out.iter().all(|e| detail(e).contains("does not parse")));
}
#[test]
fn duplicate_fn_keys_are_refused_before_and_independently_of_decimal_parse() {
    let mut m = fixture();
    m.functions.push(function(0, true));
    rows(&mut m, &["fn:x", "fn:x", "fn:0", "fn:0"]);
    let out = run(&m, Stage::Reserved).0;
    assert_eq!(out.len(), 3);
    assert!(detail(&out[0]).contains("does not parse"));
    assert_eq!(
        detail(&out[1]),
        "disclosure row fn:x appears more than once"
    );
    assert_eq!(
        detail(&out[2]),
        "disclosure row fn:0 appears more than once"
    );
}
#[test]
fn actual_sparse_ids_and_any_bodied_duplicate_are_used_instead_of_table_position() {
    let mut m = fixture();
    m.functions = vec![function(9, false), function(9, true), function(4, false)];
    rows(&mut m, &["fn:9", "fn:4", "fn:0"]);
    let out = run(&m, Stage::Reserved).0;
    assert_eq!(out.len(), 2);
    assert_eq!(
        detail(&out[0]),
        "disclosure row fn:4 names no bodied function (function 4 is a body-less declaration)"
    );
    assert_eq!(
        detail(&out[1]),
        "disclosure row fn:0 names no bodied function"
    );
}
#[test]
fn non_fn_families_and_uppercase_prefixes_are_neither_parsed_nor_duplicate_checked() {
    let mut m = fixture();
    rows(
        &mut m,
        &[
            "FN:0",
            "FN:0",
            "general:x",
            "general:x",
            "linked:bad",
            "skipped:",
        ],
    );
    assert!(run(&m, Stage::Reserved).0.is_empty());
}
#[test]
fn malformed_key_debug_escaping_and_full_external_path_are_byte_identical() {
    let mut m = fixture();
    let key = "fn:λ'\"\n\u{200d}".repeat(500);
    rows(&mut m, &[&key]);
    let out = run(&m, Stage::Reserved).0;
    assert_eq!(
        detail(&out[0]),
        format!(
            "disclosure row {key:?} does not parse: a `fn:` key is `fn:<FuncId index>` in canonical decimal"
        )
    );
    m.spec_modules[0].origin = SpecOrigin::External("λ\n'".repeat(2000) + "TAIL");
    run(&m, Stage::Reserved);
}
#[test]
fn returned_full_name_and_detail_strings_are_independent_of_later_input_mutation() {
    let mut m = offenders();
    let out = run(&m, Stage::Reserved).0;
    let old = out.clone();
    m.spec_modules.clear();
    assert_eq!(out, old);
}
