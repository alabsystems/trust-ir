// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS4.17 (F-079, cheap half; decision gate DG-54): item identity
//! diagnostics.
//!
//! Two changes to the one rule TrustIr has for "no def owns two rows"
//! (`docs/SPEC_RATIFICATIONS.md` §1.1: the link-time symbol `Function.name`
//! is the only def identity on the wire):
//!
//! * `ValidationError::DuplicateFunctionSymbol` names WHO claimed the symbol
//!   twice: each holder's recorded producer and `display_path`, verbatim
//!   (`None` stays `None`, printed `untagged` / `unrecorded`). Before, it
//!   carried two ids and a name, so a Rust-vs-Clean collision in a
//!   two-language module read the same as two rows of one producer.
//! * `ValidationError::SyntheticSymbolName` refuses a `Function.name`
//!   carrying the `<shadowed-by-` marker. `~/trust`'s Clean-origin join
//!   retires a shadowed Rust declaration by RENAMING it to
//!   `<name>::<shadowed-by-clean-origin:FuncId(N)>` (it keeps its ids
//!   dense; the format does not require that); the renamed row validated as
//!   an ordinary `External`
//!   declaration of a symbol no object defines, sharing the definition's
//!   `display_path`. DECIDE (DG-54), Recommended option adopted: refuse the
//!   synthetic symbol and have the producer DROP the orphan (WS5) — no
//!   `Linkage::Retired` tombstone, because no consumer needs one.
//!
//! The substring rule is a TRIPWIRE for the one measured producer spelling,
//! not a closure: a producer renaming the orphan to any other marker passes
//! it. The structural closure (a symbol-alphabet rule, `NonLinkSymbolName`)
//! waits on WS5/F-087 moving def-paths out of `Function.name`; the variant's
//! rustdoc says so.
//!
//! Rows ported (archived at
//! `reports/2026-09-17-two-language-proof-program/evidence/understand.json`):
//!
//! * `design-0827/no-def-owns-two-rows` — was PARTIAL (the retired-orphan
//!   shape validated clean); flips: the orphan is refused by name, the
//!   un-renamed collision names both producers, and the producer's repair
//!   (orphan dropped) validates.
//! * `spec-surface-0709/03-shared-namespace-duplicates` — was PARTIAL (the
//!   diagnostic named two ids only); flips PARTIALLY: both producers and both
//!   display paths are named. What stays open: no source SPAN (a `Function`
//!   carries none) and no sort dimension (the symbol namespace is functions
//!   only).
//! * `spec-surface-0709/17-identity-names-are-views` stays GAP: it is the
//!   ItemKey/CitationRef half, a decision gate co-owned with WS3; no test here
//!   claims it.
//!
//! The TEXT half of the synthetic name (it must still round-trip: the codec is
//! not the validator) is held by `trust-ir`'s
//! `c08_names_outside_the_identifier_alphabet_round_trip_quoted` and the
//! conformance row `b7.names.text_refuses.clean_shadowed`, which now also pins
//! this refusal; trust-ir-build's tests do not build the parser.

use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, FuncId};
use trust_ir::{Endianness, Module, Producer, StructPassingPolicy, TargetInfo};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{ModuleBuilder, validate_changed, validate_module};

/// The spelling `~/trust` mints (`clean_origin_join.rs`) for the retired row
/// of `m::cleanAdd` shadowed by the Clean definition `FuncId(1)`.
const RETIRED: &str = "m::cleanAdd::<shadowed-by-clean-origin:FuncId(1)>";

/// The pinned target every fixture here is built for (a body-less external
/// declaration is an ABI boundary, admissible only under a pinned target).
fn pinned_target() -> TargetInfo {
    TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("sysv64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

/// The honest two-language module, in this table order:
///
/// * `#0` `program` — Rust (`TRust`, display path `app::program`), calls `#1`;
/// * `#1` `m::cleanAdd` — Clean (`Clean`, display path `Island.cleanAdd`).
///
/// Two producers, two distinct link-time symbols: it validates clean.
fn honest() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("item_identity", pinned_target());
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let program = mb.declare_function("program", ft);
    let clean_add = mb.declare_function("m::cleanAdd", ft);

    let mut body = mb.define_function(program).expect("program");
    let entry = body.create_block();
    let x = body.add_block_param(entry, Ty::I32);
    body.switch_to_block(entry);
    let r = body.call(clean_add, vec![x]);
    body.ret(vec![r]);
    body.set_producer(Producer::TRust);
    body.set_display_path("app::program");
    body.build();

    let mut body = mb.define_function(clean_add).expect("cleanAdd");
    let entry = body.create_block();
    let x = body.add_block_param(entry, Ty::I32);
    body.switch_to_block(entry);
    body.ret(vec![x]);
    body.set_producer(Producer::Clean);
    body.set_display_path("Island.cleanAdd");
    body.build();

    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The honest module plus the Rust declaration the Clean definition shadows,
/// as a bodyless `External` row `#2` named `name`, carrying the Rust
/// producer and the definition's display path (the measured producer shape).
fn with_rust_declaration(name: &str) -> Module {
    let mut module = honest();
    let ty = module.functions[1].ty;
    let mut declaration = trust_ir::Function::new(FuncId::new(2), name, ty, BlockId::new(0));
    declaration.producer = Some(Producer::TRust);
    declaration.display_path = Some("Island.cleanAdd".into());
    module.functions.push(declaration);
    module
}

fn synthetic(function: u32, name: &str) -> ValidationError {
    ValidationError::SyntheticSymbolName {
        function,
        name: name.into(),
    }
}

/// Whether a rendered `DuplicateFunctionSymbol` names both holders by
/// producer token, so a reader can tell a Rust-vs-Clean collision from a
/// one-producer one. The mutation control below holds this check to reject a
/// rendering that drops them.
fn names_both_producers(text: &str) -> Result<(), String> {
    for token in ["producer trust", "producer clean"] {
        if !text.contains(token) {
            return Err(format!("{text:?} does not name `{token}`"));
        }
    }
    Ok(())
}

/// The error the Rust/Clean collision on `program` must produce: both
/// holders, attributed.
fn program_collision() -> ValidationError {
    ValidationError::DuplicateFunctionSymbol {
        name: "program".into(),
        first: 0,
        second: 1,
        first_producer: Some(Producer::TRust),
        second_producer: Some(Producer::Clean),
        first_display_path: Some("app::program".into()),
        second_display_path: Some("Island.cleanAdd".into()),
    }
}

// ---------------------------------------------------------------------------
// positive
// ---------------------------------------------------------------------------

/// Positive: two producers, two distinct link-time symbols, one call edge
/// across the seam — nothing to refuse.
#[test]
fn an_honest_two_language_module_with_distinct_symbols_validates() {
    let module = honest();
    assert_eq!(module.functions[0].producer, Some(Producer::TRust));
    assert_eq!(module.functions[1].producer, Some(Producer::Clean));
    assert_eq!(validate_module(&module), []);
}

// ---------------------------------------------------------------------------
// negative twins, each refused by the SPECIFIC named reason
// ---------------------------------------------------------------------------

/// Negative twin: the Clean row takes the Rust row's symbol. The ONLY error
/// is `DuplicateFunctionSymbol`, and it names both producers and both
/// display paths, in id order.
#[test]
fn a_rust_and_a_clean_row_sharing_a_symbol_name_both_producers() {
    let mut module = honest();
    module.functions[1].name = "program".into();
    let errors = validate_module(&module);
    assert_eq!(errors, [program_collision()]);
    let text = errors[0].to_string();
    assert_eq!(names_both_producers(&text), Ok(()));
    assert!(
        text.contains("\"app::program\"") && text.contains("\"Island.cleanAdd\""),
        "both display paths are named: {text}"
    );
}

/// Negative twin: the retired row, renamed with the synthetic marker, is
/// refused as `SyntheticSymbolName` and nothing else.
#[test]
fn a_shadowed_by_clean_origin_declaration_is_a_synthetic_symbol_name() {
    let module = with_rust_declaration(RETIRED);
    assert_eq!(validate_module(&module), [synthetic(2, RETIRED)]);
}

/// The rule is about the NAME, whatever the row is: a DEFINITION carrying
/// the marker is refused the same way (a producer cannot launder the spelling
/// by giving the orphan a body).
#[test]
fn a_definition_carrying_the_marker_is_refused_alike() {
    let mut module = honest();
    module.functions[1].name = RETIRED.into();
    assert_eq!(validate_module(&module), [synthetic(1, RETIRED)]);
}

/// The rule is module-level: the incremental entry point that deep-validates
/// ONLY the changed functions (here: none) still refuses it.
#[test]
fn the_synthetic_name_rule_is_not_skipped_by_the_incremental_filter() {
    let module = with_rust_declaration(RETIRED);
    assert_eq!(validate_changed(&module, &[]), [synthetic(2, RETIRED)]);
}

/// A synthetic row that ALSO collides reports both rules: the name is not a
/// symbol, and the symbol is held twice. Neither masks the other.
#[test]
fn a_duplicated_synthetic_name_reports_both_rules() {
    let mut module = with_rust_declaration(RETIRED);
    module.functions[1].name = RETIRED.into();
    let errors = validate_module(&module);
    assert_eq!(
        errors,
        [
            synthetic(1, RETIRED),
            synthetic(2, RETIRED),
            ValidationError::DuplicateFunctionSymbol {
                name: RETIRED.into(),
                first: 1,
                second: 2,
                first_producer: Some(Producer::Clean),
                second_producer: Some(Producer::TRust),
                first_display_path: Some("Island.cleanAdd".into()),
                second_display_path: Some("Island.cleanAdd".into()),
            },
        ]
    );
}

/// No guessing: a holder that records neither a producer nor a display path
/// is printed as such, never attributed to a producer.
#[test]
fn an_unrecorded_holder_is_printed_untagged_and_unrecorded() {
    let mut module = honest();
    module.functions[1].name = "program".into();
    module.functions[1].producer = None;
    module.functions[1].display_path = None;
    let errors = validate_module(&module);
    assert_eq!(errors.len(), 1, "{errors:?}");
    let ValidationError::DuplicateFunctionSymbol {
        second_producer,
        second_display_path,
        ..
    } = &errors[0]
    else {
        panic!("expected DuplicateFunctionSymbol: {errors:?}");
    };
    assert_eq!((second_producer, second_display_path), (&None, &None));
    let text = errors[0].to_string();
    assert!(
        text.contains("#1: producer untagged, display path unrecorded"),
        "{text}"
    );
    assert!(text.contains("#0: producer trust"), "{text}");
}

// ---------------------------------------------------------------------------
// mutation controls
// ---------------------------------------------------------------------------

/// Mutation control: the producer check is held to discriminate. A renderer
/// that drops the attribution (the pre-WS4.17 text) fails it, and so does a
/// raise site that drops the producers (the real `Display` over the same
/// error with `None` producers) — while the real rendering passes.
#[test]
fn a_mutant_dropping_the_producer_tokens_fails_the_attribution_check() {
    let error = program_collision();
    assert_eq!(names_both_producers(&error.to_string()), Ok(()));

    // Mutant 1: the Display arm without the attribution clause.
    fn pre_ws4_17_render(error: &ValidationError) -> String {
        let ValidationError::DuplicateFunctionSymbol {
            name,
            first,
            second,
            ..
        } = error
        else {
            unreachable!("only rendered over DuplicateFunctionSymbol")
        };
        format!(
            "functions #{first} and #{second} share the link symbol {name:?}; \
             ambiguous name-keyed identity, fail-closed"
        )
    }
    assert!(names_both_producers(&pre_ws4_17_render(&error)).is_err());

    // Mutant 2: the raise site copies no producer.
    let ValidationError::DuplicateFunctionSymbol {
        name,
        first,
        second,
        first_display_path,
        second_display_path,
        ..
    } = error
    else {
        unreachable!()
    };
    let dropped = ValidationError::DuplicateFunctionSymbol {
        name,
        first,
        second,
        first_producer: None,
        second_producer: None,
        first_display_path,
        second_display_path,
    };
    assert!(names_both_producers(&dropped.to_string()).is_err());
    // ... and the structural comparison in the negative twin catches it too.
    assert_ne!(dropped, program_collision());
}

/// Mutation control for the synthetic rule: the refusal is exactly the
/// marker. The same module with the orphan under its REAL name is the
/// un-renamed collision (`DuplicateFunctionSymbol`, attributed), and a name
/// that merely resembles the marker without it (`<shadowed>`, no `-by-`) is
/// not refused by this rule — the tripwire is the measured spelling, and
/// widening it is WS5's symbol-alphabet decision, not a guess made here.
#[test]
fn the_synthetic_rule_fires_on_the_marker_and_only_the_marker() {
    let near_miss = "m::cleanAdd::<shadowed>";
    let module = with_rust_declaration(near_miss);
    assert_eq!(validate_module(&module), []);

    let module = with_rust_declaration("m::cleanAdd");
    assert_eq!(
        validate_module(&module),
        [ValidationError::DuplicateFunctionSymbol {
            name: "m::cleanAdd".into(),
            first: 1,
            second: 2,
            first_producer: Some(Producer::Clean),
            second_producer: Some(Producer::TRust),
            first_display_path: Some("Island.cleanAdd".into()),
            second_display_path: Some("Island.cleanAdd".into()),
        }]
    );
}

// ---------------------------------------------------------------------------
// ported rows, named after the row
// ---------------------------------------------------------------------------

/// Row `design-0827/no-def-owns-two-rows` (was PARTIAL): "a validate-level
/// rule that no def owns two rows (defined-shadows-declaration)". Measured at
/// 4efb21bc: a bodyless row renamed `m::cleanAdd::<shadowed-by-clean-origin:
/// FuncId(1)>` sharing display path `Island.cleanAdd` with the definition
/// VALIDATED ok. Now, for one def (`Island.cleanAdd`):
///
/// 1. the producer's rename-out-of-the-namespace is refused by name;
/// 2. the orphan under its real name is the attributed collision;
/// 3. the producer's repair — the orphan DROPPED — validates, one row per def.
///    (The orphan is the last row, so nothing follows it to renumber; the
///    format requires no dense `FuncId`s in any case.)
#[test]
fn design_0827_no_def_owns_two_rows() {
    let renamed = with_rust_declaration(RETIRED);
    assert_eq!(validate_module(&renamed), [synthetic(2, RETIRED)]);

    let unrenamed = with_rust_declaration("m::cleanAdd");
    let errors = validate_module(&unrenamed);
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::DuplicateFunctionSymbol {
                name,
                first_producer: Some(Producer::Clean),
                second_producer: Some(Producer::TRust),
                ..
            }] if name == "m::cleanAdd"
        ),
        "{errors:?}"
    );

    let mut repaired = renamed;
    repaired
        .functions
        .retain(|f| !f.name.contains("<shadowed-by-"));
    assert_eq!(validate_module(&repaired), []);
    let owners = repaired
        .functions
        .iter()
        .filter(|f| f.display_path.as_deref() == Some("Island.cleanAdd"))
        .count();
    assert_eq!(owners, 1, "exactly one row owns the def");
}

/// Row `spec-surface-0709/03-shared-namespace-duplicates` (was PARTIAL,
/// flips PARTIALLY): "same-path same-sort duplicates are a hard error naming
/// BOTH producers' spans". A Rust `program` and a Clean def claiming the
/// same symbol are a hard error from the default entry point, and the
/// diagnostic now names both producers and both display paths (it named two
/// ids only). Still open, and not claimed: SPANS (a `Function` carries no
/// source span) and the SORT dimension (the symbol namespace is functions
/// only) — both with the ItemKey decision gate (WS3).
#[test]
fn spec_surface_0709_03_shared_namespace_duplicates() {
    let mut module = honest();
    module.functions[1].name = "program".into();
    let errors = validate_module(&module);
    assert_eq!(errors, [program_collision()]);
    let text = errors[0].to_string();
    assert_eq!(names_both_producers(&text), Ok(()), "{text}");
    assert!(
        text.contains("#0: producer trust, display path \"app::program\"")
            && text.contains("#1: producer clean, display path \"Island.cleanAdd\""),
        "each holder is attributed by id: {text}"
    );
}
