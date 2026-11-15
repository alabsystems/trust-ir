// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn exact_none_complete_and_empty_partial_labels_match_the_original() {
    let mut module = Module::new("none");
    assert_eq!(
        run(&module).0,
        Err(CompletenessError::IncompletenessUnclaimed)
    );
    module.completeness = Some(ModuleCompleteness::Complete);
    assert_eq!(run(&module).0, Ok(()));
    assert_eq!(
        run(&partial(vec![])).0,
        Err(CompletenessError::ModuleIncomplete { rows: vec![] })
    );
}
#[test]
fn all_physical_rows_order_duplicates_and_option_empty_distinctions_are_copied() {
    let module = fixtures::module();
    let expected = module.completeness.clone();
    let (result, _) = run(&module);
    let Err(CompletenessError::ModuleIncomplete { rows }) = result else {
        panic!("partial label")
    };
    assert_eq!(rows, fixtures::rows());
    assert_eq!(module.completeness, expected);
    let Some(ModuleCompleteness::Partial(original)) = &module.completeness else {
        unreachable!()
    };
    for (input, output) in original.iter().zip(&rows) {
        assert_ne!(input.symbol.as_ptr(), output.symbol.as_ptr());
        if !input.reason.is_empty() {
            assert_ne!(input.reason.as_ptr(), output.reason.as_ptr());
        }
    }
    assert_eq!(rows[0].display_path, None);
    assert_eq!(rows[1].display_path, Some(String::new()));
}
#[test]
fn every_field_tail_and_many_identical_symbols_survive_without_normalization() {
    let symbol = "λ".repeat(3000) + "symbol-tail";
    let path = "p".repeat(5000) + "path-tail\0";
    let reason = "😀".repeat(1700) + "reason-tail";
    let rows = (0..35)
        .map(|_| row(&symbol, Some(&path), &reason))
        .collect::<Vec<_>>();
    assert_eq!(
        run(&partial(rows.clone())).0,
        Err(CompletenessError::ModuleIncomplete { rows })
    );
}
#[test]
fn complete_claim_is_only_its_label_and_never_an_independent_truth_or_type_check() {
    let mut module = Module::new("not-type-validated");
    module.types = vec![trust_ir::ty::Ty::Tuple(vec![
        trust_ir::ty::Ty::Error;
        10000
    ])];
    module.completeness = Some(ModuleCompleteness::Complete);
    let (result, observer) = run(&module);
    assert_eq!(result, Ok(()));
    assert!(observer.work < 1000);
}
#[test]
fn exact_static_count_and_optional_empty_path_display_match_ordinary() {
    assert_eq!(
        text(&CompletenessError::IncompletenessUnclaimed).0,
        "the module makes no completeness claim (Module.completeness is None); a consumer that needs a complete module refuses it, never assumes it"
    );
    assert_eq!(
        text(&CompletenessError::ModuleIncomplete { rows: vec![] }).0,
        "the module claims to be partial: 0 unlowered item(s)"
    );
    assert_eq!(
        text(&CompletenessError::ModuleIncomplete {
            rows: vec![row("x", Some(""), "why")]
        })
        .0,
        "the module claims to be partial: 1 unlowered item(s); \"x\" (): why"
    );
    for count in [1, 10, 17] {
        text(&CompletenessError::ModuleIncomplete {
            rows: vec![row("s", None, "r"); count],
        });
    }
}
#[test]
fn symbols_use_string_debug_but_paths_and_reasons_remain_exact_raw_utf8() {
    for symbol in [
        "",
        "'\"\\\n\r\t\0\u{7f}",
        "λé中😀",
        "a\u{301}\u{200d}\u{2028}\u{e000}\u{10ffff}",
    ] {
        let error = CompletenessError::ModuleIncomplete {
            rows: vec![row(symbol, Some("raw\n'\"\\\0λ"), "reason\n'\"\\\0中")],
        };
        let (actual, _) = text(&error);
        assert!(actual.contains(" (raw\n'\"\\\0λ): reason\n'\"\\\0中"));
    }
    text(&CompletenessError::ModuleIncomplete {
        rows: fixtures::rows(),
    });
}
#[test]
fn count_decimal_uses_all_original_usize_bits_including_zero_and_maximum() {
    for value in [0, 1, 10, u16::MAX as usize, usize::MAX] {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut output = String::new();
        Work {
            session: &mut session,
            site: site(),
        }
        .number(value, &mut output)
        .unwrap();
        assert_eq!(output, value.to_string());
    }
}
#[test]
fn consuming_both_error_variants_retires_every_owned_nested_field_before_finish() {
    for error in fixtures::errors() {
        let observer = retired(error);
        let (last, earlier) = observer.events.split_last().unwrap();
        assert_eq!(
            (last.phase, last.work, last.copy_bytes),
            (ExecutionPhase::Publication, 0, 0)
        );
        assert!(
            earlier
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.copy_bytes == 0)
        );
        assert_eq!(
            earlier.first().unwrap().work,
            size_of::<CompletenessError>() + 1
        );
    }
    let error = CompletenessError::ModuleIncomplete {
        rows: vec![row(&"λ".repeat(2000), Some(""), &"r".repeat(5000))],
    };
    let observer = retired(error);
    for bytes in [4000, 0, 5000] {
        assert!(
            observer
                .events
                .iter()
                .any(|e| e.phase == ExecutionPhase::ScratchRetirement
                    && e.work == bytes + size_of::<String>() + 1)
        );
    }
}
