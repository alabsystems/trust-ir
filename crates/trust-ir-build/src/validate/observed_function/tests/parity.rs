// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all_structure_debug_diagnostics_preserve_original_order_and_payloads() {
    let f = fixture();
    assert_parity(&f, Case::Structure);
    let (errors, _) = observed(&f, Case::Structure);
    assert!(matches!(
        &errors[0],
        ValidationError::InvalidValueName { value: 99, .. }
    ));
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::MidBlockTerminator { op, .. } if op == "return"))
    );
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::DuplicateBlockId(0)))
    );
    assert!(matches!(
        errors.last().unwrap(),
        ValidationError::EntryBlockNotFound(7)
    ));
}
#[test]
fn bodyless_declaration_and_contract_rules_keep_debug_prefix_even_before_early_return() {
    for linkage in [
        Linkage::External,
        Linkage::ExternalWeak,
        Linkage::Internal,
        Linkage::Private,
        Linkage::Weak,
        Linkage::LinkOnce,
        Linkage::AvailableExternally,
        Linkage::WeakOdr,
        Linkage::LinkOnceOdr,
    ] {
        for summary in [false, true] {
            let mut f = fixture();
            f.blocks.clear();
            f.linkage = linkage;
            f.summary = summary.then(FunctionSummary::default);
            assert_parity(&f, Case::Structure);
            let (errors, _) = observed(&f, Case::Structure);
            assert_eq!(
                errors.contains(&ValidationError::EmptyFunction),
                !summary && !matches!(linkage, Linkage::External | Linkage::ExternalWeak)
            );
            assert!(matches!(
                &errors[0],
                ValidationError::InvalidValueName { .. }
            ));
        }
    }
}
#[test]
fn debug_value_names_resolve_all_params_and_results_with_duplicate_precedence() {
    let mut f = fixture();
    f.scopes = None;
    f.value_names = Some(vec![
        (ValueId::new(3), "p".into()),
        (ValueId::new(5), "r".into()),
        (ValueId::new(99), "ghost".into()),
        (ValueId::new(99), "twice".into()),
    ]);
    assert_parity(&f, Case::Structure);
    let (errors, _) = observed(&f, Case::Structure);
    let names: Vec<_> = errors
        .into_iter()
        .filter(|e| matches!(e, ValidationError::InvalidValueName { .. }))
        .collect();
    assert_eq!(names.len(), 2);
    assert!(
        matches!(&names[1], ValidationError::InvalidValueName { detail, .. } if detail == "the same SSA value appears more than once")
    );
}
#[test]
fn scope_parent_and_inline_chain_matrix_matches_actual_ordinary_validator() {
    for root in [None, Some(0), Some(1)] {
        for parent in [None, Some(0), Some(1), Some(u32::MAX)] {
            for callee in ["", "callee", " "] {
                let mut f = fixture();
                f.scopes = Some(vec![
                    ScopeData::new(root, None),
                    ScopeData {
                        parent,
                        span: None,
                        inlined_at: Some(InlinedAt {
                            span: SourceSpan {
                                file: 2,
                                line: 0,
                                col: 0,
                            },
                            callee: callee.into(),
                        }),
                    },
                ]);
                assert_parity(&f, Case::Structure);
            }
        }
    }
    for scopes in [None, Some(vec![])] {
        let mut f = fixture();
        f.scopes = scopes;
        assert_parity(&f, Case::Structure);
    }
}
#[test]
fn terminator_checks_preserve_mid_last_empty_and_duplicate_block_diagnostics() {
    for first in [
        Inst::Return { values: vec![] },
        Inst::Br {
            target: BlockId::new(0),
            args: vec![],
        },
        Inst::NullPtr,
    ] {
        for last in [None, Some(Inst::NullPtr), Some(Inst::Unreachable)] {
            let mut f = fixture();
            f.blocks[0].body = vec![InstrNode::new(first.clone())];
            if let Some(last) = last {
                f.blocks[0].body.push(InstrNode::new(last));
            }
            assert_parity(&f, Case::Structure);
        }
    }
    let mut f = fixture();
    f.blocks[0].body.clear();
    assert_parity(&f, Case::Structure);
}
#[test]
fn unicode_blank_newline_and_nul_metadata_match_original_else_if_precedence() {
    for text in [
        "",
        " \n\t",
        "\u{2003}\u{202f}",
        "\u{200b}",
        " x ",
        "x\ny",
        "x\0y",
    ] {
        let mut f = fixture();
        f.body_gate = Some(trust_ir::BodyGate::Gated {
            authority: text.into(),
            evidence: None,
        });
        f.display_path = Some(text.into());
        f.section = Some(text.into());
        assert_parity(&f, Case::BodyGate);
        assert_parity(&f, Case::Symbols);
    }
}
#[test]
fn every_linkage_visibility_pair_keeps_the_exact_fixed_law_table_result() {
    for linkage in [
        Linkage::External,
        Linkage::ExternalWeak,
        Linkage::Internal,
        Linkage::Private,
        Linkage::Weak,
        Linkage::LinkOnce,
        Linkage::AvailableExternally,
        Linkage::WeakOdr,
        Linkage::LinkOnceOdr,
    ] {
        for visibility in [
            Visibility::Default,
            Visibility::Hidden,
            Visibility::Protected,
        ] {
            let mut f = fixture();
            f.linkage = linkage;
            f.visibility = visibility;
            assert_parity(&f, Case::Symbols);
        }
    }
}
#[test]
fn bounded_decimal_scope_diagnostic_preserves_usize_extremes_without_formatting_allocation() {
    for count in [0, 1, u32::MAX as usize, usize::MAX] {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut state = Checking::default();
        state.scope_overflow(81, count, &mut work).unwrap();
        assert_eq!(
            state.errors,
            vec![ValidationError::InvalidScopeTree {
                function: 81,
                scope: u32::MAX,
                detail: format!(
                    "the scope table holds {count} entries; a scope past index {} can be named by nothing (ScopeData.parent and InstrNode.scope are u32)",
                    u32::MAX
                )
            }]
        );
        state.retire_scratch(&mut work);
        state.retire_errors(&mut work);
    }
}
