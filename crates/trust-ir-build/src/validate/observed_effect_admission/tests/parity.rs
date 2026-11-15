// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn absent_function_summary_or_effects_is_exactly_none_never_an_admitted_default() {
    let mut m = fixture(false);
    for policy in [ImportPolicy::Structural, ImportPolicy::Refuse] {
        assert_ordinary(&m, FuncId::new(u32::MAX), policy);
        assert_ordinary(&m, FuncId::new(221), policy);
    }
    m.functions[0].summary.as_mut().unwrap().effects = None;
    assert_ordinary(&m, FuncId::new(221), ImportPolicy::Structural);
    m.functions[0].summary = None;
    assert_ordinary(&m, FuncId::new(221), ImportPolicy::Refuse);
    m.functions.clear();
    assert_ordinary(&m, FuncId::new(221), ImportPolicy::Structural);
}
#[test]
fn all_nine_linkages_preserve_the_exact_definition_rule_under_both_nonlinked_policies() {
    for linkage in linkages() {
        let mut m = fixture(false);
        m.functions[0].linkage = linkage;
        for policy in [ImportPolicy::Structural, ImportPolicy::Refuse] {
            assert_eq!(
                ordinary(&m, FuncId::new(221), policy).is_some(),
                !matches!(
                    linkage,
                    Linkage::Weak | Linkage::LinkOnce | Linkage::ExternalWeak
                )
            );
            assert_ordinary(&m, FuncId::new(221), policy);
        }
    }
}
#[test]
fn every_declaration_linkage_stays_havoc_without_a_recorded_authenticated_outcome() {
    for linkage in linkages() {
        let mut m = fixture(true);
        m.functions[0].linkage = linkage;
        for policy in [ImportPolicy::Structural, ImportPolicy::Refuse] {
            assert!(ordinary(&m, FuncId::new(221), policy).is_none());
            assert_ordinary(&m, FuncId::new(221), policy);
        }
    }
}
#[test]
fn lookup_keeps_direct_slot_precedence_and_first_physical_fallback_even_for_duplicates() {
    let mut m = fixture(false);
    let mut first = m.functions[0].clone();
    first.id = FuncId::new(1);
    first.name = "first physical".into();
    let mut slot = first.clone();
    slot.name = "canonical slot".into();
    m.functions = vec![first, slot];
    for id in [FuncId::new(1), FuncId::new(0), FuncId::new(u32::MAX)] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let actual = function_by_id_observed(&m, id, &mut s, site()).unwrap();
        match (actual, m.function_by_id(id)) {
            (Some(a), Some(b)) => assert!(core::ptr::eq(a, b)),
            (None, None) => {}
            _ => panic!("lookup changed"),
        }
    }
    assert_eq!(
        m.function_by_id(FuncId::new(1)).unwrap().name,
        "canonical slot"
    );
    m.functions[0].id = FuncId::new(7);
    m.functions[1].id = FuncId::new(7);
    assert_ordinary(&m, FuncId::new(7), ImportPolicy::Structural);
    assert_eq!(
        m.function_by_id(FuncId::new(7)).unwrap().name,
        "first physical"
    );
    m.functions.reverse();
    assert_ordinary(&m, FuncId::new(7), ImportPolicy::Structural);
    assert_eq!(
        m.function_by_id(FuncId::new(7)).unwrap().name,
        "canonical slot"
    );
}
#[test]
fn borrowed_effect_payloads_names_and_body_storage_are_not_cloned_or_prewalked() {
    let m = fixture(false);
    let baseline = assert_ordinary(&m, FuncId::new(221), ImportPolicy::Refuse);
    let mut huge = m.clone();
    huge.functions[0].name = "λ\0".repeat(100000);
    huge.functions[0]
        .blocks
        .extend((1..1000).map(|i| Block::new(BlockId::new(i))));
    let effects = huge.functions[0]
        .summary
        .as_mut()
        .unwrap()
        .effects
        .as_mut()
        .unwrap();
    effects.reads = EffectSet::Places(
        (0..100000)
            .map(|i| EffectPlace::Global(GlobalId::new(i)))
            .collect(),
    );
    effects.writes = effects.reads.clone();
    let changed = assert_ordinary(&huge, FuncId::new(221), ImportPolicy::Refuse);
    assert_eq!(baseline.events, changed.events);
}
