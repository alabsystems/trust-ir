// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use std::collections::BTreeMap;
pub(super) fn producers() -> [Option<Producer>; 8] {
    [
        None,
        Some(Producer::TRust),
        Some(Producer::Clean),
        Some(Producer::TrustIr),
        Some(Producer::TSwift),
        Some(Producer::TC),
        Some(Producer::Other(String::new())),
        Some(Producer::Other("λ\n\0other".into())),
    ]
}
pub(super) fn fixture() -> Module {
    let mut first = function(99, "λ<shadowed-by-clean");
    first.producer = Some(Producer::Other("first'λ".into()));
    first.display_path = Some("".into());
    let mut second = function(0, &first.name);
    second.producer = Some(Producer::Clean);
    second.display_path = Some("crate::second\nλ".into());
    let mut third = function(99, "plain");
    third.display_path = None;
    let mut fourth = function(u32::MAX, "plain");
    fourth.producer = Some(Producer::Other("tail\0".into()));
    module(vec![first, second, third, fourth])
}

pub(super) fn ordinary(module: &Module) -> Vec<ValidationError> {
    let mut errors = Vec::new();
    // This test-only block is retained byte-exact from immutable793; its
    // BTreeMap/ordinary contains/clones are an oracle, never production work.
    {
        let mut first_by_name: BTreeMap<&str, &Function> = BTreeMap::new();
        for func in &module.functions {
            if func.name.contains(SYNTHETIC_SYMBOL_MARKER) {
                errors.push(ValidationError::SyntheticSymbolName {
                    function: func.id.index(),
                    name: func.name.clone(),
                });
            }
            if let Some(first) = first_by_name.get(func.name.as_str()) {
                errors.push(ValidationError::DuplicateFunctionSymbol {
                    name: func.name.clone(),
                    first: first.id.index(),
                    second: func.id.index(),
                    first_producer: first.producer.clone(),
                    second_producer: func.producer.clone(),
                    first_display_path: first.display_path.clone(),
                    second_display_path: func.display_path.clone(),
                });
            } else {
                first_by_name.insert(func.name.as_str(), func);
            }
        }
    }
    errors
}
