// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all_three_definition_tables_keep_physical_order_kind_id_and_one_error_per_match() {
    let out = run(&fixture(), &registry()).0;
    let definitions: Vec<_> = out
        .iter()
        .map(|e| match e {
            ValidationError::HandleRuntimeSpelledStructurally { def, .. } => def.as_str(),
            _ => panic!("wrong diagnostic"),
        })
        .collect();
    assert_eq!(
        definitions,
        ["struct #17", "struct #0", "enum #9", "record #4294967295"]
    );
}
#[test]
fn exact_runtime_name_is_required_without_case_folding_prefix_or_suffix_matches() {
    let mut m = Module::new("");
    m.structs = [
        "rt::zero",
        "RT::Zero",
        "rt::Zero_tail",
        "rt",
        "λ::Zero",
        "rt::Zero",
    ]
    .iter()
    .enumerate()
    .map(|(i, name)| structure(i as u32, name))
    .collect();
    let out = run(&m, &registry()).0;
    assert_eq!(out.len(), 1);
    assert!(
        matches!(&out[0], ValidationError::HandleRuntimeSpelledStructurally { def, runtime } if def == "struct #5" && runtime == "rt::Zero")
    );
    assert!(run(&m, &HandleRegistry { pins: vec![] }).0.is_empty());
}
#[test]
fn every_actual_trusted_runtime_is_checked_not_only_the_occurring_handle_identity() {
    let r = HandleRegistry {
        pins: TRUSTED_HANDLE_RUNTIMES.to_vec(),
    };
    let mut m = Module::new("");
    m.structs = r
        .pins()
        .iter()
        .enumerate()
        .map(|(i, row)| structure(i as u32, row.runtime))
        .collect();
    assert_eq!(run(&m, &r).0.len(), r.pins().len());
}
#[test]
fn all_unsigned_decimal_boundaries_keep_exact_u32_definition_identity() {
    let r = registry();
    let mut m = Module::new("");
    let ids = [
        0,
        1,
        9,
        10,
        11,
        99,
        100,
        999,
        1000,
        999_999_999,
        1_000_000_000,
        u32::MAX,
    ];
    m.records = ids
        .iter()
        .copied()
        .map(|id| record(id, "rt::Zero"))
        .collect();
    let out = run(&m, &r).0;
    for (error, id) in out.iter().zip(ids) {
        assert!(
            matches!(error, ValidationError::HandleRuntimeSpelledStructurally { def, .. } if def == &format!("record #{id}"))
        );
    }
}
#[test]
fn definition_type_payload_and_registry_name_entry_contracts_are_unread() {
    let a = fixture();
    let mut b = a.clone();
    for row in &mut b.structs {
        row.fields.push(trust_ir::FieldDef {
            name: "opaque".repeat(4096),
            ty: Ty::Tuple(vec![Ty::Bool; 4096]),
            offset: Some(u64::MAX),
        });
    }
    let r = registry();
    let mut other = registry();
    let entries: &'static [HandleEntryPoint] = Box::leak(
        vec![
            HandleEntryPoint {
                role: "opaque",
                symbol: "opaque_symbol",
                def_path: "opaque::path",
                params: &[PinnedTy::Handle],
                returns: &[]
            };
            2048
        ]
        .into_boxed_slice(),
    );
    for pin in &mut other.pins {
        pin.name = Box::leak("UnrelatedName".repeat(4096).into_boxed_str());
        pin.entry_points = entries;
    }
    assert_eq!(run(&a, &r).1.events, run(&b, &other).1.events);
}
