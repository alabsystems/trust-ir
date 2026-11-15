// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all_memory_role_subsets_deduplicate_sort_and_keep_function_before_nodes() {
    let all = [
        ProofAnnotation::ReadonlyTable,
        ProofAnnotation::AtomicSetInsert,
        ProofAnnotation::AppendOnlyBuffer,
    ];
    for mask in 0u8..8 {
        let mut proofs = vec![ProofAnnotation::Tainted];
        for (index, proof) in all.iter().enumerate() {
            if mask & (1 << index) != 0 {
                proofs.push(proof.clone());
                proofs.push(proof.clone());
            }
        }
        let mut node = InstrNode::new(Inst::NullPtr).with_result(ValueId::new(7));
        node.proofs = proofs.clone();
        let mut f = function(vec![node]);
        f.proofs = proofs;
        let errors = parity(&f, Case::Memory);
        assert_eq!(errors.len(), if mask.count_ones() > 1 { 2 } else { 0 });
        if errors.len() == 2 {
            assert!(
                matches!(&errors[0], ValidationError::ConflictingFunctionMemoryRoles { func_name, .. } if func_name == &f.name)
            );
            assert!(matches!(
                &errors[1],
                ValidationError::ConflictingMemoryRoles {
                    block: 0,
                    value: Some(7),
                    ..
                }
            ));
        }
    }
}
#[test]
fn actual_role_display_tokens_and_raw_function_name_match_original_without_formatting() {
    let errors = parity(&fixture(), Case::Memory);
    assert!(
        matches!(&errors[0], ValidationError::ConflictingFunctionMemoryRoles { roles, .. } if roles == &["append_only_buffer", "readonly_table"])
    );
    assert!(
        matches!(&errors[1], ValidationError::ConflictingMemoryRoles { roles, .. } if roles == &["atomic_set_insert", "readonly_table"])
    );
    for (proof, token) in [
        (&ProofAnnotation::AppendOnlyBuffer, memory::ROLES[0]),
        (&ProofAnnotation::AtomicSetInsert, memory::ROLES[1]),
        (&ProofAnnotation::ReadonlyTable, memory::ROLES[2]),
    ] {
        assert!(proof.is_memory_role());
        assert_eq!(proof.to_string(), token);
    }
    let mut f = fixture();
    f.blocks[0].body[0].results.clear();
    assert!(matches!(
        &parity(&f, Case::Memory)[1],
        ValidationError::ConflictingMemoryRoles { value: None, .. }
    ));
}
#[test]
fn havoc_legal_undef_plain_store_and_illegal_volatile_other_nodes_match_exact_locations() {
    let instructions = vec![
        Inst::Undef { ty: Ty::U8 },
        Inst::Store {
            ty: Ty::U8,
            ptr: ValueId::new(0),
            value: ValueId::new(1),
            volatile: false,
            align: None,
        },
        Inst::Store {
            ty: Ty::U8,
            ptr: ValueId::new(0),
            value: ValueId::new(1),
            volatile: true,
            align: None,
        },
        Inst::NullPtr,
        Inst::Return { values: vec![] },
    ];
    let mut nodes = Vec::new();
    for instruction in instructions {
        let mut node = InstrNode::new(instruction);
        node.proofs = vec![
            ProofAnnotation::FreshSymbolicHavoc,
            ProofAnnotation::RegionHavocStore,
        ];
        nodes.push(node);
    }
    let errors = parity(&function(nodes), Case::Havoc);
    assert_eq!(errors.len(), 8);
    assert!(
        matches!(&errors[0], ValidationError::HavocMarkerMisplaced { marker: "RegionHavocStore", location } if location.ends_with("instruction 0 (undef)"))
    );
    assert!(
        matches!(&errors[1], ValidationError::HavocMarkerMisplaced { marker: "FreshSymbolicHavoc", location } if location.ends_with("instruction 1 (store)"))
    );
}
#[test]
fn function_scope_havoc_and_duplicate_markers_preserve_input_order_and_verbatim_unicode() {
    let mut f = function(vec![]);
    f.proofs = vec![
        ProofAnnotation::RegionHavocStore,
        ProofAnnotation::FreshSymbolicHavoc,
        ProofAnnotation::RegionHavocStore,
    ];
    let errors = parity(&f, Case::Havoc);
    assert_eq!(errors.len(), 3);
    assert!(
        matches!(&errors[0], ValidationError::HavocMarkerMisplaced { marker: "RegionHavocStore", location } if location == &format!("function '{}' (function scope)", f.name))
    );
    let mut empty = f;
    empty.proofs.clear();
    empty.blocks.clear();
    for case in [Case::Memory, Case::Havoc] {
        assert!(parity(&empty, case).is_empty());
    }
}
