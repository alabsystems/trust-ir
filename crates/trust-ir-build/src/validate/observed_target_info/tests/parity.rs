// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn present_target_pointer_and_empty_triple_order_and_exact_allowed_set() {
    for pointer_size in [0, 1, 2, 3, 4, 8, 16, u32::MAX] {
        let mut m = fixtures::module(0);
        let mut ti = fixtures::target();
        ti.pointer_size = pointer_size;
        ti.triple.clear();
        m.target_info = Some(ti);
        let out = run(&m).0;
        if matches!(pointer_size, 1 | 2 | 4 | 8) {
            assert_eq!(out, vec![ValidationError::TargetTripleEmpty]);
        } else {
            assert_eq!(
                out,
                vec![
                    ValidationError::TargetPointerSizeInvalid { pointer_size },
                    ValidationError::TargetTripleEmpty
                ]
            );
        }
    }
}
#[test]
fn present_target_does_not_run_boundary_scan_and_whitespace_triple_is_not_normalized() {
    let mut m = fixtures::module(0);
    let mut ti = fixtures::target();
    ti.triple = " ".into();
    m.target_info = Some(ti);
    m.functions[0].name = "opaque".repeat(10000);
    let (out, o) = run(&m);
    assert!(out.is_empty());
    assert_eq!(
        o.events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Validation)
            .count(),
        4
    );
}
#[test]
fn all_eight_direct_invoke_panic_and_indirect_routes_match_actual_original_catalog() {
    for kind in 0..8 {
        let out = run(&fixtures::module(kind)).0;
        assert_eq!(out.len(), 1);
        let ValidationError::TargetInfoRequired { boundary } = &out[0] else {
            panic!("boundary")
        };
        let prefix = match kind {
            0 | 1 => "cross-convention call edge",
            2 => "cross-convention invoke edge",
            3 | 4 => "cross-convention panic-site edge",
            _ => "cross-convention indirect call edge",
        };
        assert!(boundary.starts_with(prefix));
    }
}
#[test]
fn all_calling_convention_spellings_and_same_convention_positive_twins_are_exact() {
    for conv in CallingConv::ALL {
        assert_eq!(boundary::convention(conv), conv.to_string());
        for kind in 0..8 {
            let mut m = fixtures::module(kind);
            m.functions[1].calling_conv = conv;
            m.functions[0].blocks[0].body = vec![InstrNode::new(fixtures::edge(kind, conv))];
            let out = run(&m).0;
            assert_eq!(out.is_empty(), conv == CallingConv::Rust);
        }
    }
}
#[test]
fn bodyless_external_and_external_weak_precede_every_earlier_stored_edge() {
    for linkage in [Linkage::External, Linkage::ExternalWeak] {
        let mut m = fixtures::module(0);
        let mut external = fixtures::function(77, "foreign`λ\n", CallingConv::C);
        external.linkage = linkage;
        external.blocks.clear();
        m.functions.push(external);
        let out = run(&m).0;
        assert_eq!(
            out,
            vec![ValidationError::TargetInfoRequired {
                boundary: format!("bodyless {linkage} declaration `foreign`λ\n`")
            }]
        );
    }
}
#[test]
fn bodyless_rust_or_nonexternal_rows_do_not_trigger_and_duplicate_direct_targets_do_not_select_a_body()
 {
    for linkage in [
        Linkage::Internal,
        Linkage::Private,
        Linkage::AvailableExternally,
        Linkage::Weak,
        Linkage::WeakOdr,
        Linkage::LinkOnce,
        Linkage::LinkOnceOdr,
    ] {
        let mut m = Module::new("nonexternal");
        let mut f = fixtures::function(5, "f", CallingConv::C);
        f.blocks.clear();
        f.linkage = linkage;
        m.functions.push(f);
        assert!(run(&m).0.is_empty());
    }
    let mut m = fixtures::module(0);
    m.functions.push(m.functions[1].clone());
    assert!(run(&m).0.is_empty());
    m.functions.retain(|f| f.id != FuncId::new(5));
    assert!(run(&m).0.is_empty());
}
#[test]
fn first_node_order_all_physical_unreachable_rows_and_unsited_assert_are_exact() {
    let mut m = fixtures::module(0);
    m.functions[0].entry = BlockId::new(999);
    let mut later = fixtures::function(6, "later", CallingConv::Swift);
    later.blocks[0].body.push(InstrNode::new(Inst::Unreachable));
    m.functions.push(later);
    let call = InstrNode::new(Inst::Call {
        callee: FuncId::new(6),
        args: vec![],
    });
    m.functions[0].blocks[0].body.insert(0, call);
    let out = run(&m).0;
    assert!(
        matches!(&out[0],ValidationError::TargetInfoRequired{boundary} if boundary.ends_with("`later` (swiftcc)"))
    );
    m.functions[0].blocks[0].body = vec![InstrNode::new(Inst::Assert {
        cond: ValueId::new(0),
        kind: trust_ir::inst::AssertKind::Unspecified,
        site: None,
    })];
    assert!(run(&m).0.is_empty());
}
#[test]
fn full_raw_name_tails_and_duplicate_bodyless_external_identity_are_preserved() {
    let mut m = fixtures::module(0);
    m.functions[0].name = "λ".repeat(3000) + "caller-tail";
    m.functions[1].name = "😀".repeat(1500) + "callee-tail";
    assert_eq!(run(&m).0.len(), 1);
    let mut external = fixtures::function(10, "duplicate-external", CallingConv::C);
    external.blocks.clear();
    external.linkage = Linkage::External;
    m.functions.push(external);
    assert!(
        matches!(&run(&m).0[0],ValidationError::TargetInfoRequired{boundary} if boundary=="bodyless external declaration `duplicate-external`")
    );
}
