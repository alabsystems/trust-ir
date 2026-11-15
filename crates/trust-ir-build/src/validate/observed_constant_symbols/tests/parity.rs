// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_missing_and_function_only_preserve_not_a_global_precedence() {
    let m = Module::new("");
    assert_eq!(
        run(&m, "missing").0,
        (false, Err(PointerConstantRefusal::NotAModuleGlobal))
    );
    let mut m = fixture();
    m.globals.clear();
    m.functions.push(function(8, "target"));
    assert_eq!(
        run(&m, "target").0.1,
        Err(PointerConstantRefusal::NotAModuleGlobal)
    );
}
#[test]
fn exact_unique_actual_global_is_returned_at_its_stored_position() {
    let m = fixture();
    assert_eq!(run(&m, "target").0, (false, Ok(1)));
    assert_eq!(run(&m, "other").0, (false, Ok(0)));
}
#[test]
fn all_duplicate_global_rows_count_before_definition_tls_or_linkage() {
    let mut m = fixture();
    m.globals[1].initializer = None;
    m.globals[1].tls = Some(TlsModel::LocalExec);
    m.globals[1].linkage = Linkage::Weak;
    for _ in 0..5 {
        m.globals.push(global("target"));
    }
    assert_eq!(
        run(&m, "target").0.1,
        Err(PointerConstantRefusal::AmbiguousSymbol {
            globals: 6,
            functions: 0
        })
    );
}
#[test]
fn all_same_name_functions_count_independent_of_id_ambiguity_or_body() {
    let mut m = fixture();
    for _ in 0..7 {
        m.functions.push(function(9, "target"));
    }
    m.functions
        .last_mut()
        .unwrap()
        .blocks
        .push(trust_ir::Block::new(BlockId::new(0)));
    assert_eq!(
        run(&m, "target").0.1,
        Err(PointerConstantRefusal::AmbiguousSymbol {
            globals: 1,
            functions: 7
        })
    );
}
#[test]
fn exact_definition_then_tls_then_interposable_order_is_preserved() {
    let mut m = fixture();
    m.globals[1].initializer = None;
    m.globals[1].tls = Some(TlsModel::GeneralDynamic);
    m.globals[1].linkage = Linkage::Weak;
    assert_eq!(
        run(&m, "target").0.1,
        Err(PointerConstantRefusal::GlobalNotDefined)
    );
    m.globals[1].initializer = Some(Constant::Bool(false));
    assert_eq!(
        run(&m, "target").0.1,
        Err(PointerConstantRefusal::ThreadLocal)
    );
    m.globals[1].tls = None;
    assert_eq!(
        run(&m, "target").0.1,
        Err(PointerConstantRefusal::InterposableLinkage {
            linkage: Linkage::Weak
        })
    );
}
#[test]
fn every_actual_linkage_cell_and_tls_model_matches_ordinary_rule() {
    let mut m = fixture();
    for linkage in [
        Linkage::External,
        Linkage::Internal,
        Linkage::Private,
        Linkage::Weak,
        Linkage::LinkOnce,
        Linkage::AvailableExternally,
        Linkage::ExternalWeak,
        Linkage::WeakOdr,
        Linkage::LinkOnceOdr,
    ] {
        m.globals[1].linkage = linkage;
        let out = run(&m, "target").0.1;
        if linkage.is_interposable() {
            assert_eq!(
                out,
                Err(PointerConstantRefusal::InterposableLinkage { linkage })
            );
        } else {
            assert_eq!(out, Ok(1));
        }
    }
    for tls in [
        TlsModel::LocalExec,
        TlsModel::InitialExec,
        TlsModel::GeneralDynamic,
        TlsModel::LocalDynamic,
    ] {
        m.globals[1].tls = Some(tls);
        assert_eq!(
            run(&m, "target").0.1,
            Err(PointerConstantRefusal::ThreadLocal)
        );
    }
}
#[test]
fn weak_membership_uses_bodyless_externalweak_existential_name_rule() {
    let mut m = fixture();
    assert!(run(&m, "weak").0.0);
    m.functions[1]
        .blocks
        .push(trust_ir::Block::new(BlockId::new(0)));
    assert!(!run(&m, "weak").0.0);
    let mut duplicate = function(2, "weak");
    duplicate.linkage = Linkage::ExternalWeak;
    m.functions.push(duplicate);
    assert!(run(&m, "weak").0.0);
    m.functions.last_mut().unwrap().linkage = Linkage::Weak;
    assert!(!run(&m, "weak").0.0);
}
#[test]
fn long_unicode_names_require_exact_last_byte_and_length_identity() {
    let name = "é🦀中".repeat(500);
    let mut m = fixture();
    m.globals[1].name = format!("{name}a");
    m.functions[1].name = format!("{name}b");
    assert_eq!(run(&m, &format!("{name}a")).0, (false, Ok(1)));
    assert_eq!(
        run(&m, &format!("{name}b")).0,
        (true, Err(PointerConstantRefusal::NotAModuleGlobal))
    );
    assert_eq!(
        run(&m, &name).0,
        (false, Err(PointerConstantRefusal::NotAModuleGlobal))
    );
    m.globals[0].name.clear();
    assert_eq!(run(&m, "").0, (false, Ok(0)));
}
