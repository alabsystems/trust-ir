// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::expr::{BinderData, BinderInfo, FVarId, Multiplicity};

fn bundle(count: usize) -> ScopedProofComponentBundle {
    let value = Expr::nat_lit(7);
    let ty = Expr::const_str("Nat");
    ScopedProofComponentBundle {
        declarations: (0..count)
            .map(|n| ScopedProofDeclaration {
                id: FVarId::new(n as u64 + 1),
                name: Name::from_string("Declaration").num(n as u64),
                binder: BinderInfo::Default.into(),
                non_dep: false,
                type_: ty.clone(),
                value: Some(value.clone()),
            })
            .collect(),
        outer_count: 0,
        root: value,
        goal: ty,
        work: None,
    }
}

fn envelope(root_tag: &str, records: Expr, outer: usize) -> Expr {
    tagged(
        root_tag,
        [
            Expr::nat_lit(outer as u64),
            records,
            Expr::const_str("Nat"),
            Expr::const_str("Nat"),
            Expr::nat_lit(7),
        ],
    )
}

fn carrier(records: Expr, count: usize) -> Expr {
    tagged(
        BALANCED_DECLARATIONS_TAG,
        [Expr::nat_lit(count as u64), records],
    )
}

fn decode(expression: &Expr) -> Result<(ScopedProofComponentBundle, Expr), String> {
    ScopedProofComponentBundle::decode_with_claim(&trust_ir::proof::encode_clean_expr_dag_v2(
        expression,
    )?)
}

fn drop_spine(mut expression: Expr, right: bool) {
    while let ExprKind::App(left, child) = expression.kind() {
        let next = if right { child } else { left }.as_ref().clone();
        expression = next;
    }
}

fn assert_shared_app_children(left: &Expr, right: &Expr) {
    let (ExprKind::App(left_fn, left_arg), ExprKind::App(right_fn, right_arg)) =
        (left.kind(), right.kind())
    else {
        panic!("expected application shells with shared children");
    };
    assert!(std::sync::Arc::ptr_eq(left_fn, right_fn));
    assert!(std::sync::Arc::ptr_eq(left_arg, right_arg));
}

#[test]
fn many_shallow_declarations_roundtrip_in_one_dag_without_spending_linear_depth() {
    let mut original = bundle(5_000);
    // Expr owns its top kind by value; only its children have Arc identities.
    // Non-atomic inert data makes cross-field DAG sharing observable.
    original.root = Expr::app(Expr::const_str("f"), Expr::nat_lit(7));
    original.goal = Expr::app(Expr::const_str("T"), Expr::const_str("Nat"));
    for declaration in &mut original.declarations {
        declaration.value = Some(original.root.clone());
        declaration.type_ = original.goal.clone();
    }
    let claim = original.goal.clone();
    assert_shared_app_children(
        original.declarations[0].value.as_ref().unwrap(),
        &original.root,
    );
    assert_shared_app_children(&original.declarations[0].type_, &claim);
    // The old envelope fails for the same ordinary shallow data, before any
    // model or kernel proof is involved. Its existing depth cap is unchanged.
    let old_records = tagged(
        DECLARATIONS_TAG,
        original.declarations.iter().map(|d| {
            Expr::let_named(
                d.name.clone(),
                d.type_.clone(),
                d.value.clone().unwrap(),
                Expr::fvar(d.id),
                d.non_dep,
            )
        }),
    );
    let old = envelope(ROOT_TAG, old_records.clone(), 0);
    assert!(
        trust_ir::proof::encode_clean_expr_dag_v2(&old)
            .unwrap_err()
            .contains("graph depth limit")
    );
    drop(old);
    drop_spine(old_records, false);
    let bytes = original.encode_with_claim(&claim).unwrap();
    let (decoded, external) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(external, claim);
    assert_eq!(decoded.declarations.len(), original.declarations.len());
    for (a, b) in original.declarations.iter().zip(&decoded.declarations) {
        assert_eq!(a.id, b.id);
        assert_eq!(a.name, b.name);
        assert_eq!(a.type_, b.type_);
        assert_eq!(a.value, b.value);
        assert_eq!(a.binder, b.binder);
        assert_eq!(a.non_dep, b.non_dep);
    }
    assert_eq!(decoded.root, original.root);
    assert_eq!(decoded.goal, original.goal);
    assert_shared_app_children(
        decoded.declarations[0].value.as_ref().unwrap(),
        &decoded.root,
    );
    assert_shared_app_children(&decoded.declarations[0].type_, &external);
    assert_shared_app_children(
        decoded.declarations[0].value.as_ref().unwrap(),
        decoded.declarations[4_999].value.as_ref().unwrap(),
    );
    assert_shared_app_children(
        &decoded.declarations[0].type_,
        &decoded.declarations[4_999].type_,
    );
    assert_eq!(decoded.encode_with_claim(&external).unwrap(), bytes);
}

#[test]
fn balanced_records_preserve_parameter_and_definition_attributes_without_normalizing() {
    let mut original = bundle(0);
    for info in [
        BinderInfo::Default,
        BinderInfo::Implicit,
        BinderInfo::StrictImplicit,
        BinderInfo::InstImplicit,
    ] {
        for mult in [Multiplicity::Zero, Multiplicity::One, Multiplicity::Many] {
            for present in [false, true] {
                original.declarations.push(ScopedProofDeclaration {
                    id: FVarId::new(original.declarations.len() as u64 + 1),
                    name: Name::from_string("ExactName"),
                    binder: BinderData { info, mult },
                    non_dep: true,
                    type_: Expr::const_str("Nat"),
                    value: present.then(|| Expr::nat_lit(7)),
                });
            }
        }
    }
    // A definition whose value happens to be its identity remains a present
    // value. Decode is data only; replay will reject this circular definition.
    let id = FVarId::new(original.declarations.len() as u64 + 1);
    original.declarations.push(ScopedProofDeclaration {
        id,
        name: Name::anon(),
        binder: BinderInfo::Default.into(),
        non_dep: false,
        type_: Expr::const_str("Nat"),
        value: Some(Expr::fvar(id)),
    });
    let bytes = original.encode_with_claim(&original.goal).unwrap();
    let (decoded, _) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(decoded.declarations.len(), original.declarations.len());
    for (a, b) in original.declarations.iter().zip(&decoded.declarations) {
        assert_eq!(a.id, b.id);
        assert_eq!(a.name, b.name);
        assert_eq!(a.binder, b.binder);
        assert_eq!(a.non_dep, b.non_dep);
        assert_eq!(a.type_, b.type_);
        assert_eq!(a.value, b.value);
    }
}

#[test]
fn explicit_old_envelope_keeps_its_original_reader_and_cannot_masquerade_as_balanced() {
    let mut original = bundle(3);
    original.declarations[0].value = None;
    original.declarations[0].binder = BinderData {
        info: BinderInfo::Implicit,
        mult: Multiplicity::One,
    };
    let records = tagged(
        DECLARATIONS_TAG,
        original.declarations.iter().map(|d| match &d.value {
            Some(value) => Expr::let_named(
                d.name.clone(),
                d.type_.clone(),
                value.clone(),
                Expr::fvar(d.id),
                false,
            ),
            None => Expr::lam(d.binder, d.type_.clone(), Expr::fvar(d.id)),
        }),
    );
    let (decoded, claim) = decode(&envelope(ROOT_TAG, records.clone(), 0)).unwrap();
    assert_eq!(decoded.declarations.len(), 3);
    assert_eq!(decoded.declarations[0].id, original.declarations[0].id);
    assert_eq!(
        decoded.declarations[0].binder,
        original.declarations[0].binder
    );
    assert_eq!(decoded.declarations[0].name, Name::anon());
    assert!(!decoded.declarations[0].non_dep);
    assert!(decoded.declarations[0].value.is_none());
    assert_eq!(decoded.declarations[1].name, original.declarations[1].name);
    assert_eq!(
        decoded.declarations[1].value,
        original.declarations[1].value
    );
    assert_eq!(claim, original.goal);
    assert!(decode(&envelope(BALANCED_ROOT_TAG, records, 0)).is_err());
    let balanced = carrier(balanced_records(&original.declarations), 3);
    assert!(decode(&envelope(ROOT_TAG, balanced.clone(), 0)).is_err());
    assert!(
        decode(&envelope(
            "trust_ir.test.scoped_proof.unsupported.v1",
            balanced,
            0
        ))
        .is_err()
    );
}

#[test]
fn count_split_leaf_identity_and_outer_telescope_mutations_refuse() {
    let original = bundle(33);
    let valid = balanced_records(&original.declarations);
    assert!(decode(&envelope(BALANCED_ROOT_TAG, carrier(valid.clone(), 33), 0)).is_ok());
    assert!(decode(&envelope(BALANCED_ROOT_TAG, carrier(valid, 32), 0)).is_err());
    let reversed_split = tagged(
        BRANCH_TAG,
        [
            tagged(LEAF_TAG, original.declarations[..17].iter().map(record)),
            tagged(LEAF_TAG, original.declarations[17..].iter().map(record)),
        ],
    );
    assert!(decode(&envelope(BALANCED_ROOT_TAG, carrier(reversed_split, 33), 0)).is_err());
    let oversized_leaf = tagged(LEAF_TAG, original.declarations.iter().map(record));
    assert!(decode(&envelope(BALANCED_ROOT_TAG, carrier(oversized_leaf, 33), 0)).is_err());
    let empty = tagged(LEAF_TAG, []);
    assert!(decode(&envelope(BALANCED_ROOT_TAG, carrier(empty.clone(), 0), 0)).is_ok());
    assert!(decode(&envelope(BALANCED_ROOT_TAG, carrier(empty.clone(), 0), 1)).is_err());
    assert!(
        decode(&envelope(
            BALANCED_ROOT_TAG,
            carrier(empty, MAX_DECLARATIONS + 1),
            0
        ))
        .is_err()
    );
    let wrong_identity = tagged(
        PARAMETER_TAG,
        [Expr::let_named(
            Name::anon(),
            Expr::const_str("Nat"),
            Expr::fvar(FVarId::new(2)),
            Expr::lam(
                BinderInfo::Default,
                Expr::fvar(FVarId::new(1)),
                Expr::fvar(FVarId::new(1)),
            ),
            false,
        )],
    );
    assert!(
        decode(&envelope(
            BALANCED_ROOT_TAG,
            carrier(tagged(LEAF_TAG, [wrong_identity]), 1),
            0,
        ))
        .is_err()
    );
}

#[test]
fn balancing_records_does_not_raise_the_original_expression_depth_allowance() {
    let mut deep = Expr::nat_lit(0);
    for _ in 0..trust_ir::proof::CLEAN_EXPR_DAG_V2_MAX_DEPTH {
        deep = Expr::app(Expr::const_str("f"), deep);
    }
    let mut original = bundle(1);
    original.declarations[0].value = Some(deep.clone());
    assert!(
        original
            .encode_with_claim(&original.goal)
            .unwrap_err()
            .contains("graph depth limit")
    );
    drop(original);
    drop_spine(deep, true);
}
