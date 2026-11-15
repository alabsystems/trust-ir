// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Compact memo indices are storage, not a new dependency or scope authority.

use super::*;
use clean_kernel::{BinderInfo, Environment, Level, TypeChecker};
use std::mem::size_of;

#[test]
fn compact_memo_indices_preserve_none_zero_and_every_addressable_boundary() {
    for raw in [None, Some(0), Some(1), Some(255), Some(usize::MAX - 1)] {
        let entry = MemoEntry {
            replacement: None,
            declarations: MemoEntry::compact(raw),
            dependencies: MemoEntry::compact(raw),
        };
        assert_eq!(entry.declarations(), raw);
        assert_eq!(entry.dependencies(), raw);
        assert_eq!(entry.clone().declarations(), raw);
        assert_eq!(entry.clone().dependencies(), raw);
        assert_eq!(
            entry.declarations.map(NonZeroUsize::get),
            raw.map(|i| i + 1)
        );
    }
    // Arena Vecs contain non-zero-sized nodes and cannot own usize::MAX.
    // Unrepresentable input must never wrap to the None sentinel.
    assert!(std::panic::catch_unwind(|| MemoEntry::compact(Some(usize::MAX))).is_err());
}

#[test]
fn compact_memo_layout_removes_two_words_from_each_retained_entry_kind() {
    #[allow(dead_code)]
    struct LegacyMemo {
        replacement: Option<Arc<Expr>>,
        declarations: Option<usize>,
        dependencies: Option<usize>,
    }
    #[allow(dead_code)]
    struct LegacyContext {
        entry: LegacyMemo,
        context: usize,
        binder_depth: u32,
        ordinary_count: usize,
    }
    #[allow(dead_code)]
    struct LegacyClosed {
        entry: LegacyMemo,
        context: usize,
    }
    let saved = 2 * size_of::<usize>();
    assert_eq!(size_of::<Option<NonZeroUsize>>(), size_of::<usize>());
    assert_eq!(size_of::<MemoEntry>() + saved, size_of::<LegacyMemo>());
    assert_eq!(
        size_of::<ContextEntry>() + saved,
        size_of::<LegacyContext>()
    );
    assert_eq!(size_of::<ClosedEntry>() + saved, size_of::<LegacyClosed>());
    eprintln!(
        "memo layout bytes: exact {} -> {}, contextual {} -> {}, named-closed {} -> {}; not RSS",
        size_of::<LegacyMemo>(),
        size_of::<MemoEntry>(),
        size_of::<LegacyContext>(),
        size_of::<ContextEntry>(),
        size_of::<LegacyClosed>(),
        size_of::<ClosedEntry>(),
    );
}

#[test]
fn compact_memo_decodes_actual_arena_zero_and_preserves_strict_proof_replay() {
    let id = FVarId::new(1);
    let nat = Expr::const_str("Nat");
    let eq = |left: Expr, right: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nat.clone(), left, right],
        )
    };
    let value = Expr::fvar(id);
    let shared = Arc::new(Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat.clone(), value.clone()],
    ));
    let body = Expr::app_arc(
        Arc::new(Expr::lam(
            BinderInfo::Default,
            eq(value.clone(), value.clone()),
            Expr::bvar(0),
        )),
        shared,
    );
    let mut scope = TermScope::new();
    let input = scope.lam(id, BinderInfo::Default, nat.clone(), body);
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let closed = input.fold_opt_or_clone(&mut closer);
    assert!(closer.error.is_none());
    assert!(
        closer
            .memo
            .values()
            .any(|entry| entry.dependencies() == Some(0))
    );
    assert!(
        closer
            .named_closed
            .values()
            .any(|entry| entry.entry.declarations() == Some(0))
    );
    for entry in closer
        .memo
        .values()
        .chain(closer.named_closed.values().map(|e| &e.entry))
    {
        assert!(
            entry
                .dependencies()
                .is_none_or(|i| i < closer.dependencies.len())
        );
        assert!(
            entry
                .declarations()
                .is_none_or(|i| i < closer.footprints.len())
        );
        let copy = entry.clone();
        assert_eq!(copy.dependencies(), entry.dependencies());
        assert_eq!(copy.declarations(), entry.declarations());
        if let (Some(left), Some(right)) = (&entry.replacement, &copy.replacement) {
            assert!(Arc::ptr_eq(left, right));
        }
    }
    let expected = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        eq(Expr::bvar(0), Expr::bvar(0)),
    );
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_nat().unwrap();
    let mut checker = TypeChecker::new(&env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    let inferred = checker.infer_type(&closed).unwrap();
    assert!(checker.is_def_eq(&inferred, &expected));
    assert!(env.audit_certification(&expected, &closed).is_certified());
    let forged = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        eq(
            Expr::bvar(0),
            Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0)),
        ),
    );
    assert!(!checker.is_def_eq(&inferred, &forged));
    assert!(!env.audit_certification(&forged, &closed).is_certified());
    let bytes = trust_ir::proof::encode_clean_expr_dag_v2(&closed).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
    assert!(env.audit_certification(&expected, &decoded).is_certified());
    assert_eq!(scope.close(&input).unwrap(), closed);
}
