// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Ordinary shared candidates, not actual Return or native/source evidence.
use super::*;
use clean_kernel::KernelTypeError;
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};

fn environment() -> &'static Environment {
    shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env()
}
fn limits() -> Limits {
    Limits {
        max_operations: 1_000,
        max_locals: 100,
        max_list_items: 100,
        max_lookup_candidates: 32,
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}
fn independent_owner_goal() -> Expr {
    let memory = Expr::bvar(3);
    let owner = Expr::bvar(1);
    let original_rows = app("ir_byte_mem_allocs_v1", [memory]);
    close(
        [
            constant("IRByteMemoryV1"),
            app("IRList", [constant("Nat")]),
            constant("Nat"),
            eq(
                &constant("Bool"),
                app(
                    "ir_byte_memory_owners_v1",
                    [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)],
                ),
                constant("Bool.true"),
            ),
        ],
        eq(
            &app("IRList", [constant("IRByteAllocationV1")]),
            app("ir_byte_retire_allocs_v1", [owner, original_rows.clone()]),
            original_rows,
        ),
        true,
    )
}
fn strict(term: Expr, goal: Expr, accepted: bool) {
    assert!(!term.has_fvar_quick() && !term.has_loose_bvars());
    assert!(!goal.has_fvar_quick() && !goal.has_loose_bvars());
    let decoded_term = trust_ir::proof::decode_clean_expr_dag_v2(
        &trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap(),
    )
    .unwrap();
    let decoded_goal = trust_ir::proof::decode_clean_expr_dag_v2(
        &trust_ir::proof::encode_clean_expr_dag_v2(&goal).unwrap(),
    )
    .unwrap();
    assert_eq!(decoded_term, term);
    assert_eq!(decoded_goal, goal);
    for (term, goal) in [(term, goal), (decoded_term, decoded_goal)] {
        let mut checker = TypeChecker::new(environment());
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        assert_eq!(checker.heartbeat_limit(), 2_000_000);
        checker
            .check_type(&goal, &Expr::sort(Level::zero()))
            .unwrap();
        let checked = checker.check_type(&term, &goal);
        assert!(
            !checker.heartbeat_spent(),
            "resource stop is not a verdict: {checked:?}"
        );
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        if accepted {
            checked.unwrap();
            let audit = environment().audit_certification(&goal, &term);
            assert!(audit.is_certified());
            for name in audit.dependencies {
                assert!(environment().axiom_deps(&name).unwrap().is_empty());
                assert!(
                    environment()
                        .foundational_axiom_deps(&name)
                        .unwrap()
                        .is_empty()
                );
                assert!(environment().trust_marker_deps(&name).unwrap().is_empty());
            }
        } else {
            assert!(matches!(
                checked.unwrap_err(),
                KernelTypeError::TypeMismatch { .. }
            ));
        }
    }
}

// Independent original inputs and goal, not copied from candidate metadata.
fn universal(forged_owners: bool, forged_bound: bool) -> (Expr, Expr) {
    let types = [
        constant("IRByteMemoryV1"),
        app("IRList", [constant("Nat")]),
        constant("Nat"),
        constant("Nat"),
        yes(app(
            "ir_byte_memory_owners_v1",
            [Expr::bvar(3), Expr::bvar(2), Expr::bvar(1)],
        )),
        app("Nat.le", [Expr::bvar(2), Expr::bvar(1)]),
    ];
    let memory = Expr::bvar(5);
    let owners = Expr::bvar(4);
    let next = Expr::bvar(3);
    let retiring = Expr::bvar(2);
    let rows = app("ir_byte_mem_allocs_v1", [memory.clone()]);
    let goal = eq(
        &app("IRList", [constant("IRByteAllocationV1")]),
        app("ir_byte_retire_allocs_v1", [retiring.clone(), rows.clone()]),
        rows,
    );
    let guard = app(
        "ir_byte_memory_owners_v1",
        [memory.clone(), owners.clone(), next.clone()],
    );
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let equation = assembler
        .byte_retire_beyond_bound(
            memory,
            owners,
            next.clone(),
            retiring.clone(),
            PendingEquality::candidate(
                constant("Bool"),
                guard,
                constant("Bool.true"),
                if forged_owners {
                    constant("True.intro")
                } else {
                    Expr::bvar(1)
                },
            ),
            PendingProof::candidate(
                app("Nat.le", [next, retiring]),
                if forged_bound {
                    constant("True.intro")
                } else {
                    Expr::bvar(0)
                },
            ),
        )
        .unwrap();
    assert_eq!(equation.proposition(), goal);
    assert_eq!(
        (
            assembler.operations(),
            assembler.locals,
            assembler.local_scope().allocated()
        ),
        (33, 0, 0)
    );
    (
        close(types.clone(), equation.term, false),
        close(types, goal, true),
    )
}

#[test]
fn retirement_bound_is_universal_over_original_memory_owners_and_order() {
    let (term, goal) = universal(false, false);
    strict(term, goal, true);
    // Different caller order and an unused outer input: actual operands and
    // proof domains cannot depend on the recipe's private six-slot ordering.
    let types = [
        constant("Nat"),
        constant("IRByteMemoryV1"),
        constant("Nat"),
        app("IRList", [constant("Nat")]),
        constant("Nat"),
        yes(app(
            "ir_byte_memory_owners_v1",
            [Expr::bvar(3), Expr::bvar(1), Expr::bvar(4)],
        )),
        app("Nat.le", [Expr::bvar(5), Expr::bvar(1)]),
    ];
    let mut scope = Scope::new();
    let equation = Assembler::new(&mut scope, limits())
        .unwrap()
        .byte_retire_beyond_bound(
            Expr::bvar(5),
            Expr::bvar(3),
            Expr::bvar(6),
            Expr::bvar(2),
            PendingEquality::candidate(
                constant("Bool"),
                app(
                    "ir_byte_memory_owners_v1",
                    [Expr::bvar(5), Expr::bvar(3), Expr::bvar(6)],
                ),
                constant("Bool.true"),
                Expr::bvar(1),
            ),
            PendingProof::candidate(app("Nat.le", [Expr::bvar(6), Expr::bvar(2)]), Expr::bvar(0)),
        )
        .unwrap();
    let original_rows = app("ir_byte_mem_allocs_v1", [Expr::bvar(5)]);
    let original_goal = eq(
        &app("IRList", [constant("IRByteAllocationV1")]),
        app(
            "ir_byte_retire_allocs_v1",
            [Expr::bvar(2), original_rows.clone()],
        ),
        original_rows,
    );
    assert_eq!(equation.proposition(), original_goal);
    strict(
        close(types.clone(), equation.term, false),
        close(types, original_goal, true),
        true,
    );
}

#[test]
fn retirement_bound_retains_forged_premises_and_unused_invalid_lets() {
    let (_, goal) = universal(false, false);
    for (owners, bound) in [(true, false), (false, true)] {
        let (term, mutant_goal) = universal(owners, bound);
        assert_eq!(mutant_goal, goal);
        strict(term, goal.clone(), false);
    }
    let mut scope = Scope::new();
    let rule = Assembler::new(&mut scope, limits())
        .unwrap()
        .byte_retirement_owner_rule()
        .unwrap();
    // The independent statement is unchanged; the invalid proof LET is in the
    // proof only. Its value must be checked even though the body does not use it.
    let original_goal = independent_owner_goal();
    assert_eq!(rule.proposition(), &original_goal);
    strict(
        Expr::let_named(
            Name::anon(),
            eq(&constant("Nat"), nat(0), nat(1)),
            refl(&constant("Nat"), nat(0)),
            rule.term().lift(1),
            false,
        ),
        original_goal,
        false,
    );
}

#[test]
fn retirement_bound_inhabited_history_keeps_dead_rows_and_exact_endpoints() {
    let rows = list(
        "IRByteAllocationV1",
        &[
            app(
                "IRByteAllocationV1.mk",
                [nat(16), nat(1), nat(0), constant("Bool.true")],
            ),
            app(
                "IRByteAllocationV1.mk",
                [nat(32), nat(1), nat(1), constant("Bool.false")],
            ),
        ],
    );
    let bytes = lam(constant("Nat"), app("IROption.none", [constant("Nat")]));
    let memory = app("IRByteMemoryV1.mk", [rows.clone(), bytes, nat(64)]);
    let owners = list("Nat", &[]);
    let guard = app(
        "ir_byte_memory_owners_v1",
        [memory.clone(), owners.clone(), nat(2)],
    );
    let claim = eq(
        &app("IRList", [constant("IRByteAllocationV1")]),
        app(
            "ir_byte_retire_allocs_v1",
            [nat(2), app("ir_byte_mem_allocs_v1", [memory.clone()])],
        ),
        app("ir_byte_mem_allocs_v1", [memory.clone()]),
    );
    let mut scope = Scope::new();
    let term = Assembler::new(&mut scope, limits())
        .unwrap()
        .byte_retire_beyond_bound(
            memory.clone(),
            owners,
            nat(2),
            nat(2),
            PendingEquality::candidate(
                constant("Bool"),
                guard,
                constant("Bool.true"),
                refl(&constant("Bool"), constant("Bool.true")),
            ),
            PendingProof::candidate(
                app("Nat.le", [nat(2), nat(2)]),
                app("Nat.le_refl", [nat(2)]),
            ),
        )
        .unwrap()
        .term;
    strict(term.clone(), claim, true);
    for wrong_rows in [
        list("IRByteAllocationV1", &[]),
        list(
            "IRByteAllocationV1",
            &[
                app(
                    "IRByteAllocationV1.mk",
                    [nat(16), nat(1), nat(0), constant("Bool.false")],
                ),
                app(
                    "IRByteAllocationV1.mk",
                    [nat(32), nat(1), nat(1), constant("Bool.false")],
                ),
            ],
        ),
    ] {
        strict(
            term.clone(),
            eq(
                &allocations_type(),
                retired(nat(2), allocations(memory.clone())),
                wrong_rows,
            ),
            false,
        );
    }
}

#[test]
fn retirement_rule_neutral_telescope_needs_no_caller_local_slots() {
    let mut scope = Scope::with_limits(crate::scoped_local::LocalScopeLimits {
        max_locals: 1,
        ..Default::default()
    });
    let mut policy = limits();
    policy.max_locals = 1;
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    let held = assembler.local(constant("Nat")).unwrap();
    let before = assembler.local_scope().allocated();
    for paid in [38, 75] {
        let rule = assembler.byte_retirement_owner_rule().unwrap();
        assert_eq!(
            (
                assembler.operations(),
                assembler.locals,
                assembler.local_scope().allocated()
            ),
            (paid, 1, before)
        );
        let goal = independent_owner_goal();
        assert_eq!(rule.proposition(), &goal);
        strict(
            assembler
                .local_scope()
                .close(&held.let_(nat(7), rule.term().clone()))
                .unwrap(),
            goal,
            true,
        );
    }
    assert_eq!(
        assembler.local(constant("Nat")).err().unwrap(),
        "execution construction local budget exceeded"
    );
    assert_eq!(
        (
            assembler.operations(),
            assembler.locals,
            assembler.local_scope().allocated()
        ),
        (76, 1, before)
    );
}

#[test]
fn retirement_bound_metadata_and_paid_prefix_refusals_are_exact() {
    let memory = app("ir_byte_memory_empty_v1", [nat(64)]);
    let owners = list("Nat", &[]);
    for wrong in 0..4 {
        let guard = owner_guard(memory.clone(), owners.clone(), nat(1));
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let result = assembler.byte_retire_beyond_bound(
            memory.clone(),
            owners.clone(),
            nat(1),
            nat(1),
            PendingEquality::candidate(
                if wrong == 0 {
                    constant("Nat")
                } else {
                    constant("Bool")
                },
                if wrong == 1 {
                    constant("Bool.true")
                } else {
                    guard
                },
                if wrong == 2 {
                    constant("Bool.false")
                } else {
                    constant("Bool.true")
                },
                refl(&constant("Bool"), constant("Bool.true")),
            ),
            PendingProof::candidate(
                if wrong == 3 {
                    le(nat(2), nat(1))
                } else {
                    le(nat(1), nat(1))
                },
                app("Nat.le_refl", [nat(1)]),
            ),
        );
        assert_eq!(
            result.err().unwrap(),
            format!(
                "{}: different candidate terms; supply an explicit equality transport",
                [
                    "equality type",
                    "equality left endpoint",
                    "equality right endpoint",
                    "retirement bound premise"
                ][wrong]
            )
        );
        assert_eq!(
            (
                assembler.operations(),
                assembler.locals,
                assembler.local_scope().allocated()
            ),
            (33, 0, 0)
        );
    }
    for cap in 1..37 {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(
            &mut scope,
            Limits {
                max_operations: cap,
                ..limits()
            },
        )
        .unwrap();
        assert_eq!(
            assembler.byte_retirement_owner_rule().err().unwrap(),
            "execution construction operation budget exceeded"
        );
        assert_eq!(
            (
                assembler.operations(),
                assembler.locals,
                assembler.local_scope().allocated()
            ),
            (cap, 0, 0)
        );
    }
    for cap in 1..33 {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(
            &mut scope,
            Limits {
                max_operations: cap,
                ..limits()
            },
        )
        .unwrap();
        assert_eq!(
            assembler
                .byte_retire_beyond_bound(
                    memory.clone(),
                    owners.clone(),
                    nat(1),
                    nat(1),
                    PendingEquality::candidate(
                        constant("Bool"),
                        owner_guard(memory.clone(), owners.clone(), nat(1)),
                        constant("Bool.true"),
                        refl(&constant("Bool"), constant("Bool.true"))
                    ),
                    PendingProof::candidate(le(nat(1), nat(1)), app("Nat.le_refl", [nat(1)]))
                )
                .err()
                .unwrap(),
            "execution construction operation budget exceeded"
        );
        assert_eq!(
            (
                assembler.operations(),
                assembler.locals,
                assembler.local_scope().allocated()
            ),
            (cap, 0, 0)
        );
    }
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    assembler.operations = usize::MAX;
    assert_eq!(
        assembler.byte_retirement_owner_rule().err().unwrap(),
        "operation counter overflow"
    );
    assert_eq!(
        (
            assembler.operations(),
            assembler.locals,
            assembler.local_scope().allocated()
        ),
        (usize::MAX, 0, 0)
    );
    assert_eq!(
        Assembler::new(
            &mut Scope::new(),
            Limits {
                max_operations: 0,
                ..limits()
            }
        )
        .err()
        .unwrap(),
        "execution construction limits must be nonzero"
    );
}
