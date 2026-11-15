// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Independent default-budget kernel checks of typed candidate ascription.
//! These are ordinary closed proof consumers, not source or native execution.

use super::*;
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};

fn limits(operations: usize, locals: usize) -> Limits {
    Limits {
        max_operations: operations,
        max_locals: locals,
        max_list_items: 1,
        max_lookup_candidates: 1,
        lookup_heartbeats: 1,
        lookup_cache_entries: 1,
    }
}

fn environment() -> &'static Environment {
    shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env()
}

fn checker() -> TypeChecker<'static> {
    let mut checker = TypeChecker::new(environment());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    assert_eq!(checker.heartbeat_limit(), 2_000_000);
    checker
}

fn close(scope: &Scope, parameters: &[Local], expression: Expr, proof: bool) -> Expr {
    let term = scope
        .close(&parameters.iter().rev().fold(expression, |body, local| {
            if proof {
                local.lam(body)
            } else {
                local.pi(body)
            }
        }))
        .unwrap();
    assert!(!term.has_fvar_quick() && !term.has_loose_bvars());
    term
}

fn replay(term: &Expr, claim: &Expr, accepted: bool) {
    assert!(!term.has_fvar_quick() && !term.has_loose_bvars());
    assert!(!claim.has_fvar_quick() && !claim.has_loose_bvars());
    checker().check_type(claim, &Expr::prop()).unwrap();
    let term_bytes = trust_ir::proof::encode_clean_expr_dag_v2(term).unwrap();
    let claim_bytes = trust_ir::proof::encode_clean_expr_dag_v2(claim).unwrap();
    let decoded_term = trust_ir::proof::decode_clean_expr_dag_v2(&term_bytes).unwrap();
    let decoded_claim = trust_ir::proof::decode_clean_expr_dag_v2(&claim_bytes).unwrap();
    assert_eq!(&decoded_term, term);
    assert_eq!(&decoded_claim, claim);
    for actual in [term, &decoded_term] {
        let kernel = checker();
        if accepted {
            kernel.check_type(actual, claim).unwrap();
            let audit = environment().audit_certification(claim, actual);
            assert!(audit.is_certified(), "{audit:#?}");
            for dependency in &audit.dependencies {
                assert!(environment().axiom_deps(dependency).unwrap().is_empty());
                assert!(
                    environment()
                        .foundational_axiom_deps(dependency)
                        .unwrap()
                        .is_empty()
                );
                assert!(
                    environment()
                        .trust_marker_deps(dependency)
                        .unwrap()
                        .is_empty()
                );
            }
        } else {
            let error = kernel.check_type(actual, claim).unwrap_err();
            assert!(
                matches!(error, KernelTypeError::TypeMismatch { .. }),
                "{error:?}"
            );
            assert!(
                !kernel.heartbeat_spent(),
                "a budget stop is not a refutation"
            );
        }
    }
}

fn alias(value: Expr) -> Expr {
    Expr::app(
        Expr::lam(BinderInfo::Default, constant("Nat"), Expr::bvar(0)),
        value,
    )
}

fn lower_bound(word: Expr) -> Expr {
    app("ir_nat_ltb", [word, app("ir_nat_pow2", [nat(64)])])
}

fn admission(context: Expr, width: u64, word: Expr) -> Expr {
    app(
        "ir_byte_value_matches_v1",
        [
            context,
            app("IRTy.int_", [nat(width)]),
            app("IRScalar.int_", [word]),
        ],
    )
}

#[test]
fn ascription_is_a_genuine_typed_let_and_legacy_conversion_stays_unwrapped() {
    for original in [
        PendingEquality::reflexive(constant("Nat"), nat(4)),
        // Existing contextual de Bruijn references remain in the type/value,
        // outside the new proof let body. Only that body's BVar0 is new.
        PendingEquality::candidate(constant("Nat"), Expr::bvar(0), Expr::bvar(0), Expr::bvar(2)),
    ] {
        let left = alias(original.left().clone());
        let right = original.right().clone();
        let declared = eq(&constant("Nat"), left.clone(), right.clone());
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits(2, 1)).unwrap();
        let legacy = assembler
            .convert_endpoints(original.clone(), left.clone(), right.clone())
            .unwrap();
        assert_eq!(legacy.term(), original.term());
        let candidate = assembler
            .ascribe_endpoints(original.clone(), left, right)
            .unwrap();
        assert_eq!(candidate.ty, original.ty);
        assert_eq!(candidate.proposition(), declared);
        assert_eq!(
            *candidate.term(),
            Expr::let_named(
                Name::anon(),
                declared,
                original.term().clone(),
                Expr::bvar(0),
                false
            )
        );
        assert_eq!(assembler.operations(), 2);
        assert_eq!(assembler.locals, 0);
        assert_eq!(assembler.local_scope().allocated(), 0);
    }
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(1, 1)).unwrap();
    let candidate = assembler
        .ascribe_endpoints(
            PendingEquality::reflexive(constant("Nat"), nat(4)),
            alias(nat(4)),
            nat(4),
        )
        .unwrap();
    replay(
        candidate.term(),
        &eq(&constant("Nat"), alias(nat(4)), nat(4)),
        true,
    );
}

#[test]
fn neutral_admission_alias_is_retained_before_and_after_concrete_application() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(4, 3)).unwrap();
    let context = assembler.local(constant("IRByteContextV1")).unwrap();
    let word = assembler.local(constant("Nat")).unwrap();
    let fits_type = eq(
        &constant("Bool"),
        lower_bound(word.term().clone()),
        constant("Bool.true"),
    );
    let fits = assembler.local(fits_type.clone()).unwrap();
    let before = assembler.operations();
    let output = admission(context.term().clone(), 64, word.term().clone());
    let claim = eq(&constant("Bool"), output.clone(), constant("Bool.true"));
    let candidate = assembler
        .ascribe_endpoints(
            PendingEquality::candidate(
                constant("Bool"),
                lower_bound(word.term().clone()),
                constant("Bool.true"),
                fits.term().clone(),
            ),
            output,
            constant("Bool.true"),
        )
        .unwrap();
    assert_eq!(candidate.proposition(), claim);
    assert_eq!(assembler.operations(), before + 1);
    assert_eq!(assembler.locals, 3);
    assert_eq!(assembler.local_scope().allocated(), 3);
    let parameters = [context, word, fits];
    let closed_claim = close(assembler.local_scope(), &parameters, claim, false);
    let closed_term = close(
        assembler.local_scope(),
        &parameters,
        candidate.term().clone(),
        true,
    );
    // Full checking, not infer-only processing, must retain the exact declared
    // admission alias rather than exposing just the old arithmetic predicate.
    assert_eq!(
        checker().infer_type_full(&closed_term).unwrap(),
        closed_claim
    );
    replay(&closed_term, &closed_claim, true);

    let literal = nat(1_u64 << 63);
    let application = Expr::lam(
        BinderInfo::Default,
        constant("IRByteContextV1"),
        Expr::apps(
            closed_term,
            [
                Expr::bvar(0),
                literal.clone(),
                refl(&constant("Bool"), constant("Bool.true")),
            ],
        ),
    );
    let independent = Expr::pi(
        BinderInfo::Default,
        constant("IRByteContextV1"),
        eq(
            &constant("Bool"),
            admission(Expr::bvar(0), 64, literal),
            constant("Bool.true"),
        ),
    );
    replay(&application, &independent, true);
}

#[test]
fn false_alias_width_operand_and_endpoint_goals_fail_original_and_dag_replay() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(6, 3)).unwrap();
    let context = assembler.local(constant("IRByteContextV1")).unwrap();
    let word = assembler.local(constant("Nat")).unwrap();
    let fits = assembler
        .local(eq(
            &constant("Bool"),
            lower_bound(word.term().clone()),
            constant("Bool.true"),
        ))
        .unwrap();
    let original = PendingEquality::candidate(
        constant("Bool"),
        lower_bound(word.term().clone()),
        constant("Bool.true"),
        fits.term().clone(),
    );
    for (left, right) in [
        (
            admission(context.term().clone(), 32, word.term().clone()),
            constant("Bool.true"),
        ),
        (
            admission(
                context.term().clone(),
                64,
                app("Nat.succ", [word.term().clone()]),
            ),
            constant("Bool.true"),
        ),
        (
            admission(context.term().clone(), 64, word.term().clone()),
            constant("Bool.false"),
        ),
    ] {
        let claim = eq(&constant("Bool"), left.clone(), right.clone());
        let candidate = assembler
            .ascribe_endpoints(original.clone(), left, right)
            .unwrap();
        assert_eq!(candidate.proposition(), claim);
        let parameters = [context.clone(), word.clone(), fits.clone()];
        replay(
            &close(
                assembler.local_scope(),
                &parameters,
                candidate.term().clone(),
                true,
            ),
            &close(assembler.local_scope(), &parameters, claim, false),
            false,
        );
    }
    assert_eq!(assembler.operations(), 6);
    assert_eq!(assembler.locals, 3);
}

#[test]
fn declared_types_and_nested_proof_arguments_cannot_gain_admission() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(5, 1)).unwrap();
    let real_claim = eq(&constant("Nat"), nat(4), nat(4));
    for bad_term in [
        refl(&constant("Nat"), nat(5)),
        refl(&constant("Bool"), constant("Bool.true")),
        nat(4),
        // Its apparent result type is 4=4, but the argument is Nat, not Bool.
        // Strict checking of the let value must reject this nested application.
        Expr::app(
            Expr::lam(
                BinderInfo::Default,
                constant("Bool"),
                refl(&constant("Nat"), nat(4)),
            ),
            nat(4),
        ),
    ] {
        let candidate = assembler
            .ascribe_endpoints(
                PendingEquality::candidate(constant("Nat"), nat(4), nat(4), bad_term),
                nat(4),
                nat(4),
            )
            .unwrap();
        replay(candidate.term(), &real_claim, false);
    }
    let malformed = assembler
        .ascribe_endpoints(
            PendingEquality::reflexive(constant("Nat"), nat(4)),
            constant("Bool.true"),
            constant("Bool.true"),
        )
        .unwrap();
    assert_eq!(malformed.ty, constant("Nat"));
    let claim = eq(
        &constant("Nat"),
        constant("Bool.true"),
        constant("Bool.true"),
    );
    assert_eq!(malformed.proposition(), claim);
    for expression in [claim, malformed.term().clone()] {
        let kernel = checker();
        let error = kernel.infer_type_full(&expression).unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "{error:?}"
        );
        assert!(!kernel.heartbeat_spent());
    }
    assert_eq!(assembler.operations(), 5);
    assert_eq!(assembler.locals, 0);
}

#[test]
fn only_the_requested_goal_is_checked_not_old_pending_metadata() {
    let original = PendingEquality::candidate(
        constant("Nat"),
        nat(4),
        nat(5),
        refl(&constant("Nat"), nat(4)),
    );
    replay(
        original.term(),
        &eq(&constant("Nat"), nat(4), nat(5)),
        false,
    );
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(1, 1)).unwrap();
    let candidate = assembler
        .ascribe_endpoints(original, alias(nat(4)), nat(4))
        .unwrap();
    // The actual term proves the requested equality. This never grants
    // certification to the original false metadata 4=5.
    replay(
        candidate.term(),
        &eq(&constant("Nat"), alias(nat(4)), nat(4)),
        true,
    );
    assert_eq!(assembler.operations(), 1);
    assert_eq!(assembler.locals, 0);
}

#[test]
fn ascription_preserves_local_cap_and_spent_or_overflowed_operation_budgets() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(2, 1)).unwrap();
    let local = assembler.local(constant("Nat")).unwrap();
    let original = PendingEquality::reflexive(constant("Nat"), local.term().clone());
    let candidate = assembler
        .ascribe_endpoints(
            original.clone(),
            alias(local.term().clone()),
            local.term().clone(),
        )
        .unwrap();
    assert_eq!(assembler.operations(), 2);
    assert_eq!(assembler.locals, 1);
    assert_eq!(assembler.local_scope().allocated(), 1);
    assert!(assembler.local_scope().owns(&local));
    let claim = eq(
        &constant("Nat"),
        alias(local.term().clone()),
        local.term().clone(),
    );
    replay(
        &close(
            assembler.local_scope(),
            std::slice::from_ref(&local),
            candidate.term().clone(),
            true,
        ),
        &close(
            assembler.local_scope(),
            std::slice::from_ref(&local),
            claim,
            false,
        ),
        true,
    );
    let error = assembler
        .ascribe_endpoints(original, nat(4), nat(4))
        .err()
        .unwrap();
    assert!(error.contains("operation budget"), "{error}");
    assert_eq!(assembler.operations(), 2);
    assert_eq!(assembler.locals, 1);
    assert!(assembler.local_scope().owns(&local));

    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(usize::MAX, 1)).unwrap();
    assembler.operations = usize::MAX;
    let error = assembler
        .ascribe_endpoints(
            PendingEquality::reflexive(constant("Nat"), nat(4)),
            nat(4),
            nat(4),
        )
        .err()
        .unwrap();
    assert!(error.contains("operation counter overflow"), "{error}");
    assert_eq!(assembler.operations(), usize::MAX);
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), 0);
    assert!(Assembler::new(&mut Scope::new(), limits(0, 1)).is_err());
}

fn resolve_claim(machine: Expr, ids: &[u32], values: &[Expr]) -> Expr {
    eq(
        &app("IRList", [constant("IRScalar")]),
        app(
            "ir_resolve",
            [
                machine,
                list(
                    "Nat",
                    &ids.iter().map(|id| nat(u64::from(*id))).collect::<Vec<_>>(),
                ),
            ],
        ),
        list("IRScalar", values),
    )
}

#[test]
fn resolve_typed_presentation_replays_neutral_machine_order_and_duplicate_ids() {
    let mut scope = Scope::new();
    let machine = scope.try_local(constant("IRMachine")).unwrap();
    let mut policy = limits(100, 100);
    policy.max_list_items = 3;
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    let empty = assembler.resolve(machine.term(), &[]).unwrap();
    assert_eq!(assembler.operations(), 3);
    assert_eq!(assembler.locals, 0);
    let empty_claim = resolve_claim(machine.term().clone(), &[], &[]);
    assert_eq!(empty.proposition(), empty_claim);
    replay(
        &close(
            assembler.local_scope(),
            std::slice::from_ref(&machine),
            empty.term().clone(),
            true,
        ),
        &close(
            assembler.local_scope(),
            std::slice::from_ref(&machine),
            empty_claim,
            false,
        ),
        true,
    );

    let ids = [9, 2, 9];
    let values = ids.map(|id| app("ir_getd", [machine.term().clone(), nat(u64::from(id))]));
    let facts = ids
        .iter()
        .zip(&values)
        .map(|(id, value)| {
            LookupFact::candidate(
                machine.term().clone(),
                trust_ir::ValueId::new(*id),
                value.clone(),
                PendingEquality::reflexive(constant("IRScalar"), value.clone()),
            )
            .unwrap()
        })
        .collect::<Vec<_>>();
    let original = assembler.resolve(machine.term(), &facts).unwrap();
    assert_eq!(
        assembler.operations(),
        27,
        "three empty plus 24 cold nonempty charges"
    );
    let allocated = assembler.local_scope().allocated();
    let operations = assembler.operations();
    let warm = assembler.resolve(machine.term(), &facts).unwrap();
    assert_eq!(assembler.operations() - operations, 6);
    assert_eq!(assembler.local_scope().allocated(), allocated);
    assert_eq!(warm.term(), original.term());
    let claim = resolve_claim(machine.term().clone(), &ids, &values);
    assert_eq!(original.proposition(), claim);
    replay(
        &close(
            assembler.local_scope(),
            std::slice::from_ref(&machine),
            original.term().clone(),
            true,
        ),
        &close(assembler.local_scope(), &[machine], claim, false),
        true,
    );
}

#[test]
fn resolve_typed_presentation_keeps_forged_lookup_term_a_strict_semantic_refusal() {
    let mut scope = Scope::new();
    let machine = scope.try_local(constant("IRMachine")).unwrap();
    let value = constant("IRScalar.unit_");
    let fact = LookupFact::candidate(
        machine.term().clone(),
        trust_ir::ValueId::new(7),
        value.clone(),
        PendingEquality::candidate(
            constant("IRScalar"),
            app("ir_getd", [machine.term().clone(), nat(7)]),
            value.clone(),
            refl(&constant("IRScalar"), value.clone()),
        ),
    )
    .unwrap();
    let mut assembler = Assembler::new(&mut scope, limits(100, 100)).unwrap();
    let pending = assembler.resolve(machine.term(), &[fact]).unwrap();
    let claim = resolve_claim(machine.term().clone(), &[7], &[value]);
    assert_eq!(pending.proposition(), claim);
    replay(
        &close(
            assembler.local_scope(),
            std::slice::from_ref(&machine),
            pending.term().clone(),
            true,
        ),
        &close(assembler.local_scope(), &[machine], claim, false),
        false,
    );
}

#[test]
fn resolve_typed_presentation_retains_exact_machine_guard_and_unmodified_operation_cap() {
    let mut scope = Scope::new();
    let machine = scope.try_local(constant("IRMachine")).unwrap();
    let other = scope.try_local(constant("IRMachine")).unwrap();
    let value = app("ir_getd", [other.term().clone(), nat(7)]);
    let fact = LookupFact::candidate(
        other.term().clone(),
        trust_ir::ValueId::new(7),
        value.clone(),
        PendingEquality::reflexive(constant("IRScalar"), value),
    )
    .unwrap();
    let mut assembler = Assembler::new(&mut scope, limits(1, 1)).unwrap();
    let error = assembler.resolve(machine.term(), &[fact]).err().unwrap();
    assert!(error.contains("operand read machine"), "{error}");
    assert_eq!(assembler.operations(), 1);
    assert_eq!(assembler.locals, 0);
    assert!(assembler.cons_congruence.is_none());

    for cap in 1..=3 {
        let mut scope = Scope::new();
        let machine = scope.try_local(constant("IRMachine")).unwrap();
        let mut assembler = Assembler::new(&mut scope, limits(cap, 1)).unwrap();
        let result = assembler.resolve(machine.term(), &[]);
        assert_eq!(assembler.operations(), cap);
        assert_eq!(assembler.locals, 0);
        if cap < 3 {
            let error = result.err().unwrap();
            assert!(error.contains("operation budget"), "{error}");
            assert!(assembler.resolve(machine.term(), &[]).is_err());
            assert_eq!(assembler.operations(), cap, "no refund or reset");
        } else {
            let pending = result.unwrap();
            let claim = resolve_claim(machine.term().clone(), &[], &[]);
            replay(
                &close(
                    assembler.local_scope(),
                    std::slice::from_ref(&machine),
                    pending.term().clone(),
                    true,
                ),
                &close(assembler.local_scope(), &[machine], claim, false),
                true,
            );
        }
    }
}

#[test]
fn preserving_ascription_retains_both_exact_declarations_in_the_value() {
    let original = PendingEquality::reflexive(constant("Nat"), nat(4));
    let left = alias(nat(4));
    let requested = eq(&constant("Nat"), left.clone(), nat(4));
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(1, 1)).unwrap();
    let candidate = assembler
        .ascribe_preserving_endpoints(original.clone(), left, nat(4))
        .unwrap();
    assert_eq!(candidate.proposition(), requested);
    assert_eq!(
        candidate.term(),
        &Expr::let_named(
            Name::anon(),
            requested.clone(),
            Expr::let_named(
                Name::anon(),
                original.proposition(),
                original.term().clone(),
                Expr::bvar(0),
                false,
            ),
            Expr::bvar(0),
            false,
        )
    );
    assert_eq!(assembler.operations(), 1);
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), 0);
    assert_eq!(
        checker().infer_type_full(candidate.term()).unwrap(),
        requested
    );
    replay(candidate.term(), &requested, true);
}

#[test]
fn preserving_ascription_replays_contextual_bvars_without_body_capture() {
    // Caller context: x : Nat, y : Nat, h : x = y. Thus x is BVar2
    // and the actual proof is BVar0, outside BOTH newly introduced bodies.
    let original =
        PendingEquality::candidate(constant("Nat"), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0));
    let requested = eq(&constant("Nat"), alias(Expr::bvar(2)), Expr::bvar(1));
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(1, 1)).unwrap();
    let candidate = assembler
        .ascribe_preserving_endpoints(original.clone(), alias(Expr::bvar(2)), Expr::bvar(1))
        .unwrap();
    let wrap = |body: Expr, proof: bool| {
        [
            constant("Nat"),
            constant("Nat"),
            eq(&constant("Nat"), Expr::bvar(1), Expr::bvar(0)),
        ]
        .into_iter()
        .rev()
        .fold(body, |body, ty| {
            if proof {
                Expr::lam(BinderInfo::Default, ty, body)
            } else {
                Expr::pi(BinderInfo::Default, ty, body)
            }
        })
    };
    let claim = wrap(requested.clone(), false);
    replay(&wrap(candidate.term().clone(), true), &claim, true);
    // The tempting old-outer/new-body layout, without a lift, captures h
    // as a Nat endpoint. This is a genuine strict type error, not exhaustion.
    let captured = Expr::let_named(
        Name::anon(),
        original.proposition(),
        original.term().clone(),
        Expr::let_named(Name::anon(), requested, Expr::bvar(0), Expr::bvar(0), false),
        false,
    );
    replay(&wrap(captured, true), &claim, false);
    assert_eq!(assembler.operations(), 1);
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), 0);
}

#[test]
fn preserving_ascription_consumes_the_ordinary_neutral_nominal_admission() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(7, 3)).unwrap();
    let context = assembler.local(constant("IRByteContextV1")).unwrap();
    let word = assembler.local(constant("Nat")).unwrap();
    let fits = assembler
        .local(eq(
            &constant("Bool"),
            lower_bound(word.term().clone()),
            constant("Bool.true"),
        ))
        .unwrap();
    let original = PendingEquality::candidate(
        constant("Bool"),
        lower_bound(word.term().clone()),
        constant("Bool.true"),
        fits.term().clone(),
    );
    let parameters = [context.clone(), word.clone(), fits];
    for (left, right, accepted) in [
        (
            admission(context.term().clone(), 64, word.term().clone()),
            constant("Bool.true"),
            true,
        ),
        (
            admission(context.term().clone(), 32, word.term().clone()),
            constant("Bool.true"),
            false,
        ),
        (
            admission(
                context.term().clone(),
                64,
                app("Nat.succ", [word.term().clone()]),
            ),
            constant("Bool.true"),
            false,
        ),
        (
            admission(context.term().clone(), 64, word.term().clone()),
            constant("Bool.false"),
            false,
        ),
    ] {
        let claim = eq(&constant("Bool"), left.clone(), right.clone());
        let before = assembler.operations();
        let candidate = assembler
            .ascribe_preserving_endpoints(original.clone(), left, right)
            .unwrap();
        assert_eq!(candidate.proposition(), claim);
        assert_eq!(assembler.operations(), before + 1);
        replay(
            &close(
                assembler.local_scope(),
                &parameters,
                candidate.term().clone(),
                true,
            ),
            &close(assembler.local_scope(), &parameters, claim, false),
            accepted,
        );
    }
    assert_eq!(assembler.operations(), 7);
    assert_eq!(assembler.locals, 3);
    assert_eq!(assembler.local_scope().allocated(), 3);
}

#[test]
fn preserving_ascription_rejects_false_metadata_and_unused_illtyped_values() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(10, 1)).unwrap();
    let genuine = PendingEquality::reflexive(constant("Nat"), nat(4));
    let cases = [
        // The term really proves the new goal, but the original claim is false.
        (
            PendingEquality::candidate(
                constant("Nat"),
                nat(4),
                nat(5),
                refl(&constant("Nat"), nat(4)),
            ),
            alias(nat(4)),
            nat(4),
        ),
        // The old equality is genuine, but the requested equality is false.
        (genuine.clone(), alias(nat(4)), nat(5)),
        (
            PendingEquality::candidate(
                constant("Nat"),
                nat(4),
                nat(4),
                refl(&constant("Nat"), nat(5)),
            ),
            alias(nat(4)),
            nat(4),
        ),
        (
            PendingEquality::candidate(
                constant("Nat"),
                nat(4),
                nat(4),
                refl(&constant("Bool"), constant("Bool.true")),
            ),
            alias(nat(4)),
            nat(4),
        ),
        (
            PendingEquality::candidate(constant("Nat"), nat(4), nat(4), nat(4)),
            alias(nat(4)),
            nat(4),
        ),
        // Bad old declaration; the independent requested Bool goal is well typed.
        (
            PendingEquality::candidate(
                constant("Bool"),
                nat(4),
                nat(4),
                refl(&constant("Nat"), nat(4)),
            ),
            constant("Bool.true"),
            constant("Bool.true"),
        ),
        // This old value has a genuine result but an UNUSED ill-typed let.
        (
            PendingEquality::candidate(
                constant("Nat"),
                nat(4),
                nat(4),
                Expr::let_named(
                    Name::anon(),
                    constant("Bool"),
                    nat(4),
                    refl(&constant("Nat"), nat(4)),
                    false,
                ),
            ),
            alias(nat(4)),
            nat(4),
        ),
        // A value's own nested application arguments must also be checked.
        (
            PendingEquality::candidate(
                constant("Nat"),
                nat(4),
                nat(4),
                Expr::app(
                    Expr::lam(
                        BinderInfo::Default,
                        constant("Bool"),
                        refl(&constant("Nat"), nat(4)),
                    ),
                    nat(4),
                ),
            ),
            alias(nat(4)),
            nat(4),
        ),
    ];
    replay(genuine.term(), &genuine.proposition(), true);
    for (index, (original, left, right)) in cases.into_iter().enumerate() {
        let claim = eq(&original.ty, left.clone(), right.clone());
        let candidate = assembler
            .ascribe_preserving_endpoints(original, left, right)
            .unwrap();
        assert_eq!(candidate.proposition(), claim);
        replay(candidate.term(), &claim, false);
        if index == 0 {
            // Even an unused enclosing proof let cannot hide the false old claim.
            let unused = Expr::let_named(
                Name::anon(),
                claim,
                candidate.term().clone(),
                refl(&constant("Nat"), nat(4)),
                false,
            );
            replay(&unused, &eq(&constant("Nat"), nat(4), nat(4)), false);
        }
    }
    // The requested declaration itself is malformed. Keep the INDEPENDENT
    // replay statement well typed; do not put a false construction let in it.
    let malformed = assembler
        .ascribe_preserving_endpoints(
            genuine.clone(),
            constant("Bool.true"),
            constant("Bool.true"),
        )
        .unwrap();
    replay(malformed.term(), &genuine.proposition(), false);
    let retained = assembler
        .ascribe_preserving_endpoints(genuine.clone(), alias(nat(4)), nat(4))
        .unwrap();
    replay(retained.term(), &retained.proposition(), true);
    assert_eq!(assembler.operations(), 10);
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), 0);
}

#[test]
fn preserving_ascription_keeps_paid_prefixes_and_exhausted_local_caps() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(4, 1)).unwrap();
    for _ in 0..2 {
        assembler
            .conversion(constant("Nat"), nat(4), nat(4))
            .unwrap();
    }
    let local = assembler.local(constant("Nat")).unwrap();
    let original = PendingEquality::reflexive(constant("Nat"), local.term().clone());
    let candidate = assembler
        .ascribe_preserving_endpoints(
            original.clone(),
            alias(local.term().clone()),
            local.term().clone(),
        )
        .unwrap();
    replay(
        &close(
            assembler.local_scope(),
            std::slice::from_ref(&local),
            candidate.term().clone(),
            true,
        ),
        &close(
            assembler.local_scope(),
            std::slice::from_ref(&local),
            candidate.proposition(),
            false,
        ),
        true,
    );
    for _ in 0..2 {
        let error = assembler
            .ascribe_preserving_endpoints(original.clone(), nat(4), nat(4))
            .err()
            .unwrap();
        assert!(error.contains("operation budget"), "{error}");
        assert_eq!(assembler.operations(), 4);
        assert_eq!(assembler.locals, 1);
        assert_eq!(assembler.local_scope().allocated(), 1);
        assert!(assembler.local_scope().owns(&local));
    }

    // A failed explicit local allocation keeps its paid operation prefix.
    // The compound candidate neither refunds that operation nor allocates a local.
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(3, 1)).unwrap();
    let local = assembler.local(constant("Nat")).unwrap();
    let error = assembler.local(constant("Nat")).err().unwrap();
    assert!(error.contains("local budget"), "{error}");
    assert_eq!(assembler.operations(), 2);
    assert_eq!(assembler.locals, 1);
    let candidate = assembler
        .ascribe_preserving_endpoints(
            PendingEquality::reflexive(constant("Nat"), local.term().clone()),
            alias(local.term().clone()),
            local.term().clone(),
        )
        .unwrap();
    assert_eq!(assembler.operations(), 3);
    assert_eq!(assembler.locals, 1);
    assert_eq!(assembler.local_scope().allocated(), 1);
    replay(
        &close(
            assembler.local_scope(),
            std::slice::from_ref(&local),
            candidate.term().clone(),
            true,
        ),
        &close(
            assembler.local_scope(),
            std::slice::from_ref(&local),
            candidate.proposition(),
            false,
        ),
        true,
    );
    let error = assembler
        .ascribe_preserving_endpoints(
            PendingEquality::reflexive(constant("Nat"), nat(4)),
            nat(4),
            nat(4),
        )
        .err()
        .unwrap();
    assert!(error.contains("operation budget"), "{error}");
    assert_eq!(assembler.operations(), 3);
    assert_eq!(assembler.locals, 1);
    assert_eq!(assembler.local_scope().allocated(), 1);

    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(usize::MAX, 1)).unwrap();
    assembler.operations = usize::MAX;
    let error = assembler
        .ascribe_preserving_endpoints(
            PendingEquality::reflexive(constant("Nat"), nat(4)),
            nat(4),
            nat(4),
        )
        .err()
        .unwrap();
    assert!(error.contains("operation counter overflow"), "{error}");
    assert_eq!(assembler.operations(), usize::MAX);
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), 0);
    assert!(Assembler::new(&mut Scope::new(), limits(0, 1)).is_err());
}
