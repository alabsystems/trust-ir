// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Strict original/DAG controls for fixed selected-GEP templates. Authored
//! proof construction only, not source/native execution or a speed claim.

use super::*;

fn strict_closed(scope: &Scope, term: &Expr, statement: &Expr, accepted: bool) {
    replay(scope, &[], term, statement, accepted);
    if accepted {
        let term = scope.close(term).unwrap();
        let statement = scope.close(statement).unwrap();
        let audit = environment().audit_certification(&statement, &term);
        assert!(audit.is_certified());
        for dependency in audit.dependencies {
            assert!(environment().axiom_deps(&dependency).unwrap().is_empty());
            assert!(
                environment()
                    .foundational_axiom_deps(&dependency)
                    .unwrap()
                    .is_empty()
            );
            assert!(
                environment()
                    .trust_marker_deps(&dependency)
                    .unwrap()
                    .is_empty()
            );
        }
    }
}

// Literal original allocator/telescope, retained ONLY as a test oracle.
// Common legacy proof composition remains the original scoped route.
fn old_scoped_helper(a: &mut Assembler<'_>, inbounds: bool) -> Result<(Expr, Expr)> {
    let key = usize::from(inbounds);
    assert!(a.byte_gep_typed_candidates[key].is_none());
    let context = a.local(constant("IRByteContextV1"))?;
    let pointee = a.local(constant("IRTy"))?;
    let layout = a.local(constant("IRByteLayoutV1"))?;
    let stride = a.local(constant("Nat"))?;
    let pointer = a.local(constant("IRScalar"))?;
    let base = a.local(constant("Nat"))?;
    let index = a.local(constant("Nat"))?;
    let memory = a.local(constant("IRByteMemoryV1"))?;
    let input = ByteGepTyped {
        pointee: pointee.term().clone(),
        layout: layout.term().clone(),
        stride: stride.term().clone(),
        pointer: pointer.term().clone(),
        base: base.term().clone(),
        index: index.term().clone(),
        memory: memory.term().clone(),
    };
    let mut parameters = vec![
        context.clone(),
        pointee,
        layout,
        stride,
        pointer,
        base,
        index,
        memory,
    ];
    let mut equalities = Vec::with_capacity(3);
    for (ty, left, right) in input.equalities(context.term()) {
        let local = a.local(eq(&ty, left.clone(), right.clone()))?;
        equalities.push(PendingEquality::candidate(
            ty,
            left,
            right,
            local.term().clone(),
        ));
        parameters.push(local);
    }
    let mut proofs = Vec::with_capacity(5);
    for proposition in input.propositions() {
        let local = a.local(proposition.clone())?;
        proofs.push(PendingProof::candidate(proposition, local.term().clone()));
        parameters.push(local);
    }
    let membership = if inbounds {
        let local = a.local(eq(
            &constant("Bool"),
            input.resolved().membership(),
            constant("Bool.true"),
        ))?;
        let term = local.term().clone();
        parameters.push(local);
        Some(term)
    } else {
        None
    };
    let flag = constant(if inbounds { "Bool.true" } else { "Bool.false" });
    let selected = some("Nat", input.index.clone());
    let proof = a.byte_gep_resolved_term(
        input.resolved(),
        GepResolvedPremises {
            layout: equalities[0].clone(),
            layout_size: equalities[1].clone(),
            pointer: equalities[2].clone(),
            base_positive: proofs[0].clone(),
            stride_positive: proofs[1].clone(),
            stride_bound: proofs[2].clone(),
            delta_bound: proofs[3].clone(),
            result_bound: proofs[4].clone(),
        },
        PendingEquality::reflexive(option("Nat"), selected),
        input.evaluation(context.term().clone(), flag),
        membership,
        "typed GEP derived result",
    )?;
    // Independent statement: exact original dispatch/result endpoints,
    // not proof construction LETs or an inferred output answer.
    let statement = eq(
        &constant("IRByteMemoryResultV1"),
        input.evaluation(
            context.term().clone(),
            constant(if inbounds { "Bool.true" } else { "Bool.false" }),
        ),
        MemoryResult {
            value: app("IRScalar.ptr_", [input.resolved().address()]),
            memory: input.memory.clone(),
        }
        .result(),
    );
    let statement = parameters
        .iter()
        .rev()
        .fold(statement, |body, local| local.pi(body));
    let statement = a
        .scope
        .close(&statement)
        .map_err(|error| error.to_string())?;
    let term = parameters
        .iter()
        .rev()
        .fold(proof.term, |body, local| local.lam(body));
    let closed = a.scope.close(&term).map_err(|error| error.to_string())?;
    Ok((closed, statement))
}

fn actual_arguments(
    context: Expr,
    input: &ByteGepTyped,
    premises: &ByteGepTypedPremises,
    membership: Option<&PendingEquality>,
) -> Vec<Expr> {
    let mut arguments = vec![
        context,
        input.pointee.clone(),
        input.layout.clone(),
        input.stride.clone(),
        input.pointer.clone(),
        input.base.clone(),
        input.index.clone(),
        input.memory.clone(),
        premises.layout.term().clone(),
        premises.layout_size.term().clone(),
        premises.pointer.term().clone(),
        premises.base_positive.term().clone(),
        premises.stride_positive.term().clone(),
        premises.stride_bound.term().clone(),
        premises.delta_bound.term().clone(),
        premises.result_bound.term().clone(),
    ];
    if let Some(membership) = membership {
        arguments.push(membership.term().clone());
    }
    arguments
}

fn concrete() -> (Expr, ByteGepTyped, ByteGepTypedPremises) {
    let f = fixture(Ty::U8, &[Ty::U64], false, false);
    let reflected = reflect_core_module_v1_with_memory_profile(
        &f.module,
        &[(f.function, 4096)],
        CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
    )
    .unwrap();
    let model = MachineModel::new(constant("Nat"), &reflected, providers());
    let before = f.current(80, &[2], memory(80, 16, 173));
    let input = input(&f, &before, 80, 2, 1);
    let proofs = premises(model.context(), &input, 80, 2, 1);
    (model.context().clone(), input, proofs)
}

fn invoke(
    a: &mut Assembler<'_>,
    context: Expr,
    input: ByteGepTyped,
    proofs: ByteGepTypedPremises,
    membership: Option<PendingEquality>,
) -> Result<ByteGepTypedResult> {
    match membership {
        Some(membership) => a.byte_gep_typed_inbounds(context, input, proofs, membership),
        None => a.byte_gep_typed_noninbounds(context, input, proofs),
    }
}

#[test]
fn selected_gep_closed_templates_replay_original_oracle_and_exact_cold_warm_charges() {
    for inbounds in [false, true] {
        let mut old_scope = Scope::new();
        let mut old = Assembler::new(&mut old_scope, limits()).unwrap();
        let (oracle, statement) = old_scoped_helper(&mut old, inbounds).unwrap();
        assert_eq!(old.operations(), if inbounds { 37 } else { 36 });
        assert_eq!(old.locals, if inbounds { 23 } else { 22 });
        assert!(!oracle.has_fvar_quick() && !oracle.has_loose_bvars());
        strict_closed(old.local_scope(), &oracle, &statement, true);

        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let helper = a.byte_gep_typed_helper(inbounds).unwrap();
        assert_eq!(a.operations(), if inbounds { 28 } else { 27 });
        assert_eq!(old.operations() - a.operations(), 9);
        // The unchanged scoped oracle still builds four Refl/trans bridges
        // per map, versus one typed carrier in each of three neutral maps.
        assert_eq!(a.locals, 0);
        assert!(!helper.has_fvar_quick() && !helper.has_loose_bvars());
        strict_closed(a.local_scope(), &helper, &statement, true);
        let operations = a.operations();
        assert_eq!(a.byte_gep_typed_helper(inbounds).unwrap(), helper);
        assert_eq!(
            a.operations(),
            operations,
            "private warm helper adds no charge"
        );
        assert!(a.byte_gep_singleton_candidates.iter().all(Option::is_none));

        let (context, input, proofs) = concrete();
        let membership = inbounds.then(|| truth(input.checks(&context).inbounds_membership.1));
        let oracle_term = Expr::apps(
            oracle,
            actual_arguments(context.clone(), &input, &proofs, membership.as_ref()),
        );
        let result = invoke(&mut a, context, input, proofs, membership).unwrap();
        assert_eq!(
            a.operations(),
            operations + 1,
            "public warm door remains paid"
        );
        assert_eq!(a.locals, 0);
        strict_closed(
            a.local_scope(),
            &oracle_term,
            &result.evaluated.proposition(),
            true,
        );
        for proof in [&result.evaluated, &result.result_fits, &result.allocations] {
            strict_closed(a.local_scope(), proof.term(), &proof.proposition(), true);
        }
    }
}

// Actual raw caller BVars deliberately have a DIFFERENT ordering from the
// helper telescope, after two unrelated inherited inputs. No caller expression
// is lifted into the helper's binders.
fn caller_data(depth: u32) -> (Expr, ByteGepTyped) {
    let at = |position| Expr::bvar(depth - position - 1);
    (
        at(9),
        ByteGepTyped {
            pointee: at(8),
            layout: at(7),
            stride: at(6),
            pointer: at(5),
            base: at(4),
            index: at(3),
            memory: at(2),
        },
    )
}

#[test]
fn selected_gep_closed_templates_keep_reordered_outer_bvars_and_complete_memory() {
    for inbounds in [false, true] {
        let mut types = vec![
            Expr::type_(),
            constant("Nat"),
            constant("IRByteMemoryV1"),
            constant("Nat"),
            constant("Nat"),
            constant("IRScalar"),
            constant("Nat"),
            constant("IRByteLayoutV1"),
            constant("IRTy"),
            constant("IRByteContextV1"),
        ];
        for position in 0..3 {
            let (context, input) = caller_data(10 + position as u32);
            let (ty, left, right) = input.equalities(&context)[position].clone();
            types.push(eq(&ty, left, right));
        }
        for position in 0..5 {
            let (_, input) = caller_data(13 + position as u32);
            types.push(input.propositions()[position].clone());
        }
        if inbounds {
            let (_, input) = caller_data(18);
            types.push(eq(
                &constant("Bool"),
                input.resolved().membership(),
                constant("Bool.true"),
            ));
        }
        let depth = types.len() as u32;
        let (context, input) = caller_data(depth);
        let equality = |position: usize| {
            let (ty, left, right) = input.equalities(&context)[position].clone();
            PendingEquality::candidate(ty, left, right, Expr::bvar(depth - 11 - position as u32))
        };
        let bound = |position: usize| {
            PendingProof::candidate(
                input.propositions()[position].clone(),
                Expr::bvar(depth - 14 - position as u32),
            )
        };
        let proofs = ByteGepTypedPremises {
            layout: equality(0),
            layout_size: equality(1),
            pointer: equality(2),
            base_positive: bound(0),
            stride_positive: bound(1),
            stride_bound: bound(2),
            delta_bound: bound(3),
            result_bound: bound(4),
        };
        let membership = inbounds.then(|| {
            PendingEquality::candidate(
                constant("Bool"),
                input.resolved().membership(),
                constant("Bool.true"),
                Expr::bvar(0),
            )
        });
        let expected = eq(
            &constant("IRByteMemoryResultV1"),
            app(
                "ir_byte_gep_typed_v1",
                [
                    context.clone(),
                    input.pointee.clone(),
                    input.pointer.clone(),
                    some("Nat", input.index.clone()),
                    constant(if inbounds { "Bool.true" } else { "Bool.false" }),
                    input.memory.clone(),
                ],
            ),
            MemoryResult {
                value: app(
                    "IRScalar.ptr_",
                    [app(
                        "Nat.add",
                        [
                            input.base.clone(),
                            app("Nat.mul", [input.stride.clone(), input.index.clone()]),
                        ],
                    )],
                ),
                memory: input.memory.clone(),
            }
            .result(),
        );
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let result = invoke(&mut a, context, input.clone(), proofs, membership).unwrap();
        assert_eq!(a.locals, 0);
        let term = types
            .iter()
            .rev()
            .fold(result.evaluated.term().clone(), |body, ty| {
                Expr::lam(BinderInfo::Default, ty.clone(), body)
            });
        let statement = types.iter().rev().fold(expected.clone(), |body, ty| {
            Expr::pi(BinderInfo::Default, ty.clone(), body)
        });
        strict_closed(a.local_scope(), &term, &statement, true);

        // Same original semantic endpoint except the complete memory is
        // spuriously changed; no access/owner/world fact repairs this claim.
        let wrong = eq(
            &constant("IRByteMemoryResultV1"),
            result.evaluated.left().clone(),
            MemoryResult {
                value: result.result.value.clone(),
                memory: memory(80, 16, 174),
            }
            .result(),
        );
        let wrong = types.iter().rev().fold(wrong, |body, ty| {
            Expr::pi(BinderInfo::Default, ty.clone(), body)
        });
        strict_closed(a.local_scope(), &term, &wrong, false);
    }
}

#[test]
fn selected_gep_closed_templates_use_exhausted_caller_locals_without_refund() {
    for inbounds in [false, true] {
        let mut scope = Scope::new();
        let mut policy = limits();
        policy.max_locals = 1;
        let mut a = Assembler::new(&mut scope, policy).unwrap();
        let held = a.local(constant("Nat")).unwrap();
        assert_eq!(a.locals, 1);
        let (context, input, proofs) = concrete();
        let membership = inbounds.then(|| truth(input.checks(&context).inbounds_membership.1));
        let result = invoke(&mut a, context, input, proofs, membership).unwrap();
        assert_eq!(a.operations(), if inbounds { 30 } else { 29 });
        assert_eq!(a.locals, 1);
        strict_closed(
            a.local_scope(),
            result.evaluated.term(),
            &result.evaluated.proposition(),
            true,
        );
        let mut operations = a.operations();
        for _ in 0..2 {
            assert_eq!(
                a.local(constant("Nat")).err().unwrap(),
                "execution construction local budget exceeded"
            );
            operations += 1;
            assert_eq!(
                a.operations(),
                operations,
                "failed real allocation charge stays spent"
            );
            assert_eq!(a.locals, 1);
            assert!(
                held.term().has_fvar_quick(),
                "real caller local remains live"
            );
        }
        assert!(a.byte_gep_typed_candidates[usize::from(inbounds)].is_some());
    }
}

#[test]
fn selected_gep_closed_templates_partial_charges_never_publish_cache() {
    for inbounds in [false, true] {
        let public_cold = if inbounds { 29 } else { 28 };
        for cap in 1..public_cold {
            let mut scope = Scope::new();
            let mut policy = limits();
            policy.max_operations = cap;
            let mut a = Assembler::new(&mut scope, policy).unwrap();
            let (context, input, proofs) = concrete();
            let membership = inbounds.then(|| truth(input.checks(&context).inbounds_membership.1));
            assert_eq!(
                invoke(
                    &mut a,
                    context.clone(),
                    input.clone(),
                    proofs.clone(),
                    membership.clone()
                )
                .err()
                .unwrap(),
                "execution construction operation budget exceeded"
            );
            assert_eq!(a.operations(), cap);
            assert_eq!(a.locals, 0);
            assert!(a.byte_gep_typed_candidates.iter().all(Option::is_none));
            assert_eq!(
                invoke(&mut a, context, input, proofs, membership)
                    .err()
                    .unwrap(),
                "execution construction operation budget exceeded"
            );
            assert_eq!(a.operations(), cap, "failed charge has no refund/reset");
            assert!(a.byte_gep_typed_candidates.iter().all(Option::is_none));
        }
    }

    // A completed candidate is context-agnostic and cannot borrow a former
    // source module or its incoming byte bank.
    let f = fixture(Ty::U8, &[Ty::U64], false, false);
    let mut scope = Scope::new();
    let mut a = Assembler::new(&mut scope, limits()).unwrap();
    let mut previous = None;
    for (budget, base, byte) in [(4096, 80, 173), (8192, 200, 174)] {
        let reflected = reflect_core_module_v1_with_memory_profile(
            &f.module,
            &[(f.function, budget)],
            CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
        )
        .unwrap();
        let model = MachineModel::new(constant("Nat"), &reflected, providers());
        let before = f.current(base, &[2], memory(base, 16, byte));
        let input = input(&f, &before, base, 2, 1);
        let proofs = premises(model.context(), &input, base, 2, 1);
        let result = invoke(&mut a, model.context().clone(), input, proofs, None).unwrap();
        let helper = a.byte_gep_typed_candidates[0].as_ref().unwrap().clone();
        if let Some(previous) = &previous {
            assert_eq!(&helper, previous);
        }
        previous = Some(helper);
        assert_eq!(a.locals, 0);
        strict_closed(
            a.local_scope(),
            result.evaluated.term(),
            &result.evaluated.proposition(),
            true,
        );
    }
}

#[test]
fn selected_gep_closed_templates_keep_every_false_input_term_pending() {
    for inbounds in [false, true] {
        let mut old_scope = Scope::new();
        let mut old = Assembler::new(&mut old_scope, limits()).unwrap();
        let (oracle, statement) = old_scoped_helper(&mut old, inbounds).unwrap();
        strict_closed(old.local_scope(), &oracle, &statement, true);
        let mutations = if inbounds { 9 } else { 8 };
        for mutation in 0..mutations {
            let mut scope = Scope::new();
            let mut a = Assembler::new(&mut scope, limits()).unwrap();
            let (context, input, mut proofs) = concrete();
            let mut membership =
                inbounds.then(|| truth(input.checks(&context).inbounds_membership.1));
            let bad = refl(&constant("Nat"), nat(0));
            match mutation {
                0 => proofs.layout.term = bad,
                1 => proofs.layout_size.term = bad,
                2 => proofs.pointer.term = bad,
                3 => proofs.base_positive.term = bad,
                4 => proofs.stride_positive.term = bad,
                5 => proofs.stride_bound.term = bad,
                6 => proofs.delta_bound.term = bad,
                7 => proofs.result_bound.term = bad,
                _ => membership.as_mut().unwrap().term = bad,
            }
            let old_term = Expr::apps(
                oracle.clone(),
                actual_arguments(context.clone(), &input, &proofs, membership.as_ref()),
            );
            let result = invoke(&mut a, context, input, proofs, membership).unwrap();
            assert_eq!(a.locals, 0);
            strict_closed(
                a.local_scope(),
                &old_term,
                &result.evaluated.proposition(),
                false,
            );
            // Proposition and input data are genuinely true. Every invalid
            // proof argument is retained in the candidate, even if reduction
            // could hide its role in the already-closed result statement.
            strict_closed(
                a.local_scope(),
                result.evaluated.term(),
                &result.evaluated.proposition(),
                false,
            );
        }
    }
}
