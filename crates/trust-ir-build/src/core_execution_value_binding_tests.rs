// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Pending-term controls, not kernel or source execution evidence.

use super::*;

fn limits(operations: usize, items: usize) -> Limits {
    Limits {
        max_operations: operations,
        max_locals: 1,
        max_list_items: items,
        max_lookup_candidates: 1,
        lookup_heartbeats: 1,
        lookup_cache_entries: 1,
    }
}

fn fixture(count: usize) -> (FetchedSite, MachineModel, Current) {
    let model = MachineModel::from_terms(constant("W"), constant("context"), constant("providers"));
    let current = Current {
        frame: constant("frame"),
        tail: constant("tail"),
        legacy_memory: constant("legacy_memory"),
        legacy_cursor: constant("legacy_cursor"),
        world: constant("world"),
    };
    let results = list(
        "Nat",
        &(0..count).map(|i| nat(i as u64 + 7)).collect::<Vec<_>>(),
    );
    let instruction = app(
        "IRInst.const_",
        [app("IRTy.uint_", [nat(64)]), constant("literal")],
    );
    let site = FetchedSite {
        context: model.context().clone(),
        coordinate: Coordinate {
            function: FuncId::new(0),
            block: BlockId::new(0),
            instruction: 2,
        },
        function: constant("function"),
        block: constant("block"),
        node: app("IRNode.mk", [instruction.clone(), results.clone()]),
        instruction,
        results,
        site: constant("site"),
    };
    (site, model, current)
}

fn lanes(flag: bool) -> [Expr; 2] {
    [
        app("IRScalar.int_", [nat(19)]),
        app(
            "IRScalar.bool_",
            [constant(if flag { "Bool.true" } else { "Bool.false" })],
        ),
    ]
}

// Deliberately independent of the production predicate helper.
fn guard(site: &FetchedSite, model: &MachineModel, values: &[Expr]) -> Expr {
    let values = list("IRScalar", values);
    app(
        "Bool.and",
        [
            app(
                "ir_nat_eqb",
                [
                    app("ir_byte_length_v1", [constant("Nat"), site.results.clone()]),
                    app("ir_byte_length_v1", [constant("IRScalar"), values.clone()]),
                ],
            ),
            app(
                "ir_byte_values_match_v1",
                [
                    model.context().clone(),
                    app("ir_byte_site_results_v1", [site.site.clone()]),
                    values,
                ],
            ),
        ],
    )
}

fn premises(
    site: &FetchedSite,
    model: &MachineModel,
    current: &Current,
    values: &[Expr],
) -> ValueBindingPremises {
    ValueBindingPremises {
        result: PendingEquality::candidate(
            constant("Bool"),
            guard(site, model, values),
            constant("Bool.true"),
            constant("untrusted_guard"),
        ),
        before: PendingEquality::candidate(
            constant("Bool"),
            current.valid(model),
            constant("Bool.true"),
            constant("untrusted_before"),
        ),
    }
}

#[test]
fn ordered_binding_retains_both_lanes_guard_and_complete_world_without_overflow_assumption() {
    for flag in [false, true] {
        let (site, model, current) = fixture(2);
        let values = lanes(flag);
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits(20, 3)).unwrap();
        assert_eq!(
            site.value_binding_check(&model, &values).unwrap(),
            guard(&site, &model, &values)
        );
        let binding = site
            .bind_values(
                &mut assembler,
                &model,
                &current,
                &values,
                premises(&site, &model, &current, &values),
            )
            .unwrap();
        let expected_frame = app(
            "ir_frame_advance",
            [app(
                "ir_frame_set_many",
                [
                    current.frame.clone(),
                    list("Nat", &[nat(7), nat(8)]),
                    list("IRScalar", &values),
                ],
            )],
        );
        assert_eq!(binding.current().frame, expected_frame);
        assert_eq!(binding.current().tail, current.tail);
        assert_eq!(binding.current().legacy_memory, current.legacy_memory);
        assert_eq!(binding.current().legacy_cursor, current.legacy_cursor);
        assert_eq!(binding.current().world, current.world);
        assert_eq!(
            binding.equality().left(),
            &app(
                "ir_byte_bind_values_v1",
                [
                    model.world_type().clone(),
                    model.context().clone(),
                    current.machine(),
                    current.world.clone(),
                    site.results.clone(),
                    app("ir_byte_site_results_v1", [site.site.clone()]),
                    list("IRScalar", &values)
                ]
            )
        );
        assert_eq!(
            binding.equality().right(),
            &binding.current().running(&model)
        );
        assert_eq!(binding.valid().left(), &binding.current().valid(&model));
        assert_eq!(binding.valid().right(), &constant("Bool.true"));
        assert_eq!(binding.valid().term(), &constant("untrusted_before"));
        assert_eq!(assembler.operations(), 2);
        assert_eq!(assembler.local_scope().allocated(), 0);
        let proof = assembler
            .local_scope()
            .close(binding.equality().term())
            .unwrap();
        assert!(!proof.has_fvar_quick() && !proof.has_loose_bvars());
        assert_eq!(proof.get_app_args()[5], &constant("untrusted_guard"));
    }
}

#[test]
fn binding_guard_is_general_and_matches_the_existing_scalar_predicate_exactly() {
    let values = lanes(true);
    for count in 0..=3 {
        let (site, model, current) = fixture(count);
        for actual in [&values[..0], &values[..1], &values[..2]] {
            assert_eq!(
                site.value_binding_check(&model, actual).unwrap(),
                guard(&site, &model, actual)
            );
        }
        assert_eq!(
            site.scalar_checks(&model, &current, values[0].clone())
                .unwrap()
                .result,
            guard(&site, &model, &values[..1])
        );
    }
}

#[test]
fn binding_refuses_changed_order_catalog_context_world_and_evidence_after_charging() {
    for change in 0..8 {
        let (mut site, model, current) = fixture(2);
        let mut values = lanes(false);
        let mut proof = premises(&site, &model, &current, &values);
        match change {
            0 => values.swap(0, 1),
            1 => proof.result.ty = constant("Nat"),
            2 => proof.result.left = constant("Bool.true"),
            3 => proof.result.right = constant("Bool.false"),
            4 => site.site = constant("foreign_catalog"),
            5 => site.context = constant("foreign_context"),
            6 => {
                proof.before.left = Current {
                    world: constant("foreign_world"),
                    ..current.clone()
                }
                .valid(&model)
            }
            7 => proof.before.right = constant("Bool.false"),
            _ => unreachable!(),
        }
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits(20, 3)).unwrap();
        assert!(
            site.bind_values(&mut assembler, &model, &current, &values, proof)
                .is_err()
        );
        assert_eq!(assembler.operations(), 1);
        assert_eq!(assembler.local_scope().allocated(), 0);
    }
    let (site, model, current) = fixture(2);
    let values = lanes(false);
    for actual in [&values[..0], &values[..1]] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits(20, 3)).unwrap();
        assert!(
            site.bind_values(
                &mut assembler,
                &model,
                &current,
                actual,
                premises(&site, &model, &current, &values)
            )
            .is_err()
        );
        assert_eq!(assembler.operations(), 1);
    }
}

#[test]
fn binding_limits_and_run_boundary_preserve_charges_initial_configuration_and_fuel() {
    let (site, model, current) = fixture(2);
    let values = lanes(true);
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(1, 1)).unwrap();
    assert!(
        site.bind_values(
            &mut assembler,
            &model,
            &current,
            &values,
            premises(&site, &model, &current, &values)
        )
        .is_err()
    );
    assert_eq!(assembler.operations(), 1);
    assert!(
        site.bind_values(
            &mut assembler,
            &model,
            &current,
            &values[..1],
            premises(&site, &model, &current, &values[..1])
        )
        .is_err()
    );
    assert_eq!(assembler.operations(), 1);

    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits(20, 3)).unwrap();
    let binding = site
        .bind_values(
            &mut assembler,
            &model,
            &current,
            &values,
            premises(&site, &model, &current, &values),
        )
        .unwrap();
    let initial = constant("original_initial");
    let fuel = NatTerm::literal(17);
    let run = ExactRun::candidate(
        model.clone(),
        initial.clone(),
        binding.equality.left.clone(),
        fuel.clone(),
        PendingEquality::candidate(
            model.config_type(),
            model.run(&fuel, initial.clone()),
            binding.equality.left.clone(),
            constant("untrusted_execution"),
        ),
    )
    .unwrap();
    let completed = binding.complete_run(&mut assembler, run.clone()).unwrap();
    assert_eq!(completed.initial(), &initial);
    assert_eq!(completed.fuel().term(), fuel.term());
    assert_eq!(completed.reached(), &binding.current().running(&model));
    assert_eq!(assembler.operations(), 4);
    let wrong = ExactRun::candidate(
        model.clone(),
        initial.clone(),
        constant("foreign_endpoint"),
        fuel.clone(),
        PendingEquality::candidate(
            model.config_type(),
            model.run(&fuel, initial),
            constant("foreign_endpoint"),
            constant("untrusted_execution"),
        ),
    )
    .unwrap();
    assert!(binding.complete_run(&mut assembler, wrong).is_err());
    assert_eq!(assembler.operations(), 5);
    let foreign_model = MachineModel::from_terms(
        model.clone().world_type().clone(),
        model.clone().context().clone(),
        constant("foreign_provider"),
    );
    let foreign = ExactRun::candidate(
        foreign_model.clone(),
        run.initial.clone(),
        run.reached.clone(),
        run.fuel.clone(),
        PendingEquality::candidate(
            foreign_model.config_type(),
            foreign_model.run(&run.fuel, run.initial.clone()),
            run.reached.clone(),
            constant("untrusted_execution"),
        ),
    )
    .unwrap();
    assert!(binding.complete_run(&mut assembler, foreign).is_err());
    assert_eq!(assembler.operations(), 6);
}
