// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural checks of the untrusted adapter, not a substitute byte evaluator.
//! Actual reflected-module/kernel replay is a separate consuming-environment gate.

use super::*;

fn limits() -> Limits {
    Limits {
        max_operations: 10_000,
        max_locals: 1_000,
        max_list_items: 1_000,
        max_lookup_candidates: 100,
        lookup_heartbeats: 1_000_000,
        lookup_cache_entries: 16_384,
    }
}

struct Fixture {
    model: MachineModel,
    target: CallTarget,
    site: FetchedSite,
    frame: ReturnFrame,
    resolved: PendingEquality,
    admitted: PendingEquality,
    before: PendingEquality,
    parameters: Vec<Local>,
    values: Expr,
}

fn fixture(scope: &mut Scope, arity: usize) -> Fixture {
    let mut parameters = Vec::new();
    let mut local = |ty| {
        let local = scope.try_local(ty).unwrap();
        parameters.push(local.clone());
        local.term().clone()
    };
    let model = MachineModel {
        world_type: constant("Nat"),
        context: constant("test_context"),
        providers: constant("test_providers"),
    };
    let target = CallTarget {
        context: model.context.clone(),
        function_id: nat(41),
        binding: constant("test_binding"),
        signature: constant("test_signature"),
    };
    let ids = (0..arity)
        .map(|i| nat(u64::try_from(100 + (arity - i) * 3).unwrap()))
        .collect::<Vec<_>>();
    let destinations = (0..arity)
        .map(|i| nat(u64::try_from(200 + i * 7).unwrap()))
        .collect::<Vec<_>>();
    let arguments = list("Nat", &ids);
    let instruction = app("IRInst.ret", [arguments.clone()]);
    let site = FetchedSite {
        context: model.context.clone(),
        coordinate: Coordinate {
            function: FuncId::new(41),
            block: BlockId::new(17),
            instruction: 9,
        },
        function: constant("test_function"),
        block: constant("test_block"),
        node: app("IRNode.mk", [instruction.clone(), list("Nat", &[])]),
        instruction,
        results: list("Nat", &[]),
        site: constant("test_site"),
    };
    let frame = ReturnFrame {
        returning: app(
            "IRFrame.mk",
            [
                nat(41),
                nat(17),
                nat(9),
                local(app("IRList", [constant("IRBinding")])),
                list("Nat", &destinations),
            ],
        ),
        // PC12 is already the caller continuation; the adapter must not add1.
        caller: app(
            "IRFrame.mk",
            [
                nat(80),
                nat(29),
                nat(12),
                local(app("IRList", [constant("IRBinding")])),
                list("Nat", &[]),
            ],
        ),
        tail: local(app("IRList", [constant("IRFrame")])),
        legacy_memory: local(app("IRList", [constant("IRMemSlot")])),
        legacy_cursor: local(constant("Nat")),
        memory: local(constant("IRByteMemoryV1")),
        host: local(constant("Nat")),
        owner: local(constant("Nat")),
        owners: local(app("IRList", [constant("Nat")])),
        next: local(constant("Nat")),
    };
    let values = list(
        "IRScalar",
        &(0..arity)
            .map(|_| local(constant("IRScalar")))
            .collect::<Vec<_>>(),
    );
    let actual = app("ir_resolve", [frame.current(&model).machine(), arguments]);
    let value_ty = app("IRList", [constant("IRScalar")]);
    let resolved_term = local(eq(&value_ty, actual.clone(), values.clone()));
    let resolved = PendingEquality::candidate(value_ty, actual, values.clone(), resolved_term);
    let admission = site
        .return_admission(&model, &target, &frame, values.clone())
        .unwrap();
    let admitted_term = local(eq(
        &constant("Bool"),
        admission.clone(),
        constant("Bool.true"),
    ));
    let admitted = PendingEquality::candidate(
        constant("Bool"),
        admission,
        constant("Bool.true"),
        admitted_term,
    );
    let valid = frame.current(&model).valid(&model);
    let before_term = local(eq(&constant("Bool"), valid.clone(), constant("Bool.true")));
    let before =
        PendingEquality::candidate(constant("Bool"), valid, constant("Bool.true"), before_term);
    Fixture {
        model,
        target,
        site,
        frame,
        resolved,
        admitted,
        before,
        parameters,
        values,
    }
}

fn transfer(scope: &mut Scope, f: &Fixture) -> Result<ReturnTransfer> {
    f.site.return_to_caller(
        &mut Assembler::new(scope, limits())?,
        &f.model,
        &f.target,
        &f.frame,
        f.resolved.clone(),
        f.admitted.clone(),
        f.before.clone(),
    )
}

#[test]
fn return_transfer_preserves_exact_caller_owner_world_and_arbitrary_lane_count() {
    for arity in [0, 1, 3, 5, 7] {
        let mut scope = Scope::new();
        let f = fixture(&mut scope, arity);
        let transfer = transfer(&mut scope, &f).unwrap();
        let expected_frame = app(
            "ir_frame_set_many",
            [
                f.frame.caller.clone(),
                app("ir_frame_dests", [f.frame.returning.clone()]),
                f.values.clone(),
            ],
        );
        let expected_world = app(
            "IRByteWorldV1.mk",
            [
                constant("Nat"),
                app(
                    "ir_byte_retire_v1",
                    [f.frame.owner.clone(), f.frame.memory.clone()],
                ),
                f.frame.host.clone(),
                f.frame.owners.clone(),
                f.frame.next.clone(),
            ],
        );
        assert_eq!(transfer.resumed().frame, expected_frame);
        assert_eq!(transfer.resumed().world, expected_world);
        assert_eq!(transfer.resumed().tail, f.frame.tail);
        assert_eq!(transfer.resumed().legacy_memory, f.frame.legacy_memory);
        assert_eq!(transfer.resumed().legacy_cursor, f.frame.legacy_cursor);
        assert_eq!(transfer.run().fuel().term(), &nat(1));
        assert_eq!(
            transfer.run().initial(),
            &f.frame.current(&f.model).running(&f.model)
        );
        assert_eq!(
            transfer.run().reached(),
            &transfer.resumed().running(&f.model)
        );
        assert_eq!(transfer.valid().left(), &transfer.resumed().valid(&f.model));
        assert_eq!(transfer.valid().right(), &constant("Bool.true"));
        assert_eq!(
            transfer.valid().term(),
            &app(
                "ir_byte_world_pop_shape_v1",
                [
                    constant("Nat"),
                    f.frame.memory.clone(),
                    f.frame.host.clone(),
                    f.frame.owner.clone(),
                    f.frame.returning.clone(),
                    f.frame.owners.clone(),
                    f.frame.next.clone(),
                    f.frame.caller.clone(),
                    transfer.resumed().frame.clone(),
                    f.frame.tail.clone(),
                    f.frame.legacy_memory.clone(),
                    f.frame.legacy_cursor.clone(),
                    f.before.term().clone(),
                ]
            )
        );
        assert_ne!(
            transfer.valid().term(),
            f.before.term(),
            "post-world validity must be newly derived"
        );
        for term in [
            transfer.run().equality().term().clone(),
            transfer.valid().term().clone(),
        ] {
            let closed = f.parameters.iter().rev().fold(term, |body, p| p.lam(body));
            assert!(!scope.close(&closed).unwrap().has_fvar_quick());
        }
    }
}

#[test]
fn return_transfer_refuses_wrong_opcode_identity_operands_and_premise_endpoints() {
    let mut scope = Scope::new();
    let f = fixture(&mut scope, 3);
    let run = |scope: &mut Scope,
               site: &FetchedSite,
               target: &CallTarget,
               resolved: PendingEquality,
               admitted: PendingEquality,
               before: PendingEquality| {
        site.return_to_caller(
            &mut Assembler::new(scope, limits()).unwrap(),
            &f.model,
            target,
            &f.frame,
            resolved,
            admitted,
            before,
        )
    };
    for instruction in [
        app("IRInst.call", [nat(41), list("Nat", &[])]),
        app("IRInst.ret", [list("Nat", &[]), list("Nat", &[])]),
    ] {
        let mut changed = f.site.clone();
        changed.instruction = instruction;
        assert!(
            run(
                &mut scope,
                &changed,
                &f.target,
                f.resolved.clone(),
                f.admitted.clone(),
                f.before.clone()
            )
            .is_err()
        );
    }
    let mut wrong_results = f.site.clone();
    wrong_results.results = list("Nat", &[nat(1)]);
    assert!(
        run(
            &mut scope,
            &wrong_results,
            &f.target,
            f.resolved.clone(),
            f.admitted.clone(),
            f.before.clone()
        )
        .is_err()
    );
    let mut wrong_function = f.target.clone();
    wrong_function.function_id = nat(42);
    assert!(
        run(
            &mut scope,
            &f.site,
            &wrong_function,
            f.resolved.clone(),
            f.admitted.clone(),
            f.before.clone()
        )
        .is_err()
    );
    let mut wrong_context = f.target.clone();
    wrong_context.context = constant("other_context");
    assert!(
        run(
            &mut scope,
            &f.site,
            &wrong_context,
            f.resolved.clone(),
            f.admitted.clone(),
            f.before.clone()
        )
        .is_err()
    );
    let wrong_operands = PendingEquality::candidate(
        app("IRList", [constant("IRScalar")]),
        app(
            "ir_resolve",
            [
                f.frame.current(&f.model).machine(),
                list("Nat", &[nat(103), nat(106), nat(109)]),
            ],
        ),
        f.values.clone(),
        f.resolved.term().clone(),
    );
    assert!(
        run(
            &mut scope,
            &f.site,
            &f.target,
            wrong_operands,
            f.admitted.clone(),
            f.before.clone()
        )
        .is_err()
    );
    let fake_true = PendingEquality::reflexive(constant("Bool"), constant("Bool.true"));
    assert!(
        run(
            &mut scope,
            &f.site,
            &f.target,
            f.resolved.clone(),
            fake_true.clone(),
            f.before.clone()
        )
        .is_err()
    );
    assert!(
        run(
            &mut scope,
            &f.site,
            &f.target,
            f.resolved.clone(),
            f.admitted.clone(),
            fake_true
        )
        .is_err()
    );
}
