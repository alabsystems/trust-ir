// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural adapter checks. Symbols here are deliberately not installed as a
//! replacement evaluator: actual-byte replay belongs to the consuming profile.

use super::*;

fn limits() -> Limits {
    Limits {
        max_operations: 100,
        max_locals: 100,
        max_list_items: 100,
        max_lookup_candidates: 100,
        lookup_heartbeats: 1_000_000,
        lookup_cache_entries: 16_384,
    }
}

struct Fixture {
    model: MachineModel,
    entry: EntryTarget,
    arguments: Expr,
    memory: Expr,
    host: Expr,
    initial_memory: PendingEquality,
    admitted: PendingEquality,
    parameters: Vec<Local>,
}

fn fixture(scope: &mut Scope, arity: usize) -> Fixture {
    let mut parameters = Vec::new();
    let mut local = |ty| {
        let local = scope.try_local(ty).unwrap();
        parameters.push(local.clone());
        local.term().clone()
    };
    let model = MachineModel::from_terms(
        constant("Nat"),
        constant("test_entry_context"),
        constant("test_entry_providers"),
    );
    let entry = EntryTarget {
        target: CallTarget {
            context: model.context().clone(),
            function_id: nat(41),
            binding: constant("test_entry_binding"),
            signature: constant("test_entry_signature"),
        },
        function: constant("test_entry_function"),
    };
    let arguments = list(
        "IRScalar",
        &(0..arity)
            .map(|_| local(constant("IRScalar")))
            .collect::<Vec<_>>(),
    );
    let memory = local(constant("IRByteMemoryV1"));
    let host = local(constant("Nat"));
    let memory_guard = EntryTarget::memory_admission(memory.clone());
    let memory_proof = local(eq(
        &constant("Bool"),
        memory_guard.clone(),
        constant("Bool.true"),
    ));
    let initial_memory = PendingEquality::candidate(
        constant("Bool"),
        memory_guard,
        constant("Bool.true"),
        memory_proof,
    );
    let entry_guard = entry.admission(&model, arguments.clone()).unwrap();
    let entry_proof = local(eq(
        &constant("Bool"),
        entry_guard.clone(),
        constant("Bool.true"),
    ));
    let admitted = PendingEquality::candidate(
        constant("Bool"),
        entry_guard,
        constant("Bool.true"),
        entry_proof,
    );
    Fixture {
        model,
        entry,
        arguments,
        memory,
        host,
        initial_memory,
        admitted,
        parameters,
    }
}

fn initialize(assembler: &mut Assembler<'_>, fixture: &Fixture) -> Result<Initialization> {
    fixture.entry.initialize(
        assembler,
        &fixture.model,
        fixture.arguments.clone(),
        fixture.memory.clone(),
        fixture.host.clone(),
        fixture.initial_memory.clone(),
        fixture.admitted.clone(),
    )
}

#[test]
fn initialization_retains_actual_arguments_and_symbolic_historical_owner() {
    for arity in [0, 1, 2, 3, 5, 7] {
        let mut scope = Scope::new();
        let fixture = fixture(&mut scope, arity);
        let initialized =
            initialize(&mut Assembler::new(&mut scope, limits()).unwrap(), &fixture).unwrap();
        let owner = app("ir_byte_fresh_owner_v1", [fixture.memory.clone()]);
        let frame = app(
            "IRFrame.mk",
            [
                app("ir_func_id", [fixture.entry.function.clone()]),
                app("ir_func_entry", [fixture.entry.function.clone()]),
                nat(0),
                app(
                    "ir_bind_params",
                    [
                        app("ir_func_params", [fixture.entry.function.clone()]),
                        fixture.arguments.clone(),
                        list("IRBinding", &[]),
                    ],
                ),
                list("Nat", &[]),
            ],
        );
        let world = app(
            "IRByteWorldV1.mk",
            [
                fixture.model.world_type().clone(),
                fixture.memory.clone(),
                fixture.host.clone(),
                list("Nat", std::slice::from_ref(&owner)),
                app("Nat.succ", [owner]),
            ],
        );
        let machine = app(
            "IRMachine.mk",
            [
                list("IRFrame", std::slice::from_ref(&frame)),
                list("IRMemSlot", &[]),
                nat(0),
            ],
        );
        let running = app(
            "IRByteConfigV1.running",
            [
                fixture.model.world_type().clone(),
                machine.clone(),
                world.clone(),
            ],
        );
        assert_eq!(initialized.current().frame, frame);
        assert_eq!(initialized.current().world, world);
        assert_eq!(initialized.current().machine(), machine);
        assert_eq!(initialized.equality().right, running);
        assert_eq!(
            initialized.equality().left,
            app(
                "ir_byte_init_v1",
                [
                    fixture.model.world_type().clone(),
                    fixture.model.context().clone(),
                    nat(41),
                    fixture.arguments.clone(),
                    fixture.memory.clone(),
                    fixture.host.clone(),
                ]
            )
        );
        assert_eq!(
            initialized.valid().left,
            app(
                "ir_byte_world_valid_v1",
                [fixture.model.world_type().clone(), machine, world,]
            )
        );
        assert_eq!(initialized.valid().right, constant("Bool.true"));

        // Exact published-law applications, including the independently
        // derived validity, not the caller's pre-memory proof relabelled.
        let fields = initialized.equality().term.get_app_args();
        assert_eq!(fields.len(), 15);
        assert_eq!(*fields[2], nat(41));
        assert_eq!(*fields[3], fixture.arguments);
        assert_eq!(*fields[4], fixture.memory);
        assert_eq!(*fields[13], fixture.initial_memory.term);
        assert_eq!(*fields[14], fixture.admitted.term);
        assert_eq!(
            initialized.valid().term.get_app_fn(),
            &constant("ir_byte_init_current_valid_v1")
        );
        assert_ne!(initialized.valid().term, fixture.initial_memory.term);
        for term in [&initialized.equality().term, &initialized.valid().term] {
            let closed = fixture
                .parameters
                .iter()
                .rev()
                .fold(term.clone(), |body, local| local.lam(body));
            assert!(!scope.close(&closed).unwrap().has_fvar_quick());
        }
    }
}

#[test]
fn initialization_refuses_mismatched_context_or_precondition_endpoints() {
    for mutation in 0..9 {
        let mut scope = Scope::new();
        let mut fixture = fixture(&mut scope, 2);
        match mutation {
            0 => {
                fixture.model = MachineModel::from_terms(
                    fixture.model.world_type().clone(),
                    constant("other_context"),
                    fixture.model.providers().clone(),
                )
            }
            1 => fixture.initial_memory.ty = constant("Nat"),
            2 => fixture.initial_memory.left = constant("other_memory_guard"),
            3 => fixture.initial_memory.right = constant("Bool.false"),
            4 => fixture.admitted.ty = constant("Nat"),
            5 => fixture.admitted.left = constant("other_entry_guard"),
            6 => fixture.admitted.right = constant("Bool.false"),
            7 => fixture.arguments = list("IRScalar", &[]),
            8 => fixture.memory = constant("other_memory"),
            _ => unreachable!(),
        }
        assert!(
            initialize(&mut Assembler::new(&mut scope, limits()).unwrap(), &fixture).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn initialization_charges_the_shared_assembler_budget() {
    let mut scope = Scope::new();
    let fixture = fixture(&mut scope, 2);
    let mut policy = limits();
    policy.max_operations = 1;
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    assert!(initialize(&mut assembler, &fixture).is_ok());
    assert!(initialize(&mut assembler, &fixture).is_err());
}
