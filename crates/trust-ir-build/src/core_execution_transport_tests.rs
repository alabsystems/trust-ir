// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural candidate controls. The actual byte definitions and kernel
//! replay live in consuming profiles, not in a replacement byte model here.

use super::*;
use crate::term_scope::TermScopeLimits;

fn limits() -> Limits {
    Limits {
        max_operations: 20_000,
        max_locals: 1_000,
        max_list_items: 1_000,
        max_lookup_candidates: 100,
        lookup_heartbeats: 1_000_000,
        lookup_cache_entries: 16_384,
    }
}

fn model() -> MachineModel {
    MachineModel::from_terms(
        constant("Nat"),
        constant("test_transport_context"),
        constant("test_transport_providers"),
    )
}

fn current() -> Current {
    Current {
        frame: constant("actual_returned_frame"),
        tail: constant("actual_returned_tail"),
        legacy_memory: constant("actual_legacy_memory"),
        legacy_cursor: nat(53),
        world: constant("actual_after_world"),
    }
}

fn frame_equality(current: &Current) -> PendingEquality {
    PendingEquality::candidate(
        constant("IRFrame"),
        current.frame.clone(),
        constant("normalized_actual_returned_frame"),
        constant("candidate_frame_equality"),
    )
}

fn before(model: &MachineModel, current: &Current) -> PendingEquality {
    PendingEquality::candidate(
        constant("Bool"),
        current.valid(model),
        constant("Bool.true"),
        constant("candidate_actual_returned_validity"),
    )
}

#[test]
fn frame_transport_retains_the_actual_world_and_all_nonframe_fields() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let model = model();
    let current = current();
    let frame = frame_equality(&current);
    let transferred = assembler
        .transport_frame(&model, &current, frame.clone(), before(&model, &current))
        .unwrap();
    let after = transferred.current();
    assert_eq!(after.frame, frame.right);
    assert_eq!(after.tail, current.tail);
    assert_eq!(after.legacy_memory, current.legacy_memory);
    assert_eq!(after.legacy_cursor, current.legacy_cursor);
    assert_eq!(after.world, current.world);
    assert_eq!(transferred.configuration.left, current.running(&model));
    assert_eq!(transferred.configuration.right, after.running(&model));
    assert_eq!(transferred.valid.left, after.valid(&model));
    assert_eq!(transferred.valid.right, constant("Bool.true"));
    let arguments = transferred.configuration.term.get_app_args();
    assert_eq!(arguments.len(), 8);
    assert_eq!(*arguments[6], current.world);
    assert_eq!(*arguments[7], frame.term);
    assert_eq!(transferred.valid.term.get_app_args().len(), 9);
}

#[test]
fn frame_transport_rejects_foreign_or_wrongly_typed_premise_endpoints() {
    let model = model();
    let current = current();
    for mutation in 0..5 {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let mut frame = frame_equality(&current);
        let mut valid = before(&model, &current);
        match mutation {
            0 => frame.ty = constant("Nat"),
            1 => frame.left = constant("saved_pre_call_frame"),
            2 => valid.ty = constant("Nat"),
            3 => valid.left = constant("saved_pre_call_validity"),
            4 => valid.right = constant("Bool.false"),
            _ => unreachable!(),
        }
        assert!(
            assembler
                .transport_frame(&model, &current, frame, valid)
                .is_err()
        );
        assert_eq!(
            assembler.locals, 0,
            "reject before allocating helper locals"
        );
    }
}

#[test]
fn reached_transport_keeps_the_same_model_initial_and_symbolic_fuel() {
    let mut scope = Scope::new();
    let fuel = scope.try_local(constant("Nat")).unwrap();
    let model = model();
    let initial = constant("actual_initial_configuration");
    let reached = constant("actual_returned_configuration");
    let count = NatTerm::local(&fuel).unwrap();
    let run = ExactRun::candidate(
        model.clone(),
        initial.clone(),
        reached.clone(),
        count.clone(),
        PendingEquality::candidate(
            model.config_type(),
            model.run(&count, initial.clone()),
            reached.clone(),
            constant("candidate_actual_run"),
        ),
    )
    .unwrap();
    let equation = PendingEquality::candidate(
        model.config_type(),
        reached,
        constant("normalized_returned_configuration"),
        constant("candidate_configuration_equality"),
    );
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let normalized = assembler
        .transport_reached(run.clone(), equation.clone())
        .unwrap();
    assert!(normalized.model.same(&model).is_ok());
    assert_eq!(normalized.initial, initial);
    assert_eq!(normalized.fuel.term(), count.term());
    assert_eq!(normalized.reached, equation.right);
    assert_eq!(normalized.equality.left, run.equality.left);
    assert_eq!(normalized.equality.right, equation.right);
    for mutation in 0..3 {
        let mut bad = equation.clone();
        match mutation {
            0 => bad.ty = constant("IRFrame"),
            1 => bad.left = constant("saved_configuration"),
            2 => std::mem::swap(&mut bad.left, &mut bad.right),
            _ => unreachable!(),
        }
        assert!(assembler.transport_reached(run.clone(), bad).is_err());
    }
}

#[test]
fn reached_ascription_retains_original_run_and_spends_one_operation_without_locals() {
    let mut scope = Scope::new();
    let fuel = scope.try_local(constant("Nat")).unwrap();
    let model = model();
    let initial = constant("actual_initial_configuration");
    let count = NatTerm::local(&fuel).unwrap();
    let original = PendingEquality::candidate(
        model.config_type(),
        model.run(&count, initial.clone()),
        constant("actual_returned_configuration"),
        constant("candidate_actual_run"),
    );
    let run = ExactRun::candidate(
        model.clone(),
        initial.clone(),
        original.right.clone(),
        count.clone(),
        original.clone(),
    )
    .unwrap();
    let mut policy = limits();
    policy.max_operations = 1;
    policy.max_locals = 1;
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    let reached = constant("requested_returned_presentation");
    let presented = assembler
        .ascribe_reached(run.clone(), reached.clone())
        .unwrap();
    assert!(presented.model.same(&model).is_ok());
    assert_eq!(presented.initial, initial);
    assert_eq!(presented.fuel.term(), count.term());
    assert_eq!(presented.reached, reached);
    assert_eq!(presented.equality.left, original.left);
    assert_eq!(
        *presented.equality.term(),
        Expr::let_named(
            Name::anon(),
            presented.equality.proposition(),
            Expr::let_named(
                Name::anon(),
                original.proposition(),
                original.term().clone(),
                Expr::bvar(0),
                false,
            ),
            Expr::bvar(0),
            false,
        ),
    );
    assert_eq!(assembler.operations(), 1);
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), 1);
    assert!(assembler.local_scope().owns(&fuel));
    assert!(assembler.ascribe_reached(run, reached).is_err());
    assert_eq!(assembler.operations(), 1);
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), 1);
}

#[test]
fn shared_frame_helpers_do_not_capture_growing_actual_histories_per_use() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let model = model();
    let mut current = current();
    let mut valid = before(&model, &current);
    let mut checkpoint = None;
    let mut helper_locals = None;
    for count in 1..=64 {
        let frame = PendingEquality::candidate(
            constant("IRFrame"),
            current.frame.clone(),
            app("test_next_frame", [current.frame.clone()]),
            constant("candidate_frame_equality"),
        );
        let transfer = assembler
            .transport_frame(&model, &current, frame, valid)
            .unwrap();
        current = transfer.current;
        valid = transfer.valid;
        match helper_locals {
            None => helper_locals = Some(assembler.locals),
            Some(locals) => assert_eq!(assembler.locals, locals),
        }
        if count == 32 {
            checkpoint = Some(valid.term.clone());
        }
    }
    drop(assembler);
    let small = scope
        .close_with_limits(&checkpoint.unwrap(), TermScopeLimits::default())
        .unwrap();
    let large = scope
        .close_with_limits(&valid.term, TermScopeLimits::default())
        .unwrap();
    assert!(
        large.stats.visits <= 3 * small.stats.visits,
        "shared presentation proof closing grew from {} to {}",
        small.stats.visits,
        large.stats.visits
    );
    assert_eq!(small.stats.max_binder_depth, large.stats.max_binder_depth);
}
