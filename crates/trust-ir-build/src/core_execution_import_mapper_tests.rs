// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict replay of the actual provider-result mapper, not an import execution
//! or a provider admission. The input equality is an explicit theorem premise.

use super::*;
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};

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

struct Fixture {
    model: MachineModel,
    target: CallTarget,
    site: FetchedSite,
    current: Current,
    provided: PendingEquality,
    parameters: Vec<Local>,
    wrong_frame: Expr,
}

fn fixture(scope: &mut Scope) -> Fixture {
    let mut parameters = Vec::new();
    let mut local = |ty| {
        let local = scope.try_local(ty).unwrap();
        parameters.push(local.clone());
        local.term().clone()
    };
    let world_type = local(Expr::type_());
    let model = MachineModel {
        world_type: world_type.clone(),
        context: local(constant("IRByteContextV1")),
        // The actual mapper never invokes or mentions the provider function.
        providers: constant("unused_mapper_providers"),
    };
    let target = CallTarget {
        context: model.context.clone(),
        function_id: nat(55),
        binding: constant("unused_mapper_binding"),
        signature: local(constant("IRByteSignatureV1")),
    };
    let current = Current {
        frame: local(constant("IRFrame")),
        tail: local(app("IRList", [constant("IRFrame")])),
        legacy_memory: local(app("IRList", [constant("IRMemSlot")])),
        legacy_cursor: local(constant("Nat")),
        world: local(app("IRByteWorldV1", [world_type.clone()])),
    };
    let results = local(app("IRList", [constant("Nat")]));
    let site = FetchedSite {
        context: model.context.clone(),
        coordinate: Coordinate {
            function: FuncId::new(41),
            block: BlockId::new(13),
            instruction: 9,
        },
        function: constant("unused_mapper_function"),
        block: constant("unused_mapper_block"),
        node: constant("unused_mapper_node"),
        instruction: constant("unused_mapper_instruction"),
        results,
        site: constant("unused_mapper_site"),
    };
    let result_type = app("IRByteImportResultV1", [world_type]);
    let left = local(result_type.clone());
    let right = local(result_type.clone());
    let proof = local(eq(&result_type, left.clone(), right.clone()));
    let wrong_frame = local(constant("IRFrame"));
    Fixture {
        model,
        target,
        site,
        current,
        provided: PendingEquality::candidate(result_type, left, right, proof),
        parameters,
        wrong_frame,
    }
}

fn dispatch(f: &Fixture, current: &Current, result: Expr) -> Expr {
    // Independently spell the original primitive's complete application.
    app(
        "ir_byte_import_result_v1",
        [
            f.model.world_type.clone(),
            f.model.context.clone(),
            current.machine(),
            current.world.clone(),
            f.site.results.clone(),
            app("ir_byte_signature_returns_v1", [f.target.signature.clone()]),
            result,
        ],
    )
}

fn check_closed(term: Expr, claim: Expr, accepted: bool) {
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    assert!(!term.has_loose_bvars_quick() && !claim.has_loose_bvars_quick());
    let environment = shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env();
    let term_bytes = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
    let claim_bytes = trust_ir::proof::encode_clean_expr_dag_v2(&claim).unwrap();
    let decoded_term = trust_ir::proof::decode_clean_expr_dag_v2(&term_bytes).unwrap();
    let decoded_claim = trust_ir::proof::decode_clean_expr_dag_v2(&claim_bytes).unwrap();
    assert_eq!(decoded_term, term);
    assert_eq!(decoded_claim, claim);
    for (term, claim) in [(term, claim), (decoded_term, decoded_claim)] {
        let mut checker = TypeChecker::new(environment);
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        checker.set_heartbeat_limit(5_000_000);
        checker.set_max_cache_entries(100_000);
        checker
            .check_type(&claim, &Expr::sort(Level::zero()))
            .unwrap();
        let checked = checker.check_type(&term, &claim);
        if accepted {
            checked.unwrap();
            let audit = environment.audit_certification(&claim, &term);
            assert!(audit.is_certified(), "{audit:#?}");
            for dependency in &audit.dependencies {
                assert!(environment.axiom_deps(dependency).unwrap().is_empty());
                assert!(
                    environment
                        .trust_marker_deps(dependency)
                        .unwrap()
                        .is_empty()
                );
            }
        } else {
            let error = checked.unwrap_err();
            assert!(
                matches!(error, KernelTypeError::TypeMismatch { .. }),
                "actual type mismatch, not resource exhaustion: {error:?}"
            );
        }
        assert!(!checker.heartbeat_spent());
    }
}

fn replay(scope: &Scope, parameters: &[Local], proof: Expr, claim: Expr, accepted: bool) {
    let term = parameters
        .iter()
        .rev()
        .fold(proof, |body, local| local.lam(body));
    let claim = parameters
        .iter()
        .rev()
        .fold(claim, |body, local| local.pi(body));
    check_closed(
        scope.close(&term).unwrap(),
        scope.close(&claim).unwrap(),
        accepted,
    );
}

#[test]
fn provider_result_mapper_reuses_actual_partial_function_without_hot_locals() {
    let mut scope = Scope::new();
    let f = fixture(&mut scope);
    let mut policy = limits();
    policy.max_locals = 1;
    policy.max_operations = 101;
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    assembler.local(constant("Nat")).unwrap();
    let mut last = None;
    for ordinal in 0..100 {
        let proof = f
            .site
            .map_import_provider_result(
                &mut assembler,
                &f.model,
                &f.target,
                &f.current,
                f.provided.clone(),
            )
            .unwrap();
        assert_eq!((assembler.operations, assembler.locals), (ordinal + 2, 1));
        let arguments = proof.term().get_app_args();
        assert_eq!(
            arguments[4].get_app_fn(),
            &constant("ir_byte_import_result_v1")
        );
        assert_eq!(arguments[4].get_app_args().len(), 6);
        assert_eq!(arguments[5], f.provided.term());
        drop(arguments);
        assert_eq!(
            proof.proposition(),
            eq(
                &f.model.config_type(),
                dispatch(&f, &f.current, f.provided.left().clone()),
                dispatch(&f, &f.current, f.provided.right().clone()),
            )
        );
        last = Some(proof);
    }
    assert_eq!(assembler.local_scope().allocated(), f.parameters.len() + 1);
    let error = f
        .site
        .map_import_provider_result(
            &mut assembler,
            &f.model,
            &f.target,
            &f.current,
            f.provided.clone(),
        )
        .err()
        .unwrap();
    assert_eq!(error, "execution construction operation budget exceeded");
    assert_eq!((assembler.operations, assembler.locals), (101, 1));
    let proof = last.unwrap();
    replay(
        assembler.local_scope(),
        &f.parameters,
        proof.term().clone(),
        proof.proposition(),
        true,
    );
}

#[test]
fn provider_result_mapper_retains_source_operands_and_rejects_forged_equality() {
    let mut scope = Scope::new();
    let f = fixture(&mut scope);
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let proof = f
        .site
        .map_import_provider_result(
            &mut assembler,
            &f.model,
            &f.target,
            &f.current,
            f.provided.clone(),
        )
        .unwrap();
    let mut wrong = f.current.clone();
    wrong.frame = f.wrong_frame.clone();
    let claim = eq(
        &f.model.config_type(),
        dispatch(&f, &f.current, f.provided.left().clone()),
        dispatch(&f, &wrong, f.provided.right().clone()),
    );
    replay(
        assembler.local_scope(),
        &f.parameters,
        proof.term().clone(),
        claim,
        false,
    );
    let forged = PendingEquality::candidate(
        f.provided.ty.clone(),
        f.provided.left().clone(),
        f.provided.right().clone(),
        refl(&f.provided.ty, f.provided.left().clone()),
    );
    let forged = f
        .site
        .map_import_provider_result(&mut assembler, &f.model, &f.target, &f.current, forged)
        .unwrap();
    replay(
        assembler.local_scope(),
        &f.parameters,
        forged.term().clone(),
        proof.proposition(),
        false,
    );
    assert_eq!((assembler.operations, assembler.locals), (2, 0));
}

#[test]
fn provider_result_mapper_neither_escapes_input_equality_nor_grants_world_validity() {
    let mut scope = Scope::new();
    let f = fixture(&mut scope);
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let proof = f
        .site
        .map_import_provider_result(
            &mut assembler,
            &f.model,
            &f.target,
            &f.current,
            f.provided.clone(),
        )
        .unwrap();
    // Bind and replay the actual premise first. Omitting it below then means
    // a registered binder escaped, not an unrelated unknown outer variable.
    replay(
        assembler.local_scope(),
        &f.parameters,
        proof.term().clone(),
        proof.proposition(),
        true,
    );
    let missing_premise = f
        .parameters
        .iter()
        .filter(|local| local.term() != f.provided.term())
        .rev()
        .fold(proof.term().clone(), |body, local| local.lam(body));
    assert!(matches!(
        assembler.local_scope().close(&missing_premise),
        Err(crate::scoped_local::LocalScopeError::Closure(
            crate::term_scope::TermScopeError::OutOfScope(_)
        ))
    ));
    replay(
        assembler.local_scope(),
        &f.parameters,
        proof.term().clone(),
        eq(
            &constant("Bool"),
            f.current.valid(&f.model),
            constant("Bool.true"),
        ),
        false,
    );
}

#[test]
fn provider_result_mapper_does_not_capture_external_type_world_and_result_bvars() {
    let mut scope = Scope::new();
    let mut f = fixture(&mut scope);
    // Construct the actual mapper BEFORE introducing these ordinary binders.
    // The final context is U, ctx, frame, world, destinations, signature, a, b, h.
    f.model.world_type = Expr::bvar(8);
    f.model.context = Expr::bvar(7);
    f.current.frame = Expr::bvar(6);
    f.current.tail = list("IRFrame", &[]);
    f.current.legacy_memory = list("IRMemSlot", &[]);
    f.current.legacy_cursor = nat(0);
    f.current.world = Expr::bvar(5);
    f.site.results = Expr::bvar(4);
    f.target.signature = Expr::bvar(3);
    f.provided = PendingEquality::candidate(
        app("IRByteImportResultV1", [Expr::bvar(8)]),
        Expr::bvar(2),
        Expr::bvar(1),
        Expr::bvar(0),
    );
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let proof = f
        .site
        .map_import_provider_result(
            &mut assembler,
            &f.model,
            &f.target,
            &f.current,
            f.provided.clone(),
        )
        .unwrap();
    assert_eq!((assembler.operations, assembler.locals), (1, 0));
    let domains = [
        Expr::type_(),
        constant("IRByteContextV1"),
        constant("IRFrame"),
        app("IRByteWorldV1", [Expr::bvar(2)]),
        app("IRList", [constant("Nat")]),
        constant("IRByteSignatureV1"),
        app("IRByteImportResultV1", [Expr::bvar(5)]),
        app("IRByteImportResultV1", [Expr::bvar(6)]),
        eq(
            &app("IRByteImportResultV1", [Expr::bvar(7)]),
            Expr::bvar(1),
            Expr::bvar(0),
        ),
    ];
    let term = domains.iter().rev().fold(proof.term().clone(), |body, ty| {
        Expr::lam(BinderInfo::Default, ty.clone(), body)
    });
    let claim = eq(
        &f.model.config_type(),
        dispatch(&f, &f.current, f.provided.left().clone()),
        dispatch(&f, &f.current, f.provided.right().clone()),
    );
    let claim = domains.iter().rev().fold(claim, |body, ty| {
        Expr::pi(BinderInfo::Default, ty.clone(), body)
    });
    check_closed(
        assembler.local_scope().close(&term).unwrap(),
        assembler.local_scope().close(&claim).unwrap(),
        true,
    );
}
