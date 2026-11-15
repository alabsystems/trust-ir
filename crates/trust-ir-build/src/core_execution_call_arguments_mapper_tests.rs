// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual known-call argument transport. The list equality is an explicit
//! premise, never provider fidelity, call admission or a source execution.

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
    resolved: PendingEquality,
    parameters: Vec<Local>,
    wrong_binding: Expr,
    wrong_site: Expr,
    wrong_world: Expr,
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
        providers: local(app("IRByteProvidersV1", [world_type.clone()])),
    };
    let target = CallTarget {
        context: model.context.clone(),
        function_id: nat(55),
        binding: local(constant("IRByteFunctionV1")),
        signature: local(constant("IRByteSignatureV1")),
    };
    let current = Current {
        frame: local(constant("IRFrame")),
        tail: local(app("IRList", [constant("IRFrame")])),
        legacy_memory: local(app("IRList", [constant("IRMemSlot")])),
        legacy_cursor: local(constant("Nat")),
        world: local(app("IRByteWorldV1", [world_type.clone()])),
    };
    let site = FetchedSite {
        context: model.context.clone(),
        coordinate: Coordinate {
            function: FuncId::new(41),
            block: BlockId::new(13),
            instruction: 9,
        },
        function: constant("unused_argument_mapper_function"),
        block: constant("unused_argument_mapper_block"),
        node: constant("unused_argument_mapper_node"),
        instruction: constant("unused_argument_mapper_instruction"),
        results: local(app("IRList", [constant("Nat")])),
        site: local(constant("IRByteSiteV1")),
    };
    let ty = app("IRList", [constant("IRScalar")]);
    let left = local(ty.clone());
    let right = local(ty.clone());
    let proof = local(eq(&ty, left.clone(), right.clone()));
    let wrong_binding = local(constant("IRByteFunctionV1"));
    let wrong_site = local(constant("IRByteSiteV1"));
    let wrong_world = local(app("IRByteWorldV1", [world_type]));
    Fixture {
        model,
        target,
        site,
        current,
        resolved: PendingEquality::candidate(ty, left, right, proof),
        parameters,
        wrong_binding,
        wrong_site,
        wrong_world,
    }
}

fn known(f: &Fixture, binding: Expr, site: Expr, current: &Current, values: Expr) -> Expr {
    // Independent full application, not the production partial function.
    app(
        "ir_byte_call_known_v1",
        [
            f.model.world_type.clone(),
            f.model.context.clone(),
            f.model.providers.clone(),
            current.machine(),
            current.world.clone(),
            f.site.results.clone(),
            site,
            binding,
            f.target.signature.clone(),
            values,
        ],
    )
}

fn endpoint(f: &Fixture, values: Expr) -> Expr {
    known(
        f,
        f.target.binding.clone(),
        f.site.site.clone(),
        &f.current,
        values,
    )
}

fn check_closed(term: Expr, claim: Expr, accepted: bool) {
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    assert!(!term.has_loose_bvars_quick() && !claim.has_loose_bvars_quick());
    let environment = shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env();
    let decoded_term = trust_ir::proof::decode_clean_expr_dag_v2(
        &trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap(),
    )
    .unwrap();
    let decoded_claim = trust_ir::proof::decode_clean_expr_dag_v2(
        &trust_ir::proof::encode_clean_expr_dag_v2(&claim).unwrap(),
    )
    .unwrap();
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
                "{error:?}"
            );
        }
        assert!(
            !checker.heartbeat_spent(),
            "exhaustion is not a semantic refusal"
        );
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
fn known_argument_mapper_repeats_at_exhausted_local_cap_without_refunding_operations() {
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
            .target
            .map_known_arguments(
                &mut assembler,
                &f.model,
                &f.current,
                &f.site,
                f.resolved.clone(),
            )
            .unwrap();
        assert_eq!((assembler.operations, assembler.locals), (ordinal + 2, 1));
        let arguments = proof.term().get_app_args();
        assert_eq!(
            arguments[4].get_app_fn(),
            &constant("ir_byte_call_known_v1")
        );
        assert_eq!(arguments[4].get_app_args().len(), 9);
        assert_eq!(arguments[5], f.resolved.term());
        drop(arguments);
        assert_eq!(
            proof.proposition(),
            eq(
                &f.model.config_type(),
                endpoint(&f, f.resolved.left().clone()),
                endpoint(&f, f.resolved.right().clone()),
            )
        );
        last = Some(proof);
    }
    assert_eq!(assembler.local_scope().allocated(), f.parameters.len() + 1);
    let error = f
        .target
        .map_known_arguments(
            &mut assembler,
            &f.model,
            &f.current,
            &f.site,
            f.resolved.clone(),
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
fn known_argument_mapper_retains_actual_binding_site_world_and_supplied_equality() {
    let mut scope = Scope::new();
    let f = fixture(&mut scope);
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let proof = f
        .target
        .map_known_arguments(
            &mut assembler,
            &f.model,
            &f.current,
            &f.site,
            f.resolved.clone(),
        )
        .unwrap();
    let mut wrong_current = f.current.clone();
    wrong_current.world = f.wrong_world.clone();
    for right in [
        known(
            &f,
            f.wrong_binding.clone(),
            f.site.site.clone(),
            &f.current,
            f.resolved.right().clone(),
        ),
        known(
            &f,
            f.target.binding.clone(),
            f.wrong_site.clone(),
            &f.current,
            f.resolved.right().clone(),
        ),
        known(
            &f,
            f.target.binding.clone(),
            f.site.site.clone(),
            &wrong_current,
            f.resolved.right().clone(),
        ),
    ] {
        replay(
            assembler.local_scope(),
            &f.parameters,
            proof.term().clone(),
            eq(
                &f.model.config_type(),
                endpoint(&f, f.resolved.left().clone()),
                right,
            ),
            false,
        );
    }
    let forged = PendingEquality::candidate(
        f.resolved.ty.clone(),
        f.resolved.left().clone(),
        f.resolved.right().clone(),
        refl(&f.resolved.ty, f.resolved.left().clone()),
    );
    let forged = f
        .target
        .map_known_arguments(&mut assembler, &f.model, &f.current, &f.site, forged)
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
fn known_argument_mapper_neither_escapes_premise_nor_grants_call_or_validity_authority() {
    let mut scope = Scope::new();
    let f = fixture(&mut scope);
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let proof = f
        .target
        .map_known_arguments(
            &mut assembler,
            &f.model,
            &f.current,
            &f.site,
            f.resolved.clone(),
        )
        .unwrap();
    replay(
        assembler.local_scope(),
        &f.parameters,
        proof.term().clone(),
        proof.proposition(),
        true,
    );
    let missing = f
        .parameters
        .iter()
        .filter(|local| local.term() != f.resolved.term())
        .rev()
        .fold(proof.term().clone(), |body, local| local.lam(body));
    assert!(matches!(
        assembler.local_scope().close(&missing),
        Err(crate::scoped_local::LocalScopeError::Closure(
            crate::term_scope::TermScopeError::OutOfScope(_)
        ))
    ));
    for predicate in [
        f.current.valid(&f.model),
        f.target
            .admission(&f.model, &f.site, f.resolved.right().clone()),
    ] {
        replay(
            assembler.local_scope(),
            &f.parameters,
            proof.term().clone(),
            eq(&constant("Bool"), predicate, constant("Bool.true")),
            false,
        );
    }
}

#[test]
fn known_argument_mapper_keeps_external_type_provider_world_and_list_bvars_uncaptured() {
    let mut scope = Scope::new();
    let mut f = fixture(&mut scope);
    // Build the mapper before the twelve ordinary binders below are present.
    f.model.world_type = Expr::bvar(11);
    f.model.context = Expr::bvar(10);
    f.model.providers = Expr::bvar(9);
    f.current.frame = Expr::bvar(8);
    f.current.tail = list("IRFrame", &[]);
    f.current.legacy_memory = list("IRMemSlot", &[]);
    f.current.legacy_cursor = nat(0);
    f.current.world = Expr::bvar(7);
    f.site.results = Expr::bvar(6);
    f.site.site = Expr::bvar(5);
    f.target.binding = Expr::bvar(4);
    f.target.signature = Expr::bvar(3);
    f.resolved = PendingEquality::candidate(
        app("IRList", [constant("IRScalar")]),
        Expr::bvar(2),
        Expr::bvar(1),
        Expr::bvar(0),
    );
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let proof = f
        .target
        .map_known_arguments(
            &mut assembler,
            &f.model,
            &f.current,
            &f.site,
            f.resolved.clone(),
        )
        .unwrap();
    assert_eq!((assembler.operations, assembler.locals), (1, 0));
    let domains = [
        Expr::type_(),
        constant("IRByteContextV1"),
        app("IRByteProvidersV1", [Expr::bvar(1)]),
        constant("IRFrame"),
        app("IRByteWorldV1", [Expr::bvar(3)]),
        app("IRList", [constant("Nat")]),
        constant("IRByteSiteV1"),
        constant("IRByteFunctionV1"),
        constant("IRByteSignatureV1"),
        app("IRList", [constant("IRScalar")]),
        app("IRList", [constant("IRScalar")]),
        eq(
            &app("IRList", [constant("IRScalar")]),
            Expr::bvar(1),
            Expr::bvar(0),
        ),
    ];
    let term = domains.iter().rev().fold(proof.term().clone(), |body, ty| {
        Expr::lam(BinderInfo::Default, ty.clone(), body)
    });
    let independent = eq(
        &f.model.config_type(),
        endpoint(&f, f.resolved.left().clone()),
        endpoint(&f, f.resolved.right().clone()),
    );
    let claim = domains.iter().rev().fold(independent, |body, ty| {
        Expr::pi(BinderInfo::Default, ty.clone(), body)
    });
    check_closed(
        assembler.local_scope().close(&term).unwrap(),
        assembler.local_scope().close(&claim).unwrap(),
        true,
    );
}
