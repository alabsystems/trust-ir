// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordinary kernel-checked dependent logic through the execution allocator.
//! These tests install no alternate byte semantics or trusted declarations.

use super::*;
use crate::proof_assembly::{ProofAssembly, ProofLimits, ScopedProofCandidate};

fn limits() -> Limits {
    Limits {
        max_operations: 1_000,
        max_locals: 32,
        max_list_items: 100,
        max_lookup_candidates: 100,
        lookup_heartbeats: 1_000_000,
        lookup_cache_entries: 16_384,
    }
}

fn witness_premise(logic: &mut ProofAssembly) -> ScopedProofCandidate {
    let predicate = Expr::lam(
        clean_kernel::BinderInfo::Default,
        constant("Nat"),
        eq(&constant("Nat"), Expr::bvar(0), nat(9)),
    );
    let goal = Expr::apps(
        Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(Level::zero())],
        ),
        [constant("Nat"), predicate.clone()],
    );
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Exists.intro"),
            vec![Level::succ(Level::zero())],
        ),
        [
            constant("Nat"),
            predicate,
            nat(9),
            refl(&constant("Nat"), nat(9)),
        ],
    );
    logic.candidate(goal, proof).unwrap()
}

fn environment() -> Environment {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_nat().unwrap();
    env.init_exists().unwrap();
    env
}

#[test]
fn execution_allocator_composes_nested_dependent_logic_in_the_same_scope() {
    let mut scope = Scope::new();
    let mut logic = ProofAssembly::new(ProofLimits::default()).unwrap();
    let premise = witness_premise(&mut logic);
    let goal = Expr::pi(
        clean_kernel::BinderInfo::Default,
        constant("Nat"),
        premise.proposition().clone(),
    );
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let mut expired = None;
    let proof = logic
        .introduce_forall(
            &mut assembler,
            goal.clone(),
            |logic, assembler, parameter, instance| {
                assert!(assembler.local_scope().owns(&parameter));
                logic.eliminate_exists(
                    assembler,
                    &premise,
                    instance.clone(),
                    |logic, assembler, witness, evidence| {
                        assert!(assembler.local_scope().owns(&witness));
                        expired = Some(evidence.clone());
                        logic.introduce_exists(instance.clone(), witness.term().clone(), &evidence)
                    },
                )
            },
        )
        .unwrap();
    assert_eq!(
        assembler.locals, 3,
        "forall + witness + dependent evidence share one budget"
    );
    assert_eq!(assembler.operations, 3);
    assert_eq!(assembler.local_scope().allocated(), 3);
    assert!(logic.check_live(&expired.unwrap()).is_err());
    let proof = assembler.local_scope().close(proof.term()).unwrap();
    let env = environment();
    let checker = TypeChecker::new(&env);
    checker
        .check_type(&goal, &Expr::sort(Level::zero()))
        .unwrap();
    checker.check_type(&proof, &goal).unwrap();
    let audit = env.audit_certification(&goal, &proof);
    assert!(audit.is_certified(), "{audit:#?}");
    for name in &audit.dependencies {
        assert!(env.axiom_deps(name).unwrap().is_empty());
        assert!(env.trust_marker_deps(name).unwrap().is_empty());
    }
    let wrong = Expr::pi(
        clean_kernel::BinderInfo::Default,
        constant("Nat"),
        eq(&constant("Nat"), Expr::bvar(0), nat(9)),
    );
    let error = checker.check_type(&proof, &wrong).unwrap_err();
    assert!(matches!(
        error,
        clean_kernel::KernelTypeError::TypeMismatch { .. }
    ));
}

#[test]
fn dependent_witnesses_cannot_exceed_execution_caps_before_allocation() {
    for local_limit in [true, false] {
        let mut scope = Scope::new();
        let preexisting = scope.try_local(constant("Nat")).unwrap();
        let mut limits = limits();
        if local_limit {
            limits.max_locals = 1;
        } else {
            limits.max_operations = 1;
        }
        let mut assembler = Assembler::new(&mut scope, limits).unwrap();
        let mut logic = ProofAssembly::new(ProofLimits::default()).unwrap();
        let premise = witness_premise(&mut logic);
        let result = logic.eliminate_exists(
            &mut assembler,
            &premise,
            premise.proposition().clone(),
            |_, _, _, _| panic!("evidence allocation must refuse before continuation"),
        );
        assert!(result.is_err());
        assert!(assembler.local_scope().owns(&preexisting));
        assert_eq!(assembler.locals, 1);
        assert_eq!(assembler.local_scope().allocated(), 2);
        assert!(assembler.local(constant("Nat")).is_err());
        assert_eq!(assembler.local_scope().allocated(), 2);
        assert!(logic.in_root_context());
    }
}

#[test]
fn errors_and_unwind_preserve_consumed_execution_budgets_and_expire_facts() {
    let mut scope = Scope::new();
    let mut limits = limits();
    limits.max_locals = 6;
    let mut assembler = Assembler::new(&mut scope, limits).unwrap();
    let mut logic = ProofAssembly::new(ProofLimits::default()).unwrap();
    let premise = witness_premise(&mut logic);
    let mut failed = None;
    let result = logic.eliminate_exists(
        &mut assembler,
        &premise,
        premise.proposition().clone(),
        |_, assembler, _, evidence| {
            failed = Some(evidence);
            assembler.local(constant("Nat"))?;
            Err("deliberate nested execution error".into())
        },
    );
    assert!(result.is_err());
    assert_eq!(assembler.locals, 3);
    let failed = failed.unwrap();
    assert!(logic.check_live(&failed).is_err());
    let mut panicked = None;
    let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = logic.eliminate_exists(
            &mut assembler,
            &premise,
            premise.proposition().clone(),
            |_, assembler, witness, evidence| {
                panicked = Some((witness, evidence));
                assembler.local(constant("Nat"))?;
                panic!("deliberate nested execution unwind")
            },
        );
    }));
    assert!(unwind.is_err());
    assert!(logic.in_root_context());
    let (witness, evidence) = panicked.unwrap();
    assert!(assembler.local_scope().owns(&witness));
    assert!(logic.check_live(&evidence).is_err());
    assert_eq!(assembler.locals, 6);
    assert_eq!(assembler.operations, 6);
    assert_eq!(assembler.local_scope().allocated(), 6);
    assert!(assembler.local(constant("Nat")).is_err());
    assert_eq!(assembler.local_scope().allocated(), 6);
    logic.check_live(&premise).unwrap();
}
