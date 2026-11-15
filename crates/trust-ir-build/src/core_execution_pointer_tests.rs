// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent kernel checks of both pure pointer claims. These tests install
//! no replacement semantics or axioms and make no fetched/native execution claim.

use super::*;
use crate::scoped_local::LocalScopeLimits;
use crate::{ModuleBuilder, core_reflection::reflect_core_module_v1};
use clean_kernel::KernelTypeError;
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{Endianness, StructPassingPolicy, TargetInfo, Ty};

fn environment() -> &'static Environment {
    shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .expect("canonical byte vocabulary")
        .env()
}

fn checker() -> TypeChecker<'static> {
    let mut checker = TypeChecker::new(environment());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(5_000_000);
    checker.set_max_cache_entries(100_000);
    checker
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

fn context(ty: Ty, address: u64) -> Expr {
    let mut builder = ModuleBuilder::new_with_target_info(
        "pointer_word_context",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![ty.clone()], vec![ty.clone()]);
    let function = builder.declare_function("identity", signature);
    let mut body = builder.define_function(function).unwrap();
    let block = body.create_block();
    let argument = body.add_block_param(block, ty);
    body.switch_to_block(block);
    body.ret(vec![argument]);
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(crate::validate_module(&module).is_empty());
    reflect_core_module_v1(&module, &[(function, address)])
        .unwrap()
        .context_term()
        .clone()
}

fn canonical(word: Expr) -> PendingEquality {
    PendingEquality::candidate(
        constant("Bool"),
        word_guard(word),
        constant("Bool.true"),
        refl(&constant("Bool"), constant("Bool.true")),
    )
}

fn replay_terms(scope: &Scope, claim: Expr, proof: Expr, accepted: bool) {
    let claim = scope.close(&claim).unwrap();
    let proof = scope.close(&proof).unwrap();
    assert!(!claim.has_fvar_quick() && !proof.has_fvar_quick());
    let checker = checker();
    checker
        .check_type(&claim, &Expr::sort(Level::zero()))
        .expect("a semantic negative must still have a well-typed claim");
    if accepted {
        checker.check_type(&proof, &claim).unwrap();
        let audit = environment().audit_certification(&claim, &proof);
        assert!(audit.is_certified(), "{audit:#?}");
    } else {
        let error = checker.check_type(&proof, &claim).unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "{error:?}"
        );
    }
}

fn replay(scope: &Scope, candidate: &PendingEquality, accepted: bool) {
    replay_terms(
        scope,
        candidate.proposition(),
        candidate.term().clone(),
        accepted,
    );
}

#[test]
fn pointer_word_canonical_zero_one_high_bit_and_max_audit_both_claims() {
    let ctx = context(Ty::I64, 4096);
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    for word in [0, 1, 1_u64 << 63, u64::MAX] {
        let result = assembler
            .byte_pointer_word(ctx.clone(), nat(word), canonical(nat(word)))
            .unwrap();
        let expected = if word == 0 {
            constant("IRScalar.nullptr_")
        } else {
            app("IRScalar.ptr_", [nat(word)])
        };
        // Independently require the canonical value and both public claims;
        // accepting the address projection alone would miss ptr_(0) fitting.
        replay(
            assembler.local_scope(),
            &PendingEquality::candidate(
                constant("IRScalar"),
                result.value.clone(),
                expected.clone(),
                refl(&constant("IRScalar"), expected.clone()),
            ),
            true,
        );
        replay(
            assembler.local_scope(),
            &PendingEquality::candidate(
                app("IROption", [constant("Nat")]),
                app("ir_byte_pointer_address_v1", [expected.clone()]),
                some("Nat", nat(word)),
                result.address.term().clone(),
            ),
            true,
        );
        replay(
            assembler.local_scope(),
            &PendingEquality::candidate(
                constant("Bool"),
                app(
                    "ir_byte_value_matches_v1",
                    [ctx.clone(), constant("IRTy.ptr_"), expected],
                ),
                constant("Bool.true"),
                result.fits.term().clone(),
            ),
            true,
        );
        replay(assembler.local_scope(), &result.address, true);
        replay(assembler.local_scope(), &result.fits, true);
    }
}

#[test]
fn pointer_word_symbolic_context_and_canonical_word_close_and_audit() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let ctx = assembler.local(constant("IRByteContextV1")).unwrap();
    let word = assembler.local(constant("Nat")).unwrap();
    let guard = word_guard(word.term().clone());
    let premise = assembler
        .local(eq(&constant("Bool"), guard.clone(), constant("Bool.true")))
        .unwrap();
    let result = assembler
        .byte_pointer_word(
            ctx.term().clone(),
            word.term().clone(),
            PendingEquality::candidate(
                constant("Bool"),
                guard,
                constant("Bool.true"),
                premise.term().clone(),
            ),
        )
        .unwrap();
    assert!(
        !assembler
            .byte_pointer_word_candidate
            .as_ref()
            .unwrap()
            .has_fvar_quick()
    );
    for candidate in [&result.address, &result.fits] {
        replay_terms(
            assembler.local_scope(),
            ctx.pi(word.pi(premise.pi(candidate.proposition()))),
            ctx.lam(word.lam(premise.lam(candidate.term().clone()))),
            true,
        );
    }
    // The output contains this caller's actual word, not a template-local ID.
    assert_eq!(result.value, pointer_value(word.term().clone()));
}

#[test]
fn pointer_word_cache_reuses_closed_template_for_changed_actual_context_and_word() {
    let first_context = context(Ty::I64, 4096);
    let second_context = context(Ty::I32, 8192);
    assert_ne!(first_context, second_context);
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    assert!(assembler.byte_pointer_word_candidate.is_none());
    let first = assembler
        .byte_pointer_word(first_context.clone(), nat(1), canonical(nat(1)))
        .unwrap();
    let cached = assembler.byte_pointer_word_candidate.clone().unwrap();
    assert!(!cached.has_fvar_quick());
    let old_locals = assembler.locals;
    let old_allocated = assembler.local_scope().allocated();
    let old_operations = assembler.operations;
    let next_word = nat(1_u64 << 63);
    let next_bound = canonical(next_word.clone());
    let second = assembler
        .byte_pointer_word(
            second_context.clone(),
            next_word.clone(),
            next_bound.clone(),
        )
        .unwrap();
    assert_eq!(assembler.locals, old_locals);
    assert_eq!(assembler.local_scope().allocated(), old_allocated);
    assert_eq!(assembler.operations, old_operations + 1);
    assert_eq!(
        assembler.byte_pointer_word_candidate.as_ref(),
        Some(&cached)
    );
    for projection in [&second.address, &second.fits] {
        let projected = projection.term().get_app_args();
        assert_eq!(projected.len(), 3);
        let invocation = projected[2];
        assert_eq!(invocation.get_app_fn(), &cached);
        let arguments = invocation.get_app_args();
        assert_eq!(arguments.len(), 3);
        assert_eq!(arguments[0], &second_context);
        assert_eq!(arguments[1], &next_word);
        assert_eq!(arguments[2], next_bound.term());
        replay(assembler.local_scope(), projection, true);
    }
    replay(assembler.local_scope(), &first.address, true);
    replay(assembler.local_scope(), &first.fits, true);
    replay_terms(
        assembler.local_scope(),
        second.address.proposition(),
        first.address.term().clone(),
        false,
    );
    // A changed context alone is NOT a semantic refusal for Ptr: this scalar
    // profile is context independent. Require exact retained arguments above,
    // and do not call equivalent true fit claims a negative control.
    replay_terms(
        assembler.local_scope(),
        second.fits.proposition(),
        first.fits.term().clone(),
        true,
    );
}

#[test]
fn pointer_word_rejects_changed_canonical_endpoints_before_caching() {
    let ctx = context(Ty::I64, 4096);
    let expected = canonical(nat(7));
    for changed in [
        PendingEquality::candidate(
            constant("Nat"),
            expected.left().clone(),
            expected.right().clone(),
            expected.term().clone(),
        ),
        canonical(nat(8)),
        PendingEquality::candidate(
            constant("Bool"),
            expected.left().clone(),
            constant("Bool.false"),
            expected.term().clone(),
        ),
    ] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let error = assembler
            .byte_pointer_word(ctx.clone(), nat(7), changed)
            .err()
            .unwrap();
        assert!(error.contains("equality"), "{error}");
        assert_eq!(assembler.operations, 1);
        assert_eq!(assembler.locals, 0);
        assert!(assembler.byte_pointer_word_candidate.is_none());
    }
}

#[test]
fn pointer_word_false_forged_and_noncanonical_bounds_reach_type_mismatch() {
    let ctx = context(Ty::I64, 4096);
    for (word, proof) in [
        (nat(0), refl(&constant("Bool"), constant("Bool.false"))),
        (nat(7), nat(0)),
        (
            app("ir_nat_pow2", [nat(64)]),
            refl(&constant("Bool"), constant("Bool.true")),
        ),
    ] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let result = assembler
            .byte_pointer_word(
                ctx.clone(),
                word.clone(),
                PendingEquality::candidate(
                    constant("Bool"),
                    word_guard(word),
                    constant("Bool.true"),
                    proof,
                ),
            )
            .unwrap();
        // Endpoints alone must not authorize either result, even for zero,
        // whose resulting semantic equations happen to be independently true.
        replay(assembler.local_scope(), &result.address, false);
        replay(assembler.local_scope(), &result.fits, false);
    }
}

#[test]
fn pointer_word_malformed_word_is_a_claim_typing_refusal_not_semantic_evidence() {
    let ctx = context(Ty::I64, 4096);
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let malformed = app("IRScalar.int_", [nat(7)]);
    let result = assembler
        .byte_pointer_word(ctx, malformed.clone(), canonical(malformed))
        .unwrap();
    for candidate in [&result.address, &result.fits] {
        let claim = assembler
            .local_scope()
            .close(&candidate.proposition())
            .unwrap();
        assert!(!claim.has_fvar_quick());
        let error = checker()
            .check_type(&claim, &Expr::sort(Level::zero()))
            .unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "{error:?}"
        );
    }
}

#[test]
fn pointer_word_null_address_does_not_authorize_noncanonical_ptr_zero() {
    let ctx = context(Ty::I64, 4096);
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let result = assembler
        .byte_pointer_word(ctx.clone(), nat(0), canonical(nat(0)))
        .unwrap();
    replay(assembler.local_scope(), &result.address, true);
    replay(assembler.local_scope(), &result.fits, true);
    let wrong_value = app("IRScalar.ptr_", [nat(0)]);
    replay(
        assembler.local_scope(),
        &PendingEquality::candidate(
            constant("IRScalar"),
            result.value,
            wrong_value.clone(),
            refl(&constant("IRScalar"), constant("IRScalar.nullptr_")),
        ),
        false,
    );
    // pointer_address accepts ptr_(0), but the independently checked fitting
    // claim rejects it. Address recovery is deliberately weaker than fitting.
    replay(
        assembler.local_scope(),
        &PendingEquality::candidate(
            app("IROption", [constant("Nat")]),
            pointer_address(wrong_value.clone()),
            some("Nat", nat(0)),
            result.address.term().clone(),
        ),
        true,
    );
    replay(
        assembler.local_scope(),
        &PendingEquality::candidate(
            constant("Bool"),
            pointer_fits(ctx, wrong_value),
            constant("Bool.true"),
            result.fits.term().clone(),
        ),
        false,
    );
}

#[test]
fn pointer_word_operation_local_and_shared_scope_budgets_remain_fail_closed() {
    let ctx = context(Ty::I64, 4096);
    for operation_limited in [true, false] {
        let mut scope = Scope::new();
        let mut policy = limits();
        if operation_limited {
            policy.max_operations = 1;
        } else {
            policy.max_locals = 1;
        }
        let mut assembler = Assembler::new(&mut scope, policy).unwrap();
        let error = assembler
            .byte_pointer_word(ctx.clone(), nat(7), canonical(nat(7)))
            .err()
            .unwrap();
        assert!(
            error.contains(if operation_limited {
                "operation budget"
            } else {
                "local budget"
            }),
            "{error}"
        );
        assert!(assembler.byte_pointer_word_candidate.is_none());
        assert!(assembler.operations <= policy.max_operations);
        assert!(assembler.locals <= policy.max_locals);
    }

    let mut scope = Scope::with_limits(LocalScopeLimits {
        max_locals: 1,
        ..LocalScopeLimits::default()
    });
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let error = assembler
        .byte_pointer_word(ctx.clone(), nat(7), canonical(nat(7)))
        .err()
        .unwrap();
    assert!(error.contains("named local allocation limit"), "{error}");
    assert_eq!(assembler.local_scope().allocated(), 1);
    assert!(assembler.byte_pointer_word_candidate.is_none());
    drop(assembler);

    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    assembler
        .byte_pointer_word(ctx.clone(), nat(1), canonical(nat(1)))
        .unwrap();
    // A warmed helper needs one API operation and no further template locals.
    // Narrow the test policy to those exact remaining resources, never widen it.
    assembler.limits.max_locals = assembler.locals;
    assembler.limits.max_operations = assembler.operations + 1;
    let before_locals = assembler.locals;
    let result = assembler
        .byte_pointer_word(ctx.clone(), nat(7), canonical(nat(7)))
        .unwrap();
    assert_eq!(assembler.locals, before_locals);
    replay(assembler.local_scope(), &result.address, true);
    replay(assembler.local_scope(), &result.fits, true);
    let error = assembler
        .byte_pointer_word(ctx, nat(8), canonical(nat(8)))
        .err()
        .unwrap();
    assert!(error.contains("operation budget"), "{error}");
}
