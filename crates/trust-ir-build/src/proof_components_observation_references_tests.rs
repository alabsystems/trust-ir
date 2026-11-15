// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
use clean_kernel::{Environment, Level};
fn n() -> Expr {
    Expr::const_str("Nat")
}
fn parts(scope: &LocalScope, operations: usize) -> ProofComponents {
    let mut parts = ProofComponents::new(
        "generated.observation",
        ProofLimits {
            operations,
            ..Default::default()
        },
    );
    parts.set_base(scope, vec![]).unwrap();
    parts
}
#[derive(Clone, Copy)]
enum ReferencePolicy {
    Nested,
    RootOnly,
    SharedChildren,
}
fn references(
    owner: &mut ProofComponents,
    scope: &LocalScope,
    policy: ReferencePolicy,
) -> ObservationReferences {
    match policy {
        ReferencePolicy::Nested => owner.observation_references(scope),
        ReferencePolicy::RootOnly => owner.observation_references_root_only(scope),
        ReferencePolicy::SharedChildren => owner.observation_references_shared_children(scope),
    }
    .unwrap()
}
fn chain(mut root: Expr, count: usize) -> Expr {
    for _ in 0..count {
        root = Expr::app(Expr::const_str("Nat.succ"), root);
    }
    root
}

#[test]
fn shared_children_bitmap_factory_prepays_every_storage_prefix_before_publication() {
    let scope = LocalScope::new();
    let operations = 100_000;
    let required = 3 + generated_references::Memo::hash_filter_words(operations) + 1;
    for remaining in 0..=required + 1 {
        let mut owner = parts(&scope, operations);
        let available = owner.context_work_remaining().unwrap();
        owner.spend_context_work(available - remaining).unwrap();
        let before = owner.counts().3;
        let identity = owner.external_context_owner.as_ref().map(Arc::as_ptr);
        let result = owner.observation_references_shared_children(&scope);
        assert_eq!(
            result.is_ok(),
            remaining >= required,
            "remaining={remaining}"
        );
        assert!(owner.counts().3 - before <= remaining);
        if let Ok(memo) = result {
            assert_eq!(owner.counts().3 - before, required);
            assert!(memo.diagnostics().contains("bitmap_words=128"));
        } else {
            assert_eq!(
                owner.external_context_owner.as_ref().map(Arc::as_ptr),
                identity
            );
        }
    }
}

#[test]
fn generated_observation_keeps_all_input_refs_and_rechecks_changed_forbidden_sets() {
    check_generated_observation_keeps_all_input_refs_and_rechecks_changed_forbidden_sets(
        ReferencePolicy::Nested,
    );
}

#[test]
fn root_only_generated_observation_keeps_all_input_refs_and_rechecks_changed_forbidden_sets() {
    check_generated_observation_keeps_all_input_refs_and_rechecks_changed_forbidden_sets(
        ReferencePolicy::RootOnly,
    );
}

fn check_generated_observation_keeps_all_input_refs_and_rechecks_changed_forbidden_sets(
    policy: ReferencePolicy,
) {
    let mut scope = LocalScope::new();
    let callback = scope.try_local(n()).unwrap();
    let formal = scope.try_local(n()).unwrap();
    let root = formal.lam(chain(formal.term().clone(), 80));
    let mut parts = parts(&scope, 100_000);
    let mut memo = references(&mut parts, &scope, policy);
    let token = parts.constructed_observation(&scope, &memo, &root).unwrap();
    let before = parts.counts().3;
    parts
        .charged_constructed_observation_independent_of(
            &scope,
            &mut memo,
            &token,
            &root,
            &[callback.clone()],
        )
        .unwrap();
    let cold = parts.counts().3 - before;
    let before = parts.counts().3;
    parts
        .charged_constructed_observation_independent_of(
            &scope,
            &mut memo,
            &token,
            &root,
            &[callback],
        )
        .unwrap();
    assert!(parts.counts().3 - before < cold);
    // Bound formals are syntactic occurrences too. Neither a later forbidden
    // set nor scope shadow growth can turn their earlier summary into empty.
    let error = parts
        .charged_constructed_observation_independent_of(
            &scope,
            &mut memo,
            &token,
            &root,
            &[formal.clone()],
        )
        .unwrap_err();
    assert!(error.contains("depends on final"));
    assert!(
        scope
            .close_external_forest(&[root], &[formal], &[1])
            .0
            .is_err()
    );
    assert!(
        parts
            .constructed_observation(&scope, &memo, &Expr::nat_lit(0))
            .is_err()
    );
}

#[test]
fn generated_observation_rejects_foreign_replay_component_scope_and_graph() {
    check_generated_observation_rejects_foreign_replay_component_scope_and_graph(
        ReferencePolicy::Nested,
    );
}

#[test]
fn root_only_generated_observation_rejects_foreign_replay_component_scope_and_graph() {
    check_generated_observation_rejects_foreign_replay_component_scope_and_graph(
        ReferencePolicy::RootOnly,
    );
}

fn check_generated_observation_rejects_foreign_replay_component_scope_and_graph(
    policy: ReferencePolicy,
) {
    let mut scope = LocalScope::new();
    let a = scope.try_local(n()).unwrap();
    let root = a.term().clone();
    let mut owner = parts(&scope, 100_000);
    let mut one = references(&mut owner, &scope, policy);
    let token = owner.constructed_observation(&scope, &one, &root).unwrap();
    let mut two = references(&mut owner, &scope, policy);
    assert!(
        owner
            .charged_constructed_observation_independent_of(&scope, &mut two, &token, &root, &[])
            .unwrap_err()
            .contains("another replay")
    );
    let mut other = parts(&scope, 100_000);
    assert!(
        other
            .charged_constructed_observation_independent_of(&scope, &mut one, &token, &root, &[])
            .is_err()
    );
    let mut foreign = LocalScope::new();
    let same_id = foreign.try_local(n()).unwrap();
    assert_eq!(same_id.id(), a.id());
    assert!(
        owner
            .charged_constructed_observation_independent_of(&foreign, &mut one, &token, &root, &[])
            .is_err()
    );
    assert!(
        owner
            .charged_constructed_observation_independent_of(
                &scope,
                &mut one,
                &token,
                &Expr::nat_lit(0),
                &[]
            )
            .is_err()
    );
    owner
        .charged_constructed_observation_independent_of(&scope, &mut one, &token, &root, &[])
        .unwrap();
}

#[test]
fn generated_observation_first_query_checks_embedded_input_and_loose_capture() {
    check_generated_observation_first_query_checks_embedded_input_and_loose_capture(
        ReferencePolicy::Nested,
    );
}

#[test]
fn root_only_generated_observation_first_query_checks_embedded_input_and_loose_capture() {
    check_generated_observation_first_query_checks_embedded_input_and_loose_capture(
        ReferencePolicy::RootOnly,
    );
}

fn check_generated_observation_first_query_checks_embedded_input_and_loose_capture(
    policy: ReferencePolicy,
) {
    let mut scope = LocalScope::new();
    let callback = scope.try_local(n()).unwrap();
    let mut parts = parts(&scope, 100_000);
    let mut memo = references(&mut parts, &scope, policy);
    let root = chain(callback.term().clone(), 300);
    let token = parts.constructed_observation(&scope, &memo, &root).unwrap();
    assert!(
        parts
            .charged_constructed_observation_independent_of(
                &scope,
                &mut memo,
                &token,
                &root,
                &[callback]
            )
            .unwrap_err()
            .contains("depends on final")
    );
    let mut fresh = references(&mut parts, &scope, policy);
    let root = Expr::bvar(0);
    let token = parts
        .constructed_observation(&scope, &fresh, &root)
        .unwrap();
    assert!(
        parts
            .charged_constructed_observation_independent_of(&scope, &mut fresh, &token, &root, &[])
            .unwrap_err()
            .contains("loose bound")
    );
    assert!(
        parts
            .constructed_observation(&scope, &fresh, &Expr::nat_lit(0))
            .is_err()
    );
}

#[test]
fn generated_observation_full_input_height_checks_deeper_reuse_even_without_fvars() {
    check_generated_observation_full_input_height_checks_deeper_reuse_even_without_fvars(
        ReferencePolicy::Nested,
    );
}

#[test]
fn root_only_generated_observation_full_input_height_checks_deeper_reuse_even_without_fvars() {
    check_generated_observation_full_input_height_checks_deeper_reuse_even_without_fvars(
        ReferencePolicy::RootOnly,
    );
}

fn check_generated_observation_full_input_height_checks_deeper_reuse_even_without_fvars(
    policy: ReferencePolicy,
) {
    let scope = LocalScope::new();
    let mut parts = parts(&scope, 500_000);
    let mut memo = references(&mut parts, &scope, policy);
    let root = chain(Expr::nat_lit(0), 300);
    let token = parts.constructed_observation(&scope, &memo, &root).unwrap();
    parts
        .charged_constructed_observation_independent_of(&scope, &mut memo, &token, &root, &[])
        .unwrap();
    let parent = chain(root, 16_084); // 16,385 complete nodes along this path.
    let token = parts
        .constructed_observation(&scope, &memo, &parent)
        .unwrap();
    assert!(
        parts
            .charged_constructed_observation_independent_of(&scope, &mut memo, &token, &parent, &[])
            .unwrap_err()
            .contains("depth limit")
    );
    assert!(
        parts
            .constructed_observation(&scope, &memo, &Expr::nat_lit(0))
            .is_err()
    );
}

#[test]
fn generated_observation_failed_cold_scan_is_paid_poisoned_and_raw_inputs_stay_fresh() {
    check_generated_observation_failed_cold_scan_is_paid_poisoned_and_raw_inputs_stay_fresh(
        ReferencePolicy::Nested,
    );
}

#[test]
fn root_only_generated_observation_failed_cold_scan_is_paid_poisoned_and_raw_inputs_stay_fresh() {
    check_generated_observation_failed_cold_scan_is_paid_poisoned_and_raw_inputs_stay_fresh(
        ReferencePolicy::RootOnly,
    );
}

fn check_generated_observation_failed_cold_scan_is_paid_poisoned_and_raw_inputs_stay_fresh(
    policy: ReferencePolicy,
) {
    let mut scope = LocalScope::new();
    let a = scope.try_local(n()).unwrap();
    let callback = scope.try_local(n()).unwrap();
    let root = chain(a.term().clone(), 80);
    let mut owner = parts(&scope, 100_000);
    let mut memo = references(&mut owner, &scope, policy);
    let token = owner.constructed_observation(&scope, &memo, &root).unwrap();
    owner
        .charged_constructed_observation_independent_of(
            &scope,
            &mut memo,
            &token,
            &root,
            &[callback.clone()],
        )
        .unwrap();
    let before = owner.counts().3;
    owner
        .charged_independent_of(&scope, &[callback.clone()], &root)
        .unwrap();
    let first = owner.counts().3 - before;
    let before = owner.counts().3;
    owner
        .charged_independent_of(&scope, &[callback], &root)
        .unwrap();
    assert_eq!(owner.counts().3 - before, first);
    let mut small = parts(&scope, 80);
    let mut stopped = references(&mut small, &scope, policy);
    let token = small
        .constructed_observation(&scope, &stopped, &root)
        .unwrap();
    let before = small.counts().3;
    assert!(
        small
            .charged_constructed_observation_independent_of(
                &scope,
                &mut stopped,
                &token,
                &root,
                &[]
            )
            .is_err()
    );
    assert!(small.counts().3 > before);
    assert!(
        small
            .constructed_observation(&scope, &stopped, &Expr::nat_lit(0))
            .is_err()
    );
}

#[test]
fn generated_observation_typed_named_input_still_requires_original_decoded_kernel_replay() {
    check_generated_observation_typed_named_input_still_requires_original_decoded_kernel_replay(
        ReferencePolicy::Nested,
    );
}

#[test]
fn root_only_generated_observation_typed_named_input_still_requires_original_decoded_kernel_replay()
{
    check_generated_observation_typed_named_input_still_requires_original_decoded_kernel_replay(
        ReferencePolicy::RootOnly,
    );
}

fn check_generated_observation_typed_named_input_still_requires_original_decoded_kernel_replay(
    policy: ReferencePolicy,
) {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    let mut scope = LocalScope::new();
    let input = scope.try_local(n()).unwrap();
    let callback = scope.try_local(n()).unwrap();
    let formal = scope.try_local(n()).unwrap();
    let root = formal.lam(Expr::apps(
        Expr::const_str("Nat.add"),
        [input.term().clone(), formal.term().clone()],
    ));
    let ty = Expr::arrow(n(), n());
    let claim = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty.clone(), root.clone(), root.clone()],
    );
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, root.clone()],
    );
    let mut parts = parts(&scope, 100_000);
    parts
        .extend_base(OwnedProofCapture::Parameter(input.clone()))
        .unwrap();
    parts
        .extend_base(OwnedProofCapture::Parameter(callback.clone()))
        .unwrap();
    let mut memo = references(&mut parts, &scope, policy);
    let token = parts.constructed_observation(&scope, &memo, &root).unwrap();
    parts
        .charged_constructed_observation_independent_of(
            &scope,
            &mut memo,
            &token,
            &root,
            &[callback.clone()],
        )
        .unwrap();
    let closed_claim = scope.close(&input.pi(callback.pi(claim.clone()))).unwrap();
    let bundle = parts
        .close_scoped(
            &scope,
            input.lam(callback.lam(proof)),
            claim,
            crate::term_scope::TermScopeLimits::default(),
        )
        .unwrap();
    let bytes = bundle.encode_with_claim(&closed_claim).unwrap();
    let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(closed_claim, transported);
    decoded.replay(&env, &transported, 2_000_000).unwrap();
}

#[test]
fn exact_shared_multiword_observation_keeps_original_claim_and_rejects_same_proof_wrong_value() {
    check_exact_shared_multiword_observation_keeps_original_claim_and_rejects_same_proof_wrong_value(ReferencePolicy::Nested);
}

#[test]
fn root_only_exact_shared_multiword_observation_keeps_original_claim_and_rejects_same_proof_wrong_value()
 {
    check_exact_shared_multiword_observation_keeps_original_claim_and_rejects_same_proof_wrong_value(ReferencePolicy::RootOnly);
}

fn check_exact_shared_multiword_observation_keeps_original_claim_and_rejects_same_proof_wrong_value(
    policy: ReferencePolicy,
) {
    let mut scope = LocalScope::new();
    let mut globals = Vec::new();
    for _ in 0..20 {
        globals.push(scope.try_local(n()).unwrap());
        for _ in 0..63 {
            let _unused = scope.try_local(n()).unwrap();
        }
    }
    let callback = scope.try_local(n()).unwrap();
    let child = globals
        .iter()
        .skip(1)
        .fold(globals[0].term().clone(), |value, local| {
            Expr::apps(Expr::const_str("Nat.add"), [value, local.term().clone()])
        });
    let root = Expr::apps(
        Expr::const_str("Nat.add"),
        [child.clone(), globals[0].term().clone()],
    );
    let mut locals = globals.clone();
    locals.push(callback.clone());
    let mut p = parts(&scope, 100_000);
    for local in &locals {
        p.extend_base(OwnedProofCapture::Parameter(local.clone()))
            .unwrap();
    }
    let mut memo = references(&mut p, &scope, policy);
    let token = p.constructed_observation(&scope, &memo, &child).unwrap();
    p.charged_constructed_observation_independent_of(
        &scope,
        &mut memo,
        &token,
        &child,
        &[callback.clone()],
    )
    .unwrap();
    let token = p.constructed_observation(&scope, &memo, &root).unwrap();
    let before = p.counts().3;
    p.charged_constructed_observation_independent_of(
        &scope,
        &mut memo,
        &token,
        &root,
        &[callback.clone()],
    )
    .unwrap();
    let cold = p.counts().3 - before;
    if matches!(policy, ReferencePolicy::RootOnly) {
        assert!(
            cold > 50,
            "root-only policy must actually walk the embedded child"
        );
        let before = p.counts().3;
        p.charged_constructed_observation_independent_of(
            &scope,
            &mut memo,
            &token,
            &root,
            &[callback],
        )
        .unwrap();
        assert!(
            p.counts().3 - before <= 50,
            "exact whole-root reuse stays available"
        );
    } else {
        assert!(
            cold <= 50,
            "exact child sharing must avoid copying twenty distinct reference words: {cold}",
        );
    }
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let claim = Expr::apps(eq.clone(), [n(), root.clone(), root.clone()]);
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [n(), root.clone()],
    );
    let quantify = |goal| locals.iter().rev().fold(goal, |goal, local| local.pi(goal));
    let closed = scope.close(&quantify(claim.clone())).unwrap();
    let proof = locals
        .iter()
        .rev()
        .fold(proof, |proof, local| local.lam(proof));
    let bundle = p
        .close_scoped(
            &scope,
            proof,
            claim,
            crate::term_scope::TermScopeLimits::default(),
        )
        .unwrap();
    let bytes = bundle.encode_with_claim(&closed).unwrap();
    let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(closed, transported);
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    decoded.replay(&env, &transported, 2_000_000).unwrap();
    let mut wrong = bundle.clone();
    wrong.goal = Expr::apps(eq, [n(), root, Expr::nat_lit(0)]);
    assert_eq!(wrong.root, bundle.root);
    let wrong_claim = scope.close(&quantify(wrong.goal.clone())).unwrap();
    let bytes = wrong.encode_with_claim(&wrong_claim).unwrap();
    let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    let error = decoded.replay(&env, &transported, 2_000_000).err().unwrap();
    assert!(
        error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
        "{error}"
    );
}

#[test]
fn shared_children_exact_shared_multiword_observation_keeps_original_claim_and_rejects_same_proof_wrong_value()
 {
    check_exact_shared_multiword_observation_keeps_original_claim_and_rejects_same_proof_wrong_value(ReferencePolicy::SharedChildren);
}

#[test]
fn shared_children_generated_observation_failed_cold_scan_is_paid_poisoned_and_raw_inputs_stay_fresh()
 {
    check_generated_observation_failed_cold_scan_is_paid_poisoned_and_raw_inputs_stay_fresh(
        ReferencePolicy::SharedChildren,
    );
}

#[test]
fn shared_children_generated_observation_first_query_checks_embedded_input_and_loose_capture() {
    check_generated_observation_first_query_checks_embedded_input_and_loose_capture(
        ReferencePolicy::SharedChildren,
    );
}

#[test]
fn shared_children_generated_observation_full_input_height_checks_deeper_reuse_even_without_fvars()
{
    check_generated_observation_full_input_height_checks_deeper_reuse_even_without_fvars(
        ReferencePolicy::SharedChildren,
    );
}

#[test]
fn shared_children_generated_observation_keeps_all_input_refs_and_rechecks_changed_forbidden_sets()
{
    check_generated_observation_keeps_all_input_refs_and_rechecks_changed_forbidden_sets(
        ReferencePolicy::SharedChildren,
    );
}

#[test]
fn shared_children_generated_observation_rejects_foreign_replay_component_scope_and_graph() {
    check_generated_observation_rejects_foreign_replay_component_scope_and_graph(
        ReferencePolicy::SharedChildren,
    );
}

#[test]
fn shared_children_generated_observation_typed_named_input_still_requires_original_decoded_kernel_replay()
 {
    check_generated_observation_typed_named_input_still_requires_original_decoded_kernel_replay(
        ReferencePolicy::SharedChildren,
    );
}
