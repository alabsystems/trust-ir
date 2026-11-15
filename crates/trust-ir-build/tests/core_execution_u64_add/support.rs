// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use clean_kernel::{BinderInfo, Environment, Expr, KernelTypeError, Level, Name, TypeChecker};
use std::sync::OnceLock;
use trust_ir_build::{
    core_execution::{Assembler, Limits, PendingEquality, PendingProof},
    scoped_local::{LocalScope, ScopedLocal},
};

pub(super) fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
pub(super) fn app(name: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), arguments)
}
pub(super) fn nat(value: u64) -> Expr {
    Expr::nat_lit(value)
}
fn limit() -> Expr {
    app("ir_nat_pow2", [nat(64)])
}
pub(super) fn scalar(word: Expr) -> Expr {
    app("IRScalar.int_", [word])
}
pub(super) fn result(value: Expr) -> Expr {
    app("IRStepResult.value", [value])
}
pub(super) fn eq(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, left, right],
    )
}
pub(super) fn bound(word: Expr) -> Expr {
    app("Nat.lt", [word, limit()])
}
pub(super) fn bounded(word: u64) -> PendingProof {
    PendingProof::candidate(
        bound(nat(word)),
        app(
            "Nat.le_add_right",
            [app("Nat.succ", [nat(word)]), nat(u64::MAX - word)],
        ),
    )
}
pub(super) fn limits() -> Limits {
    Limits {
        max_operations: 1_000,
        max_locals: 100,
        max_list_items: 100,
        max_lookup_candidates: 32,
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}

#[derive(Clone, Copy)]
pub(super) enum Add {
    Unsigned,
    Signed,
}

impl Add {
    pub(super) fn ty(self, width: u64) -> Expr {
        app(
            match self {
                Self::Unsigned => "IRTy.uint_",
                Self::Signed => "IRTy.int_",
            },
            [nat(width)],
        )
    }
    pub(super) fn law(self) -> &'static str {
        match self {
            Self::Unsigned => "ir_byte_add_uint_canonical_v1",
            Self::Signed => "ir_byte_add_int_canonical_v1",
        }
    }
    pub(super) fn bound_law(self) -> &'static str {
        match self {
            Self::Unsigned => "ir_byte_add_uint_canonical_result_bound_v1",
            Self::Signed => "ir_byte_add_int_canonical_result_bound_v1",
        }
    }
    pub(super) fn operation(self, a: Expr, b: Expr) -> Expr {
        app(
            "ir_binop_eval",
            [c("IRBinOp.add"), self.ty(64), scalar(a), scalar(b)],
        )
    }
    pub(super) fn derive(
        self,
        assembler: &mut Assembler<'_>,
        a: Expr,
        b: Expr,
        a_bound: PendingProof,
        b_bound: PendingProof,
    ) -> (Expr, PendingEquality, PendingProof) {
        match self {
            Self::Unsigned => assembler.byte_add_u64_canonical(a, b, a_bound, b_bound),
            Self::Signed => assembler.byte_add_i64_canonical(a, b, a_bound, b_bound),
        }
        .expect("input-only pending Add and result bound")
    }
    // Independently authored expected word; never inspect producer endpoints.
    pub(super) fn word(self, a: Expr, b: Expr) -> Expr {
        let sum = app("Nat.add", [a, b]);
        Expr::apps(
            Expr::const_(
                Name::from_string("Bool.rec"),
                vec![Level::succ(Level::zero())],
            ),
            [
                Expr::lam(BinderInfo::Default, c("Bool"), c("Nat")),
                app("Nat.sub", [sum.clone(), limit()]),
                sum.clone(),
                app("ir_nat_ltb", [sum, limit()]),
            ],
        )
    }
}

fn environment() -> &'static Environment {
    static ENV: OnceLock<Environment> = OnceLock::new();
    ENV.get_or_init(|| {
        let mut spec = clean_verify::eval_ir::build_byte_prelude_spec_v1_with_stack()
            .expect("ordinary owned Byte profile, without division or shift extensions");
        spec.install_eval_ir_bounded_add_laws_v1()
            .expect("public fixed transactional bounded-Add extension");
        spec.into_environment()
    })
}
fn checker() -> TypeChecker<'static> {
    let mut tc = TypeChecker::new(environment());
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.set_heartbeat_limit(limits().lookup_heartbeats);
    tc.set_max_cache_entries(limits().lookup_cache_entries);
    tc
}
fn unspent(tc: &TypeChecker<'_>) {
    assert!(
        !tc.heartbeat_spent(),
        "a budget stop is not a mathematical verdict"
    );
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
}
fn close(
    scope: &LocalScope,
    parameters: &[ScopedLocal],
    term: &Expr,
    claim: &Expr,
) -> (Expr, Expr) {
    let term = parameters
        .iter()
        .rev()
        .fold(term.clone(), |body, local| local.lam(body));
    let claim = parameters
        .iter()
        .rev()
        .fold(claim.clone(), |body, local| local.pi(body));
    (scope.close(&term).unwrap(), scope.close(&claim).unwrap())
}
fn certify(term: &Expr, claim: &Expr, root: Option<&str>) {
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    let tc = checker();
    tc.check_type(claim, &Expr::sort(Level::zero())).unwrap();
    tc.check_type(term, claim).unwrap();
    unspent(&tc);
    let env = environment();
    let audit = env.audit_certification(claim, term);
    assert!(audit.is_certified(), "actual rooted closure: {audit:#?}");
    if let Some(root) = root {
        let name = Name::from_string(root);
        assert!(
            audit.dependencies.contains(&name),
            "retain the actual operation/bound root"
        );
        assert!(env.axiom_deps(&name).unwrap().is_empty());
        assert!(env.trust_marker_deps(&name).unwrap().is_empty());
    }
}
pub(super) fn replay(
    scope: &LocalScope,
    parameters: &[ScopedLocal],
    term: &Expr,
    claim: &Expr,
    root: Option<&str>,
) {
    let (term, claim) = close(scope, parameters, term, claim);
    certify(&term, &claim, root);
    let encoded = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&encoded).unwrap();
    assert_eq!(decoded, term, "retain the entire proof graph");
    certify(&decoded, &claim, root);
}
pub(super) fn refuses(scope: &LocalScope, term: &Expr, claim: &Expr) {
    let (term, claim) = close(scope, &[], term, claim);
    let tc = checker();
    tc.check_type(&claim, &Expr::sort(Level::zero())).unwrap();
    let error = tc.check_type(&term, &claim).unwrap_err();
    unspent(&tc);
    assert!(
        matches!(error, KernelTypeError::TypeMismatch { .. }),
        "{error:?}"
    );
}
