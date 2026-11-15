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
pub(super) fn range(amount: Expr) -> Expr {
    app("Nat.lt", [amount, nat(64)])
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
pub(super) fn in_range(amount: u64) -> PendingProof {
    assert!(amount < 64);
    PendingProof::candidate(
        range(nat(amount)),
        app(
            "Nat.le_add_right",
            [app("Nat.succ", [nat(amount)]), nat(63 - amount)],
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
pub(super) enum Shift {
    Logical,
    Arithmetic,
}

impl Shift {
    pub(super) fn law(self) -> &'static str {
        match self {
            Self::Logical => "ir_byte_lshr_u64_in_range_v1",
            Self::Arithmetic => "ir_byte_ashr_i64_in_range_v1",
        }
    }
    pub(super) fn bound_law(self) -> &'static str {
        match self {
            Self::Logical => "ir_byte_lshr_u64_in_range_result_bound_v1",
            Self::Arithmetic => "ir_byte_ashr_i64_in_range_result_bound_v1",
        }
    }
    pub(super) fn operation(self, word: Expr, amount: Expr) -> Expr {
        let (opcode, ty) = match self {
            Self::Logical => ("IRBinOp.lshr", "IRTy.uint_"),
            Self::Arithmetic => ("IRBinOp.ashr", "IRTy.int_"),
        };
        app(
            "ir_binop_eval",
            [c(opcode), app(ty, [nat(64)]), scalar(word), scalar(amount)],
        )
    }
    pub(super) fn derive(
        self,
        assembler: &mut Assembler<'_>,
        word: Expr,
        amount: Expr,
        bound: PendingProof,
        range: PendingProof,
    ) -> (Expr, PendingEquality, PendingProof) {
        match self {
            Self::Logical => assembler.byte_lshr_u64_in_range(word, amount, bound, range),
            Self::Arithmetic => assembler.byte_ashr_i64_in_range(word, amount, bound, range),
        }
        .expect("derive pending operation and bound without an answer premise")
    }
    // Independently authored result; never read the producer's endpoints here.
    pub(super) fn word(self, word: Expr, amount: Expr) -> Expr {
        let quotient = |word: Expr, fuel| {
            app(
                "ir_dm_quot",
                [app(
                    "ir_dm_go",
                    [
                        nat(1),
                        word.clone(),
                        nat(fuel),
                        app("ir_nat_pow2", [amount.clone()]),
                        app("IRDivMod.mk", [word, nat(0)]),
                    ],
                )],
            )
        };
        let logical = quotient(word.clone(), 64);
        match self {
            Self::Logical => logical,
            Self::Arithmetic => Expr::apps(
                Expr::const_(
                    Name::from_string("Bool.rec"),
                    vec![Level::succ(Level::zero())],
                ),
                [
                    Expr::lam(BinderInfo::Default, c("Bool"), c("Nat")),
                    logical.clone(),
                    app(
                        "Nat.add",
                        [logical, app("Nat.sub", [limit(), quotient(limit(), 65)])],
                    ),
                    app("ir_sign_bit", [nat(64), word]),
                ],
            ),
        }
    }
}

fn environment() -> &'static Environment {
    static ENV: OnceLock<Environment> = OnceLock::new();
    ENV.get_or_init(|| {
        let mut spec = clean_verify::eval_ir::
            build_u64_shift_by_three_output_bounds_byte_prelude_spec_v1_with_stack()
            .expect("ordinary owned checked output-bounds profile");
        spec.install_eval_ir_u64_in_range_shift_laws_v1()
            .expect("public transactional all-amount extension");
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
        assert!(audit.dependencies.contains(&name), "retain the actual root");
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
