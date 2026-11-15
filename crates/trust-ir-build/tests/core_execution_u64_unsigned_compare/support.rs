// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use clean_kernel::{Environment, Expr, KernelTypeError, Level, Name, TypeChecker};
use std::sync::OnceLock;
use trust_ir::ICmpOp;
use trust_ir_build::{
    core_execution::{Assembler, Limits, PendingEquality, PendingProof},
    scoped_local::{LocalScope, ScopedLocal},
};

#[path = "fetched.rs"]
mod fetched;

pub(super) fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
pub(super) fn app(name: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), arguments)
}
pub(super) fn nat(value: u64) -> Expr {
    Expr::nat_lit(value)
}
pub(super) fn scalar(word: Expr) -> Expr {
    app("IRScalar.int_", [word])
}
pub(super) fn boolean(flag: Expr) -> Expr {
    app("IRScalar.bool_", [flag])
}
pub(super) fn flag(value: bool) -> Expr {
    c(if value { "Bool.true" } else { "Bool.false" })
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
    app("Nat.lt", [word, app("ir_nat_pow2", [nat(64)])])
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
    // The existing actual Add/shift replay profile, unchanged.
    Limits {
        max_operations: 1_000,
        max_locals: 100,
        max_list_items: 100,
        max_lookup_candidates: 32,
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}

pub(super) const OPS: [ICmpOp; 4] = [ICmpOp::Ult, ICmpOp::Ule, ICmpOp::Ugt, ICmpOp::Uge];

#[derive(Clone, Copy)]
pub(super) enum Carrier {
    Unsigned,
    Signed,
}

impl Carrier {
    pub(super) fn ty(self, width: u64) -> Expr {
        app(
            match self {
                Self::Unsigned => "IRTy.uint_",
                Self::Signed => "IRTy.int_",
            },
            [nat(width)],
        )
    }
    pub(super) fn law(self, op: ICmpOp) -> &'static str {
        match (self, op) {
            (Self::Unsigned, ICmpOp::Ult) => "ir_byte_icmp_uint_ult_canonical_v1",
            (Self::Signed, ICmpOp::Ult) => "ir_byte_icmp_int_ult_canonical_v1",
            (Self::Unsigned, ICmpOp::Ule) => "ir_byte_icmp_uint_ule_canonical_v1",
            (Self::Signed, ICmpOp::Ule) => "ir_byte_icmp_int_ule_canonical_v1",
            (Self::Unsigned, ICmpOp::Ugt) => "ir_byte_icmp_uint_ugt_canonical_v1",
            (Self::Signed, ICmpOp::Ugt) => "ir_byte_icmp_int_ugt_canonical_v1",
            (Self::Unsigned, ICmpOp::Uge) => "ir_byte_icmp_uint_uge_canonical_v1",
            (Self::Signed, ICmpOp::Uge) => "ir_byte_icmp_int_uge_canonical_v1",
            _ => panic!("no canonical unsigned-operation law for {op:?}"),
        }
    }
    pub(super) fn operation(self, op: ICmpOp, width: u64, a: Expr, b: Expr) -> Expr {
        let opcode = match op {
            ICmpOp::Eq => "IRICmpOp.eq_",
            ICmpOp::Ne => "IRICmpOp.ne_",
            ICmpOp::Ult => "IRICmpOp.ult",
            ICmpOp::Ule => "IRICmpOp.ule",
            ICmpOp::Ugt => "IRICmpOp.ugt",
            ICmpOp::Uge => "IRICmpOp.uge",
            ICmpOp::Slt => "IRICmpOp.slt",
            ICmpOp::Sle => "IRICmpOp.sle",
            ICmpOp::Sgt => "IRICmpOp.sgt",
            ICmpOp::Sge => "IRICmpOp.sge",
        };
        app(
            "ir_icmp_eval",
            [c(opcode), self.ty(width), scalar(a), scalar(b)],
        )
    }
    pub(super) fn derive(
        self,
        assembler: &mut Assembler<'_>,
        op: ICmpOp,
        words: [Expr; 2],
        bounds: [PendingProof; 2],
    ) -> Result<(Expr, PendingEquality), String> {
        let [a, b] = words;
        let [a_bound, b_bound] = bounds;
        match self {
            Self::Unsigned => {
                assembler.byte_unsigned_compare_u64_canonical(op, a, b, a_bound, b_bound)
            }
            Self::Signed => {
                assembler.byte_unsigned_compare_i64_canonical(op, a, b, a_bound, b_bound)
            }
        }
    }
}

// Independently reconstruct the meaning; do not inspect producer endpoints.
pub(super) fn observer(op: ICmpOp, a: Expr, b: Expr) -> Expr {
    match op {
        ICmpOp::Ult => app("ir_nat_ltb", [a, b]),
        ICmpOp::Ule => app("ir_nat_leb", [a, b]),
        ICmpOp::Ugt => app("ir_nat_ltb", [b, a]),
        ICmpOp::Uge => app("ir_nat_leb", [b, a]),
        _ => panic!("unsigned test observer does not cover {op:?}"),
    }
}
pub(super) fn literal(op: ICmpOp, a: u64, b: u64) -> bool {
    match op {
        ICmpOp::Ult => a < b,
        ICmpOp::Ule => a <= b,
        ICmpOp::Ugt => a > b,
        ICmpOp::Uge => a >= b,
        _ => panic!("unsigned literal oracle does not cover {op:?}"),
    }
}

fn environment() -> &'static Environment {
    // Test-only immutable fixture over Clean's explicit checked library-owner
    // profile, not a program verdict cache or private theorem installation.
    static ENV: OnceLock<Environment> = OnceLock::new();
    ENV.get_or_init(|| {
        let spec =
            clean_verify::eval_ir::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack()
                .expect("public checked canonical-arithmetic Byte profile");
        for carrier in [Carrier::Unsigned, Carrier::Signed] {
            for op in OPS {
                let name = Name::from_string(carrier.law(op));
                let definition = spec.get_definition(carrier.law(op)).expect("stored law");
                let info = spec.env().get_const(&name).expect("actual declaration");
                assert_eq!(definition.elaborated_type.as_ref(), Some(&info.type_));
                assert_eq!(definition.elaborated_value.as_ref(), info.value.as_ref());
                spec.verify_definition(carrier.law(op))
                    .expect("ordinary strict stored-law check");
                let root = Expr::const_(
                    name.clone(),
                    info.level_params
                        .iter()
                        .cloned()
                        .map(Level::param)
                        .collect::<Vec<_>>(),
                );
                let audit = spec.env().audit_certification(&info.type_, &root);
                assert!(audit.is_certified(), "stored root: {audit:#?}");
                assert!(audit.dependencies.contains(&name));
                assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
                assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
            }
        }
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
            "retain the actual operation law"
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
pub(super) fn refuses(scope: &LocalScope, parameters: &[ScopedLocal], term: &Expr, claim: &Expr) {
    let (term, claim) = close(scope, parameters, term, claim);
    let tc = checker();
    tc.check_type(&claim, &Expr::sort(Level::zero())).unwrap();
    let error = tc.check_type(&term, &claim).unwrap_err();
    unspent(&tc);
    assert!(
        matches!(error, KernelTypeError::TypeMismatch { .. }),
        "{error:?}"
    );
    assert!(
        !environment()
            .audit_certification(&claim, &term)
            .is_certified()
    );
}
