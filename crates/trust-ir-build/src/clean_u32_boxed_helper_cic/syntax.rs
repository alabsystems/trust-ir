// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use crate::core_execution::{PendingEquality, PendingProof};
use clean_kernel::{Expr, Level, Name};
pub(super) fn c(s: &str) -> Expr {
    Expr::const_(Name::from_string(s), vec![])
}
pub(super) fn app(s: &str, a: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(s), a)
}
pub(super) fn nat(n: u64) -> Expr {
    Expr::nat_lit(n)
}
pub(super) fn boolean(v: bool) -> Expr {
    c(if v { "Bool.true" } else { "Bool.false" })
}
pub(super) fn list(ty: &str, a: impl IntoIterator<Item = Expr>) -> Expr {
    a.into_iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .fold(app("IRList.nil", [c(ty)]), |tail, h| {
            app("IRList.cons", [c(ty), h, tail])
        })
}
pub(super) fn equation(ty: Expr, l: Expr, r: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, l, r],
    )
}
pub(super) fn refl(ty: Expr, v: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, v],
    )
}
pub(super) fn truth() -> PendingEquality {
    PendingEquality::candidate(
        c("Bool"),
        boolean(true),
        boolean(true),
        refl(c("Bool"), boolean(true)),
    )
}
pub(super) fn both(a: PendingEquality, b: PendingEquality) -> PendingEquality {
    PendingEquality::candidate(
        c("Bool"),
        app("Bool.and", [a.left().clone(), b.left().clone()]),
        boolean(true),
        app(
            "ir_byte_world_and_intro_v1",
            [
                a.left().clone(),
                b.left().clone(),
                a.term().clone(),
                b.term().clone(),
            ],
        ),
    )
}
pub(super) fn u32_nat(v: Expr) -> Expr {
    app("UInt32.toNat", [v])
}
pub(super) fn u32_bound(v: Expr) -> Expr {
    Expr::proj(
        Name::from_string("Fin"),
        1,
        app("BitVec.toFin", [nat(32), app("UInt32.toBitVec", [v])]),
    )
}
pub(super) fn uint_fits(n: Expr, bound: &PendingProof) -> PendingEquality {
    PendingEquality::candidate(
        c("Bool"),
        app("ir_nat_ltb", [n.clone(), nat(4294967296)]),
        boolean(true),
        app(
            "ir_byte_ltb_of_lt_v1",
            [n, nat(4294967296), bound.term().clone()],
        ),
    )
}
pub(super) fn pointer_fits(ctx: Expr, n: Expr, bound: &PendingProof) -> PendingEquality {
    PendingEquality::candidate(
        c("Bool"),
        app(
            "ir_byte_value_matches_v1",
            [
                ctx.clone(),
                c("IRTy.ptr_"),
                app(
                    "IRScalar.ptr_",
                    [app("ir_clean_tag32_encode_v1", [n.clone()])],
                ),
            ],
        ),
        boolean(true),
        app(
            "ir_clean_tag32_encoded_pointer_v1",
            [ctx, n, bound.term().clone()],
        ),
    )
}

pub(super) fn reverse(ty: Expr, p: &PendingEquality) -> PendingEquality {
    PendingEquality::candidate(
        ty.clone(),
        p.right().clone(),
        p.left().clone(),
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            ),
            [ty, p.left().clone(), p.right().clone(), p.term().clone()],
        ),
    )
}
