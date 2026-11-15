// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Untrusted closed transport between the complete site guard and its named
//! definition. The original proof is consumed intact; only ordinary kernel
//! conversion under neutral parameters can justify the annotation.
use super::*;
use clean_kernel::BinderInfo;

fn telescope(mut body: Expr, proof: bool) -> Expr {
    // Header types use their original binder contexts: immediately before the
    // proof binder the indices are ctx=3, site=2, rows=1, resultTy=0.
    let headers = [
        constant("IRByteContextV1"),
        constant("IRByteSiteV1"),
        app("IRList", [constant("IRByteOperandV1")]),
        constant("IRTy"),
        eq(
            &constant("Bool"),
            conjunction(3, 2, 1, 0),
            constant("Bool.true"),
        ),
    ];
    for header in headers.into_iter().rev() {
        body = if proof {
            Expr::lam(BinderInfo::Default, header, body)
        } else {
            Expr::pi(BinderInfo::Default, header, body)
        };
    }
    body
}
fn conjunction(ctx: u32, site: u32, rows: u32, ty: u32) -> Expr {
    app(
        "Bool.and",
        [
            app(
                "ir_byte_sites_unique_v1",
                [app("ir_byte_context_sites_v1", [Expr::bvar(ctx)])],
            ),
            app(
                "Bool.and",
                [
                    app("ir_byte_operands_unique_v1", [Expr::bvar(rows)]),
                    app(
                        "ir_byte_ty_list_eq_v1",
                        [
                            app("ir_byte_site_results_v1", [Expr::bvar(site)]),
                            list("IRTy", &[Expr::bvar(ty)]),
                        ],
                    ),
                ],
            ),
        ],
    )
}
pub(super) fn closed_claim() -> Expr {
    // Under the final proof binder these four inputs shift by one.
    telescope(
        eq(
            &constant("Bool"),
            app(
                "ir_byte_field_site_valid_v1",
                [Expr::bvar(4), Expr::bvar(3), Expr::bvar(2), Expr::bvar(1)],
            ),
            constant("Bool.true"),
        ),
        false,
    )
}
pub(super) fn closed_candidate() -> Expr {
    Expr::let_named(
        Name::anon(),
        closed_claim(),
        telescope(Expr::bvar(0), true),
        Expr::bvar(0),
        false,
    )
}
