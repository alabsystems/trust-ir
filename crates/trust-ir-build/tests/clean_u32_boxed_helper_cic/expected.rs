// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Independent literal-source trace, not a query of a produced endpoint.
use super::*;
#[derive(Clone, Copy)]
pub(super) enum Mutation {
    None,
    Next,
    RetireCallerMemory,
    Host,
    Tag,
    Slot,
    Remaining,
    CallerPc,
}
pub(super) fn memory() -> Expr {
    let alloc = |base, size, owner, live| {
        app(
            "IRByteAllocationV1.mk",
            [
                nat(base),
                nat(size),
                nat(owner),
                c(if live { "Bool.true" } else { "Bool.false" }),
            ],
        )
    };
    app(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                [alloc(4096, 1, 0, true), alloc(8192, 1, 7, false)],
            ),
            Expr::lam(
                BinderInfo::Default,
                c("Nat"),
                app(
                    "Bool.rec",
                    [
                        Expr::lam(BinderInfo::Default, c("Bool"), app("IROption", [c("Nat")])),
                        app("IROption.none", [c("Nat")]),
                        app("IROption.some", [c("Nat"), nat(91)]),
                        app("ir_nat_eqb", [Expr::bvar(0), nat(4096)]),
                    ],
                ),
            ),
            nat(12288),
        ],
    )
}
fn bind(id: u64, v: Expr) -> Expr {
    app("IRBinding.mk", [nat(id), v])
}
fn int(n: u32) -> Expr {
    app("IRScalar.int_", [nat(n.into())])
}
fn ptr(n: u32) -> Expr {
    app("IRScalar.ptr_", [nat(2 * u64::from(n) + 1)])
}
fn frame(fid: u64, pc: u64, locals: Vec<Expr>, dests: Vec<Expr>) -> Expr {
    app(
        "IRFrame.mk",
        [
            nat(fid),
            nat(0),
            nat(pc),
            list("IRBinding", locals),
            list("Nat", dests),
        ],
    )
}
pub(super) fn endpoint(x: u32, y: u32, n: u64, remaining: u64, mutation: Mutation) -> Expr {
    let mut result = x.wrapping_add(7).wrapping_mul(y);
    if matches!(mutation, Mutation::Tag) {
        result = result.wrapping_add(1);
    }
    with_result(x, y, n, remaining, mutation, nat(result.into()))
}
pub(super) fn with_result(
    x: u32,
    y: u32,
    n: u64,
    remaining: u64,
    mutation: Mutation,
    result: Expr,
) -> Expr {
    let added = x.wrapping_add(7);
    let word = || app("IRScalar.int_", [result.clone()]);
    let tagged = || {
        app(
            "IRScalar.ptr_",
            [app(
                "Nat.add",
                [app("Nat.mul", [result.clone(), nat(2)]), nat(1)],
            )],
        )
    };
    let mut wrapper = vec![bind(0, ptr(x)), bind(1, ptr(y))];
    if n >= 1 {
        wrapper.insert(0, bind(2, int(x)));
    }
    if n >= 2 {
        wrapper.insert(0, bind(3, int(y)));
    }
    if n >= 9 {
        wrapper.insert(0, bind(4, word()));
    }
    if n >= 10 {
        wrapper.insert(0, bind(5, tagged()));
    }
    let mut mem = memory();
    if n >= 9 {
        mem = app("ir_byte_retire_v1", [nat(9), mem]);
    }
    if n >= 11 {
        mem = app("ir_byte_retire_v1", [nat(8), mem]);
    }
    if matches!(mutation, Mutation::RetireCallerMemory) {
        mem = app("ir_byte_retire_v1", [nat(0), mem]);
    }
    let next = if matches!(mutation, Mutation::Next) {
        9
    } else if n >= 5 {
        10
    } else {
        9
    };
    let owners = if n >= 11 {
        vec![]
    } else if (5..9).contains(&n) {
        vec![nat(9), nat(8)]
    } else {
        vec![nat(8)]
    };
    let world = app(
        "IRByteWorldV1.mk",
        [
            c("Nat"),
            mem,
            nat(if matches!(mutation, Mutation::Host) {
                38
            } else {
                37
            }),
            list("Nat", owners),
            nat(next),
        ],
    );
    let config = if n >= 11 {
        app(
            "IRByteConfigV1.halted",
            [
                c("Nat"),
                app("IROutcome.ret", [list("IRScalar", [tagged()])]),
                world,
            ],
        )
    } else {
        let frames = if (5..9).contains(&n) {
            let mut scalar = vec![bind(0, int(x)), bind(1, int(y))];
            if n >= 6 {
                scalar.insert(0, bind(2, int(7)));
            }
            if n >= 7 {
                scalar.insert(0, bind(3, int(added)));
            }
            if n >= 8 {
                scalar.insert(0, bind(4, word()));
            }
            vec![
                frame(70, n - 5, scalar, vec![nat(4)]),
                frame(71, 5, wrapper, vec![]),
            ]
        } else {
            vec![frame(
                71,
                if n < 5 {
                    n
                } else if matches!(mutation, Mutation::CallerPc) {
                    6
                } else {
                    n - 4
                },
                wrapper,
                vec![],
            )]
        };
        app(
            "IRByteConfigV1.running",
            [
                c("Nat"),
                app(
                    "IRMachine.mk",
                    [list("IRFrame", frames), list("IRMemSlot", []), nat(0)],
                ),
                world,
            ],
        )
    };
    let left = matches!(mutation, Mutation::Slot) || n < 3;
    let right = n < 4;
    app(
        "IRCleanTag32HelperRunV1.mk",
        [
            c("Nat"),
            app(
                "IRCleanTag32PrefixV1.mk",
                [
                    c("Nat"),
                    config,
                    c(if left { "Bool.true" } else { "Bool.false" }),
                    c(if right { "Bool.true" } else { "Bool.false" }),
                ],
            ),
            nat(if matches!(mutation, Mutation::Remaining) {
                remaining + 1
            } else {
                remaining
            }),
        ],
    )
}
