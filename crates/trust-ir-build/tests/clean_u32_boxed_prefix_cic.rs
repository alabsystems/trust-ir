// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
#![cfg(feature = "source-value-operational")]
//! Whole-module checked caller; independent complete worlds and hostile metadata.
use std::collections::BTreeMap;
use trust_ir::FuncId;
use trust_ir_build::clean_kernel::{BinderInfo, Expr, Level, Name, TypeChecker};
use trust_ir_build::clean_u32_boxed_prefix_cic::{
    CheckedTaggedPrefixCic, PrefixAllocation, PrefixCicError, PrefixWorld,
    check_tagged_u32_boxed_prefix_execution,
};
#[path = "clean_u32_boxed_prefix_cic/fixture.rs"]
mod fixture_data;
#[path = "clean_u32_boxed_prefix_cic/sites.rs"]
mod sites;
#[path = "clean_u32_boxed_prefix_cic/universal.rs"]
mod universal_tests;
use fixture_data::{fixture, runtime_sources, subject};
fn c(name: &str) -> Expr {
    let levels = if name == "Bool.rec" {
        vec![Level::succ(Level::zero())]
    } else {
        vec![]
    };
    Expr::const_(Name::from_string(name), levels)
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn nat(n: u64) -> Expr {
    Expr::nat_lit(n)
}
fn list(ty: &str, xs: impl IntoIterator<Item = Expr>) -> Expr {
    xs.into_iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .fold(app("IRList.nil", [c(ty)]), |tail, x| {
            app("IRList.cons", [c(ty), x, tail])
        })
}
fn eq(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, left, right],
    )
}
// Authored finite memory with an unrelated LIVE caller-owned allocation and a
// DEAD historical owner7, plus a byte map and host37. Expected freshowner8/next9
// are literal here, not read back from the model or production endpoint.
fn world() -> PrefixWorld {
    PrefixWorld {
        allocations: vec![
            PrefixAllocation {
                base: 4096,
                size: 1,
                owner: 0,
                live: true,
            },
            PrefixAllocation {
                base: 8192,
                size: 1,
                owner: 7,
                live: false,
            },
        ],
        bytes: BTreeMap::from([(4096, 91)]),
        next_address: 12288,
        host: 37,
    }
}
fn authored_memory() -> Expr {
    app(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                [
                    app(
                        "IRByteAllocationV1.mk",
                        [nat(4096), nat(1), nat(0), c("Bool.true")],
                    ),
                    app(
                        "IRByteAllocationV1.mk",
                        [nat(8192), nat(1), nat(7), c("Bool.false")],
                    ),
                ],
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
fn authored_endpoint(
    words: [u64; 2],
    fuel: u64,
    host: u64,
    left: bool,
    remaining: u64,
    pc: u64,
) -> Expr {
    let count = fuel.min(4);
    let mut locals = vec![
        app(
            "IRBinding.mk",
            [nat(0), app("IRScalar.ptr_", [nat(words[0])])],
        ),
        app(
            "IRBinding.mk",
            [nat(1), app("IRScalar.ptr_", [nat(words[1])])],
        ),
    ];
    if count >= 1 {
        locals.insert(
            0,
            app(
                "IRBinding.mk",
                [nat(2), app("IRScalar.int_", [nat(words[0] / 2)])],
            ),
        );
    }
    if count >= 2 {
        locals.insert(
            0,
            app(
                "IRBinding.mk",
                [nat(3), app("IRScalar.int_", [nat(words[1] / 2)])],
            ),
        );
    }
    let frame = app(
        "IRFrame.mk",
        [
            nat(71),
            nat(0),
            nat(pc),
            list("IRBinding", locals),
            list("Nat", []),
        ],
    );
    let machine = app(
        "IRMachine.mk",
        [list("IRFrame", [frame]), list("IRMemSlot", []), nat(0)],
    );
    let world = app(
        "IRByteWorldV1.mk",
        [
            c("Nat"),
            authored_memory(),
            nat(host),
            list("Nat", [nat(8)]),
            nat(9),
        ],
    );
    app(
        "IRCleanTag32RunV1.mk",
        [
            c("Nat"),
            app(
                "IRCleanTag32PrefixV1.mk",
                [
                    c("Nat"),
                    app("IRByteConfigV1.running", [c("Nat"), machine, world]),
                    c(if left { "Bool.true" } else { "Bool.false" }),
                    c(if count < 4 { "Bool.true" } else { "Bool.false" }),
                ],
            ),
            nat(remaining),
        ],
    )
}
fn independently_check(
    receipt: &CheckedTaggedPrefixCic<'_, '_>,
    words: [u64; 2],
    fuel: u64,
    endpoint: Expr,
) -> bool {
    let actual = app(
        "ir_clean_tag32_run_v1",
        [
            c("Nat"),
            receipt.source().context().clone(),
            nat(71),
            nat(0),
            nat(10),
            nat(0),
            nat(1),
            nat(fuel),
            receipt.initial().clone(),
        ],
    );
    let claim = eq(app("IRCleanTag32RunV1", [c("Nat")]), actual, endpoint);
    let mut tc = TypeChecker::new(receipt.environment());
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    let result = tc.check_type(receipt.proof(), &claim).is_ok();
    assert!(!tc.heartbeat_spent());
    assert!(!trust_ir_build::clean_kernel::tc::declaration_budget_exhausted());
    // The independently authored initial arguments are exact too, not a model
    // endpoint replay disguised as an input-identity check.
    let initial = app(
        "ir_clean_tag32_init_v1",
        [
            c("Nat"),
            receipt.source().context().clone(),
            nat(71),
            list("IRScalar", words.map(|w| app("IRScalar.ptr_", [nat(w)]))),
            authored_memory(),
            nat(37),
        ],
    );
    assert_eq!(&initial, receipt.initial());
    result
}

#[test]
fn whole_retained_module_has_checked_complete_prefixes_and_framed_world() {
    subject(fixture(), |source| {
        assert_eq!(
            source.source_value().module().functions[71].blocks[0]
                .params
                .iter()
                .map(|(id, _)| id.index())
                .collect::<Vec<_>>(),
            vec![0, 1]
        );
        for words in [[7, 11], [1, 1], [8589934591, 7]] {
            for fuel in [0, 1, 2, 3, 4, 9] {
                let receipt = check_tagged_u32_boxed_prefix_execution(
                    source,
                    FuncId(71),
                    &runtime_sources(),
                    words,
                    fuel,
                    &world(),
                )
                .unwrap();
                let count = fuel.min(4);
                assert_eq!(
                    (receipt.consumed(), receipt.remaining()),
                    (count, fuel - count)
                );
                assert!(core::ptr::eq(receipt.source(), source));
                let endpoint = authored_endpoint(words, fuel, 37, count < 3, fuel - count, count);
                assert!(independently_check(&receipt, words, fuel, endpoint));
                if fuel == 9 {
                    for bad in [
                        authored_endpoint(words, fuel, 38, false, 5, 4), // wrong host/world
                        authored_endpoint(words, fuel, 37, true, 5, 4),  // unconsumed occurrence
                        authored_endpoint(words, fuel, 37, false, 4, 4), // wrong remaining fuel
                        authored_endpoint(words, fuel, 37, false, 5, 3), // wrong actual handoff site
                    ] {
                        assert!(!independently_check(&receipt, words, fuel, bad));
                    }
                }
            }
        }
    });
}

#[test]
fn canonical_input_source_and_entry_world_refusals_precede_proof_receipts() {
    subject(fixture(), |source| {
        for words in [[0, 1], [2, 1], [8589934593, 1]] {
            assert!(matches!(
                check_tagged_u32_boxed_prefix_execution(
                    source,
                    FuncId(71),
                    &runtime_sources(),
                    words,
                    0,
                    &world()
                ),
                Err(PrefixCicError::TaggedDomain)
            ));
        }
        let mut bad = world();
        bad.allocations[1].live = true;
        // Canonical initializer rejects unrelated LIVE owner7. We do not
        // repair/erase its memory in order to manufacture a successful proof.
        assert!(
            check_tagged_u32_boxed_prefix_execution(
                source,
                FuncId(71),
                &runtime_sources(),
                [7, 11],
                0,
                &bad
            )
            .is_err()
        );
        let mut sources = runtime_sources();
        sources.rc_core = b"same-name impostor";
        assert!(
            check_tagged_u32_boxed_prefix_execution(
                source,
                FuncId(71),
                &sources,
                [7, 11],
                0,
                &world()
            )
            .is_err()
        );
    });
}
