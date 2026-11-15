// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
// Mutate only mathematical site data, never a ModuleValidationReport or source
// receipt. This checks the NEW profile's hostile-data behavior, not admission
// of a fabricated metadata-bearing producer module.
fn release_catalog(context: &Expr, rows: Expr) -> Expr {
    fn sites(xs: &Expr, rows: &Expr) -> Expr {
        let args = xs.get_app_args();
        if xs.get_app_fn() == &c("IRList.nil") {
            return xs.clone();
        }
        let [ty, site, tail] = args.as_slice() else {
            panic!("site list");
        };
        let fields = site.get_app_args();
        let site = if fields[0] == &nat(71) && fields[1] == &nat(0) && fields[2] == &nat(2) {
            assert_eq!(site.get_app_fn(), &c("IRByteSiteV1.mk"));
            let mut data: Vec<_> = fields.into_iter().cloned().collect();
            data.push(rows.clone());
            app("IRByteSiteV1.mkt", data)
        } else {
            (*site).clone()
        };
        app("IRList.cons", [(*ty).clone(), site, sites(tail, rows)])
    }
    let mut fields: Vec<_> = context.get_app_args().into_iter().cloned().collect();
    fields[4] = sites(&fields[4], &rows);
    Expr::apps(context.get_app_fn().clone(), fields)
}
fn raw_model_replay(
    receipt: &CheckedTaggedPrefixCic<'_, '_>,
    context: Expr,
    params: [u64; 2],
    expected: Expr,
) -> bool {
    let initial = app(
        "ir_clean_tag32_init_v1",
        [
            c("Nat"),
            context.clone(),
            nat(71),
            list(
                "IRScalar",
                [
                    app("IRScalar.ptr_", [nat(7)]),
                    app("IRScalar.ptr_", [nat(11)]),
                ],
            ),
            authored_memory(),
            nat(37),
        ],
    );
    let actual = app(
        "ir_clean_tag32_run_v1",
        [
            c("Nat"),
            context,
            nat(71),
            nat(0),
            nat(10),
            nat(params[0]),
            nat(params[1]),
            nat(4),
            initial,
        ],
    );
    let ty = app("IRCleanTag32RunV1", [c("Nat")]);
    let claim = eq(ty.clone(), actual, expected.clone());
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, expected],
    );
    let mut tc = TypeChecker::new(receipt.environment());
    tc.set_allow_partial(false);
    tc.set_allow_unsafe(false);
    let result = tc.check_type(&proof, &claim).is_ok();
    assert!(!tc.heartbeat_spent());
    assert!(!trust_ir_build::clean_kernel::tc::declaration_budget_exhausted());
    result
}
fn malformed_site_endpoint() -> Expr {
    let world = app(
        "IRByteWorldV1.mk",
        [
            c("Nat"),
            authored_memory(),
            nat(37),
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
                    app(
                        "IRByteConfigV1.halted",
                        [
                            c("Nat"),
                            app("IROutcome.type_error", [c("IRFault.bad_field")]),
                            world,
                        ],
                    ),
                    c("Bool.true"),
                    c("Bool.true"),
                ],
            ),
            nat(1),
        ],
    )
}

#[test]
fn release_checks_actual_parameter_signature_and_present_operand_catalog() {
    subject(fixture(), |source| {
        let receipt = check_tagged_u32_boxed_prefix_execution(
            source,
            FuncId(71),
            &runtime_sources(),
            [7, 11],
            4,
            &world(),
        )
        .unwrap();
        let operand = |id, ty| app("IRByteOperandV1.mk", [nat(id), ty]);
        let valid = release_catalog(
            source.context(),
            list("IRByteOperandV1", [operand(0, c("IRTy.ptr_"))]),
        );
        assert!(raw_model_replay(
            &receipt,
            valid,
            [0, 1],
            authored_endpoint([7, 11], 4, 37, false, 0, 4)
        ));
        for rows in [
            list("IRByteOperandV1", []),
            list(
                "IRByteOperandV1",
                [operand(0, app("IRTy.uint_", [nat(64)]))],
            ),
            list("IRByteOperandV1", [operand(1, c("IRTy.ptr_"))]),
            list(
                "IRByteOperandV1",
                [operand(0, c("IRTy.ptr_")), operand(0, c("IRTy.ptr_"))],
            ),
            list(
                "IRByteOperandV1",
                [
                    operand(0, c("IRTy.ptr_")),
                    operand(0, app("IRTy.uint_", [nat(64)])),
                ],
            ),
        ] {
            let bad = release_catalog(source.context(), rows);
            assert!(raw_model_replay(
                &receipt,
                bad.clone(),
                [0, 1],
                malformed_site_endpoint()
            ));
            assert!(!raw_model_replay(
                &receipt,
                bad,
                [0, 1],
                authored_endpoint([7, 11], 4, 37, false, 0, 4)
            ));
        }
        for params in [[1, 0], [0, 0], [7, 1]] {
            assert!(raw_model_replay(
                &receipt,
                source.context().clone(),
                params,
                malformed_site_endpoint()
            ));
            assert!(!raw_model_replay(
                &receipt,
                source.context().clone(),
                params,
                authored_endpoint([7, 11], 4, 37, false, 0, 4)
            ));
        }
    });
}
