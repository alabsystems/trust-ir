// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
use super::*;
use clean_kernel::KernelTypeError;

fn z(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string(name), vec![Level::zero()]),
        args,
    )
}
fn environment() -> Environment {
    let mut env = Environment::default();
    install_indexed_domain_into(&mut env).unwrap();
    install_enumerated_domain_into(&mut env).unwrap();
    env
}
fn capture(name: &str, goal: &Expr, proof: &Expr, verdict: &str) {
    if let Some(root) = std::env::var_os("TRUST_IR_ENUMERATION_ARTIFACT_DIR") {
        let root = std::path::PathBuf::from(root).join(name);
        std::fs::create_dir_all(&root).unwrap();
        for (name, value) in [("goal.bin", goal), ("proof.bin", proof)] {
            std::fs::write(
                root.join(name),
                trust_ir::proof::encode_clean_expr_v1(value).unwrap(),
            )
            .unwrap();
        }
        std::fs::write(root.join("verdict.txt"), verdict).unwrap();
    }
}
fn check(env: &Environment, name: &str, goal: Expr, proof: Expr, accepted: bool) {
    let decode = |e: &Expr| {
        trust_ir::proof::decode_clean_expr_v1(&trust_ir::proof::encode_clean_expr_v1(e).unwrap())
            .unwrap()
    };
    let (goal, proof) = (decode(&goal), decode(&proof));
    let mut tc = TypeChecker::new(env);
    tc.set_heartbeat_limit(HEARTBEAT_LIMIT);
    tc.set_max_cache_entries(CACHE_ENTRY_LIMIT);
    let _goal_type = tc.infer_type(&goal).unwrap();
    let _proof_type = tc.infer_type(&proof).unwrap();
    let verdict = tc.check_type(&proof, &goal);
    if accepted {
        verdict.unwrap();
        assert!(env.audit_certification(&goal, &proof).is_certified());
        capture(
            name,
            &goal,
            &proof,
            "kernel accepted finite enumeration component; no provider/source/native authority\n",
        );
    } else {
        assert!(matches!(
            verdict.unwrap_err(),
            KernelTypeError::TypeMismatch { .. }
        ));
        assert!(!tc.heartbeat_spent());
        capture(
            name,
            &goal,
            &proof,
            "semantic TypeMismatch; no provider/source/native authority\n",
        );
    }
}

#[test]
fn symbolic_enumeration_laws_recheck_and_retain_existing_domain_wires() {
    let mut env = Environment::default();
    install_indexed_domain_into(&mut env).unwrap();
    let old_names = [
        DOMAIN_LENGTH,
        DOMAIN_STEP,
        DOMAIN_FOLD,
        DOMAIN_COMPLETE,
        DOMAIN_AT,
        DOMAIN_AT_MEMBERS,
        DOMAIN_AT_SOUND,
        DOMAIN_AT_COVER,
        DOMAIN_AT_END,
    ];
    let old: Vec<_> = old_names
        .iter()
        .map(|name| {
            let info = env.get_const(&Name::from_string(name)).unwrap();
            (info.type_.clone(), info.value.clone())
        })
        .collect();
    install_enumerated_domain_into(&mut env).unwrap();
    for (name, (ty, value)) in old_names.into_iter().zip(old) {
        let info = env.get_const(&Name::from_string(name)).unwrap();
        assert_eq!(info.type_, ty);
        assert_eq!(info.value, value);
        capture(
            &format!("old-wire-{}", name.rsplit('.').next().unwrap()),
            &ty,
            value.as_ref().unwrap(),
            "type/body bytes unchanged by the additive installer\n",
        );
    }
    for name in &NAMES[1..] {
        recheck_theorem(&env, name).unwrap();
        let info = env.get_const(&Name::from_string(name)).unwrap();
        capture(
            name.rsplit('.').next().unwrap(),
            &info.type_,
            info.value.as_ref().unwrap(),
            "generic theorem rechecked by the kernel; no provider/source/native authority\n",
        );
    }
    assert!(install_enumerated_domain_into(&mut env).is_err());
}

#[test]
fn ordinary_counted_table_consumer_uses_symbolic_indices_and_allows_repeated_values() {
    let env = environment();
    let nat = Expr::const_str("Nat");
    let f = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::apps(
            Expr::const_str("Nat.add"),
            [Expr::bvar(0), Expr::nat_lit(7)],
        ),
    );
    let values = z(DOMAIN_ENUMERATE, [nat.clone(), f.clone(), Expr::nat_lit(3)]);
    // Instantiate actual theorem telescopes rather than naming an unchecked
    // result. The table is symbolic data, not emitted or Rust-materialized rows.
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            nat.clone(),
            z(DOMAIN_LENGTH, [nat.clone(), values.clone()]),
            Expr::nat_lit(3),
        ],
    );
    check(
        &env,
        "ordinary-table-exact-count",
        goal,
        z(
            DOMAIN_ENUMERATE_LENGTH,
            [nat.clone(), f.clone(), Expr::nat_lit(3)],
        ),
        true,
    );
    let opt = z("Option", [nat.clone()]);
    let expected = z("Option.some", [nat.clone(), Expr::nat_lit(8)]);
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            opt.clone(),
            z(DOMAIN_AT, [nat.clone(), values, Expr::nat_lit(1)]),
            expected.clone(),
        ],
    );
    let proof = z(
        DOMAIN_ENUMERATE_SOME,
        [
            nat.clone(),
            f,
            Expr::nat_lit(3),
            Expr::nat_lit(1),
            Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.refl"),
                    vec![Level::succ(Level::zero())],
                ),
                [Expr::const_str("Bool"), flag(true)],
            ),
        ],
    );
    check(&env, "ordinary-table-selected-index", goal, proof, true);
    let identity = Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0));
    let values = z(
        DOMAIN_ENUMERATE,
        [nat.clone(), identity.clone(), Expr::nat_lit(3)],
    );
    for (name, index, theorem, bound) in [
        ("ordinary-table-exact-end", 3, DOMAIN_ENUMERATE_END, false),
        ("ordinary-table-after-end", 5, DOMAIN_ENUMERATE_NONE, true),
    ] {
        let goal = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [
                opt.clone(),
                z(
                    DOMAIN_AT,
                    [nat.clone(), values.clone(), Expr::nat_lit(index)],
                ),
                z("Option.none", [nat.clone()]),
            ],
        );
        let mut args = vec![nat.clone(), identity.clone(), Expr::nat_lit(3)];
        if bound {
            args.push(Expr::nat_lit(index));
            args.push(Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.refl"),
                    vec![Level::succ(Level::zero())],
                ),
                [Expr::const_str("Bool"), flag(false)],
            ));
        }
        check(&env, name, goal, z(theorem, args), true);
    }
    let empty = z(
        DOMAIN_ENUMERATE,
        [nat.clone(), identity.clone(), Expr::nat_lit(0)],
    );
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            opt,
            z(DOMAIN_AT, [nat.clone(), empty, Expr::nat_lit(0)]),
            z("Option.none", [nat.clone()]),
        ],
    );
    check(
        &env,
        "ordinary-empty-table-end",
        goal,
        z(
            DOMAIN_ENUMERATE_END,
            [nat.clone(), identity, Expr::nat_lit(0)],
        ),
        true,
    );
    let repeated = Expr::lam(BinderInfo::Default, nat.clone(), Expr::nat_lit(9));
    let values = z(
        DOMAIN_ENUMERATE,
        [nat.clone(), repeated.clone(), Expr::nat_lit(3)],
    );
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            nat.clone(),
            z(DOMAIN_LENGTH, [nat.clone(), values]),
            Expr::nat_lit(3),
        ],
    );
    check(
        &env,
        "ordinary-repeated-values-keep-count",
        goal,
        z(DOMAIN_ENUMERATE_LENGTH, [nat, repeated, Expr::nat_lit(3)]),
        true,
    );
}

#[test]
fn symbolic_enumeration_rejects_wrong_index_count_and_premature_exhaustion() {
    let env = environment();
    let nat = Expr::const_str("Nat");
    let f = Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0));
    let values = z(DOMAIN_ENUMERATE, [nat.clone(), f, Expr::nat_lit(3)]);
    let opt = z("Option", [nat.clone()]);
    for (name, ty, actual, wrong) in [
        (
            "wrong-index",
            opt.clone(),
            z(DOMAIN_AT, [nat.clone(), values.clone(), Expr::nat_lit(1)]),
            z("Option.some", [nat.clone(), Expr::nat_lit(2)]),
        ),
        (
            "wrong-count",
            nat.clone(),
            z(DOMAIN_LENGTH, [nat.clone(), values.clone()]),
            Expr::nat_lit(2),
        ),
        (
            "premature-exhaustion",
            opt.clone(),
            z(DOMAIN_AT, [nat.clone(), values.clone(), Expr::nat_lit(2)]),
            z("Option.none", [nat.clone()]),
        ),
        (
            "invented-after-end",
            opt,
            z(DOMAIN_AT, [nat.clone(), values, Expr::nat_lit(3)]),
            z("Option.some", [nat, Expr::nat_lit(3)]),
        ),
    ] {
        let goal = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [ty.clone(), actual, wrong.clone()],
        );
        let proof = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [ty, wrong],
        );
        check(&env, name, goal, proof, false);
    }
}
