// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Downstream controls for the exact Clean dependency's checked inductive
//! admission boundary. These exercise public kernel APIs, not an unchecked
//! fixture path, and do not prove the Rust kernel or its compiled binary sound.

use clean_kernel::env::EnvError;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{Environment, Expr, Name, TypeChecker};

fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn family(name: &str, constructor: &str) -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string(name),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string(constructor),
                type_: constant(name),
            }],
        }],
    }
}

fn mutual_family() -> InductiveDecl {
    let mut declaration = family("NamespaceLeft", "NamespaceLeft.mk");
    declaration
        .types
        .extend(family("NamespaceRight", "NamespaceRight.mk").types);
    declaration
}

fn admit(
    env: &mut Environment,
    declaration: InductiveDecl,
    core_only: bool,
) -> Result<(), EnvError> {
    if core_only {
        env.add_inductive_core(declaration)
    } else {
        env.add_inductive(declaration)
    }
}

fn table_state(env: &Environment) -> (usize, usize, usize, usize, u64) {
    (
        env.num_constants(),
        env.num_inductives(),
        env.num_constructors(),
        env.num_recursors(),
        env.generation(),
    )
}

fn declaration_names(declaration: &InductiveDecl) -> Vec<Name> {
    declaration
        .types
        .iter()
        .flat_map(|family| {
            let mut names = vec![family.name.clone()];
            names.extend(family.constructors.iter().map(|ctor| ctor.name.clone()));
            for suffix in ["rec", "casesOn", "recOn", "noConfusionType", "noConfusion"] {
                names.push(Name::from_string(&format!("{}.{suffix}", family.name)));
            }
            names
        })
        .collect()
}

fn metadata(env: &Environment, declaration: &InductiveDecl) -> Vec<serde_json::Value> {
    // These public metadata types lack PartialEq. Compare every serialized
    // field, including constructor ownership and recursor rules, not Debug
    // strings or table counts alone. This snapshot is not proof evidence.
    declaration_names(declaration)
        .iter()
        .map(|name| {
            serde_json::to_value((
                name,
                env.get_const(name),
                env.get_inductive(name),
                env.get_constructor(name),
                env.get_recursor(name),
            ))
            .expect("serialize the public declaration metadata")
        })
        .collect()
}

fn assert_absent(env: &Environment, declaration: &InductiveDecl) {
    for name in declaration_names(declaration) {
        assert!(env.get_const(&name).is_none(), "unexpected constant {name}");
        assert!(
            env.get_inductive(&name).is_none(),
            "unexpected inductive {name}"
        );
        assert!(
            env.get_constructor(&name).is_none(),
            "unexpected constructor {name}"
        );
        assert!(
            env.get_recursor(&name).is_none(),
            "unexpected recursor {name}"
        );
    }
}

fn assert_typed(env: &Environment, declaration: &InductiveDecl) {
    let checker = TypeChecker::new(env);
    for family in &declaration.types {
        let family_expr = Expr::const_(family.name.clone(), vec![]);
        assert_eq!(
            checker
                .infer_type_full(&family_expr)
                .expect("infer the admitted family"),
            Expr::type_()
        );
        assert!(env.get_inductive(&family.name).is_some());
        assert!(
            env.get_recursor(&Name::from_string(&format!("{}.rec", family.name)))
                .is_some(),
            "admission must really generate a recursor"
        );
        for (index, constructor) in family.constructors.iter().enumerate() {
            let stored = env
                .get_constructor(&constructor.name)
                .expect("admission must store actual constructor metadata");
            assert_eq!(stored.inductive_name, family.name);
            assert_eq!(stored.constructor_idx as usize, index);
            assert_eq!(stored.type_, constructor.type_);
            assert_eq!(
                checker
                    .infer_type_full(&Expr::const_(constructor.name.clone(), vec![]))
                    .expect("fully infer the actual admitted constructor"),
                family_expr
            );
        }
    }
}

fn populated_environment(core_only: bool) -> (Environment, InductiveDecl) {
    let mut env = Environment::new();
    let retained = family("NamespaceRetained", "NamespaceRetained.mk");
    admit(&mut env, retained.clone(), core_only).expect("admit the retained positive control");
    assert_typed(&env, &retained);
    (env, retained)
}

fn assert_duplicate(error: EnvError, collision: &str, core_only: bool) {
    assert!(
        matches!(error, EnvError::DuplicateName(ref name) if name == &Name::from_string(collision)),
        "core_only={core_only}: expected DuplicateName({collision}), got {error:?}"
    );
}

#[test]
fn own_family_collision_returns_an_error_without_mutating_the_environment() {
    for core_only in [false, true] {
        let (mut env, retained) = populated_environment(core_only);
        let before = table_state(&env);
        let retained_metadata = metadata(&env, &retained);
        let invalid = family("NamespaceSelf", "NamespaceSelf");
        assert_absent(&env, &invalid);

        // No catch_unwind: a panic must fail this control, not masquerade as
        // the required checked refusal. The older pin panicked in debug here.
        let error = admit(&mut env, invalid.clone(), core_only)
            .expect_err("a family/constructor collision must return an error, not panic");
        assert_duplicate(error, "NamespaceSelf", core_only);
        assert_eq!(table_state(&env), before);
        assert_eq!(metadata(&env, &retained), retained_metadata);
        assert_absent(&env, &invalid);
        assert_typed(&env, &retained);

        let valid = family("NamespaceSelf", "NamespaceSelf.mk");
        admit(&mut env, valid.clone(), core_only)
            .expect("the same family with a distinct constructor remains admissible");
        assert_typed(&env, &valid);
        assert_typed(&env, &retained);
        assert_eq!(metadata(&env, &retained), retained_metadata);
    }
}

#[test]
fn sibling_family_collision_is_transactional_in_both_mutual_orders() {
    for core_only in [false, true] {
        for reversed in [false, true] {
            let (mut env, retained) = populated_environment(core_only);
            let before = table_state(&env);
            let retained_metadata = metadata(&env, &retained);
            let mut valid = mutual_family();
            let mut invalid = valid.clone();
            invalid.types[0].constructors[0].name = Name::from_string("NamespaceRight");
            if reversed {
                invalid.types.reverse();
                valid.types.reverse();
            }
            assert_absent(&env, &invalid);
            let error = admit(&mut env, invalid.clone(), core_only).unwrap_err();
            assert_duplicate(error, "NamespaceRight", core_only);
            assert_eq!(table_state(&env), before, "reversed={reversed}");
            assert_eq!(metadata(&env, &retained), retained_metadata);
            assert_absent(&env, &invalid);
            assert_typed(&env, &retained);

            admit(&mut env, valid.clone(), core_only)
                .expect("the distinct-name mutual block in the same order must succeed");
            assert_typed(&env, &valid);
            assert_typed(&env, &retained);
            assert_eq!(metadata(&env, &retained), retained_metadata);
        }
    }
}

#[test]
fn genuine_reregistration_is_a_noop_but_duplicate_payload_is_refused() {
    for core_only in [false, true] {
        let (mut env, retained) = populated_environment(core_only);
        let valid = mutual_family();
        admit(&mut env, valid.clone(), core_only).expect("genuinely admit the mutual block");
        assert_typed(&env, &valid);
        let before = table_state(&env);
        let retained_metadata = metadata(&env, &retained);
        let mutual_metadata = metadata(&env, &valid);

        admit(&mut env, valid.clone(), core_only)
            .expect("an identical valid re-registration remains a successful no-op");
        assert_eq!(table_state(&env), before);
        assert_eq!(metadata(&env, &valid), mutual_metadata);
        assert_eq!(metadata(&env, &retained), retained_metadata);

        let mut invalid = valid.clone();
        let repeated = invalid.types[0].constructors[0].clone();
        invalid.types[0].constructors.push(repeated);
        let error = admit(&mut env, invalid, core_only)
            .expect_err("already-present names must not bypass intra-block uniqueness");
        assert_duplicate(error, "NamespaceLeft.mk", core_only);
        assert_eq!(table_state(&env), before);
        assert_eq!(metadata(&env, &valid), mutual_metadata);
        assert_eq!(metadata(&env, &retained), retained_metadata);
        assert_typed(&env, &valid);
        assert_typed(&env, &retained);

        let fresh = family("NamespaceAfterRefusal", "NamespaceAfterRefusal.mk");
        admit(&mut env, fresh.clone(), core_only)
            .expect("refusing the duplicate packet must not poison later admission");
        assert_typed(&env, &fresh);
        assert_eq!(metadata(&env, &valid), mutual_metadata);
        assert_eq!(metadata(&env, &retained), retained_metadata);
    }
}
