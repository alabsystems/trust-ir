// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Downstream controls for the exact Clean projection-checking dependency.
//! These execute kernel APIs; they do not prove the Rust implementation sound.

use clean_kernel::cert::{CertVerifier, ProofCert};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{BinderInfo, Environment, Expr, Name, TypeChecker};
use std::sync::Arc;

fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn environment() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("admit Nat");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("ProjectionProof"),
            type_: Expr::prop(),
            constructors: vec![Constructor {
                name: Name::from_string("ProjectionProof.intro"),
                type_: constant("ProjectionProof"),
            }],
        }],
    })
    .expect("admit a real inhabited proposition");
    env
}

fn structure(
    env: &mut Environment,
    name: &str,
    in_prop: bool,
    fields: Vec<Expr>,
    values: Vec<Expr>,
) -> (Name, Expr) {
    let name_id = Name::from_string(name);
    let constructor = format!("{name}.mk");
    let constructor_type = fields
        .into_iter()
        .rev()
        .fold(constant(name), |body, domain| {
            Expr::pi(BinderInfo::Default, domain, body)
        });
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name_id.clone(),
            type_: if in_prop { Expr::prop() } else { Expr::type_() },
            constructors: vec![Constructor {
                name: Name::from_string(&constructor),
                type_: constructor_type,
            }],
        }],
    })
    .expect("the structure must be admitted without unchecked declarations");
    let inner = values.into_iter().fold(constant(&constructor), Expr::app);
    assert_eq!(
        TypeChecker::new(env).infer_type_full(&inner).unwrap(),
        constant(name)
    );
    (name_id, inner)
}

fn assert_rejected_projection(env: &Environment, name: Name, inner: Expr, index: u32) {
    let (inner_type, inner_cert) = TypeChecker::new(env)
        .infer_type_with_cert(&inner)
        .expect("produce the genuine checked inner certificate");
    assert_eq!(
        CertVerifier::new(env).verify(&inner_cert, &inner).unwrap(),
        inner_type
    );
    let projection = Expr::proj(name.clone(), index, inner);
    let expected_error = |error| {
        matches!(error, clean_kernel::KernelTypeError::InvalidProjFromProp { field_idx }
            if field_idx == index)
    };
    assert!(expected_error(
        TypeChecker::new(env).infer_type(&projection).unwrap_err()
    ));
    assert!(expected_error(
        TypeChecker::new(env)
            .infer_type_with_cert(&projection)
            .unwrap_err()
    ));
    // Both the inner certificate and claimed domain are correct. The defect
    // was missing Prop-elimination eligibility, not a forged type claim.
    let certificate = ProofCert::Proj {
        struct_name: name,
        idx: index,
        expr_cert: Arc::new(inner_cert),
        expr_type: Box::new(inner_type),
        field_type: Box::new(constant("Nat")),
    };
    assert!(
        CertVerifier::new(env)
            .verify(&certificate, &projection)
            .is_err(),
        "forbidden Prop-to-data extraction cannot acquire certificate authority"
    );
}

#[test]
fn genuine_inner_certificate_cannot_authorize_prop_to_data_projection() {
    let mut env = environment();
    let (name, inner) = structure(
        &mut env,
        "PropWithData",
        true,
        vec![constant("Nat")],
        vec![Expr::nat_lit(7)],
    );
    assert_rejected_projection(&env, name, inner, 0);
}

#[test]
fn proof_fields_survive_unused_data_fields_and_repeated_queries() {
    let mut env = environment();
    let (name, inner) = structure(
        &mut env,
        "MixedProofFields",
        true,
        vec![
            constant("ProjectionProof"),
            constant("Nat"),
            constant("ProjectionProof"),
        ],
        vec![
            constant("ProjectionProof.intro"),
            Expr::nat_lit(7),
            constant("ProjectionProof.intro"),
        ],
    );
    let public = TypeChecker::new(&env);
    let certified = TypeChecker::new(&env);
    for index in [0, 2, 0, 2] {
        let projection = Expr::proj(name.clone(), index, inner.clone());
        assert_eq!(
            public.infer_type(&projection).unwrap(),
            constant("ProjectionProof")
        );
        let (ty, certificate) = certified.infer_type_with_cert(&projection).unwrap();
        assert_eq!(ty, constant("ProjectionProof"));
        assert_eq!(
            CertVerifier::new(&env)
                .verify(&certificate, &projection)
                .unwrap(),
            ty
        );
    }
    // A successful prefix must not make the unused data projection eligible.
    let forbidden = Expr::proj(name.clone(), 1, inner.clone());
    assert!(public.infer_type(&forbidden).is_err());
    assert!(certified.infer_type_with_cert(&forbidden).is_err());
    assert_rejected_projection(&env, name, inner, 1);
}

fn assert_capacity_independent(capacity: usize) {
    let mut env = environment();
    // Both sliding cache generations must turn over before the walk ends.
    let fields = 2 * (capacity + 1) + 1;
    let (name, inner) = structure(
        &mut env,
        "DataFields",
        false,
        vec![constant("Nat"); fields],
        (0..fields)
            .map(|index| Expr::nat_lit(index as u64))
            .collect(),
    );
    for descending in [false, true] {
        let mut public = TypeChecker::new(&env);
        let mut certified = TypeChecker::new(&env);
        public.set_max_cache_entries(capacity);
        certified.set_max_cache_entries(capacity);
        for step in 0..(fields * 3) {
            let index = if descending {
                fields - 1 - step % fields
            } else {
                step % fields
            };
            let projection = Expr::proj(name.clone(), index as u32, inner.clone());
            assert_eq!(
                public.infer_type(&projection).unwrap_or_else(|error| {
                    panic!("capacity {capacity}, field {index}: {error:?}")
                }),
                constant("Nat")
            );
            let (ty, certificate) = certified.infer_type_with_cert(&projection).unwrap();
            assert_eq!(ty, constant("Nat"));
            assert_eq!(
                CertVerifier::new(&env)
                    .verify(&certificate, &projection)
                    .unwrap(),
                ty
            );
        }
    }
}

#[test]
fn zero_cache_capacity_does_not_reject_valid_data_projection() {
    assert_capacity_independent(0);
}

#[test]
fn one_cache_entry_does_not_reject_valid_data_projection() {
    assert_capacity_independent(1);
}
