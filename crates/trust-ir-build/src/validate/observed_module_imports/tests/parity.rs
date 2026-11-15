// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn complete_row_equality_matches_derived_identity_for_every_current_field_and_producer() {
    let mut variants = vec![];
    for producer in [
        None,
        Some(Producer::TRust),
        Some(Producer::Clean),
        Some(Producer::TrustIr),
        Some(Producer::TSwift),
        Some(Producer::TC),
        Some(Producer::Other("".into())),
        Some(Producer::Other("λ\0full".into())),
    ] {
        for scheme in IdentityScheme::ALL {
            for algorithm in [
                ProofDigestAlgorithm::Sha256,
                ProofDigestAlgorithm::TrustIrStableV1,
            ] {
                let mut import = row("same");
                import.producer = producer.clone();
                import.scheme = scheme;
                import.digest.algorithm = algorithm;
                variants.push(import);
            }
        }
    }
    let mut renamed = row("different");
    variants.push(renamed.clone());
    renamed.name.clear();
    variants.push(renamed);
    let mut byte = row("same");
    byte.digest.bytes[31] ^= 1;
    variants.push(byte);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    for a in &variants {
        for b in &variants {
            assert_eq!(work.import_equal(a, b).unwrap(), a == b);
        }
    }
    assert!(work.session.first_refusal().is_none());
    assert_eq!(
        work.session.remaining_fuel(),
        InterpretOptions::default().fuel
    );
}
#[test]
fn interning_precedes_identity_and_reports_every_later_duplicate_against_the_first() {
    let m = fixture();
    let (out, _) = run(&m);
    assert_eq!(
        out,
        vec![
            ValidationError::ImportTableNotInterned {
                first: 0,
                duplicate: 1,
                name: "a".into()
            },
            ValidationError::ImportTableNotInterned {
                first: 2,
                duplicate: 3,
                name: "b".into()
            },
            ValidationError::ImportIdentityConflict {
                first: 0,
                conflicting: 2,
                first_name: "a".into(),
                conflicting_name: "b".into()
            },
            ValidationError::ImportIdentityConflict {
                first: 0,
                conflicting: 3,
                first_name: "a".into(),
                conflicting_name: "b".into()
            }
        ]
    );
}
#[test]
fn mixed_recorded_producers_and_schemes_keep_distinct_rows_and_coherent_artifact_names() {
    let mut m = Module::new("mixed");
    m.imports = vec![
        row("dep").with_producer(Producer::TRust),
        row("dep").with_producer(Producer::Clean),
        row("dep"),
        row("dep").with_scheme(IdentityScheme::V2),
    ];
    assert!(run(&m).0.is_empty());
    m.imports.push(m.imports[1].clone());
    assert_eq!(
        run(&m).0,
        vec![ValidationError::ImportTableNotInterned {
            first: 1,
            duplicate: 4,
            name: "dep".into()
        }]
    );
}
#[test]
fn identity_ignores_scheme_producer_but_compares_the_full_digest_algorithm_and_bytes() {
    let mut m = Module::new("identity");
    let a = row("first").with_scheme(IdentityScheme::V2);
    let mut b = row("second").with_producer(Producer::Other("producer".into()));
    let mut c = row("third");
    c.digest.algorithm = ProofDigestAlgorithm::TrustIrStableV1;
    let mut d = row("fourth");
    d.digest.bytes[31] ^= 1;
    m.imports = vec![a, b.clone(), c, d];
    let (out, _) = run(&m);
    assert_eq!(
        out,
        vec![ValidationError::ImportIdentityConflict {
            first: 0,
            conflicting: 1,
            first_name: "first".into(),
            conflicting_name: "second".into()
        }]
    );
    b.name = "first".into();
    m.imports[1] = b;
    assert!(run(&m).0.is_empty());
}
#[test]
fn first_stored_name_survives_conflicting_rows_and_unicode_empty_names_are_not_normalized() {
    let mut m = Module::new("first");
    m.imports = vec![row(""), row(" λ\0"), row(""), row(" λ\0")];
    let (out, _) = run(&m);
    assert_eq!(out.len(), 4);
    assert_eq!(
        out[2],
        ValidationError::ImportIdentityConflict {
            first: 0,
            conflicting: 1,
            first_name: "".into(),
            conflicting_name: " λ\0".into()
        }
    );
    assert_eq!(
        out[3],
        ValidationError::ImportIdentityConflict {
            first: 0,
            conflicting: 3,
            first_name: "".into(),
            conflicting_name: " λ\0".into()
        }
    );
}
#[test]
fn full_long_name_and_other_producer_tails_participate_in_row_identity() {
    let name = "λ".repeat(3000);
    let mut m = Module::new("long");
    let a = row(&name).with_producer(Producer::Other(format!("{}a", "p".repeat(4000))));
    let mut b = a.clone();
    b.producer = Some(Producer::Other(format!("{}b", "p".repeat(4000))));
    m.imports = vec![a.clone(), b, a];
    assert_eq!(
        run(&m).0,
        vec![ValidationError::ImportTableNotInterned {
            first: 0,
            duplicate: 2,
            name
        }]
    );
}
#[test]
fn empty_table_has_no_diagnostics_and_unrelated_module_payloads_are_outside_this_rule() {
    let mut m = Module::new("empty");
    m.types = vec![Ty::Tuple(vec![Ty::Error; 10_000])];
    let (out, o) = run(&m);
    assert!(out.is_empty());
    assert!(o.work < 100);
}
#[test]
fn diagnostic_id_saturation_matches_original_without_truncating_a_physical_row_search() {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    for n in [0, 1, u32::MAX as usize, usize::MAX] {
        assert_eq!(work.id(n).unwrap(), u32::try_from(n).unwrap_or(u32::MAX));
    }
    if let Some(n) = (u32::MAX as usize).checked_add(1) {
        assert_eq!(work.id(n).unwrap(), u32::MAX);
    }
}
