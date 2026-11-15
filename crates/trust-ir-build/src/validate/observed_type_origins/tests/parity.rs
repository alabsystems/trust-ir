// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn first_physical_holder_and_struct_then_enum_order_are_exact() {
    let out = run(&fixture()).0;
    assert_eq!(out.len(), 3);
    for (error, first, second, table) in [
        (&out[0], "first", "later", "struct"),
        (&out[1], "first", "cross-table", "enum"),
        (&out[2], "clean-first", "clean-later", "enum"),
    ] {
        assert!(
            matches!(error,ValidationError::TypeOriginConflict{first:a,second:b,first_table:"struct",second_table:t,first_module:None,second_module:None,..} if a==first && b==second && *t==table)
        );
    }
}
#[test]
fn absent_keys_never_match_and_same_names_ids_or_structure_do_not_supply_a_key() {
    let mut m = fixture();
    for s in &mut m.structs {
        s.origin = None;
        s.name = "same".into();
    }
    for e in &mut m.enums {
        e.origin = None;
        e.name = "same".into();
    }
    assert!(run(&m).0.is_empty());
}
#[test]
fn all_rust_fields_and_digest_algorithm_and_last_bytes_distinguish_keys() {
    let a = rust();
    for case in 0..4 {
        let mut b = a.clone();
        if let TypeOrigin::Rust {
            stable_crate_id,
            def_path_hash,
            args_digest,
        } = &mut b
        {
            match case {
                0 => *stable_crate_id ^= 1,
                1 => def_path_hash[15] ^= 1,
                2 => args_digest.algorithm = ProofDigestAlgorithm::TrustIrStableV1,
                3 => args_digest.bytes[31] ^= 1,
                _ => unreachable!(),
            }
        }
        assert!(!equality(&a, &b).0);
        let mut m = Module::new("distinct");
        m.structs = vec![strukt(0, "a", Some(a.clone())), strukt(1, "b", Some(b))];
        assert!(run(&m).0.is_empty());
    }
    assert!(equality(&a, &a).0);
}
#[test]
fn clean_variant_full_decl_and_both_digest_fields_are_not_normalized() {
    let a = clean();
    for case in 0..3 {
        let mut b = a.clone();
        if let TypeOrigin::Clean { decl, env_digest } = &mut b {
            match case {
                0 => decl.push('x'),
                1 => env_digest.algorithm = ProofDigestAlgorithm::Sha256,
                2 => env_digest.bytes[31] ^= 1,
                _ => unreachable!(),
            }
        }
        assert!(!equality(&a, &b).0);
    }
    assert!(equality(&a, &a).0);
    assert!(!equality(&a, &rust()).0);
    assert!(!equality(&rust(), &a).0);
}
#[test]
fn exact_rust_zero_padded_hex_numeric_extremes_and_full_digest_spelling() {
    for n in [0, 1, u64::MAX] {
        for algorithm in [
            ProofDigestAlgorithm::Sha256,
            ProofDigestAlgorithm::TrustIrStableV1,
        ] {
            let origin = TypeOrigin::Rust {
                stable_crate_id: n,
                def_path_hash: [0xff; 16],
                args_digest: digest(algorithm, 0xab),
            };
            let (text, _) = spelling(&origin);
            assert!(text.starts_with(&format!("rust(crate={n:#018x}, path={}", "ff".repeat(16))));
            assert!(text.ends_with("ab)"));
        }
    }
}
#[test]
fn exact_clean_debug_unicode_escaping_apostrophes_and_full_names_survive() {
    for decl in [
        "",
        "'\"\\\n\r\t\0\u{7f}",
        "λ中😀",
        "a\u{301}\u{200d}\u{2028}\u{e000}\u{10ffff}",
    ] {
        spelling(&TypeOrigin::Clean {
            decl: decl.into(),
            env_digest: digest(ProofDigestAlgorithm::Sha256, 5),
        });
    }
    let origin = TypeOrigin::Clean {
        decl: "λ".repeat(3000) + "tail",
        env_digest: digest(ProofDigestAlgorithm::Sha256, 7),
    };
    let mut m = Module::new("long");
    m.structs = vec![
        strukt(0, &("first".repeat(1000) + "a"), Some(origin.clone())),
        strukt(1, &("second".repeat(1000) + "b"), Some(origin)),
    ];
    assert_eq!(run(&m).0.len(), 1);
}
#[test]
fn all_later_same_origin_rows_reference_only_the_first_even_across_duplicate_ids() {
    let mut m = Module::new("many");
    m.structs = (0..20)
        .map(|i| strukt(7, &format!("s{i}"), Some(rust())))
        .collect();
    m.enums = (0..10)
        .map(|i| enm(7, &format!("e{i}"), Some(rust())))
        .collect();
    let out = run(&m).0;
    assert_eq!(out.len(), 29);
    assert!(
        out.iter()
            .all(|e| matches!(e,ValidationError::TypeOriginConflict{first,..} if first=="s0"))
    );
}
#[test]
fn origin_rule_ignores_unrelated_struct_fields_and_enum_payloads() {
    let mut m = fixture();
    let (_, before) = run(&m);
    for s in &mut m.structs {
        s.fields = vec![trust_ir::ty::FieldDef {
            name: "untrusted".repeat(1000),
            ty: Ty::Tuple(vec![Ty::Error; 1000]),
            offset: None,
        }];
    }
    let (_, after) = run(&m);
    assert_eq!(before.events, after.events);
}
