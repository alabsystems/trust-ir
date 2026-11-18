// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Canonical, resource-bounded legacy-bincode carrier for Clean kernel terms.
//!
//! Existing TrustIR/Clean TV and contract payloads use bincode 1.x's historical
//! helper-function wire format: little-endian fixed-width integers. This module
//! preserves those bytes while replacing the legacy decoder's unlimited and
//! trailing-byte-accepting behavior with one exact whole-slice contract.

#[cfg(test)]
use super::clean_proof_carrier::KERNEL_ENVIRONMENT_DIGEST_V1_DOMAIN;
use super::clean_proof_carrier::{
    CLEAN_EXPR_V1_MAX_BYTES, KernelConstantV1, KernelConstructorV1, KernelEnvironmentDigestV1,
    KernelInductiveV1, KernelQuotientV1, KernelRecursorRuleV1, KernelRecursorV1,
    clean_cic_statement_carrier_digest_v1, codec, encode_clean_expr_carrier_v1,
};
use super::evidence::ProofDigest;
use bincode::Options;
#[cfg(test)]
use clean_kernel::env::ConstantInfo;
use clean_kernel::env::{Declaration, Environment};
#[cfg(test)]
use clean_kernel::{ConstructorVal, InductiveVal, QuotVal, RecursorVal};
use clean_kernel::{DecodeResourceLimits, Expr, Name};

/// Maximum aggregate Expr/Level/Name nodes decoded from one carrier.
pub const CLEAN_EXPR_V1_MAX_NODES: usize = 2_000_000;
/// Maximum recursive Expr/Level/Name depth decoded from one carrier.
pub const CLEAN_EXPR_V1_MAX_DEPTH: usize = 4_096;

/// Encode this kernel's expression through the shared unchanged v1 carrier.
/// This compatibility wrapper retains the existing nominal API; the carrier
/// itself is data only and the consumer's decoder/replay remains mandatory.
pub fn encode_clean_expr_v1(expr: &Expr) -> Result<Vec<u8>, String> {
    encode_clean_expr_carrier_v1(expr)
}

/// Identify this kernel's statement using the shared unchanged v1 domain.
/// This is an identity, not a kernel judgment or proof admission.
pub fn clean_cic_statement_digest(statement: &Expr) -> Result<ProofDigest, String> {
    clean_cic_statement_carrier_digest_v1(statement)
}

/// Decode one untrusted kernel expression with exact whole-slice, byte, node,
/// depth, and canonical-reencoding checks.
pub fn decode_clean_expr_v1(bytes: &[u8]) -> Result<Expr, String> {
    decode_with_limits(
        bytes,
        CLEAN_EXPR_V1_MAX_BYTES,
        CLEAN_EXPR_V1_MAX_NODES,
        CLEAN_EXPR_V1_MAX_DEPTH,
    )
}

fn decode_with_limits(
    bytes: &[u8],
    max_bytes: usize,
    max_nodes: usize,
    max_depth: usize,
) -> Result<Expr, String> {
    if bytes.len() > max_bytes {
        return Err(format!(
            "Clean Expr v1 carrier is {} bytes, exceeds limit {max_bytes}",
            bytes.len()
        ));
    }
    let expr = clean_kernel::with_decode_resource_limits(
        DecodeResourceLimits {
            max_nodes,
            max_depth,
        },
        || codec(max_bytes).deserialize::<Expr>(bytes),
    )
    .map_err(|error| format!("decode Clean Expr v1: {error}"))?;

    // `reject_trailing_bytes` establishes whole-slice consumption. Re-encoding
    // additionally pins one canonical spelling and catches future serde codecs
    // that accept alternate structural representations.
    let canonical = codec(max_bytes)
        .serialize(&expr)
        .map_err(|error| format!("re-encode Clean Expr v1: {error}"))?;
    if canonical != bytes {
        return Err(format!(
            "non-canonical Clean Expr v1 carrier: supplied {} bytes, canonical encoding is {} bytes",
            bytes.len(),
            canonical.len()
        ));
    }
    Ok(expr)
}

/// Maximum encoded size of one island declaration closure (64 MiB) — the
/// same byte ceiling as one [`encode_clean_expr_v1`] carrier.
pub const ISLAND_DECLARATIONS_V1_MAX_BYTES: usize = 64 * 1024 * 1024;
/// Maximum number of declarations one island may carry.
pub const ISLAND_DECLARATIONS_V1_MAX_DECLARATIONS: usize = 4_096;
/// Maximum aggregate Expr/Level/Name nodes decoded from one island (the
/// budget spans EVERY declaration: an island is one carrier, not many).
pub const ISLAND_DECLARATIONS_V1_MAX_NODES: usize = 4_000_000;
/// Maximum recursive Expr/Level/Name depth decoded from one island.
pub const ISLAND_DECLARATIONS_V1_MAX_DEPTH: usize = CLEAN_EXPR_V1_MAX_DEPTH;

/// Encode an island's declaration closure (roadmap WS1.13) in the canonical
/// bincode-1-compatible carrier [`decode_island_declarations_v1`] reads — the
/// bytes an [`IslandEnvironment::declarations`] holds, in the order the
/// validator will insert them (a declaration may cite only the anchor
/// environment and the declarations BEFORE it).
///
/// [`IslandEnvironment::declarations`]: crate::proof::IslandEnvironment::declarations
pub fn encode_island_declarations_v1(declarations: &[Declaration]) -> Result<Vec<u8>, String> {
    if declarations.len() > ISLAND_DECLARATIONS_V1_MAX_DECLARATIONS {
        return Err(format!(
            "island carries {} declarations, exceeds limit {ISLAND_DECLARATIONS_V1_MAX_DECLARATIONS}",
            declarations.len()
        ));
    }
    let bytes = codec(ISLAND_DECLARATIONS_V1_MAX_BYTES)
        .serialize(declarations)
        .map_err(|error| format!("encode island declarations v1: {error}"))?;
    if bytes.len() > ISLAND_DECLARATIONS_V1_MAX_BYTES {
        return Err(format!(
            "island declarations v1 carrier is {} bytes, exceeds limit \
             {ISLAND_DECLARATIONS_V1_MAX_BYTES}",
            bytes.len()
        ));
    }
    Ok(bytes)
}

/// Decode an UNTRUSTED island declaration closure with the same exact
/// whole-slice, byte, node, depth and canonical-re-encoding checks as
/// [`decode_clean_expr_v1`], plus a declaration-count ceiling. This is the
/// anchor's own bounded decoder (`docs/SPEC_RATIFICATIONS.md` §8): nothing
/// else in trust-ir reads the bytes, and a decoded declaration is still
/// nothing until the Clean kernel accepts it on insertion.
pub fn decode_island_declarations_v1(bytes: &[u8]) -> Result<Vec<Declaration>, String> {
    decode_island_with_limits(
        bytes,
        ISLAND_DECLARATIONS_V1_MAX_BYTES,
        ISLAND_DECLARATIONS_V1_MAX_NODES,
        ISLAND_DECLARATIONS_V1_MAX_DEPTH,
        ISLAND_DECLARATIONS_V1_MAX_DECLARATIONS,
    )
}

fn decode_island_with_limits(
    bytes: &[u8],
    max_bytes: usize,
    max_nodes: usize,
    max_depth: usize,
    max_declarations: usize,
) -> Result<Vec<Declaration>, String> {
    if bytes.len() > max_bytes {
        return Err(format!(
            "island declarations v1 carrier is {} bytes, exceeds limit {max_bytes}",
            bytes.len()
        ));
    }
    let declarations = clean_kernel::with_decode_resource_limits(
        DecodeResourceLimits {
            max_nodes,
            max_depth,
        },
        || codec(max_bytes).deserialize::<Vec<Declaration>>(bytes),
    )
    .map_err(|error| format!("decode island declarations v1: {error}"))?;
    if declarations.len() > max_declarations {
        return Err(format!(
            "island carries {} declarations, exceeds limit {max_declarations}",
            declarations.len()
        ));
    }
    let canonical = codec(max_bytes)
        .serialize(&declarations)
        .map_err(|error| format!("re-encode island declarations v1: {error}"))?;
    if canonical != bytes {
        return Err(format!(
            "non-canonical island declarations v1 carrier: supplied {} bytes, canonical \
             encoding is {} bytes",
            bytes.len(),
            canonical.len()
        ));
    }
    Ok(declarations)
}

/// The CONTENT identity of a kernel environment —
/// [`CertificateBinding::environment_digest`] (roadmap WS1.12a; finding
/// F-007): SHA-256 under `trust_ir.clean_cic.environment.v1` over every
/// declaration the environment holds, in a canonical order that does not
/// depend on insertion order or hashing.
///
/// The preimage is: the [`CleanMode`] name; then the constants, inductives,
/// constructors, recursors and quotient primitives, each table sorted by
/// name, each entry spelled with every field that bears on a kernel judgment
/// — names, universe parameters, kind, reducibility, the type (and value
/// where one exists) as v1 carriers, and the structural counts and flags of
/// the inductive family. A lazily-backed environment is refused: its constants
/// are not enumerable, so its identity cannot be stated.
///
/// This is computed by trust-ir over the pinned `clean-kernel`'s public
/// iteration API, not by the kernel itself: the kernel exposes no canonical
/// environment digest (measured at the pinned rev), and a digest defined here
/// is what both the minter and the re-checker run, so they agree by
/// construction. What it establishes: a certificate re-checks only in an
/// environment whose DECLARATIONS equal the minting one's. What it does not:
/// the kernel's own type-checking code is not in the preimage (that is the
/// build identity, WS8.4).
///
/// [`CertificateBinding::environment_digest`]: crate::proof::CertificateBinding::environment_digest
/// [`CleanMode`]: clean_kernel::CleanMode
pub fn kernel_environment_digest(env: &Environment) -> Result<ProofDigest, String> {
    fn names(values: &[Name]) -> Vec<String> {
        values.iter().map(ToString::to_string).collect()
    }
    if env.has_constant_source() {
        return Err(
            "kernel environment is lazily backed: its declarations are not enumerable, so its \
             identity cannot be stated"
                .to_string(),
        );
    }
    let mut constants: Vec<_> = env.constants().collect();
    constants.sort_by_key(|c| c.name.to_string());
    let digest = KernelEnvironmentDigestV1::new(&format!("{:?}", env.mode())).constants(
        constants.into_iter().map(|c| {
            Ok(KernelConstantV1 {
                name: c.name.to_string(),
                level_params: names(&c.level_params),
                kind: format!("{:?}", c.kind),
                is_reducible: c.is_reducible,
                reducibility: format!("{:?}", c.reducibility),
                type_: encode_clean_expr_v1(&c.type_)?,
                value: c.value.as_ref().map(encode_clean_expr_v1).transpose()?,
            })
        }),
    )?;
    let mut inductives: Vec<_> = env.inductives().collect();
    inductives.sort_by_key(|i| i.name.to_string());
    let digest = digest.inductives(inductives.into_iter().map(|i| {
        Ok(KernelInductiveV1 {
            name: i.name.to_string(),
            level_params: names(&i.level_params),
            type_: encode_clean_expr_v1(&i.type_)?,
            num_params: i.num_params,
            num_indices: i.num_indices,
            all_names: names(&i.all_names),
            constructor_names: names(&i.constructor_names),
            flags: [i.is_recursive, i.is_reflexive, i.is_large_elim, i.is_nested],
        })
    }))?;
    let mut constructors: Vec<_> = env.constructors().collect();
    constructors.sort_by_key(|c| c.name.to_string());
    let digest = digest.constructors(constructors.into_iter().map(|c| {
        Ok(KernelConstructorV1 {
            name: c.name.to_string(),
            inductive_name: c.inductive_name.to_string(),
            level_params: names(&c.level_params),
            type_: encode_clean_expr_v1(&c.type_)?,
            num_params: c.num_params,
            num_fields: c.num_fields,
            constructor_idx: c.constructor_idx,
        })
    }))?;
    let mut recursors: Vec<_> = env.recursors().collect();
    recursors.sort_by_key(|r| r.name.to_string());
    let digest = digest.recursors(recursors.into_iter().map(|r| {
        Ok(KernelRecursorV1 {
            name: r.name.to_string(),
            arg_order: format!("{:?}", r.arg_order),
            level_params: names(&r.level_params),
            type_: encode_clean_expr_v1(&r.type_)?,
            inductive_name: r.inductive_name.to_string(),
            counts: [r.num_params, r.num_indices, r.num_motives, r.num_minors],
            rules: r
                .rules
                .iter()
                .map(|rule| {
                    Ok(KernelRecursorRuleV1 {
                        constructor_name: rule.constructor_name.to_string(),
                        num_fields: rule.num_fields,
                        recursive_fields: rule.recursive_fields.clone(),
                        rhs: encode_clean_expr_v1(&rule.rhs)?,
                    })
                })
                .collect::<Result<Vec<_>, String>>()?,
            is_k: r.is_k,
        })
    }))?;
    let mut quotients: Vec<_> = env.quotients().collect();
    quotients.sort_by_key(|q| q.name.to_string());
    digest
        .quotients(quotients.into_iter().map(|q| {
            Ok(KernelQuotientV1 {
                name: q.name.to_string(),
                level_params: names(&q.level_params),
                type_: encode_clean_expr_v1(&q.type_)?,
                kind: format!("{:?}", q.kind),
            })
        }))?
        .finish()
}

// Frozen pre-boundary framing is retained only as an independent ABI regression oracle.
#[cfg(test)]
fn legacy_environment_digest_v1(env: &Environment) -> Result<ProofDigest, String> {
    use super::evidence::{write_len_stable, write_str_stable, write_u8_stable, write_u32_stable};
    fn names(out: &mut Vec<u8>, names: &[Name]) {
        write_len_stable(out, names.len());
        for name in names {
            write_str_stable(out, &name.to_string());
        }
    }
    fn expr(out: &mut Vec<u8>, e: &Expr) -> Result<(), String> {
        let bytes =
            bincode::serialize(e).map_err(|error| format!("legacy Expr carrier: {error}"))?;
        write_len_stable(out, bytes.len());
        out.extend_from_slice(&bytes);
        Ok(())
    }
    fn debug_tag(out: &mut Vec<u8>, value: &dyn core::fmt::Debug) {
        write_str_stable(out, &format!("{value:?}"));
    }
    if env.has_constant_source() {
        return Err(
            "kernel environment is lazily backed: its declarations are not enumerable, so its \
             identity cannot be stated"
                .to_string(),
        );
    }
    let mut out = Vec::new();
    debug_tag(&mut out, &env.mode());

    let mut constants: Vec<&ConstantInfo> = env.constants().collect();
    constants.sort_by_key(|c| c.name.to_string());
    write_len_stable(&mut out, constants.len());
    for c in constants {
        write_str_stable(&mut out, &c.name.to_string());
        names(&mut out, &c.level_params);
        debug_tag(&mut out, &c.kind);
        write_u8_stable(&mut out, u8::from(c.is_reducible));
        debug_tag(&mut out, &c.reducibility);
        expr(&mut out, &c.type_)?;
        match &c.value {
            None => write_u8_stable(&mut out, 0),
            Some(value) => {
                write_u8_stable(&mut out, 1);
                expr(&mut out, value)?;
            }
        }
    }

    let mut inductives: Vec<&InductiveVal> = env.inductives().collect();
    inductives.sort_by_key(|i| i.name.to_string());
    write_len_stable(&mut out, inductives.len());
    for i in inductives {
        write_str_stable(&mut out, &i.name.to_string());
        names(&mut out, &i.level_params);
        expr(&mut out, &i.type_)?;
        write_u32_stable(&mut out, i.num_params);
        write_u32_stable(&mut out, i.num_indices);
        names(&mut out, &i.all_names);
        names(&mut out, &i.constructor_names);
        for flag in [i.is_recursive, i.is_reflexive, i.is_large_elim, i.is_nested] {
            write_u8_stable(&mut out, u8::from(flag));
        }
    }

    let mut constructors: Vec<&ConstructorVal> = env.constructors().collect();
    constructors.sort_by_key(|c| c.name.to_string());
    write_len_stable(&mut out, constructors.len());
    for c in constructors {
        write_str_stable(&mut out, &c.name.to_string());
        write_str_stable(&mut out, &c.inductive_name.to_string());
        names(&mut out, &c.level_params);
        expr(&mut out, &c.type_)?;
        write_u32_stable(&mut out, c.num_params);
        write_u32_stable(&mut out, c.num_fields);
        write_u32_stable(&mut out, c.constructor_idx);
    }

    let mut recursors: Vec<&RecursorVal> = env.recursors().collect();
    recursors.sort_by_key(|r| r.name.to_string());
    write_len_stable(&mut out, recursors.len());
    for r in recursors {
        write_str_stable(&mut out, &r.name.to_string());
        debug_tag(&mut out, &r.arg_order);
        names(&mut out, &r.level_params);
        expr(&mut out, &r.type_)?;
        write_str_stable(&mut out, &r.inductive_name.to_string());
        for count in [r.num_params, r.num_indices, r.num_motives, r.num_minors] {
            write_u32_stable(&mut out, count);
        }
        write_len_stable(&mut out, r.rules.len());
        for rule in &r.rules {
            write_str_stable(&mut out, &rule.constructor_name.to_string());
            write_u32_stable(&mut out, rule.num_fields);
            write_len_stable(&mut out, rule.recursive_fields.len());
            for recursive in &rule.recursive_fields {
                write_u8_stable(&mut out, u8::from(*recursive));
            }
            expr(&mut out, &rule.rhs)?;
        }
        write_u8_stable(&mut out, u8::from(r.is_k));
    }

    let mut quotients: Vec<&QuotVal> = env.quotients().collect();
    quotients.sort_by_key(|q| q.name.to_string());
    write_len_stable(&mut out, quotients.len());
    for q in quotients {
        write_str_stable(&mut out, &q.name.to_string());
        names(&mut out, &q.level_params);
        expr(&mut out, &q.type_)?;
        debug_tag(&mut out, &q.kind);
    }

    Ok(ProofDigest::sha256_domain(
        KERNEL_ENVIRONMENT_DIGEST_V1_DOMAIN,
        &out,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn statement_digest_is_domain_separated_and_content_bound() {
        let a = clean_cic_statement_digest(&Expr::const_str("Bool.true")).unwrap();
        let b = clean_cic_statement_digest(&Expr::const_str("Bool.false")).unwrap();
        assert_ne!(a, b);
        let raw = ProofDigest::sha256(
            <sha2::Sha256 as sha2::Digest>::digest(
                encode_clean_expr_v1(&Expr::const_str("Bool.true")).unwrap(),
            )
            .into(),
        );
        assert_ne!(a, raw, "the domain separates the digest from a bare hash");
    }

    #[test]
    fn environment_digest_is_deterministic_and_sees_every_declaration() {
        let base = Environment::with_prelude();
        let d1 = kernel_environment_digest(&base).unwrap();
        let d2 = kernel_environment_digest(&Environment::with_prelude()).unwrap();
        assert_eq!(d1, d2, "two builds of the prelude have one identity");
        let mut extended = base.clone();
        extended
            .add_decl(clean_kernel::env::Declaration::Definition {
                name: Name::from_string("WS1_12.probe"),
                level_params: vec![],
                type_: Expr::const_str("Nat"),
                value: Expr::nat_lit(7),
                is_reducible: true,
            })
            .expect("a closed Nat definition is admitted");
        let d3 = kernel_environment_digest(&extended).unwrap();
        assert_ne!(
            d1, d3,
            "one added definition changes the environment identity"
        );
    }

    #[test]
    fn neutral_environment_carrier_preserves_the_complete_legacy_kernel_identity() {
        let mut env = Environment::with_prelude();
        assert_eq!(
            kernel_environment_digest(&env).expect("neutral prelude identity"),
            legacy_environment_digest_v1(&env).expect("frozen legacy prelude identity")
        );
        env.add_decl(Declaration::Definition {
            name: Name::from_string("NeutralBoundary.seven"),
            level_params: vec![],
            type_: Expr::const_str("Nat"),
            value: Expr::nat_lit(7),
            is_reducible: true,
        })
        .expect("the actual kernel accepts a closed definition");
        assert_eq!(
            kernel_environment_digest(&env).expect("neutral extended identity"),
            legacy_environment_digest_v1(&env).expect("frozen legacy extended identity")
        );
    }

    #[test]
    fn encoding_is_byte_compatible_with_legacy_bincode_helpers() {
        let expr = Expr::app(Expr::const_str("f"), Expr::nat_lit(7));
        assert_eq!(
            encode_clean_expr_v1(&expr).unwrap(),
            bincode::serialize(&expr).unwrap(),
            "hardening must not change the existing bincode-1 wire bytes"
        );
    }

    #[test]
    fn exact_decode_rejects_suffix_and_byte_overrun() {
        let bytes = encode_clean_expr_v1(&Expr::const_str("Bool.true")).unwrap();
        let mut suffixed = bytes.clone();
        suffixed.push(0);
        assert!(decode_clean_expr_v1(&suffixed).is_err());
        assert!(
            decode_with_limits(&bytes, bytes.len().saturating_sub(1), 100, 100).is_err(),
            "an encoded term over the configured byte cap must reject"
        );
    }

    fn island() -> Vec<Declaration> {
        vec![
            Declaration::Definition {
                name: Name::from_string("WS1_13.seven"),
                level_params: vec![],
                type_: Expr::const_str("Nat"),
                value: Expr::nat_lit(7),
                is_reducible: true,
            },
            Declaration::Theorem {
                name: Name::from_string("WS1_13.seven_eq"),
                level_params: vec![],
                type_: Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq"),
                        vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
                    ),
                    [
                        Expr::const_str("Nat"),
                        Expr::const_str("WS1_13.seven"),
                        Expr::nat_lit(7),
                    ],
                ),
                value: Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq.refl"),
                        vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
                    ),
                    [Expr::const_str("Nat"), Expr::nat_lit(7)],
                ),
            },
        ]
    }

    #[test]
    fn island_declarations_round_trip_canonically() {
        let bytes = encode_island_declarations_v1(&island()).unwrap();
        let back = decode_island_declarations_v1(&bytes).unwrap();
        assert_eq!(back.len(), 2);
        assert_eq!(
            encode_island_declarations_v1(&back).unwrap(),
            bytes,
            "decode then encode is the identity on a canonical carrier"
        );
    }

    #[test]
    fn island_decode_rejects_suffix_overrun_and_too_many_declarations() {
        let bytes = encode_island_declarations_v1(&island()).unwrap();
        let mut suffixed = bytes.clone();
        suffixed.push(0);
        assert!(decode_island_declarations_v1(&suffixed).is_err());
        assert!(
            decode_island_with_limits(&bytes, bytes.len() - 1, 10_000, 100, 10).is_err(),
            "an island over the byte cap must reject"
        );
        let error = decode_island_with_limits(&bytes, bytes.len(), 10_000, 100, 1)
            .expect_err("two declarations over a one-declaration cap");
        assert!(error.contains("declarations"), "{error}");
        let error = decode_island_with_limits(&bytes, bytes.len(), 3, 100, 10)
            .expect_err("the node budget spans the whole island");
        assert!(error.contains("node"), "{error}");
    }

    #[test]
    fn exact_decode_rejects_excessive_recursive_depth() {
        let mut expr = Expr::nat_lit(0);
        for _ in 0..16 {
            expr = Expr::app(Expr::const_str("f"), expr);
        }
        let bytes = encode_clean_expr_v1(&expr).unwrap();
        let error = decode_with_limits(&bytes, bytes.len(), 10_000, 8)
            .expect_err("deep expression must fail inside the scoped decoder");
        assert!(error.contains("depth"), "unexpected error: {error}");
    }
}
