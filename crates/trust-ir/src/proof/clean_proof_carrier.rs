// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Kernel-neutral framing of the existing Clean proof wire and identities.
//!
//! These functions identify data. They do not decode a kernel expression,
//! reconstruct a proposition, admit a declaration, or confer proof authority.
//! In particular, a successful serialization/digest cannot replace the bounded
//! decoder and actual kernel replay required by `ModuleCleanCicRechecker`.
//! Kernel owners project their own expression/environment values into this
//! carrier without passing nominal kernel types across the crate boundary.

use super::evidence::{
    ProofDigest, write_len_stable, write_str_stable, write_u8_stable, write_u32_stable,
};
use bincode::Options;
use serde::Serialize;

/// Existing maximum encoded size of one Clean expression carrier (64 MiB).
pub const CLEAN_EXPR_V1_MAX_BYTES: usize = 64 * 1024 * 1024;
/// Existing statement identity domain. Changing it changes the proof ABI.
pub const CLEAN_CIC_STATEMENT_DIGEST_V1_DOMAIN: &str = "trust_ir.clean_cic.statement.v1";
/// Existing environment identity domain. Changing it changes the proof ABI.
pub const KERNEL_ENVIRONMENT_DIGEST_V1_DOMAIN: &str = "trust_ir.clean_cic.environment.v1";

pub(super) fn codec(limit: usize) -> impl Options {
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_little_endian()
        .reject_trailing_bytes()
        .with_limit(limit as u64)
}

/// Encode the caller's kernel expression with the unchanged bincode-1 wire.
///
/// `Serialize` removes a nominal dependency on one kernel source revision; it
/// is not evidence that an arbitrary serializable value is a Clean expression.
/// Consumers still decode the whole carrier under their kernel's node/depth
/// limits, check canonical re-encoding, and replay the independently derived
/// claim. The byte limit and legacy integer encoding are unchanged.
pub fn encode_clean_expr_carrier_v1<T: Serialize + ?Sized>(expr: &T) -> Result<Vec<u8>, String> {
    let bytes = codec(CLEAN_EXPR_V1_MAX_BYTES)
        .serialize(expr)
        .map_err(|error| format!("encode Clean Expr v1: {error}"))?;
    check_expr_bytes(&bytes)?;
    Ok(bytes)
}

/// Identify the canonical carrier of the caller's statement, without judging it.
pub fn clean_cic_statement_carrier_digest_v1<T: Serialize + ?Sized>(
    statement: &T,
) -> Result<ProofDigest, String> {
    let bytes = encode_clean_expr_carrier_v1(statement)?;
    Ok(ProofDigest::sha256_domain(
        CLEAN_CIC_STATEMENT_DIGEST_V1_DOMAIN,
        &bytes,
    ))
}

fn check_expr_bytes(bytes: &[u8]) -> Result<(), String> {
    if bytes.len() > CLEAN_EXPR_V1_MAX_BYTES {
        return Err(format!(
            "Clean Expr v1 carrier is {} bytes, exceeds limit {}",
            bytes.len(),
            CLEAN_EXPR_V1_MAX_BYTES
        ));
    }
    Ok(())
}

fn names(out: &mut Vec<u8>, values: &[String]) {
    write_len_stable(out, values.len());
    for name in values {
        write_str_stable(out, name);
    }
}

fn expr(out: &mut Vec<u8>, bytes: &[u8]) -> Result<(), String> {
    check_expr_bytes(bytes)?;
    write_len_stable(out, bytes.len());
    out.extend_from_slice(bytes);
    Ok(())
}

fn ordered(previous: &mut Option<String>, name: &str) -> Result<(), String> {
    if previous.as_deref().is_some_and(|last| last > name) {
        return Err("kernel environment records must have sorted names".into());
    }
    *previous = Some(name.to_owned());
    Ok(())
}

/// One constant's identity fields, projected by its kernel owner.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelConstantV1 {
    /// Display spelling of its kernel name.
    pub name: String,
    /// Display spellings of universe parameters, in their original order.
    pub level_params: Vec<String>,
    /// Existing debug spelling of the constant kind.
    pub kind: String,
    /// Existing reducibility flag.
    pub is_reducible: bool,
    /// Existing debug spelling of the reducibility hint.
    pub reducibility: String,
    /// Canonical v1 carrier of the type.
    pub type_: Vec<u8>,
    /// Canonical v1 carrier of the value, when present.
    pub value: Option<Vec<u8>>,
}

/// One inductive's identity fields, projected by its kernel owner.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelInductiveV1 {
    /// Display spelling of the name.
    pub name: String,
    /// Universe parameter names, in original order.
    pub level_params: Vec<String>,
    /// Canonical v1 type carrier.
    pub type_: Vec<u8>,
    /// Number of parameters.
    pub num_params: u32,
    /// Number of indices.
    pub num_indices: u32,
    /// Names in the mutual block, in original order.
    pub all_names: Vec<String>,
    /// Constructor names, in original order.
    pub constructor_names: Vec<String>,
    /// Recursive, reflexive, large-elimination and nested flags, in that order.
    pub flags: [bool; 4],
}

/// One constructor's identity fields, projected by its kernel owner.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelConstructorV1 {
    /// Display spelling of the name.
    pub name: String,
    /// Display spelling of its inductive name.
    pub inductive_name: String,
    /// Universe parameter names, in original order.
    pub level_params: Vec<String>,
    /// Canonical v1 type carrier.
    pub type_: Vec<u8>,
    /// Number of parameters.
    pub num_params: u32,
    /// Number of fields.
    pub num_fields: u32,
    /// Index within its inductive's constructors.
    pub constructor_idx: u32,
}

/// One recursor rule's identity fields, in the kernel's rule order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelRecursorRuleV1 {
    /// Display spelling of its constructor name.
    pub constructor_name: String,
    /// Number of fields.
    pub num_fields: u32,
    /// Existing recursive-field flags.
    pub recursive_fields: Vec<bool>,
    /// Canonical v1 carrier of the rule body.
    pub rhs: Vec<u8>,
}

/// One recursor's identity fields, projected by its kernel owner.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelRecursorV1 {
    /// Display spelling of the name.
    pub name: String,
    /// Existing debug spelling of the argument order.
    pub arg_order: String,
    /// Universe parameter names, in original order.
    pub level_params: Vec<String>,
    /// Canonical v1 type carrier.
    pub type_: Vec<u8>,
    /// Display spelling of its inductive name.
    pub inductive_name: String,
    /// Parameter, index, motive and minor-premise counts, in that order.
    pub counts: [u32; 4],
    /// Rules, in the kernel's original order.
    pub rules: Vec<KernelRecursorRuleV1>,
    /// Existing K-recursion flag.
    pub is_k: bool,
}

/// One quotient's identity fields, projected by its kernel owner.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelQuotientV1 {
    /// Display spelling of the name.
    pub name: String,
    /// Universe parameter names, in original order.
    pub level_params: Vec<String>,
    /// Canonical v1 type carrier.
    pub type_: Vec<u8>,
    /// Existing debug spelling of its quotient kind.
    pub kind: String,
}

/// Incrementally frame the existing environment-v1 identity.
///
/// Call the five section methods once, in order, then `finish`. An exact-size
/// iterator lets each owner encode one record at a time; no second environment
/// or full collection of serialized terms is required. Names within a section
/// must already be sorted, matching the original typed adapter; equal display
/// spellings retain their original order, as the v1 framing did.
/// Owners must refuse lazy/non-enumerable environments before beginning.
///
/// This is a data digest, not a kernel judgment or an immutable environment
/// lease. Every certificate still needs its ordinary kernel and binding replay.
#[derive(Debug)]
pub struct KernelEnvironmentDigestV1 {
    out: Vec<u8>,
    section: u8,
}

impl KernelEnvironmentDigestV1 {
    /// Begin with the existing debug spelling of the kernel mode.
    #[must_use]
    pub fn new(mode: &str) -> Self {
        let mut out = Vec::new();
        write_str_stable(&mut out, mode);
        Self { out, section: 0 }
    }

    fn begin_section(&mut self, section: u8, count: usize) -> Result<(), String> {
        if self.section != section {
            return Err("kernel environment sections are missing, repeated or out of order".into());
        }
        self.section += 1;
        write_len_stable(&mut self.out, count);
        Ok(())
    }

    /// Frame constants, in sorted-name order.
    pub fn constants<I>(mut self, values: I) -> Result<Self, String>
    where
        I: ExactSizeIterator<Item = Result<KernelConstantV1, String>>,
    {
        let expected = values.len();
        self.begin_section(0, expected)?;
        let mut seen = 0;
        let mut previous = None;
        for value in values {
            seen += 1;
            if seen > expected {
                return Err("kernel environment iterator exceeds its declared count".into());
            }
            let c = value?;
            ordered(&mut previous, &c.name)?;
            write_str_stable(&mut self.out, &c.name);
            names(&mut self.out, &c.level_params);
            write_str_stable(&mut self.out, &c.kind);
            write_u8_stable(&mut self.out, u8::from(c.is_reducible));
            write_str_stable(&mut self.out, &c.reducibility);
            expr(&mut self.out, &c.type_)?;
            match c.value {
                None => write_u8_stable(&mut self.out, 0),
                Some(value) => {
                    write_u8_stable(&mut self.out, 1);
                    expr(&mut self.out, &value)?;
                }
            }
        }
        if seen != expected {
            return Err("kernel environment iterator is shorter than its declared count".into());
        }
        Ok(self)
    }

    /// Frame inductives, in sorted-name order.
    pub fn inductives<I>(mut self, values: I) -> Result<Self, String>
    where
        I: ExactSizeIterator<Item = Result<KernelInductiveV1, String>>,
    {
        let expected = values.len();
        self.begin_section(1, expected)?;
        let mut seen = 0;
        let mut previous = None;
        for value in values {
            seen += 1;
            if seen > expected {
                return Err("kernel environment iterator exceeds its declared count".into());
            }
            let i = value?;
            ordered(&mut previous, &i.name)?;
            write_str_stable(&mut self.out, &i.name);
            names(&mut self.out, &i.level_params);
            expr(&mut self.out, &i.type_)?;
            write_u32_stable(&mut self.out, i.num_params);
            write_u32_stable(&mut self.out, i.num_indices);
            names(&mut self.out, &i.all_names);
            names(&mut self.out, &i.constructor_names);
            for flag in i.flags {
                write_u8_stable(&mut self.out, u8::from(flag));
            }
        }
        if seen != expected {
            return Err("kernel environment iterator is shorter than its declared count".into());
        }
        Ok(self)
    }

    /// Frame constructors, in sorted-name order.
    pub fn constructors<I>(mut self, values: I) -> Result<Self, String>
    where
        I: ExactSizeIterator<Item = Result<KernelConstructorV1, String>>,
    {
        let expected = values.len();
        self.begin_section(2, expected)?;
        let mut seen = 0;
        let mut previous = None;
        for value in values {
            seen += 1;
            if seen > expected {
                return Err("kernel environment iterator exceeds its declared count".into());
            }
            let c = value?;
            ordered(&mut previous, &c.name)?;
            write_str_stable(&mut self.out, &c.name);
            write_str_stable(&mut self.out, &c.inductive_name);
            names(&mut self.out, &c.level_params);
            expr(&mut self.out, &c.type_)?;
            write_u32_stable(&mut self.out, c.num_params);
            write_u32_stable(&mut self.out, c.num_fields);
            write_u32_stable(&mut self.out, c.constructor_idx);
        }
        if seen != expected {
            return Err("kernel environment iterator is shorter than its declared count".into());
        }
        Ok(self)
    }

    /// Frame recursors, in sorted-name order.
    pub fn recursors<I>(mut self, values: I) -> Result<Self, String>
    where
        I: ExactSizeIterator<Item = Result<KernelRecursorV1, String>>,
    {
        let expected = values.len();
        self.begin_section(3, expected)?;
        let mut seen = 0;
        let mut previous = None;
        for value in values {
            seen += 1;
            if seen > expected {
                return Err("kernel environment iterator exceeds its declared count".into());
            }
            let r = value?;
            ordered(&mut previous, &r.name)?;
            write_str_stable(&mut self.out, &r.name);
            write_str_stable(&mut self.out, &r.arg_order);
            names(&mut self.out, &r.level_params);
            expr(&mut self.out, &r.type_)?;
            write_str_stable(&mut self.out, &r.inductive_name);
            for count in r.counts {
                write_u32_stable(&mut self.out, count);
            }
            write_len_stable(&mut self.out, r.rules.len());
            for rule in r.rules {
                write_str_stable(&mut self.out, &rule.constructor_name);
                write_u32_stable(&mut self.out, rule.num_fields);
                write_len_stable(&mut self.out, rule.recursive_fields.len());
                for recursive in rule.recursive_fields {
                    write_u8_stable(&mut self.out, u8::from(recursive));
                }
                expr(&mut self.out, &rule.rhs)?;
            }
            write_u8_stable(&mut self.out, u8::from(r.is_k));
        }
        if seen != expected {
            return Err("kernel environment iterator is shorter than its declared count".into());
        }
        Ok(self)
    }

    /// Frame quotients, in sorted-name order.
    pub fn quotients<I>(mut self, values: I) -> Result<Self, String>
    where
        I: ExactSizeIterator<Item = Result<KernelQuotientV1, String>>,
    {
        let expected = values.len();
        self.begin_section(4, expected)?;
        let mut seen = 0;
        let mut previous = None;
        for value in values {
            seen += 1;
            if seen > expected {
                return Err("kernel environment iterator exceeds its declared count".into());
            }
            let q = value?;
            ordered(&mut previous, &q.name)?;
            write_str_stable(&mut self.out, &q.name);
            names(&mut self.out, &q.level_params);
            expr(&mut self.out, &q.type_)?;
            write_str_stable(&mut self.out, &q.kind);
        }
        if seen != expected {
            return Err("kernel environment iterator is shorter than its declared count".into());
        }
        Ok(self)
    }

    /// Finish only after every section was framed successfully.
    pub fn finish(self) -> Result<ProofDigest, String> {
        if self.section != 5 {
            return Err("kernel environment identity is incomplete".into());
        }
        Ok(ProofDigest::sha256_domain(
            KERNEL_ENVIRONMENT_DIGEST_V1_DOMAIN,
            &self.out,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn finish_empty(digest: KernelEnvironmentDigestV1) -> Result<ProofDigest, String> {
        digest
            .constants(std::iter::empty())?
            .inductives(std::iter::empty())?
            .constructors(std::iter::empty())?
            .recursors(std::iter::empty())?
            .quotients(std::iter::empty())?
            .finish()
    }

    #[test]
    fn a_non_kernel_consumer_uses_the_unchanged_fixed_width_wire_and_domain() {
        // Deliberately data, not a kernel term or proof-authority fixture.
        let record = (17u32, 29u64);
        let bytes = encode_clean_expr_carrier_v1(&record).expect("modeled serializable data");
        assert_eq!(
            bytes,
            bincode::serialize(&record).expect("legacy bincode wire")
        );
        assert_eq!(bytes, [17, 0, 0, 0, 29, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(
            clean_cic_statement_carrier_digest_v1(&record).expect("data identity"),
            ProofDigest::sha256_domain(CLEAN_CIC_STATEMENT_DIGEST_V1_DOMAIN, &bytes)
        );
    }

    #[test]
    fn empty_environment_keeps_the_complete_five_section_legacy_framing() {
        // u64 length(4), bytes("Mode"), then five u64 zero section counts.
        let mut legacy = vec![4, 0, 0, 0, 0, 0, 0, 0, b'M', b'o', b'd', b'e'];
        legacy.extend_from_slice(&[0; 40]);
        assert_eq!(
            finish_empty(KernelEnvironmentDigestV1::new("Mode")).expect("complete identity"),
            ProofDigest::sha256_domain(KERNEL_ENVIRONMENT_DIGEST_V1_DOMAIN, &legacy)
        );
        assert!(KernelEnvironmentDigestV1::new("Mode").finish().is_err());
        assert!(
            KernelEnvironmentDigestV1::new("Mode")
                .inductives(std::iter::empty())
                .is_err()
        );
        assert_ne!(
            finish_empty(KernelEnvironmentDigestV1::new("Mode")).expect("first mode"),
            finish_empty(KernelEnvironmentDigestV1::new("Other")).expect("other mode")
        );
    }

    fn constant(name: &str) -> KernelConstantV1 {
        KernelConstantV1 {
            name: name.into(),
            level_params: vec![],
            kind: "MODELED".into(),
            is_reducible: false,
            reducibility: "MODELED".into(),
            type_: vec![0],
            value: None,
        }
    }

    #[test]
    fn environment_rejects_reordered_or_failed_records() {
        assert!(
            KernelEnvironmentDigestV1::new("Mode")
                .constants([Ok(constant("b")), Ok(constant("a"))].into_iter())
                .is_err()
        );
        assert!(
            KernelEnvironmentDigestV1::new("Mode")
                .constants([Ok(constant("a")), Ok(constant("a"))].into_iter())
                .is_ok(),
            "v1 keeps equal display spellings in their original order"
        );
        let failed = vec![Err(
            "kernel owner could not serialize the record".to_string()
        )];
        assert!(
            KernelEnvironmentDigestV1::new("Mode")
                .constants(failed.into_iter())
                .is_err()
        );
    }

    #[test]
    fn environment_checks_the_iterator_count_instead_of_trusting_it() {
        struct WrongSize(Option<KernelConstantV1>);
        impl Iterator for WrongSize {
            type Item = Result<KernelConstantV1, String>;
            fn next(&mut self) -> Option<Self::Item> {
                self.0.take().map(Ok)
            }
            fn size_hint(&self) -> (usize, Option<usize>) {
                (0, Some(0))
            }
        }
        impl ExactSizeIterator for WrongSize {}
        assert!(
            KernelEnvironmentDigestV1::new("Mode")
                .constants(WrongSize(Some(constant("a"))))
                .is_err()
        );
    }
}
