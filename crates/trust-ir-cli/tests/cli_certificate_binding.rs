// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Transport of the certificate-binding carrier (binary v61,
//! `CERTIFICATE_BINDING_FORMAT_VERSION`). These synthetic certificates make no
//! proof-validity claim: every conversion must RETAIN the binding, byte for
//! byte in meaning, independently of later certificate validation — the
//! binary writer included, which before v61 refused the module rather than
//! drop it.

mod common;

use std::fs;

use common::trust_ir_cmd;
use tempfile::tempdir;
use trust_ir::proof::{
    CertificateBinding, CleanCicKernelRecheck, ProofCertificate, ProofDigest, ProofEvidence,
};
use trust_ir::{Module, ProofId};

fn module(bound: bool) -> Module {
    let mut module = Module::new("certificate_binding_transport");
    module.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(73),
        prover: "synthetic transport fixture; not certified".into(),
        evidence: ProofEvidence::CleanCic {
            term: vec![1, 2],
            context: vec![3, 4],
            lineage: ProofDigest::sha256([5; 32]),
            kernel_recheck: Some(CleanCicKernelRecheck {
                module: "TransportFixture".into(),
                theorems: vec![],
                anchor: "transport-fixture".into(),
                allowed_axioms: vec![],
                binding: bound.then(|| {
                    Box::new(CertificateBinding::new(
                        ProofDigest::sha256([6; 32]),
                        ProofDigest::sha256([7; 32]),
                    ))
                }),
            }),
        },
        assurance: None,
    });
    module
}

#[test]
fn binary_conversion_carries_the_binding_and_never_unbinds_the_input() {
    let dir = tempdir().expect("tempdir");
    let bound = module(true);
    let input = dir.path().join("bound.json");
    let original = serde_json::to_vec(&bound).expect("json");
    fs::write(&input, &original).expect("write input");
    let binary = dir.path().join("bound.bin");
    let output = trust_ir_cmd()
        .args(["convert", "--from", "json", "--to", "bin"])
        .arg(&input)
        .arg(&binary)
        .output()
        .expect("convert");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let bytes = fs::read(&binary).expect("bin");
    assert_eq!(
        &bytes[8..12],
        &trust_ir::binary::CERTIFICATE_BINDING_FORMAT_VERSION.to_le_bytes(),
        "a bound module is written at the carrier's version"
    );
    assert_eq!(
        trust_ir::binary::deserialize_module(&bytes).expect("decode"),
        bound,
        "the binding survives the binary round trip"
    );
    assert_eq!(fs::read(&input).expect("retained input"), original);

    for format in ["json", "msgpack"] {
        let target = dir.path().join(format!("retained.{format}"));
        let output = trust_ir_cmd()
            .args(["convert", "--from", "bin", "--to", format])
            .arg(&binary)
            .arg(&target)
            .output()
            .expect("carrying conversion");
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let bytes = fs::read(target).expect("read transport");
        let decoded: Module = if format == "json" {
            serde_json::from_slice(&bytes).expect("json")
        } else {
            rmp_serde::from_slice(&bytes).expect("msgpack")
        };
        assert_eq!(decoded, bound);
    }

    // Control: the unbound twin keeps its older version.
    let unbound = module(false);
    fs::write(&input, serde_json::to_vec(&unbound).expect("json")).expect("write control");
    let output = trust_ir_cmd()
        .args(["convert", "--from", "json", "--to", "bin"])
        .arg(&input)
        .arg(&binary)
        .output()
        .expect("unbound control");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let bytes = fs::read(binary).expect("bin");
    assert!(
        u32::from_le_bytes(bytes[8..12].try_into().expect("header"))
            < trust_ir::binary::CERTIFICATE_BINDING_FORMAT_VERSION
    );
    assert_eq!(
        trust_ir::binary::deserialize_module(&bytes).expect("decode"),
        unbound
    );
}

#[test]
fn digest_of_a_bound_module_names_the_carrier_version() {
    let dir = tempdir().expect("tempdir");
    let input = dir.path().join("bound.json");
    fs::write(&input, serde_json::to_vec(&module(true)).expect("json")).expect("write input");
    let output = trust_ir_cmd()
        .arg("digest")
        .arg(&input)
        .output()
        .expect("digest");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        stdout.contains(&format!(
            "wire_version: {}",
            trust_ir::binary::CERTIFICATE_BINDING_FORMAT_VERSION
        )),
        "{stdout}"
    );
    // The binding is part of the identity: the unbound twin digests apart.
    let unbound = dir.path().join("unbound.json");
    fs::write(&unbound, serde_json::to_vec(&module(false)).expect("json")).expect("write");
    let control = trust_ir_cmd()
        .arg("digest")
        .arg(&unbound)
        .output()
        .expect("digest");
    assert!(control.status.success());
    let stable = |out: &str| {
        out.lines()
            .find(|line| line.trim_start().starts_with("stable_digest:"))
            .map(str::to_string)
            .expect("a stable_digest line")
    };
    assert_ne!(
        stable(&stdout),
        stable(&String::from_utf8_lossy(&control.stdout))
    );
}
