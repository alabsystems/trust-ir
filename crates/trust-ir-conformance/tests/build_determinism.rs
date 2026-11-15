// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// G19 — build determinism / bit-reproducibility.
//
// This is the FORCING FUNCTION for the bootstrap leg's foundation rung:
// Diverse Double-Compilation, the admitted Trust-native stage0 seed, and the
// lineage-closure predicate are all definitionally unexecutable until
//
//     same source  ->  bit-identical trust-ir serialization
//                       + identical module-level proof digest
//
// holds. This test asserts exactly that, and is engineered to *catch*
// nondeterminism, not paper over it:
//
//   (a) It builds a deliberately non-trivial module (multiple functions, multi-
//       block diamond control flow with block params + branch args, the scalar
//       / memory / atomic instruction mix, tuple aggregates, several constants,
//       multiple globals, named structs/enums with fields, and interned
//       debug-info source files + obligation diagnostics) so that every
//       arena/table and the string-interning pool are exercised.
//
//   (b) It serializes that module TWICE *in the same process* and asserts the
//       bytes and the `Module::stable_digest()` are identical. (A floor; within
//       one process Rust's `HashMap` `RandomState` is fixed, so this alone
//       cannot catch HashMap-order leaks.)
//
//   (c) It re-executes THIS TEST BINARY in a fresh CHILD PROCESS (gated by the
//       `TRUST_IR_DETERMINISM_CHILD` env var). A new process gets a fresh,
//       independently-randomized `HashMap`/`HashSet` `RandomState`. The child
//       builds the *same* module from the *same* source and prints
//       `len:<hex-digest>:<hex-of-serialized-bytes>` to stdout. The parent
//       asserts the child's serialization bytes AND digest are byte-identical
//       to its own. If any serialization/interning/digest path leaked HashMap
//       or HashSet iteration order into the output, the two processes' random
//       seeds would diverge and this assertion would go RED.
//
// We do NOT weaken the assertion to make it pass: it compares full bytes and
// the full 32-byte digest across a real process boundary.

#![cfg(feature = "all")] // needs trust-ir/binary (serialize_module + stable_digest)

use std::process::Command;

use trust_ir::constant::Constant;
use trust_ir::inst::{ICmpOp, Ordering};
use trust_ir::ty::Ty;
use trust_ir::{EnumDef, EnumVariant, FieldDef, Global, Linkage, ObligationDiagnostic, StructDef};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

/// Build the canonical non-trivial determinism fixture.
///
/// CRITICAL: this must perform the *exact same* sequence of builder operations
/// every time it is called, in any process — that is what makes "same source"
/// meaningful. It touches: function-type interning, multiple functions, diamond
/// CFG with block params and branch args, scalar/memory/atomic instructions,
/// tuple aggregates, structs + enums with named fields, several globals with
/// constant initializers, interned source files, and obligation diagnostics.
fn build_fixture() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("g19_determinism_fixture");

    // Interned debug-info source files (Module::intern_file is Vec-backed and
    // idempotent — order is the call order, deterministic).
    let _f0 = mb.intern_file("src/alpha.rs");
    let _f1 = mb.intern_file("src/beta.rs");
    let _f2 = mb.intern_file("src/alpha.rs"); // dedup; must not append.

    // Named struct with fields (exercises struct + field-name interning).
    let s_id = trust_ir::StructId::new(0);
    mb.add_struct(StructDef {
        id: s_id,
        name: "Pair".into(),
        fields: vec![
            FieldDef {
                name: "lo".into(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "hi".into(),
                ty: Ty::I64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });

    // Function-type interning (two distinct signatures).
    let ft_binop = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
    let ft_cmp = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::Bool]);

    // Function 1: diamond CFG with block params + branch args, arithmetic,
    // memory (alloca/store), constants, and a tuple aggregate.
    {
        let mut fb: FunctionBuilder<'_> = mb.function("arith_diamond", ft_binop);
        let entry = fb.create_block();
        let then_bb = fb.create_block();
        let else_bb = fb.create_block();
        let merge_bb = fb.create_block();

        let merge_param = fb.add_block_param(merge_bb, Ty::I64);

        fb.switch_to_block(entry);
        let a = fb.add_block_param(entry, Ty::I64);
        let b = fb.add_block_param(entry, Ty::I64);
        let k = fb.iconst(Ty::I64, 7);
        let cond = fb.icmp(ICmpOp::Slt, Ty::I64, a, b);
        let slot = fb.alloca(Ty::I64);
        fb.store(Ty::I64, slot, a);
        fb.condbr(cond, then_bb, vec![], else_bb, vec![]);

        fb.switch_to_block(then_bb);
        let s = fb.add(Ty::I64, a, b);
        let s2 = fb.add(Ty::I64, s, k);
        fb.br(merge_bb, vec![s2]);

        fb.switch_to_block(else_bb);
        let d = fb.sub(Ty::I64, a, b);
        fb.br(merge_bb, vec![d]);

        fb.switch_to_block(merge_bb);
        fb.ret(vec![merge_param]);
        fb.build();
    }

    // Function 2: comparison + atomics (instruction variety + memory ordering).
    {
        let mut fb: FunctionBuilder<'_> = mb.function("atomic_eq", ft_cmp);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let x = fb.add_block_param(entry, Ty::I32);
        let y = fb.add_block_param(entry, Ty::I32);
        let cmp = fb.icmp(ICmpOp::Eq, Ty::I32, x, y);
        let slot = fb.alloca(Ty::I32);
        fb.atomic_store(Ty::I32, slot, x, Ordering::SeqCst);
        let _loaded = fb.atomic_load(Ty::I32, slot, Ordering::Acquire);
        fb.ret(vec![cmp]);
        fb.build();
    }

    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");

    // Named enum with variants (exercises enum + variant-name interning).
    m.enums.push(EnumDef {
        id: trust_ir::EnumId::new(0),
        name: "Tag".into(),
        variants: vec![
            EnumVariant {
                name: "Zero".into(),
                fields: vec![],
                field_names: Vec::new(),
            },
            EnumVariant {
                name: "One".into(),
                fields: vec![Ty::I32],
                field_names: Vec::new(),
            },
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: None,
        origin: None,
    });

    // Several globals with constant initializers (constant-pool + global codec).
    m.globals.push(Global {
        name: "G_lo".into(),
        ty: Ty::I64,
        mutable: false,
        initializer: Some(Constant::Int(42)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    m.globals.push(Global {
        name: "G_hi".into(),
        ty: Ty::I32,
        mutable: true,
        initializer: Some(Constant::Int(-7)),
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    m.globals.push(Global {
        name: "G_agg".into(),
        ty: Ty::Tuple(vec![Ty::I64, Ty::I64]),
        mutable: false,
        initializer: Some(Constant::Aggregate(vec![
            Constant::Int(1),
            Constant::Int(2),
        ])),
        linkage: Linkage::Private,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });

    // A proof obligation (exercises the obligations table + description
    // interning) that the diagnostic below references — validation requires the
    // sidecar to point at a real obligation.
    m.proof_obligations
        .push(trust_ir::proof::ProofObligation::new(
            trust_ir::ProofId::new(0),
            trust_ir::proof::ObligationKind::PanicFreedom,
            trust_ir::proof::ProofStatus::Pending,
            "fixture obligation",
        ));

    // Obligation diagnostic (sidecar) — exercises diagnostic string interning
    // and a SourceSpan into the interned file table.
    m.obligation_diagnostics.push(ObligationDiagnostic {
        obligation: trust_ir::ProofId::new(0),
        severity: trust_ir::DiagnosticSeverity::Note,
        message: "determinism fixture note".into(),
        location: None,
        detail: Some("detail string".into()),
    });

    m
}

/// `len:<hex digest>:<hex serialized bytes>` — the wire format the child prints.
fn fingerprint() -> String {
    let m = build_fixture();
    // Sanity: the fixture must be well-formed (a malformed fixture would make
    // the determinism claim vacuous).
    let errs = trust_ir_build::validate_module(&m);
    assert!(errs.is_empty(), "fixture failed validation: {errs:?}");

    let bytes = trust_ir::binary::serialize_module(&m).expect("serialize_module: test fixture");
    let digest = m.stable_digest();

    // Cross-check: the legacy V2 identity is exactly the domain-separated
    // SHA-256 over the canonical bytes, and stable_digest() (the portable V3
    // identity, WS4.10) is the same construction over the module with every
    // debug file path blanked (table length kept), under the v3 domain.
    assert!(
        !m.files.is_empty(),
        "the fixture must carry a file table, or V3 == V2-image is vacuous"
    );
    let legacy =
        trust_ir::proof::ProofDigest::sha256_domain(trust_ir::MODULE_IDENTITY_DOMAIN_V2, &bytes);
    assert_eq!(
        m.stable_digest_under(trust_ir::IdentityScheme::V2),
        legacy,
        "Module::stable_digest_under(V2) diverged from serialize_module + SHA-256"
    );
    let mut blanked = m.clone();
    for path in &mut blanked.files {
        path.clear();
    }
    let expected = trust_ir::proof::ProofDigest::sha256_domain(
        trust_ir::MODULE_IDENTITY_DOMAIN,
        &trust_ir::binary::serialize_module(&blanked).expect("serialize_module: test fixture"),
    );
    assert_eq!(
        digest, expected,
        "Module::stable_digest diverged from serialize_module(files blanked) + SHA-256"
    );

    let mut out = format!("len:{}:", bytes.len());
    for b in &digest.bytes {
        out.push_str(&format!("{b:02x}"));
    }
    out.push(':');
    for b in &bytes {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

#[test]
fn determinism_same_process() {
    // Floor: identical across repeated in-process builds.
    let first = fingerprint();
    for i in 0..8 {
        assert_eq!(
            first,
            fingerprint(),
            "in-process build {i}: serialization/digest changed across rebuilds"
        );
    }
}

#[test]
fn determinism_across_processes() {
    // If invoked as the child (re-exec of this test binary), emit the
    // fingerprint and exit. The child has a *fresh* HashMap/HashSet RandomState.
    if std::env::var("TRUST_IR_DETERMINISM_CHILD").is_ok() {
        // Wrap in unique markers on their own line so the libtest banner /
        // trailing punctuation around our payload cannot corrupt extraction.
        println!("<<<FP>>>{}<<<END>>>", fingerprint());
        return;
    }

    // Parent: build once here, then spawn N children and demand byte-identical
    // serialization + identical digest from every one of them. Different
    // processes => different hash seeds => any HashMap/HashSet iteration leaking
    // into the serialized bytes or the digest would diverge here.
    let parent = fingerprint();

    let exe = std::env::current_exe().expect("current_exe");

    for run in 0..4 {
        let output = Command::new(&exe)
            .args([
                "--exact",
                "determinism_across_processes",
                "--nocapture",
                "--quiet",
            ])
            .env("TRUST_IR_DETERMINISM_CHILD", "1")
            // Vary an unrelated env var across runs to discourage any incidental
            // process-identical state; the real entropy source is the per-process
            // HashMap RandomState seed.
            .env("TRUST_IR_DETERMINISM_SALT", run.to_string())
            .output()
            .expect("spawn child determinism process");

        assert!(
            output.status.success(),
            "child run {run} failed: status={:?}\nstdout={}\nstderr={}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );

        let stdout = String::from_utf8(output.stdout).expect("child stdout utf8");
        // Extract the payload from between our unique markers (robust against the
        // libtest banner / trailing punctuation the harness prints around it).
        let start = stdout
            .find("<<<FP>>>")
            .unwrap_or_else(|| panic!("child run {run}: no fingerprint marker:\n{stdout}"))
            + "<<<FP>>>".len();
        let end = stdout[start..]
            .find("<<<END>>>")
            .unwrap_or_else(|| panic!("child run {run}: no end marker:\n{stdout}"))
            + start;
        let child = &stdout[start..end];

        assert_eq!(
            parent, child,
            "child run {run}: cross-process serialization/digest is NOT bit-identical \
             (HashMap/HashSet order leaked into the output)"
        );
    }
}
