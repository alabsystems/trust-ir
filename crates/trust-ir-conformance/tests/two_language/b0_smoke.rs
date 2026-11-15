//! b0 — smoke rows. Proves the two-language harness end to end on the
//! smallest two-language module: one `Producer::TRust` function calling one
//! `Producer::Clean` function.
//!
//! Ported (roadmap WS8.6) from the archived Part B battery
//! `reports/2026-09-17-two-language-proof-program/partb/tests/b0_smoke.rs`,
//! measured there at trust-ir 4efb21bc. Every row is checked against
//! `RATCHETS.tsv`. The linked-run row (`b0.cli_linked_run`) runs the real CLI
//! binary and lives in `crates/trust-ir-cli/tests/two_language_cli.rs`.

mod common;

use common::{feature_check, roundtrip_all, run_nullary, run_with_args};
use trust_ir::interpret::InterpretValue;
use trust_ir::ty::Ty;
use trust_ir::{BodyGate, Module, Producer};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

/// ```text
/// [Clean] clean_addmul(a: u64, b: u64) -> u64 = a * b + a        (wrapping)
/// [TRust] program() -> u64                    = clean_addmul(6, 7)   == 48
/// ```
/// `skew_call` = the negative twin: the Rust caller passes ONE argument to the
/// two-parameter Clean callee (a producer compiled against a stale signature).
fn build(skew_call: bool) -> Module {
    let mut mb = ModuleBuilder::new("b0_smoke");
    let binary = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);

    let clean_addmul = {
        let mut fb = mb.function("clean_addmul", binary);
        fb.set_producer(Producer::Clean);
        fb.set_display_path("Smoke.addmul");
        fb.set_body_gate(BodyGate::Gated {
            authority: "clean-kernel-tv".into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let ab = fb.mul(Ty::U64, a, b);
        let out = fb.add(Ty::U64, ab, a);
        fb.ret(vec![out]);
        fb.build()
    };

    {
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        fb.set_display_path("smoke::program");
        fb.set_body_gate(BodyGate::Gated {
            authority: "trust-verify".into(),
            evidence: None,
        });
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let six = fb.uconst(Ty::U64, 6);
        let seven = fb.uconst(Ty::U64, 7);
        let args = if skew_call {
            vec![six]
        } else {
            vec![six, seven]
        };
        let out = fb.call(clean_addmul, args);
        fb.ret(vec![out]);
        fb.build();
    }

    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn b0_smoke() {
    let module = build(false);

    // 1. shape: two functions, two producers, one Rust->Clean call edge.
    let producers: Vec<_> = module
        .functions
        .iter()
        .map(|f| (f.name.as_str(), f.producer.clone()))
        .collect();
    assert!(feature_check(
        "b0.mixed_producers",
        producers
            == vec![
                ("clean_addmul", Some(Producer::Clean)),
                ("program", Some(Producer::TRust)),
            ],
        &format!("{producers:?}"),
    ));

    // 2. validate: zero errors.
    let errors = validate_module(&module);
    assert!(feature_check(
        "b0.validate",
        errors.is_empty(),
        &format!("validate_module errors={errors:?}"),
    ));

    // 2'. negative twin: the skewed Rust->Clean edge is refused for the right
    //     reason, attributed to both producers.
    let skewed = validate_module(&build(true));
    let twin = skewed.iter().any(|e| {
        matches!(
            e,
            ValidationError::CallArgCountMismatch {
                expected: 2,
                actual: 1,
                caller_producer: Some(caller),
                callee_producer: Some(callee),
                ..
            } if caller.as_str() == Producer::TRust.to_string()
                && callee.as_str() == Producer::Clean.to_string()
        )
    });
    assert!(feature_check(
        "b0.validate.negative_twin",
        twin,
        &format!("skewed call edge => {skewed:?}"),
    ));

    // 3. four-format round trip. body_gate/display_path are v41 contract
    //    surface, so the writer must select >= 41.
    let rt = roundtrip_all(&module);
    assert!(feature_check(
        "b0.roundtrip.production",
        rt.lossless_production(),
        &rt.summary(),
    ));
    assert!(feature_check(
        "b0.roundtrip.text",
        rt.text.lossless(),
        &rt.text.summary(),
    ));
    assert!(feature_check(
        "b0.wire_version",
        rt.binary_version == 41,
        &format!(
            "writer selected v{} (VERSION={})",
            rt.binary_version,
            trust_ir::binary::VERSION
        ),
    ));

    // 4. execute through both languages on the reference interpreter.
    let program = run_nullary(&module, "program");
    let got = program
        .as_ref()
        .ok()
        .and_then(|v| v.first())
        .and_then(common::as_u128);
    assert!(feature_check(
        "b0.interpret.rust_calls_clean",
        got == Some(48),
        &format!("program() = {program:?}"),
    ));

    // 4'. a parameterised entry, and wrapping semantics at u64.
    let wrapped = run_with_args(
        &module,
        "clean_addmul",
        vec![
            InterpretValue::int(Ty::U64, i128::from(u64::MAX)).unwrap(),
            InterpretValue::int(Ty::U64, 2).unwrap(),
        ],
    );
    let expect = u128::from(u64::MAX.wrapping_mul(2).wrapping_add(u64::MAX));
    let got = wrapped
        .as_ref()
        .ok()
        .and_then(|v| v.first())
        .and_then(common::as_u128);
    assert!(feature_check(
        "b0.interpret.wrapping_u64",
        got == Some(expect),
        &format!("clean_addmul(u64::MAX, 2) = {wrapped:?}, expected {expect}"),
    ));
}

#[test]
fn two_language_b0() {
    common::run_target("b0", &[("b0_smoke", b0_smoke)]);
}
