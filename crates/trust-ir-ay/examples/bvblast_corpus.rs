// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Measure the bit-blast proof route over a directory of real
//! frontend-emitted `.trust_ir` modules.
//!
//! ```text
//! cargo run -p trust-ir-ay --example bvblast_corpus --release -- <dir> [--determinism]
//! ```
//!
//! Reports, per obligation kind: how many obligations are sited, how many derive
//! a goal (and why the rest do not), how many prove, how many validate, how many
//! survive the full authority replay, and the wall time and payload bytes. The
//! numbers this prints are the deliverable — it never estimates.

use std::collections::BTreeMap;
use std::path::Path;
use std::time::Instant;

use trust_ir::proof::{GoalDeriveError, ObligationKind, ProofStatus};
use trust_ir_ay::bvblast;

fn kind_tag(kind: &ObligationKind) -> &'static str {
    match kind {
        ObligationKind::BoundsCheck => "BoundsCheck",
        ObligationKind::ArithmeticSafety => "ArithmeticSafety",
        ObligationKind::MemorySafety => "MemorySafety",
        ObligationKind::PanicFreedom => "PanicFreedom",
        _ => "other",
    }
}

fn derive_bucket(err: &GoalDeriveError) -> String {
    match err {
        GoalDeriveError::NoSite => "no-site".into(),
        GoalDeriveError::SiteFunctionMismatch { .. } => "site-function-mismatch".into(),
        GoalDeriveError::SiteNotResolvable { .. } => "site-not-resolvable".into(),
        GoalDeriveError::NotALoweredAssert { detail } => {
            if detail.contains("THEN arm diverges") {
                "not-assert:then-diverges".into()
            } else if detail.contains("both successors") {
                "not-assert:both-diverge".into()
            } else if detail.contains("neither successor") {
                "not-assert:neither-diverges".into()
            } else {
                "not-assert:not-a-condbr".into()
            }
        }
        GoalDeriveError::ConditionNotPure { detail, .. } => {
            if let Some(rest) = detail.strip_prefix("it is defined by ") {
                format!("impure:{}", rest.split(',').next().unwrap_or(rest).trim())
            } else {
                "impure:cross-block".into()
            }
        }
        GoalDeriveError::Unsupported { detail } => {
            format!("unsupported:{}", detail.split(' ').next().unwrap_or("?"))
        }
        GoalDeriveError::Shape(_) => "shape".into(),
        GoalDeriveError::GroundGoal => "ground-goal".into(),
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let dir = args
        .next()
        .expect("usage: bvblast_corpus <dir> [--determinism]");
    let determinism = args.any(|a| a == "--determinism");

    let mut files: Vec<_> = std::fs::read_dir(Path::new(&dir))
        .expect("corpus directory")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|e| e == "trust_ir"))
        .collect();
    files.sort();

    let mut sited: BTreeMap<&str, usize> = BTreeMap::new();
    let mut derived: BTreeMap<&str, usize> = BTreeMap::new();
    let mut derive_fail: BTreeMap<String, usize> = BTreeMap::new();
    let mut proved: BTreeMap<&str, usize> = BTreeMap::new();
    let mut prove_fail: BTreeMap<String, usize> = BTreeMap::new();
    let mut total_obligations = 0usize;
    let mut parse_failures = 0usize;
    let mut payload_bytes = 0usize;
    let mut proof_shapes: Vec<(String, String, usize, u128)> = Vec::new();
    // The END-TO-END leg: attach evidence, then re-validate the mutated module
    // under the replay capability. Only rows that survive THIS are discharged.
    let mut attached = 0usize;
    let mut authority_accepted = 0usize;
    let mut authority_rejected: Vec<String> = Vec::new();
    let mut without_capability_invalid = 0usize;

    let start = Instant::now();
    for path in &files {
        let text = std::fs::read_to_string(path).expect("read module");
        let Ok(module) = trust_ir::parser::parse_module(&text) else {
            parse_failures += 1;
            continue;
        };
        for obligation in &module.proof_obligations {
            total_obligations += 1;
            let tag = kind_tag(&obligation.kind);
            if obligation.site.is_none() {
                continue;
            }
            *sited.entry(tag).or_default() += 1;
            match trust_ir::proof::derive_site_goal(&module, obligation) {
                Err(err) => {
                    *derive_fail.entry(derive_bucket(&err)).or_default() += 1;
                }
                Ok(goal) => {
                    *derived.entry(tag).or_default() += 1;
                    let t0 = Instant::now();
                    match bvblast::prove(&goal) {
                        Ok(proof) => {
                            let elapsed = t0.elapsed().as_millis();
                            *proved.entry(tag).or_default() += 1;
                            let payload = bvblast::BvBlastCertPayload::new(&goal, proof);
                            let bytes = payload.to_bytes().expect("payload").len();
                            payload_bytes += bytes;
                            let function = module
                                .functions
                                .iter()
                                .find(|f| {
                                    Some(f.id) == obligation.site.as_ref().map(|s| s.function)
                                })
                                .map(|f| f.name.clone())
                                .unwrap_or_default();
                            proof_shapes.push((
                                function,
                                format!("{:?}", obligation.kind),
                                bytes,
                                elapsed,
                            ));
                        }
                        Err(err) => {
                            let bucket = match &err {
                                bvblast::ProveError::NoRefutation => "no-refutation(FALSE)".into(),
                                bvblast::ProveError::GroundGoal => "ground-goal".into(),
                                bvblast::ProveError::Shape(_) => "shape".into(),
                                bvblast::ProveError::OutOfScope(_) => "out-of-scope".into(),
                                bvblast::ProveError::Incomplete(_) => "incomplete".into(),
                                bvblast::ProveError::ValidationFailed(_) => {
                                    "validate-failed".to_string()
                                }
                            };
                            *prove_fail.entry(bucket).or_default() += 1;
                        }
                    }
                }
            }
        }
    }

    // ── END TO END ────────────────────────────────────────────────────────
    // Re-walk the modules that produced a proof, run the real producer entry
    // point, and validate the result BOTH ways: with the capability (must be
    // clean) and without it (must be INVALID — the capability is load-bearing).
    for path in &files {
        let text = std::fs::read_to_string(path).expect("read module");
        let Ok(mut module) = trust_ir::parser::parse_module(&text) else {
            continue;
        };
        let outcomes = bvblast::attach_bvblast_evidence(&mut module);
        let discharged = outcomes.iter().filter(|o| o.discharged).count();
        if discharged == 0 {
            continue;
        }
        attached += discharged;

        let authority = bvblast::BvBlastAuthority::new();
        let report = trust_ir_build::validate_module_report_with_authority(&module, &authority);
        if report.errors().is_empty() {
            authority_accepted += discharged;
        } else {
            authority_rejected.push(format!("{:?}: {:?}", path.file_name().unwrap(), report.errors()));
        }
        // The same module WITHOUT the capability must be rejected.
        if !trust_ir_build::validate_module(&module).is_empty() {
            without_capability_invalid += discharged;
        }
    }

    println!(
        "modules            : {} ({parse_failures} parse failures)",
        files.len()
    );
    println!("proof obligations  : {total_obligations}");
    println!("sited              : {:?}", sited);
    println!("goal derived       : {:?}", derived);
    println!("derive refusals    : {:?}", derive_fail);
    println!("PROVED + VALIDATED : {:?}", proved);
    println!("prove refusals     : {:?}", prove_fail);
    println!("payload bytes total: {payload_bytes}");
    println!("--- end to end ---");
    println!("attached (Pending -> Discharged)      : {attached}");
    println!("VALID under BvBlastAuthority          : {authority_accepted}");
    println!("INVALID without the capability        : {without_capability_invalid}");
    if !authority_rejected.is_empty() {
        println!("authority rejections                  : {authority_rejected:?}");
    }
    println!("wall time          : {:?}", start.elapsed());
    println!("--- proved shapes ---");
    for (function, kind, bytes, ms) in &proof_shapes {
        println!("  {kind:<18} {bytes:>8} B {ms:>5} ms  {function}");
    }

    if determinism {
        // Gate (10) of the authority chain compares a re-derived CNF to the
        // stored one. That comparison is only meaningful if the blaster is
        // run-to-run deterministic; measure it rather than assume it.
        println!("--- determinism ---");
        let goal = trust_ir::proof::BvGoal::predicate(trust_ir::proof::BvTerm::Not(Box::new(
            trust_ir::proof::BvTerm::CarryOut {
                lhs: Box::new(trust_ir::proof::BvTerm::And(
                    Box::new(trust_ir::proof::BvTerm::leaf("v1", 64)),
                    Box::new(trust_ir::proof::BvTerm::Const {
                        value: 15,
                        width: 64,
                    }),
                )),
                rhs: Box::new(trust_ir::proof::BvTerm::Const {
                    value: 16,
                    width: 64,
                }),
                is_sub: true,
            },
        )));
        let a = bvblast::prove(&goal).expect("proves");
        let b = bvblast::prove(&goal).expect("proves");
        println!("  vars equal       : {}", a.vars == b.vars);
        println!("  bit_lemmas equal : {}", a.bit_lemmas == b.bit_lemmas);
        println!("  clauses equal    : {}", a.clauses == b.clauses);
        println!("  refutation equal : {}", a.refutation == b.refutation);
    }

    let _ = ProofStatus::Pending;
}
