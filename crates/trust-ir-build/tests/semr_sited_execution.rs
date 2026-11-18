// Copyright 2026 Andrew Yates. Apache-2.0.
//! Complete quoted word-program replay; no decoded or emitted-byte coverage.
//! Uses the tensor consumer's existing pinned Lake/reference-entry protocol.

use std::collections::{BTreeSet, HashSet};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use clean_kernel::env::{ConstantKind, Declaration, Environment};
use clean_kernel::expr::{Expr, UsedConstants};
use clean_kernel::{KernelEnvError, KernelTypeError, Name, ReferenceRefusal, TheoryId};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::{DefinitionSafety, load_module_with_deps, parse_module, reference_base_closed};

const MODULES: [&str; 2] = ["SemRSitedExecution", "SemRSitedExecutionCheck"];
const BASE: &str = "SemR.SitedExecution";
const CHECK: &str = "SemR.SitedExecution.Check";
const WRONG: [&str; 11] = [
    "WrongDivResult",
    "WrongRemResult",
    "WrongEntry",
    "WrongGlobal",
    "WrongKind",
    "WrongOperands",
    "WrongSwappedBody",
    "WrongRemovedGuard",
    "WrongReceiver",
    "WrongBudget",
    "MissingNonzero",
];
const AX0: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];
const QUOT: [&str; 4] = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"];
const BANNED: [&str; 4] = [
    "sorryAx",
    "Lean.ofReduceBool",
    "Lean.ofReduceNat",
    "Lean.trustCompiler",
];

fn n(name: &str) -> Name {
    Name::from_string(name)
}

fn reach(env: &Environment, root: &Name) -> HashSet<Name> {
    let mut seen = HashSet::new();
    let mut pending = vec![root.clone()];
    while let Some(name) = pending.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let mut used = HashSet::new();
        if let Some(c) = env.get_const(&name) {
            c.type_
                .used_constants_dag(UsedConstants::WithProjectionStructures, &mut used);
            if let Some(v) = &c.value {
                v.used_constants_dag(UsedConstants::WithProjectionStructures, &mut used);
            }
        }
        if let Some(i) = env.get_inductive(&name) {
            i.type_
                .used_constants_dag(UsedConstants::WithProjectionStructures, &mut used);
            used.extend(i.constructor_names.iter().cloned());
            used.extend(i.all_names.iter().cloned());
        }
        if let Some(c) = env.get_constructor(&name) {
            c.type_
                .used_constants_dag(UsedConstants::WithProjectionStructures, &mut used);
            used.insert(c.inductive_name.clone());
        }
        if let Some(r) = env.get_recursor(&name) {
            r.type_
                .used_constants_dag(UsedConstants::WithProjectionStructures, &mut used);
            used.insert(r.inductive_name.clone());
        }
        pending.extend(used.into_iter().filter(|x| !seen.contains(x)));
    }
    seen
}

fn package() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean/semr")
}

fn build() -> PathBuf {
    let stdlib = clean_olean::require_pinned_lean_lib_path().expect("installed pinned Lean4.30rc2");
    let lake = stdlib.parent().unwrap().parent().unwrap().join("bin/lake");
    let version = Command::new(&lake)
        .arg("--version")
        .output()
        .expect("Lake identity");
    assert!(version.status.success());
    assert!(String::from_utf8_lossy(&version.stdout).contains("Lean version 4.30.0-rc2"));
    assert_eq!(
        std::fs::read_to_string(package().join("lean-toolchain"))
            .unwrap()
            .trim(),
        "leanprover/lean4:v4.30.0-rc2"
    );
    let output = Command::new(lake)
        .current_dir(package())
        .args([
            "build",
            "SemRSitedExecutionCheck",
            "SemRSitedExecutionAxiomAudit",
        ])
        .output()
        .expect("pinned lake build");
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    package().join(".lake/build/lib/lean")
}

fn offer(name: &str, statement: &str, proof: &Expr) -> Declaration {
    Declaration::Theorem {
        name: n(name),
        level_params: vec![],
        type_: Expr::const_(n(statement), vec![]),
        value: proof.clone(),
    }
}

fn good_for(wrong: &str) -> String {
    match wrong {
        "MissingNonzero" => format!("{BASE}.nonzero_run"),
        "WrongRemResult" => format!("{CHECK}.rem_sample"),
        "WrongEntry" | "WrongGlobal" | "WrongKind" | "WrongOperands" | "WrongRemovedGuard" => {
            format!("{CHECK}.zero_sample")
        }
        _ => format!("{CHECK}.div_sample"),
    }
}

fn lean_bad_offers(lib: &Path) {
    let stdlib = clean_olean::require_pinned_lean_lib_path().unwrap();
    let lean = stdlib.parent().unwrap().parent().unwrap().join("bin/lean");
    for wrong in WRONG {
        let good = good_for(wrong);
        let source =
            format!("import SemRSitedExecutionCheck\nexample : {CHECK}.{wrong} := {good}\n");
        let mut child = Command::new(&lean)
            .args(["-j2", "--stdin"])
            .current_dir(package())
            .env("LEAN_PATH", lib)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("actual pinned Lean bad proof offer");
        child
            .stdin
            .take()
            .unwrap()
            .write_all(source.as_bytes())
            .unwrap();
        let output = child.wait_with_output().unwrap();
        let diagnostic = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.status.code(), Some(1), "{wrong}: {diagnostic}");
        assert!(
            diagnostic.to_ascii_lowercase().contains("type mismatch"),
            "{wrong}: {diagnostic}"
        );
        eprintln!("sited_execution_lean_false_control: {wrong}: exit1\n{diagnostic}");
    }
}

#[test]
fn quoted_sited_word_runs_replay_with_receiver_body_and_panic_controls() {
    let lib = build();
    lean_bad_offers(&lib);
    let stdlib = clean_olean::require_pinned_lean_lib_path().unwrap();
    eprintln!(
        "sited_execution_input: lib={}; stdlib={}",
        lib.display(),
        stdlib.display()
    );
    let mut env = Environment::for_lean_replay();
    load_module_with_deps(&mut env, MODULES[1], &[lib.clone(), stdlib])
        .expect("load helper closure");
    let mut targets = BTreeSet::new();
    for module in MODULES {
        for suffix in ["olean.private", "olean.server"] {
            assert!(
                !lib.join(format!("{module}.{suffix}")).exists(),
                "split module"
            );
        }
        let parsed =
            parse_module(&std::fs::read(lib.join(format!("{module}.olean"))).unwrap()).unwrap();
        assert_eq!(
            parsed.const_names.iter().collect::<BTreeSet<_>>(),
            parsed
                .constants
                .iter()
                .map(|c| &c.name)
                .collect::<BTreeSet<_>>()
        );
        for c in parsed.constants {
            match c.definition_safety {
                Some(DefinitionSafety::Unsafe | DefinitionSafety::Partial) => {
                    assert!(
                        c.name.ends_with("._unsafe_rec"),
                        "unexpected unsafe/partial {}",
                        c.name
                    );
                }
                _ => {
                    targets.insert(n(&c.name));
                }
            }
        }
    }
    assert!(!targets.is_empty());
    let built = reference_base_closed(&env, &targets, &ClosedRecheckOptions::default())
        .expect("reference entry");
    assert!(
        built.report.passed(),
        "{}; {:?}",
        built.report.verdict_sentence(),
        built.report.refusals
    );
    assert!(
        built.entry_refusals.is_empty(),
        "{:?}",
        built.entry_refusals
    );
    let admitted = built.admitted.len();
    for name in &targets {
        let cone = reach(built.kernel().environment(), name);
        for used in &cone {
            assert!(
                !BANNED.iter().any(|bad| *used == n(bad)),
                "{name} reaches {used}"
            );
            if let Some(c) = built.kernel().environment().get_const(used)
                && c.kind == ConstantKind::Axiom
                && c.value.is_none()
            {
                assert!(
                    AX0.iter()
                        .chain(QUOT.iter())
                        .any(|allowed| *used == n(allowed)),
                    "{name} reaches non-Ax0 axiom {used}"
                );
            }
        }
    }
    for meaning in [
        "SemR.SitedExecution.model",
        "SemR.SitedExecution.nodes",
        "SemR.SitedExecution.initial",
        "SemR.SitedExecution.execute",
        "SemR.SitedExecution.operation",
        "SemR.SitedExecution.result",
        "SemR.execNode",
        "SemR.Step",
        "SemR.step_sound",
        "SemR.step_complete",
        "SemR.run",
        "SemR.run_sound",
        "SemR.run_complete",
        "SemR.Bad",
        "SemR.BodyViolation",
        "SemR.SitedDivPanic.step",
    ] {
        assert!(
            built.admitted.contains(&n(meaning)),
            "missing meaning {meaning}"
        );
    }
    let mut kernel = built.into_kernel().expect("passing reference entry");
    assert_eq!(kernel.theory_id(), TheoryId::LeanReferenceV1);
    for (theorem, contract, argument) in [
        (
            "nonzero_run",
            "DivContract",
            Some("SemR.DivPanicKind.divByZero"),
        ),
        (
            "nonzero_run",
            "RemContract",
            Some("SemR.DivPanicKind.remByZero"),
        ),
        ("zero_run", "ZeroContract", None),
        ("nonzero_excludes_body_violation", "NoBadContract", None),
    ] {
        let source = format!("{BASE}.{theorem}");
        let raw = Expr::const_(n(&source), vec![]);
        let proof = match argument {
            Some(name) => Expr::app(raw, Expr::const_(n(name), vec![])),
            None => raw,
        };
        assert_eq!(
            kernel.environment().get_const(&n(&source)).unwrap().kind,
            ConstantKind::Theorem
        );
        kernel
            .add_checked(offer(
                &format!("SitedExecutionConsumer.{contract}"),
                &format!("{CHECK}.{contract}"),
                &proof,
            ))
            .expect("independent complete program contract");
    }
    for wrong in WRONG {
        let good = good_for(wrong);
        let proof = Expr::const_(n(&good), vec![]);
        let failure = kernel
            .add_checked(offer(
                &format!("SitedExecutionConsumer.{wrong}"),
                &format!("{CHECK}.{wrong}"),
                &proof,
            ))
            .expect_err("genuine false statement must fail");
        assert!(
            matches!(
                failure,
                ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
                    source: KernelTypeError::TypeMismatch { .. },
                    ..
                })
            ),
            "unexpected refusal {failure:?}"
        );
        eprintln!("sited_execution_false_control: {wrong}: {failure:?}");
    }
    eprintln!(
        "sited_execution_reference: {} targets, {admitted} admitted; four complete program contracts; eleven false controls; Ax0; quoted Step only, no decoder/bytes credit",
        targets.len()
    );
}
