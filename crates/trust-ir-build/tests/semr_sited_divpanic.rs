// Copyright 2026 Andrew Yates. Apache-2.0.
//! Bounded canonical helper replay, not decoded Assert or emitted-byte coverage.
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

const MODULES: [&str; 2] = ["SemRSitedDivPanic", "SemRSitedDivPanicCheck"];
const BASE: &str = "SemR.SitedDivPanic";
const CHECK: &str = "SemR.SitedDivPanic.Check";
const WRONG: [&str; 6] = [
    "WrongKind",
    "WrongEntry",
    "WrongGlobal",
    "WrongOffset",
    "WrongOperands",
    "WrongPreservation",
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
            "SemRSitedDivPanicCheck",
            "SemRSitedDivPanicAxiomAudit",
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

fn lean_bad_offers(lib: &Path) {
    let stdlib = clean_olean::require_pinned_lean_lib_path().unwrap();
    let lean = stdlib.parent().unwrap().parent().unwrap().join("bin/lean");
    for wrong in WRONG {
        let good = if wrong == "WrongPreservation" {
            "true_outcome"
        } else {
            "div_outcome"
        };
        let source =
            format!("import SemRSitedDivPanicCheck\nexample : {CHECK}.{wrong} := {CHECK}.{good}\n");
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
        eprintln!("sited_divpanic_lean_false_control: {wrong}: exit1\n{diagnostic}");
    }
}

#[test]
fn canonical_sited_divpanic_helpers_replay_with_exact_identity_and_false_controls() {
    let lib = build();
    lean_bad_offers(&lib);
    let stdlib = clean_olean::require_pinned_lean_lib_path().unwrap();
    eprintln!(
        "sited_divpanic_input: lib={}; stdlib={}",
        lib.display(),
        stdlib.display()
    );
    let mut env = Environment::for_lean_replay();
    load_module_with_deps(&mut env, MODULES[1], &[lib.clone(), stdlib])
        .expect("load helper closure");
    let mut targets = BTreeSet::new();
    // The canonical evaluator now owns the branch/SSA relations and their
    // proofs. Retain every declaration of that moved family as an explicit
    // target, including meanings no longer reached by the metadata checks.
    for module in MODULES.into_iter().chain(["SemR"]) {
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
            if module == "SemR" && !c.name.starts_with("SemR.SitedDivPanic.") {
                continue;
            }
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
        "on",
        "step",
        "failure",
        "Asserts",
        "Reads",
        "complete",
        "sound",
        "step_complete",
        "step_sound",
        "admissible",
        "Admissible",
        "admissible_iff",
        "failure_is_bad",
        "step_false_is_bad",
    ] {
        assert!(
            built.admitted.contains(&n(&format!("{BASE}.{meaning}"))),
            "missing meaning {meaning}"
        );
    }
    assert!(
        built.admitted.contains(&n("SemR.Bad")),
        "new panic classification not replayed"
    );
    let mut kernel = built.into_kernel().expect("passing reference entry");
    assert_eq!(kernel.theory_id(), TheoryId::LeanReferenceV1);
    for (theorem, contract) in [
        ("true_exact", "TrueContract"),
        ("false_exact", "FalseContract"),
        ("step_true", "SSATrueContract"),
        ("step_false", "SSAFalseContract"),
    ] {
        let source = format!("{BASE}.{theorem}");
        let proof = Expr::const_(n(&source), vec![]);
        assert_eq!(
            kernel.environment().get_const(&n(&source)).unwrap().kind,
            ConstantKind::Theorem
        );
        kernel
            .add_checked(offer(
                &format!("SitedDivPanicConsumer.{theorem}"),
                &format!("{CHECK}.{contract}"),
                &proof,
            ))
            .expect("independent exact general statement");
    }
    for wrong in WRONG {
        let good = if wrong == "WrongPreservation" {
            "true_outcome"
        } else {
            "div_outcome"
        };
        let proof = Expr::const_(n(&format!("{CHECK}.{good}")), vec![]);
        let failure = kernel
            .add_checked(offer(
                &format!("SitedDivPanicConsumer.{wrong}"),
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
        eprintln!("sited_divpanic_false_control: {wrong}: {failure:?}");
    }
    eprintln!(
        "sited_divpanic_reference: {} targets, {admitted} admitted; four exact general statements; six false controls; Ax0; helper only, no Step/decoder/bytes credit",
        targets.len()
    );
}
