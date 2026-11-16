// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Clean kernel checks that an integer matrix multiply by SemR's
//! `TensorContract` equals its loop nest, for every shape (PKG-U13a).
//!
//! `lean/semr/TensorContraction.lean` states the claim (`SemR.TensorStatement`:
//! for every pointer width, integer element type and shape `m × k` by
//! `k × n`, the contraction of two well-formed operands is the textbook loop
//! nest's `m × n` tensor, or the `usize` refusal) over `evalContract`, the
//! helper SemR's `Step` rule and its executable share, and proves it
//! (`SemR.tensor_matmul_eq_loopNest`). This test builds that module with the
//! package's pinned Lean (4.30.0-rc2, Clean's reference pin), loads its
//! `.olean` closure into Clean, replays every constant the module declares,
//! together with its whole dependency cone (`SemR`'s definitions and Lean's
//! `Init` alike), through Clean's reference kernel entry
//! (`reference_base_closed`, theory `LeanReferenceV1`), and requires each to
//! be admitted with an axiom closure inside Ax0 and no native-evaluation or
//! `sorry` constant in its cone. The negative control hands the kernel the
//! same proof term as a proof of `SemR.ForgedTensorStatement` (the claim with
//! the result's extents transposed, which the module also proves false) and
//! requires a kernel refusal; the positive control beside it is the true
//! statement under a fresh name.
//!
//! What it does not claim: it judges SemR's contraction, not the reference
//! interpreter's (the SemR differential in trust-ir-conformance holds the two
//! together on its runs), and no machine lowering (`TensorContract` is outside
//! the lowering-target subset).

use std::collections::{BTreeSet, HashSet};
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

use clean_kernel::env::{ConstantKind, Declaration, Environment};
use clean_kernel::expr::{Expr, UsedConstants};
use clean_kernel::name::Name;
use clean_kernel::{ReferenceKernel, ReferenceRefusal, TheoryId};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::{DefinitionSafety, load_module_with_deps, parse_module, reference_base_closed};

/// The Lean SemR is written in and Clean's reference entry replays.
const PIN: &str = "leanprover/lean4:v4.30.0-rc2";
/// The proof module (`lean/semr/TensorContraction.lean`, `lean_lib` in the
/// package's lakefile).
const MODULE: &str = "TensorContraction";
const THEOREM: &str = "SemR.tensor_matmul_eq_loopNest";
const STATEMENT: &str = "SemR.TensorStatement";
const FORGED: &str = "SemR.ForgedTensorStatement";
const REFUTATION: &str = "SemR.forged_is_false";
const AX0: [&str; 3] = ["propext", "Quot.sound", "Classical.choice"];
const QUOT_FORMERS: [&str; 4] = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"];
const BANNED: [&str; 4] = [
    "sorryAx",
    "Lean.ofReduceBool",
    "Lean.ofReduceNat",
    "Lean.trustCompiler",
];
/// Words the module's code (comments stripped) must not contain.
const BANNED_WORDS: [&str; 7] = [
    "native_decide",
    "partial",
    "sorry",
    "axiom",
    "implemented_by",
    "extern",
    "unsafe",
];

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn semr_package() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean/semr")
}

/// The Lake that builds SemR: `TRUST_IR_SEMR_LAKE`, `TRUST_IR_LAKE`, elan's
/// shim, then `PATH` (the order of the other SemR tests).
fn lake() -> Option<PathBuf> {
    if let Some(explicit) = std::env::var_os("TRUST_IR_SEMR_LAKE") {
        return Some(explicit.into());
    }
    if let Some(explicit) = std::env::var_os("TRUST_IR_LAKE") {
        return Some(explicit.into());
    }
    if let Some(home) = std::env::var_os("HOME") {
        let shim = Path::new(&home).join(".elan/bin/lake");
        if shim.is_file() {
            return Some(shim);
        }
    }
    std::env::split_paths(&std::env::var_os("PATH")?)
        .map(|directory| directory.join("lake"))
        .find(|candidate| candidate.is_file())
}

/// Lean's code with its comments removed (`--` to the end of the line, and
/// nested `/- … -/` blocks, doc comments included).
fn lean_code_only(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut depth = 0usize;
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i..].starts_with(b"/-") {
            depth += 1;
            i += 2;
        } else if depth > 0 && bytes[i..].starts_with(b"-/") {
            depth -= 1;
            i += 2;
        } else if depth == 0 && bytes[i..].starts_with(b"--") {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
        } else {
            if depth == 0 {
                out.push(bytes[i] as char);
            }
            i += 1;
        }
    }
    out
}

/// Every constant `root` reaches through types, values, inductive families,
/// constructors and recursors (Clean's `semr_reference` walk).
fn reach(env: &Environment, root: &Name) -> HashSet<Name> {
    let mut seen: HashSet<Name> = HashSet::new();
    let mut stack = vec![root.clone()];
    while let Some(x) = stack.pop() {
        if !seen.insert(x.clone()) {
            continue;
        }
        let mut used = HashSet::new();
        let walk = |e: &Expr, used: &mut HashSet<Name>| {
            e.used_constants_dag(UsedConstants::WithProjectionStructures, used);
        };
        if let Some(c) = env.get_const(&x) {
            walk(&c.type_, &mut used);
            if let Some(v) = &c.value {
                walk(v, &mut used);
            }
        }
        if let Some(i) = env.get_inductive(&x) {
            walk(&i.type_, &mut used);
            used.extend(i.constructor_names.iter().cloned());
            used.extend(i.all_names.iter().cloned());
        }
        if let Some(c) = env.get_constructor(&x) {
            walk(&c.type_, &mut used);
            used.insert(c.inductive_name.clone());
        }
        if let Some(r) = env.get_recursor(&x) {
            walk(&r.type_, &mut used);
            used.insert(r.inductive_name.clone());
        }
        stack.extend(used.into_iter().filter(|u| !seen.contains(u)));
    }
    seen
}

/// The axioms `root` reaches, the quotient formers excluded.
fn axioms_of(env: &Environment, root: &Name) -> BTreeSet<String> {
    reach(env, root)
        .into_iter()
        .filter(|x| {
            env.get_const(x)
                .is_some_and(|c| c.kind == ConstantKind::Axiom && c.value.is_none())
        })
        .map(|x| x.to_string())
        .filter(|x| !QUOT_FORMERS.contains(&x.as_str()))
        .collect()
}

fn theorem_as(name: &str, statement: &str, proof: &Expr) -> Declaration {
    Declaration::Theorem {
        name: n(name),
        level_params: vec![],
        type_: Expr::const_(n(statement), vec![]),
        value: proof.clone(),
    }
}

/// Build the module with the package's pinned Lean, or `None` when no Lake
/// exists and Lean is not required.
fn build_module() -> Option<PathBuf> {
    let Some(lake) = lake() else {
        assert_ne!(
            std::env::var("TRUST_IR_REQUIRE_LEAN").as_deref(),
            Ok("1"),
            "TRUST_IR_REQUIRE_LEAN=1 but no lake builds lean/semr"
        );
        eprintln!("SKIPPED: tensor_contraction_equals_loop_nest needs lake (Lean {PIN})");
        return None;
    };
    let package = semr_package();
    let pin = std::fs::read_to_string(package.join("lean-toolchain")).expect("lean-toolchain");
    assert_eq!(pin.trim(), PIN, "SemR's Lean is Clean's reference pin");
    let mut command = Command::new(&lake);
    command.current_dir(&package).env_remove("SDKROOT");
    if let Some(bin) = lake.parent() {
        let mut path = bin.as_os_str().to_os_string();
        path.push(":");
        path.push(std::env::var_os("PATH").unwrap_or_default());
        command.env("PATH", path);
    }
    let out = command
        .args(["build", MODULE])
        .output()
        .expect("run lake build");
    let log = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(out.status.success(), "lake build {MODULE} failed:\n{log}");
    assert!(!log.contains("declaration uses 'sorry'"), "{log}");
    Some(package.join(".lake/build/lib/lean"))
}

#[test]
fn tensor_contraction_equals_loop_nest() {
    // The source: imports only SemR, no escape hatch in its code.
    let source = std::fs::read_to_string(semr_package().join(format!("{MODULE}.lean")))
        .expect("the proof module's source");
    let code = lean_code_only(&source);
    let imports: Vec<&str> = code
        .lines()
        .map(str::trim)
        .filter(|line| line.starts_with("import "))
        .collect();
    assert_eq!(imports, ["import SemR"], "{MODULE} imports only SemR");
    for word in BANNED_WORDS {
        assert!(!code.contains(word), "{MODULE}'s code contains `{word}`");
    }
    for name in [STATEMENT, FORGED, THEOREM, REFUTATION] {
        let local = name.trim_start_matches("SemR.");
        assert!(
            code.contains(&format!("theorem {local} ")) || code.contains(&format!("def {local} ")),
            "{MODULE} declares {local}"
        );
    }

    let Some(lib) = build_module() else {
        return;
    };
    let stdlib = clean_olean::require_pinned_lean_lib_path()
        .unwrap_or_else(|e| panic!("{e} (Clean's reference entry reads Lean {PIN})"));
    // Record the actual strict resolver result: a still-valid build-time
    // library can take precedence over the runtime installation root.
    writeln!(
        std::io::stderr().lock(),
        "tensor_contraction_pinned_input: pin={PIN}; clean_stdlib={}",
        stdlib.display()
    )
    .expect("write the selected pinned input");

    // No split modules: the base `.olean` is the whole module.
    for module in [MODULE, "SemR"] {
        for part in ["olean.private", "olean.server"] {
            let sibling = lib.join(format!("{module}.{part}"));
            assert!(
                !sibling.exists(),
                "{} exists: a split module",
                sibling.display()
            );
        }
    }

    let mut env = Environment::for_lean_replay();
    load_module_with_deps(&mut env, MODULE, &[lib.clone(), stdlib])
        .unwrap_or_else(|e| panic!("load {MODULE}: {e}"));

    // Every kernel declaration the module makes is a target.
    let path = lib.join(format!("{MODULE}.olean"));
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let parsed = parse_module(&bytes).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
    let listed: BTreeSet<&str> = parsed.const_names.iter().map(String::as_str).collect();
    let carried: BTreeSet<&str> = parsed.constants.iter().map(|c| c.name.as_str()).collect();
    assert_eq!(listed, carried, "{MODULE}: constNames and constants agree");
    let mut targets: BTreeSet<Name> = BTreeSet::new();
    let mut violations: Vec<String> = Vec::new();
    for c in &parsed.constants {
        match c.definition_safety {
            Some(DefinitionSafety::Unsafe | DefinitionSafety::Partial) => {
                if !c.name.ends_with("._unsafe_rec") {
                    violations.push(format!(
                        "{}: a {:?} declaration that is not a compiler twin",
                        c.name, c.definition_safety
                    ));
                }
            }
            _ => {
                targets.insert(n(&c.name));
            }
        }
    }
    for name in [STATEMENT, FORGED, THEOREM, REFUTATION] {
        assert!(targets.contains(&n(name)), "{MODULE} declares {name}");
    }

    let built = reference_base_closed(&env, &targets, &ClosedRecheckOptions::default())
        .expect("the reference entry starts");
    if !built.report.passed() {
        violations.push(format!("replay: {}", built.report.verdict_sentence()));
        for refusal in &built.report.refusals {
            violations.push(format!("replay refusal: {refusal:?}"));
        }
    }
    for (unit, refusal) in &built.entry_refusals {
        violations.push(format!("{unit}: refused by the entry: {refusal:?}"));
    }
    let ax0: BTreeSet<String> = AX0.iter().map(|s| (*s).to_string()).collect();
    {
        let k = built.kernel().environment();
        for name in &targets {
            let present = k.get_const(name).is_some()
                || k.get_inductive(name).is_some()
                || k.get_constructor(name).is_some()
                || k.get_recursor(name).is_some();
            if !present {
                violations.push(format!("{name}: not admitted through the entry"));
                continue;
            }
            if let Some(c) = k.get_const(name)
                && matches!(c.kind, ConstantKind::Axiom | ConstantKind::Opaque)
            {
                violations.push(format!("{name}: is an {:?} constant", c.kind));
            }
            let closure = axioms_of(k, name);
            if !closure.is_subset(&ax0) {
                violations.push(format!("{name}: closure {closure:?} is not ⊆ Ax0"));
            }
            let cone = reach(k, name);
            for bad in BANNED {
                if cone.contains(&n(bad)) {
                    violations.push(format!("{name}: reaches {bad}"));
                }
            }
        }
    }
    assert!(
        violations.is_empty(),
        "{} violation(s):\n  {}",
        violations.len(),
        violations.join("\n  ")
    );
    // SemR's contraction itself went through the entry, not only the theorem.
    for generated in [
        "SemR.evalContract",
        "SemR.contractElems",
        "SemR.contractDims",
        "SemR.multiIdx",
        "SemR.Val",
        "SemR.Ty",
    ] {
        assert!(
            built.admitted.contains(&n(generated)),
            "{generated} was not admitted through the entry"
        );
    }
    let admitted = built.admitted.len();
    let mut k: ReferenceKernel = built.into_kernel().expect("a passing, pinned replay");
    assert_eq!(k.theory_id(), TheoryId::LeanReferenceV1);
    let thm = k
        .environment()
        .get_const(&n(THEOREM))
        .expect("the theorem is admitted")
        .clone();
    assert_eq!(thm.kind, ConstantKind::Theorem, "{THEOREM} is a theorem");
    assert_eq!(
        thm.type_,
        Expr::const_(n(STATEMENT), vec![]),
        "{THEOREM} proves exactly {STATEMENT}"
    );
    let closure = axioms_of(k.environment(), &n(THEOREM));
    assert!(closure.is_subset(&ax0), "{closure:?}");

    // Controls: the proof term is accepted as a proof of the true statement
    // under a fresh name, and refused by the kernel as a proof of the forged one.
    let proof = thm.value.clone().expect("the theorem has a proof term");
    k.add_checked(theorem_as("TensorContraction.control", STATEMENT, &proof))
        .expect("the proof checks against the true statement");
    let refusal = k
        .add_checked(theorem_as("TensorContraction.forged", FORGED, &proof))
        .expect_err("the forged statement must be refused");
    assert!(
        matches!(refusal, ReferenceRefusal::Kernel(_)),
        "a kernel refusal, got {refusal:?}"
    );
    let forged_false = k
        .environment()
        .get_const(&n(REFUTATION))
        .expect("the refutation is admitted");
    assert_eq!(forged_false.kind, ConstantKind::Theorem);

    // The evidence line goes to the process's stderr directly, past libtest's
    // capture of `eprintln!`, so a passing run prints it (the tracker's exit
    // test reads it).
    let evidence = format!(
        "tensor_contraction_equals_loop_nest: Clean's reference kernel (LeanReferenceV1) admitted \
         {THEOREM} : {STATEMENT} ({admitted} constants replayed, {} declared by {MODULE}); \
         closure {closure:?} ⊆ Ax0; forged statement {FORGED} refused by the kernel ({REFUTATION} \
         proves it false)",
        targets.len()
    );
    writeln!(std::io::stderr().lock(), "{evidence}").expect("write the evidence line");
}
