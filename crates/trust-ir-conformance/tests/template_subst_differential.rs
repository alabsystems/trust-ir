// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Amendment S (`docs/SPEC_RATIFICATIONS.md` §22): the Rust <-> Lean
// SUBSTITUTION differential. Rust's level-S substitution (`TyG::try_map_ext`,
// the map `instantiate` substitutes with) and Lean's `substTy`
// (`lean/trust_ir-semantics/TrustIr/Template.lean`, run by the `trustir_eval`
// oracle's `template_subst` request) must agree on every case:
//
//   * every type a golden template spells (its `types` and `func_types` rows,
//     block parameters, instruction types and contract fields), under the
//     arguments and type-hole answers of every corpus instance of it;
//   * `CASES` generated level-S types over every `TyG` constructor, with
//     generated parameter and hole images, some of them deliberately missing
//     (Rust's substitution fails, Lean's is `none`: they must agree on that
//     too).
//
// A disagreement is a mismatch and fails the test. `unsupported` (a type the
// Lean decoder has no mirror for) is coverage, RATCHETED at
// `UNSUPPORTED_LEDGER`. Runs when `lake` exists, as gate 12's
// `lean_exec_differential` does (`TRUST_IR_LAKE`, `$HOME/.elan/bin/lake`,
// `PATH`); `TRUST_IR_REQUIRE_LEAN=1` makes a missing `lake` a failure.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use serde_json::{Value as Json, json};
use trust_ir::template::{HoleAnswer, InstArg, ScriptedAnswer, Template, TypeContract};
use trust_ir::ty::{DialectTy, FatPtrKind, HandleTy, SetRepr};
use trust_ir::{
    ClosureTyId, EnumId, FuncTyId, PredId, RecordId, StructId, TemplateRef, Ty, TyG, TyId,
};
use trust_ir_conformance::template_fixtures::instances;

/// Generated cases.
const CASES: u64 = 2_000;

/// Cases the Lean decoder refused by name. Only goes down.
const UNSUPPORTED_LEDGER: usize = 0;

// ---------------------------------------------------------------------------
// The oracle (as `lean_exec_differential.rs` builds it)
// ---------------------------------------------------------------------------

fn lean_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean/trust_ir-semantics")
}

fn find_lake() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("TRUST_IR_LAKE") {
        return Some(PathBuf::from(p));
    }
    if let Some(home) = std::env::var_os("HOME") {
        let elan = Path::new(&home).join(".elan/bin/lake");
        if elan.is_file() {
            return Some(elan);
        }
    }
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|d| d.join("lake"))
        .find(|p| p.is_file())
}

/// `lake build trustir_eval`, with `lean` beside `lake` on PATH and `SDKROOT`
/// removed (`lean_exec_differential.rs`, `LAKE_SCRUBBED_ENV`, says why).
fn oracle() -> Option<&'static PathBuf> {
    static ORACLE: OnceLock<Option<PathBuf>> = OnceLock::new();
    ORACLE
        .get_or_init(|| {
            let require = std::env::var("TRUST_IR_REQUIRE_LEAN").is_ok_and(|v| v == "1");
            let Some(lake) = find_lake() else {
                assert!(!require, "TRUST_IR_REQUIRE_LEAN=1 but no `lake` was found");
                eprintln!("SKIPPED: the substitution differential needs `lake` (elan)");
                return None;
            };
            let mut path = std::env::var_os("PATH").unwrap_or_default();
            if let Some(bin) = lake.parent() {
                let mut joined = std::ffi::OsString::from(bin);
                joined.push(":");
                joined.push(&path);
                path = joined;
            }
            let dir = lean_dir();
            let out = Command::new(&lake)
                .arg("build")
                .arg("trustir_eval")
                .current_dir(&dir)
                .env("PATH", path)
                .env_remove("SDKROOT")
                .output()
                .unwrap_or_else(|e| panic!("cannot run {}: {e}", lake.display()));
            assert!(
                out.status.success(),
                "`lake build trustir_eval` failed:\n{}\n{}",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
            let exe = dir.join(".lake/build/bin/trustir_eval");
            assert!(exe.is_file(), "{} is missing", exe.display());
            Some(exe)
        })
        .as_ref()
}

// ---------------------------------------------------------------------------
// Cases and verdicts
// ---------------------------------------------------------------------------

/// One substitution: a level-S type and the images of its names by index
/// (`None`: no image).
struct Case {
    label: String,
    ty: TyG<TemplateRef>,
    params: Vec<Option<Ty>>,
    holes: Vec<Option<Ty>>,
}

/// Rust's substitution: `try_map_ext` with every name looked up; `None` when
/// a name has no image.
fn rust_subst(case: &Case) -> Option<Ty> {
    case.ty
        .try_map_ext(&mut |r| {
            let image = match r {
                TemplateRef::Param(p) => case.params.get(p.index() as usize),
                TemplateRef::Hole(h) => case.holes.get(h.index() as usize),
            };
            image.cloned().flatten().ok_or(())
        })
        .ok()
}

#[derive(Debug, PartialEq)]
enum Verdict {
    Agree,
    Mismatch(String),
    Unsupported(String),
    Error(String),
}

fn verdict(j: &Json) -> Verdict {
    if j.get("agree") == Some(&Json::Bool(true)) {
        Verdict::Agree
    } else if let Some(m) = j.get("mismatch") {
        Verdict::Mismatch(m.to_string())
    } else if let Some(u) = j.get("unsupported") {
        Verdict::Unsupported(u.to_string())
    } else {
        Verdict::Error(j.to_string())
    }
}

/// The request: images by index (`null`: no image) and Rust's result.
fn request(cases: &[Case]) -> Json {
    let images = |v: &[Option<Ty>]| -> Vec<Json> {
        v.iter()
            .map(|t| match t {
                Some(t) => serde_json::to_value(t).expect("Ty serializes"),
                None => Json::Null,
            })
            .collect()
    };
    json!({
        "template_subst": cases
            .iter()
            .map(|case| {
                let expected = rust_subst(case)
                    .map(|t| serde_json::to_value(t).expect("Ty serializes"))
                    .unwrap_or(Json::Null);
                json!({
                    "ty": serde_json::to_value(&case.ty).expect("TyG serializes"),
                    "params": images(&case.params),
                    "holes": images(&case.holes),
                    "expected": expected,
                })
            })
            .collect::<Vec<_>>()
    })
}

fn run_lean(exe: &Path, cases: &[Case]) -> Vec<Verdict> {
    let tmp = std::env::temp_dir().join(format!(
        "trustir-template-subst-{}.json",
        std::process::id()
    ));
    std::fs::write(&tmp, serde_json::to_vec(&request(cases)).expect("request")).expect("write");
    let out = Command::new(exe)
        .arg(&tmp)
        .output()
        .expect("run trustir_eval");
    let _ = std::fs::remove_file(&tmp);
    let reply: Json = serde_json::from_slice(&out.stdout).unwrap_or_else(|e| {
        panic!(
            "oracle reply is not JSON ({e}): {}",
            String::from_utf8_lossy(&out.stdout)
        )
    });
    let Json::Array(items) = reply else {
        panic!("oracle refused the request: {reply}");
    };
    assert_eq!(items.len(), cases.len(), "one verdict per case");
    items.iter().map(verdict).collect()
}

struct Tally {
    agree: usize,
    unsupported: usize,
    failures: Vec<String>,
}

fn differential(exe: &Path, cases: &[Case]) -> Tally {
    let mut tally = Tally {
        agree: 0,
        unsupported: 0,
        failures: Vec::new(),
    };
    for (case, v) in cases.iter().zip(run_lean(exe, cases)) {
        match v {
            Verdict::Agree => tally.agree += 1,
            Verdict::Unsupported(_) => tally.unsupported += 1,
            other => tally.failures.push(format!(
                "{}: {:?} (rust: {:?})",
                case.label,
                other,
                rust_subst(case)
            )),
        }
    }
    tally
}

// ---------------------------------------------------------------------------
// The corpus: the goldens under their instances
// ---------------------------------------------------------------------------

fn template_types(t: &Template) -> Vec<TyG<TemplateRef>> {
    let m = &t.module;
    let mut out: Vec<TyG<TemplateRef>> = m.types.clone();
    for sig in &m.func_types {
        out.extend(sig.params.iter().chain(&sig.returns).cloned());
    }
    for function in &m.functions {
        for block in &function.blocks {
            out.extend(block.params.iter().map(|(_, ty)| ty.clone()));
            for node in &block.body {
                node.inst.for_each_ty(|ty| out.push(ty.clone()));
            }
        }
    }
    for hole in &t.header.holes {
        if let trust_ir::template::HoleKind::Type { contract } = &hole.kind {
            match contract {
                // A thin-pointer contract names no type: the answer is `Ty::Ptr`.
                TypeContract::Opaque | TypeContract::ThinPointer => {}
                TypeContract::Struct { fields } => out.extend(fields.iter().cloned()),
                TypeContract::Enum { variants, .. } => {
                    out.extend(variants.iter().flatten().cloned());
                }
            }
        }
    }
    out
}

fn golden_cases() -> Vec<Case> {
    let mut cases = Vec::new();
    for instance in instances().expect("every instance golden builds") {
        let params: Vec<Option<Ty>> = instance
            .host
            .arguments
            .iter()
            .map(|arg| match arg {
                InstArg::Type(ty) => Some(ty.clone()),
                InstArg::Const(_) | InstArg::Host(_) => None,
            })
            .collect();
        let holes: Vec<Option<Ty>> = instance
            .host
            .holes
            .iter()
            .map(|answer| match answer {
                ScriptedAnswer::Answer(HoleAnswer::Type(ty)) => Some(ty.clone()),
                _ => None,
            })
            .collect();
        for (i, ty) in template_types(&instance.template).into_iter().enumerate() {
            cases.push(Case {
                label: format!("{}#{i}", instance.name),
                ty,
                params: params.clone(),
                holes: holes.clone(),
            });
        }
    }
    cases
}

// ---------------------------------------------------------------------------
// Generated cases
// ---------------------------------------------------------------------------

/// xorshift64*: deterministic, dependency-free.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// Every `TyG` constructor's head, at level `X`, with `leaf` producing the
/// children (and `ext` the extension, `None` at level R).
fn gen_ty<X>(rng: &mut Rng, depth: u32, ext: &mut dyn FnMut(&mut Rng) -> Option<TyG<X>>) -> TyG<X> {
    let pick = if depth == 0 {
        rng.below(30)
    } else {
        rng.below(43)
    };
    if pick >= 40
        && let Some(e) = ext(rng)
    {
        return e;
    }
    let id = rng.below(5) as u32;
    let mut child = |rng: &mut Rng| Box::new(gen_ty(rng, depth.saturating_sub(1), ext));
    match pick {
        0 => TyG::I8,
        1 => TyG::I16,
        2 => TyG::I32,
        3 => TyG::I64,
        4 => TyG::I128,
        5 => TyG::U8,
        6 => TyG::U16,
        7 => TyG::U32,
        8 => TyG::U64,
        9 => TyG::U128,
        10 => TyG::Isize,
        11 => TyG::Usize,
        12 => TyG::Char,
        13 => TyG::F16,
        14 => TyG::F32,
        15 => TyG::F64,
        16 => TyG::Bool,
        17 => TyG::Ptr,
        18 => TyG::Unit,
        19 => TyG::Never,
        20 => TyG::Struct(StructId::new(id)),
        21 => TyG::Array(TyId::new(id), rng.below(9)),
        22 => TyG::Enum(EnumId::new(id)),
        23 => TyG::Func(FuncTyId::new(id)),
        24 => TyG::FatPtr(match rng.below(3) {
            0 => FatPtrKind::Slice(TyId::new(id)),
            1 => FatPtrKind::Str,
            _ => FatPtrKind::TraitObject { trait_id: id },
        }),
        25 => TyG::Set(
            TyId::new(id),
            if rng.below(2) == 0 {
                SetRepr::Bitset
            } else {
                SetRepr::Boxed
            },
        ),
        26 => TyG::Sequence(TyId::new(id)),
        27 => TyG::Record(RecordId::new(id)),
        28 => TyG::Closure(ClosureTyId::new(id)),
        29 => TyG::Refine(TyId::new(id), PredId::new(id)),
        30 => TyG::Dialect(Box::new(DialectTy::new("demo", "cell", 1 + id))),
        31 => TyG::Handle(Box::new(HandleTy::new("Nat", "trust_bignum::Nat"))),
        32 => TyG::Error,
        33 => TyG::Ref(child(rng)),
        34 => TyG::RefMut(child(rng)),
        35 => TyG::PtrConst(child(rng)),
        36 => TyG::PtrMut(child(rng)),
        37 => TyG::Rc(child(rng)),
        38 => TyG::Vector(child(rng), 2 + rng.below(7) as u32),
        _ => {
            let n = rng.below(4) as usize;
            TyG::Tuple((0..n).map(|_| *child(rng)).collect())
        }
    }
}

fn generated_cases() -> Vec<Case> {
    let mut rng = Rng(0x5EED_7E3A_1A7E_0001);
    (0..CASES)
        .map(|n| {
            let param_count = rng.below(4) as u32;
            let hole_count = rng.below(4) as u32;
            let mut no_ext = |_: &mut Rng| None;
            let mut images = |rng: &mut Rng, count: u32| -> Vec<Option<Ty>> {
                (0..count)
                    .map(|_| {
                        // One image in eight is missing.
                        (rng.below(8) != 0).then(|| gen_ty(rng, 2, &mut no_ext))
                    })
                    .collect()
            };
            let params = images(&mut rng, param_count);
            let holes = images(&mut rng, hole_count);
            // Names may reach one past the tables: an out-of-scope name is a
            // case both sides must call unsubstitutable.
            let mut ext = |rng: &mut Rng| -> Option<TyG<TemplateRef>> {
                Some(TyG::Ext(if rng.below(2) == 0 {
                    TemplateRef::Param(trust_ir::ParamId::new(
                        rng.below(param_count as u64 + 1) as u32
                    ))
                } else {
                    TemplateRef::Hole(trust_ir::HoleId::new(
                        rng.below(hole_count as u64 + 1) as u32
                    ))
                }))
            };
            let ty = gen_ty(&mut rng, 3, &mut ext);
            Case {
                label: format!("generated#{n}"),
                ty,
                params,
                holes,
            }
        })
        .collect()
}

fn head(ty: &TyG<TemplateRef>) -> String {
    format!("{ty:?}")
        .chars()
        .take_while(char::is_ascii_alphanumeric)
        .collect()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn template_subst_differential() {
    let golden = golden_cases();
    let generated = generated_cases();
    // The generator reaches every constructor, so the agreement is over all.
    let mut heads: BTreeSet<String> = BTreeSet::new();
    fn walk(ty: &TyG<TemplateRef>, heads: &mut BTreeSet<String>) {
        heads.insert(head(ty));
        match ty {
            TyG::Tuple(items) => items.iter().for_each(|t| walk(t, heads)),
            TyG::Ref(t)
            | TyG::RefMut(t)
            | TyG::PtrConst(t)
            | TyG::PtrMut(t)
            | TyG::Rc(t)
            | TyG::Vector(t, _) => walk(t, heads),
            _ => {}
        }
    }
    for case in &generated {
        walk(&case.ty, &mut heads);
    }
    assert!(
        heads.len() >= 41,
        "the generator reaches every TyG constructor: {heads:?}"
    );
    assert!(
        generated.iter().any(|c| rust_subst(c).is_none())
            && generated.iter().any(|c| rust_subst(c).is_some()),
        "both outcomes are exercised"
    );
    assert!(
        golden.len() >= 40,
        "the golden half is not vacuous: {}",
        golden.len()
    );

    let Some(exe) = oracle() else { return };
    for (what, cases) in [("goldens", &golden), ("generated", &generated)] {
        let tally = differential(exe, cases);
        assert!(
            tally.failures.is_empty(),
            "{what}: Rust and Lean substitution disagree on {} case(s): {:#?}",
            tally.failures.len(),
            &tally.failures[..tally.failures.len().min(10)]
        );
        eprintln!(
            "template_subst_differential {what}: {} agree, {} unsupported",
            tally.agree, tally.unsupported
        );
        if what == "generated" {
            assert_eq!(
                tally.unsupported, UNSUPPORTED_LEDGER,
                "the unsupported count moved: lower UNSUPPORTED_LEDGER if it fell"
            );
        } else {
            assert_eq!(tally.unsupported, 0, "every golden type has a Lean mirror");
        }
    }
}

/// MUTATION CONTROL (no `lake` needed): the comparator calls a `mismatch`
/// reply a failure and an error reply a failure, never coverage.
#[test]
fn a_mismatch_or_error_reply_is_never_agreement() {
    assert_eq!(verdict(&json!({"agree": true})), Verdict::Agree);
    assert!(matches!(
        verdict(&json!({"mismatch": "none"})),
        Verdict::Mismatch(_)
    ));
    assert!(matches!(verdict(&json!({"error": "x"})), Verdict::Error(_)));
    assert!(matches!(
        verdict(&json!({"unsupported": "ty.X"})),
        Verdict::Unsupported(_)
    ));
    // And the Rust side really substitutes: a parameter becomes its image,
    // a missing image is no result.
    let case = Case {
        label: "control".into(),
        ty: TyG::Ref(Box::new(TyG::Ext(TemplateRef::Param(
            trust_ir::ParamId::new(0),
        )))),
        params: vec![Some(Ty::U64)],
        holes: vec![],
    };
    assert_eq!(rust_subst(&case), Some(Ty::Ref(Box::new(Ty::U64))));
    let gap = Case {
        params: vec![None, Some(Ty::U8)],
        ..case
    };
    assert_eq!(rust_subst(&gap), None);
}

/// Live, when `lake` exists: a forged expectation is reported as a mismatch
/// by the oracle, so agreement is not the oracle's default.
#[test]
fn the_oracle_reports_a_forged_expectation() {
    let Some(exe) = oracle() else { return };
    let request = json!({"template_subst": [{
        "ty": {"Ext": {"Param": 0}},
        "params": ["U64"],
        "holes": [],
        "expected": "U32",
    }]});
    let tmp = std::env::temp_dir().join(format!(
        "trustir-template-subst-forged-{}.json",
        std::process::id()
    ));
    std::fs::write(&tmp, request.to_string()).expect("write");
    let out = Command::new(exe).arg(&tmp).output().expect("run");
    let _ = std::fs::remove_file(&tmp);
    let reply: Json = serde_json::from_slice(&out.stdout).expect("json");
    assert!(
        matches!(verdict(&reply[0]), Verdict::Mismatch(_)),
        "{reply}"
    );
}

// Additive constructor population; original tests/corpus/ratchets above stay intact.
#[path = "template_subst_differential/constructor_coverage.rs"]
mod constructor_coverage;

#[path = "template_subst_differential/raw_boundary.rs"]
mod raw_boundary;
