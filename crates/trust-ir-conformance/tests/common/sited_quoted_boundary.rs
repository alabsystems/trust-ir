// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Actual quoted SemR runs beside validated canonical Rust interpreter runs.
//! Complete module bytes stay refused: no decoded-fragment or Rust-source credit.

use super::*;
use trust_ir::constant::Constant;
use trust_ir::inst::{AssertKind, BinOp, ICmpOp, PanicLocation, PanicSite};
use trust_ir::interpret::PanicLocationValue;
use trust_ir::ty::FuncTy;
use trust_ir::value::GlobalId;
use trust_ir::{Block, BlockId, Function, Global, Inst, InstrNode, Linkage, ValueId};

#[derive(Clone, Copy, Debug)]
struct Case {
    rem: bool,
    entry: u32,
    global: u32,
    a: u64,
    b: u64,
    mutation: u8,
}

impl Case {
    fn kind(self) -> AssertKind {
        if self.rem {
            AssertKind::RemByZero
        } else {
            AssertKind::DivByZero
        }
    }

    fn name(self) -> &'static str {
        if self.rem {
            "rem_by_zero"
        } else {
            "div_by_zero"
        }
    }

    fn result(self) -> u64 {
        match self.mutation {
            1 => self.a,
            _ if self.rem ^ (self.mutation == 2) => self.a % self.b,
            _ => self.a / self.b,
        }
    }
}

fn module(case: Case) -> Module {
    let mut module = Module::new("quoted_sited_division");
    // External declarations require a target. The quoted model uses default
    // 64-bit words; this supplies equal word semantics, not an ABI binding.
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let word = module
        .add_func_type(FuncTy::unrecorded(vec![Ty::U64; 2], vec![Ty::U64], false))
        .unwrap();
    let panic = module
        .add_func_type(FuncTy::unrecorded(vec![Ty::Ptr], vec![], false))
        .unwrap();
    let v = ValueId::new;
    let mut function = Function::new(FuncId::new(7), "guarded_word", word, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0))
        .with_param(v(0), Ty::U64)
        .with_param(v(1), Ty::U64);
    block.body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(0),
        })
        .with_result(v(2)),
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Ne,
            ty: Ty::U64,
            lhs: v(1),
            rhs: v(2),
        })
        .with_result(v(3)),
        InstrNode::new(Inst::Assert {
            cond: v(3),
            kind: case.kind(),
            site: Some(PanicSite {
                entry: FuncId::new(case.entry),
                location: PanicLocation::Global(GlobalId::new(case.global)),
            }),
        }),
        InstrNode::new(Inst::BinOp {
            op: if case.rem ^ (case.mutation == 2) {
                BinOp::URem
            } else {
                BinOp::UDiv
            },
            ty: Ty::U64,
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(4)),
        InstrNode::new(Inst::Return {
            values: vec![v(if case.mutation == 1 { 0 } else { 4 })],
        }),
    ];
    function.blocks.push(block);
    module.functions.push(function);
    for id in [41, 42] {
        module.functions.push(Function::new(
            FuncId::new(id),
            format!("panic_{id}"),
            panic,
            BlockId::new(0),
        ));
    }
    for id in 0..2 {
        module.globals.push(Global {
            name: format!("location_{id}"),
            ty: Ty::U64,
            mutable: false,
            initializer: Some(Constant::Int(i128::from(id))),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
    }
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{case:?}: {errors:?}");
    module
}

// I/O only. Base cases call the actual theorem-bearing execute definition.
// Mutants change actual selected body nodes and use the SAME runFunction.
const DRIVER: &str = r#"import SemRSitedExecution
import SemRRuntimeMain
open SemR

def mutateNode (kind : DivPanicKind) (mode : Nat) (n : Node) : Node :=
  match n.inst with
  | .ret _ => if mode == 1 then { n with inst := .ret [0] } else n
  | .binop _ t a b => if mode == 2 then
      { n with inst := .binop (match kind with | .divByZero => .urem | .remByZero => .udiv) t a b }
    else n
  | _ => n

def modelFor (kind : DivPanicKind) (site : SitedDivPanic.Site) (mode : Nat) : Module :=
  let m := SitedExecution.model kind site
  { m with functions := m.functions.map (fun f => if f.id == 7 then
      { f with blocks := f.blocks.map (fun b => { b with body := b.body.map (mutateNode kind mode) }) }
    else f) }

def renderIdentity (o : Out) : String :=
  match o with
  | .globalDivPanic p =>
    let kind := match p.kind with | .divByZero => "div_by_zero" | .remByZero => "rem_by_zero"
    let operands := match p.operands with | none => "null" | some xs => jlist (xs.map toString)
    "\"panic_kind\":" ++ jstr kind ++ ",\"operands\":" ++ operands
  | _ => "\"panic_kind\":null,\"operands\":null"

def tagBoundary (tag : Nat) : String :=
  match inst 54 #[] [tag, 3, 1, 1, 41, 0, 1] with
  | .err (.unsupported feature) => feature
  | _ => "unexpected admission or malformed result"

def main (argv : List String) : IO UInt32 := do
  match argv with
  | [file] =>
    IO.println ("{\"tag66\":" ++ jstr (tagBoundary 66) ++ ",\"tag67\":" ++ jstr (tagBoundary 67) ++ "}")
    let text ← IO.FS.readFile file
    for line in (text.splitOn "\n").filter (fun l => !(l.all Char.isWhitespace)) do
      match line.splitOn " " with
      | [kind, entry, global, a, b, mode] =>
        match entry.toNat?, global.toNat?, a.toNat?, b.toNat?, mode.toNat? with
        | some entry, some global, some a, some b, some mode =>
          let kind := if kind == "rem" then DivPanicKind.remByZero else .divByZero
          let site : SitedDivPanic.Site := ⟨entry, global⟩
          let m := modelFor kind site mode
          let o := if mode == 0 then SitedExecution.execute kind site a b
            else runFunction m 7 [.int .u64 a, .int .u64 b] 5 1
          IO.println ("{\"out\":" ++ renderOut 64 o ++ "," ++ renderIdentity o ++ ",\"selected\":" ++ moduleSummary m ++ "}")
        | _, _, _, _, _ => throw (IO.userError "bad quoted run numbers")
      | _ => throw (IO.userError "bad quoted run fields")
    pure 0
  | _ => pure 2
"#;

pub(super) fn check(exe: &Path) {
    let lake = semr_lake().expect("the required SemR oracle already built");
    let build = lake_build_command(&lake, &semr_dir(), "SemRSitedExecution")
        .arg("SemRRuntimeMain")
        .output()
        .expect("build quoted execution imports");
    assert!(
        build.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );
    let scratch = SemrScratch::new("quoted-sited-div");
    let driver = scratch.path("QuotedSitedRuns.lean");
    fs::write(&driver, DRIVER).expect("write quoted I/O driver");
    let pairs = [
        (0, 0),
        (1, 0),
        (u64::MAX, 0),
        (0, 1),
        (1, 1),
        (u64::MAX, 1),
        (u64::MAX, 2),
        (u64::MAX, u64::MAX),
        (1 << 63, 3),
        (17, 5),
        (15, 3),
    ];
    let mut cases = vec![];
    let mut blobs = vec![];
    for rem in [false, true] {
        for (entry, global) in [(41, 1), (42, 0), (41, 0), (42, 1)] {
            let base = Case {
                rem,
                entry,
                global,
                a: 0,
                b: 0,
                mutation: 0,
            };
            let original = module(base);
            let blob = trust_ir::binary::serialize_module(&original)
                .expect("complete canonical sited module");
            assert!(header_version(&blob) >= trust_ir::binary::PANIC_SITE_FORMAT_VERSION);
            let decoded =
                trust_ir::binary::deserialize_module(&blob).expect("Rust decodes complete module");
            assert!(trust_ir_build::validate_module(&decoded).is_empty());
            assert_eq!(
                decoded.globals, original.globals,
                "no global data is erased"
            );
            blobs.push(blob);
            for (a, b) in pairs {
                cases.push(Case { a, b, ..base });
            }
            for mutation in [1, 2] {
                cases.push(Case {
                    a: 17,
                    b: 5,
                    mutation,
                    ..base
                });
            }
        }
    }
    assert_eq!(
        semr_decode(exe, &blobs),
        vec![json!({"unsupported": "globals"}); blobs.len()],
        "complete modules refuse at globals before sited instruction tags; no sanitization"
    );
    let runs = scratch.path("runs.txt");
    fs::write(
        &runs,
        cases
            .iter()
            .map(|c| {
                format!(
                    "{} {} {} {} {} {}\n",
                    if c.rem { "rem" } else { "div" },
                    c.entry,
                    c.global,
                    c.a,
                    c.b,
                    c.mutation
                )
            })
            .collect::<String>(),
    )
    .unwrap();
    let out = lake_package_command(&lake, &semr_dir())
        .arg("env")
        .arg("lean")
        .arg("--run")
        .arg(&driver)
        .arg(&runs)
        .output()
        .expect("run actual quoted functions");
    assert!(
        out.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let replies: Vec<Json> = String::from_utf8(out.stdout)
        .unwrap()
        .lines()
        .map(|line| {
            serde_json::from_str(line).unwrap_or_else(|e| panic!("quoted JSON: {e}: {line}"))
        })
        .collect();
    assert_eq!(replies.len(), cases.len() + 1);
    assert_eq!(
        replies[0],
        json!({"tag66": "inst.assert.sited", "tag67": "inst.assert.sited"}),
        "separate raw instruction controls retain both refusals"
    );
    let mut outcomes = vec![];
    for (case, reply) in cases.iter().copied().zip(&replies[1..]) {
        let module = module(case);
        let args = [case.a, case.b].map(|n| InterpretValue::int(Ty::U64, i128::from(n)).unwrap());
        let actual = Interpreter::with_module(&module)
            .with_options(InterpretOptions {
                fuel: 5,
                max_call_depth: 1,
                panic_strategy: PanicStrategy::Abort,
            })
            .execute_func(FuncId::new(7), args);
        let quoted = status_or_semr_verdict(&reply["out"]);
        assert_eq!(quoted, semr_rust_verdict(&actual), "quoted/native {case:?}");
        let selected = &reply["selected"]["fns"];
        assert_eq!(selected[0][0], 7);
        assert_eq!(selected[1][0], 41);
        assert_eq!(selected[2][0], 42);
        assert_eq!(selected[1][3], json!([]), "panic entry is bodyless");
        assert_eq!(
            selected[2][3],
            json!([]),
            "alternate panic entry is bodyless"
        );
        let body = &selected[0][3][0][2];
        assert_eq!(body.as_array().unwrap().len(), 5);
        assert_eq!(
            body[2],
            json!([
                format!(
                    "quoted.assert_sited.{}.entry{}.global{}",
                    case.name(),
                    case.entry,
                    case.global
                ),
                [3],
                []
            ])
        );
        assert_eq!(
            body[4],
            json!(["ret", [if case.mutation == 1 { 0 } else { 4 }], []])
        );
        if case.b == 0 {
            let error = actual.unwrap_err();
            assert_eq!(
                error.code,
                InterpretErrorCode::Panic,
                "entry was never called"
            );
            let panic = error.panic().expect("structured panic");
            assert_eq!(panic.kind, case.kind());
            assert_eq!(panic.operands, None);
            let site = panic.site.expect("sited panic");
            assert_eq!(site.entry, FuncId::new(case.entry));
            assert_eq!(
                site.location,
                PanicLocationValue::Global {
                    global: GlobalId::new(case.global),
                    offset: 0
                }
            );
            assert_eq!(reply["panic_kind"], case.name());
            assert_eq!(
                reply.get("operands"),
                Some(&Json::Null),
                "None must not become Some [] or an omitted field"
            );
        } else {
            let outcome = actual.unwrap();
            assert_eq!(outcome.host_calls, 0);
            assert_eq!(
                outcome.returns,
                vec![InterpretValue::int(Ty::U64, i128::from(case.result())).unwrap()]
            );
            assert!(reply["panic_kind"].is_null());
        }
        outcomes.push((case, reply["out"].clone()));
    }
    for (mutant, outcome) in &outcomes {
        if mutant.mutation != 0 {
            let base = outcomes
                .iter()
                .find(|(c, _)| {
                    c.rem == mutant.rem
                        && c.entry == mutant.entry
                        && c.global == mutant.global
                        && c.a == mutant.a
                        && c.b == mutant.b
                        && c.mutation == 0
                })
                .unwrap();
            assert_ne!(
                *outcome, base.1,
                "actual body mutant must change the return: {mutant:?}"
            );
        }
    }
    for rem in [false, true] {
        let at = |entry, global| {
            &outcomes
                .iter()
                .find(|(c, _)| {
                    c.rem == rem && c.entry == entry && c.global == global && c.a == 1 && c.b == 0
                })
                .unwrap()
                .1
        };
        assert_ne!(
            at(41, 1),
            at(42, 1),
            "entry swaps alone must change the false outcome"
        );
        assert_ne!(
            at(41, 0),
            at(41, 1),
            "global swaps alone must change the false outcome"
        );
    }
    eprintln!(
        "quoted-sited-div: {} actual function/interpreter runs, {} complete globals refusals, separate tag66/67 refusals; no decoded parity credit",
        cases.len(),
        blobs.len()
    );
}
