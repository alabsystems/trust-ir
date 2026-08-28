// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Bridge ↔ subset agreement gate.
//
// Two spellings of lowering-target subset v2 exist by design:
//   * `trust_ir::ConformanceSubset` (crates/trust-ir/src/bridge.rs) — the
//     dependency-free in-process classifier behind
//     `Module::check_conformance_subset`;
//   * `trust_ir_conformance::subset` — the machine-readable mirror of
//     `lowering-target-subset.md`, doc-lockstep-gated by
//     tests/lowering_subset.rs.
// They once disagreed on PtrToPtr, Transmute, DialectOp, LandingPad / Resume
// / CoroSuspend, Refine, and Custom proof annotations — every verdict below
// is one that actually drifted. This gate pins the two spellings VERDICT-
// and VERSION-identical, and pins the repo to exactly these two spellings.

use std::path::{Path, PathBuf};

use trust_ir::ty::{FatPtrKind, SetRepr};
use trust_ir::{
    Block, BlockId, CastOp, ClosureTyId, ConformanceSubset, Constant, DialectInst, EnumId, FuncId,
    FuncTy, FuncTyId, Function, Inst, InstrNode, Module, PredId, ProofAnnotation, ProofTag,
    RecordId, StructId, Ty, TyId, ValueId,
};
use trust_ir_conformance::subset::{
    CASTOP_ALLOWLIST_V2, SUBSET_VERSION, TY_ALLOWLIST_V2, castop_name, module_subset_violations,
    ty_name,
};

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn b(index: u32) -> BlockId {
    BlockId::new(index)
}

/// One version, two spellings: the struct constant and the allowlist
/// constant must be bumped together (the doc marker is pinned to
/// `SUBSET_VERSION` by the lowering_subset gate, closing the triangle).
#[test]
fn subset_version_is_single_valued() {
    assert_eq!(
        ConformanceSubset::CURRENT.version,
        SUBSET_VERSION,
        "bump ConformanceSubset::CURRENT and subset::SUBSET_VERSION together"
    );
}

/// Every `CastOp` verdict agrees between the bridge classifier and the
/// allowlist. `castop_name`'s exhaustive match compile-breaks on a new
/// variant, forcing it onto this list.
#[test]
fn cast_op_verdicts_agree() {
    const ALL: &[CastOp] = &[
        CastOp::Trunc,
        CastOp::ZExt,
        CastOp::SExt,
        CastOp::FPTrunc,
        CastOp::FPExt,
        CastOp::FPToUI,
        CastOp::FPToSI,
        CastOp::UIToFP,
        CastOp::SIToFP,
        CastOp::PtrToInt,
        CastOp::IntToPtr,
        CastOp::PtrToPtr,
        CastOp::Bitcast,
        CastOp::Transmute,
        CastOp::ReifyFnPointer,
        CastOp::FPToSISat,
        CastOp::FPToUISat,
    ];
    assert_eq!(ALL.len(), 17, "CastOp count moved: extend this list");
    for &op in ALL {
        let name = castop_name(op);
        assert_eq!(
            ConformanceSubset::cast_op_excluded(op).is_none(),
            CASTOP_ALLOWLIST_V2.contains(&name),
            "CastOp::{name}: bridge and subset verdicts drifted"
        );
    }
}

/// Every `Ty` variant verdict agrees. One representative per variant;
/// composite carriers use clean elements so only the outer variant decides.
/// (Both classifiers match `Ty` exhaustively, so a new variant forces an
/// explicit decision on each side; keep a representative here when it does.)
#[test]
fn ty_verdicts_agree() {
    let representatives: Vec<Ty> = vec![
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::U128,
        Ty::Isize,
        Ty::Usize,
        Ty::Char,
        Ty::Error,
        Ty::F16,
        Ty::F32,
        Ty::F64,
        Ty::Bool,
        Ty::Ptr,
        Ty::Unit,
        Ty::Never,
        Ty::FatPtr(FatPtrKind::Str),
        Ty::Vector(Box::new(Ty::I32), 4),
        Ty::Tuple(vec![Ty::I32]),
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::Ref(Box::new(Ty::I32)),
        Ty::RefMut(Box::new(Ty::I32)),
        Ty::PtrConst(Box::new(Ty::I32)),
        Ty::PtrMut(Box::new(Ty::I32)),
        Ty::Rc(Box::new(Ty::I32)),
        Ty::Array(TyId::new(0), 4),
        Ty::Struct(StructId::new(0)),
        Ty::Enum(EnumId::new(0)),
        Ty::Func(FuncTyId::new(0)),
        Ty::Sequence(TyId::new(0)),
        Ty::Set(TyId::new(0), SetRepr::Boxed),
        Ty::Record(RecordId::new(0)),
        Ty::Closure(ClosureTyId::new(0)),
    ];
    for ty in &representatives {
        let name = ty_name(ty);
        assert_eq!(
            ConformanceSubset::ty_excluded(ty).is_none(),
            TY_ALLOWLIST_V2.contains(&name),
            "Ty::{name}: bridge and subset verdicts drifted"
        );
    }
}

fn finish(mut module: Module, mut func: Function, mut block: Block) -> Module {
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    func.blocks.push(block);
    module.add_function(func);
    module
}

fn cast_module(op: CastOp, src_ty: Ty, dst_ty: Ty) -> Module {
    let mut module = Module::new("bridge-agreement-cast");
    let ft = module.add_func_type(FuncTy {
        params: vec![src_ty.clone()],
        returns: vec![],
        is_vararg: false,
    });
    let func = Function::new(FuncId::new(0), "probe", ft, b(0));
    let mut block = Block::new(b(0)).with_param(v(0), src_ty.clone());
    block.body.push(
        InstrNode::new(Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand: v(0),
        })
        .with_result(v(1)),
    );
    finish(module, func, block)
}

fn inst_module(inst: Inst, results: u32) -> Module {
    let mut module = Module::new("bridge-agreement-inst");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![],
        is_vararg: false,
    });
    let func = Function::new(FuncId::new(0), "probe", ft, b(0));
    let mut block = Block::new(b(0)).with_param(v(0), Ty::Ptr);
    let mut node = InstrNode::new(inst);
    for index in 0..results {
        node = node.with_result(v(index + 1));
    }
    block.body.push(node);
    finish(module, func, block)
}

fn dialect_module(dialect: &str, op: &str) -> Module {
    inst_module(
        Inst::DialectOp(Box::new(
            DialectInst::new(dialect, op).with_result_ty(Ty::I32),
        )),
        1,
    )
}

fn custom_proof_module() -> Module {
    let mut module = Module::new("bridge-agreement-proof");
    let ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    let func = Function::new(FuncId::new(0), "probe", ft, b(0));
    let mut block = Block::new(b(0));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(1),
        })
        .with_result(v(0))
        .with_proof(ProofAnnotation::Custom(ProofTag::new(0))),
    );
    finish(module, func, block)
}

fn refine_param_module() -> Module {
    let refined = Ty::Refine(TyId::new(0), PredId::new(0));
    let mut module = Module::new("bridge-agreement-refine");
    let ft = module.add_func_type(FuncTy {
        params: vec![refined.clone()],
        returns: vec![],
        is_vararg: false,
    });
    let func = Function::new(FuncId::new(0), "probe", ft, b(0));
    let block = Block::new(b(0)).with_param(v(0), refined);
    finish(module, func, block)
}

/// Whole-module verdicts agree AND land on the ratified answer, for every
/// construct on which the two spellings historically disagreed.
#[test]
fn boundary_modules_agree_on_the_ratified_verdicts() {
    let cases: Vec<(bool, &str, Module)> = vec![
        (
            true,
            "scalar transmute",
            cast_module(CastOp::Transmute, Ty::I32, Ty::U32),
        ),
        (
            false,
            "aggregate transmute",
            cast_module(
                CastOp::Transmute,
                Ty::Tuple(vec![Ty::I32, Ty::I32]),
                Ty::I64,
            ),
        ),
        (
            true,
            "ptr-to-ptr",
            cast_module(CastOp::PtrToPtr, Ty::Ptr, Ty::Ptr),
        ),
        (
            false,
            "fp-to-si-sat",
            cast_module(CastOp::FPToSISat, Ty::F64, Ty::I32),
        ),
        (
            false,
            "reify-fn-pointer",
            cast_module(CastOp::ReifyFnPointer, Ty::Ptr, Ty::Ptr),
        ),
        (
            false,
            "landing-pad",
            inst_module(
                Inst::LandingPad {
                    is_cleanup: true,
                    catch_type_indices: vec![],
                },
                2,
            ),
        ),
        (false, "resume", inst_module(Inst::Resume { exn: v(0) }, 0)),
        (
            false,
            "coro-suspend",
            inst_module(
                Inst::CoroSuspend {
                    frame: v(0),
                    state_slot: 0,
                    next_state: 1,
                    value: v(0),
                },
                1,
            ),
        ),
        (
            true,
            "vector dialect op",
            dialect_module("vector", "reduce"),
        ),
        (false, "clean dialect op", dialect_module("clean", "rc_inc")),
        (false, "custom node proof", custom_proof_module()),
        (false, "refine param", refine_param_module()),
    ];
    for (accept, label, module) in &cases {
        let bridge_ok = module.check_conformance_subset().is_ok();
        let subset_ok = module_subset_violations(module).is_empty();
        assert_eq!(
            bridge_ok, subset_ok,
            "{label}: bridge and subset verdicts drifted"
        );
        assert_eq!(
            bridge_ok, *accept,
            "{label}: verdict moved off the ratified answer"
        );
    }
}

/// The repo carries exactly TWO spellings of the subset — the bridge
/// classifier and the machine allowlists. A third spelling must register in
/// this gate (and join the agreement battery above) or fail here. The match
/// patterns are split with `concat!` so this file does not match itself.
#[test]
fn subset_spellings_are_registered() {
    let crates_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .to_path_buf();
    let version_pattern = concat!("SUBSET_VERSION", ": u32");
    let classifier_pattern = concat!("pub struct ", "ConformanceSubset");
    let mut version_decls: Vec<PathBuf> = Vec::new();
    let mut classifier_decls: Vec<PathBuf> = Vec::new();
    scan(&crates_dir, &mut |path, text| {
        if text.contains(version_pattern) {
            version_decls.push(path.to_path_buf());
        }
        if text.contains(classifier_pattern) {
            classifier_decls.push(path.to_path_buf());
        }
    });
    let suffixes = |paths: &[PathBuf]| -> Vec<String> {
        let mut names: Vec<String> = paths
            .iter()
            .map(|path| path.to_string_lossy().replace('\\', "/"))
            .collect();
        names.sort();
        names
    };
    let version_decls = suffixes(&version_decls);
    assert_eq!(
        version_decls.len(),
        1,
        "exactly one SUBSET_VERSION declaration allowed, found: {version_decls:?}"
    );
    assert!(
        version_decls[0].ends_with("trust-ir-conformance/src/subset.rs"),
        "SUBSET_VERSION moved: {version_decls:?}"
    );
    let classifier_decls = suffixes(&classifier_decls);
    assert_eq!(
        classifier_decls.len(),
        1,
        "exactly one ConformanceSubset declaration allowed, found: {classifier_decls:?}"
    );
    assert!(
        classifier_decls[0].ends_with("trust-ir/src/bridge.rs"),
        "ConformanceSubset moved: {classifier_decls:?}"
    );
}

fn scan(dir: &Path, visit: &mut impl FnMut(&Path, &str)) {
    for entry in std::fs::read_dir(dir).expect("read_dir") {
        let path = entry.expect("dir entry").path();
        if path.is_dir() {
            if path
                .file_name()
                .is_some_and(|name| name == "target" || name == "fixtures")
            {
                continue;
            }
            scan(&path, visit);
        } else if path.extension().is_some_and(|ext| ext == "rs")
            && let Ok(text) = std::fs::read_to_string(&path)
        {
            visit(&path, &text);
        }
    }
}
