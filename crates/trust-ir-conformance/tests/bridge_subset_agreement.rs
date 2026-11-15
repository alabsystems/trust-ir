// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Bridge ↔ subset agreement gate.
//
// Two spellings of the lowering-target subset (v3 since WS2.9) exist by design:
//   * `trust_ir::ConformanceSubset` (crates/trust-ir/src/bridge.rs) — the
//     dependency-free in-process classifier behind
//     `Module::check_conformance_subset`;
//   * `trust_ir_conformance::subset` — the machine-readable mirror of
//     `lowering-target-subset.md`, doc-lockstep-gated by
//     tests/lowering_subset.rs.
// They once disagreed on PtrToPtr, Transmute, DialectOp, LandingPad / Resume
// / CoroSuspend, Refine, Custom proof annotations, and (F-042, until subset
// v3) Dealloc — every verdict below is one that actually drifted. This gate
// pins the two spellings VERDICT- and VERSION-identical, and pins the repo to
// exactly these two spellings.
//
// Ported proof-program rows (reports/2026-09-17-two-language-proof-program):
//   * `trust-ir-self-declared/bridge-vs-subset-dealloc-drift` (F-042) — the
//     bridge admitted `Dealloc` through its inline-type fallthrough while the
//     mirror had dropped it in v2 (G18-1). GAP -> PASS in WS2.9.
//   * `crit.unex04` (F-037), the wasm32 half — a 32-bit or big-endian module
//     was inside the subset unless it used a fat pointer, while the Lean
//     memory model encodes every pointer as eight little-endian bytes. v3's
//     structural condition 5 makes that BY-DESIGN out of subset.

use std::path::{Path, PathBuf};

use trust_ir::ty::{ClosureTy, FatPtrKind, SetRepr};
use trust_ir::{
    Block, BlockId, CastOp, ClosureTyId, ConformanceSubset, Constant, DialectInst, Endianness,
    EnumId, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode, Module, PredId, ProofAnnotation,
    ProofTag, RecordId, StructId, SubsetSite, TargetInfo, Ty, TyId, ValueId,
};
use trust_ir_conformance::subset::{
    CASTOP_ALLOWLIST_V4, SUBSET_VERSION, TY_ALLOWLIST_V4, castop_name, char_origin_violation,
    module_subset_violations, ty_name,
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
            CASTOP_ALLOWLIST_V4.contains(&name),
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
        Ty::Dialect(Box::new(trust_ir::DialectTy::new("example", "value", 1))),
        Ty::handle("Nat", "trust_bignum::Nat"),
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
        // The tensor region (PKG-U13a): no memory layout, outside the subset.
        Ty::Tensor(Box::new(Ty::I32), 2),
    ];
    for ty in &representatives {
        let name = ty_name(ty);
        assert_eq!(
            ConformanceSubset::ty_excluded(ty).is_none(),
            TY_ALLOWLIST_V4.contains(&name),
            "Ty::{name}: bridge and subset verdicts drifted"
        );
    }
}

fn finish(mut module: Module, mut func: Function, mut block: Block) -> Module {
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

fn cast_module(op: CastOp, src_ty: Ty, dst_ty: Ty) -> Module {
    let mut module = Module::new("bridge-agreement-cast");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![src_ty.clone()],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
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
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
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
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
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

/// `probe(p: ptr, x: T) { store T x -> p }` pinned to `target` (or unpinned).
fn store_module(stored_ty: Ty, target: Option<TargetInfo>) -> Module {
    let mut module = Module::new("bridge-agreement-store");
    module.target_info = target;
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, stored_ty.clone()],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let func = Function::new(FuncId::new(0), "probe", ft, b(0));
    let mut block = Block::new(b(0))
        .with_param(v(0), Ty::Ptr)
        .with_param(v(1), stored_ty.clone());
    block.body.push(InstrNode::new(Inst::Store {
        ty: stored_ty,
        ptr: v(0),
        value: v(1),
        volatile: false,
        align: None,
    }));
    finish(module, func, block)
}

fn target(triple: &str, pointer_size: u32, endianness: Endianness) -> Option<TargetInfo> {
    Some(TargetInfo {
        triple: triple.into(),
        pointer_size,
        endianness,
        abi: None,
        struct_passing: Default::default(),
    })
}

fn wasm32() -> Option<TargetInfo> {
    target("wasm32-unknown-unknown", 4, Endianness::Little)
}

fn big_endian_64() -> Option<TargetInfo> {
    target("powerpc64-unknown-linux-gnu", 8, Endianness::Big)
}

fn x86_64() -> Option<TargetInfo> {
    target("x86_64-unknown-linux-gnu", 8, Endianness::Little)
}

fn refine_param_module() -> Module {
    let refined = Ty::Refine(TyId::new(0), PredId::new(0));
    let mut module = Module::new("bridge-agreement-refine");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![refined.clone()],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let func = Function::new(FuncId::new(0), "probe", ft, b(0));
    let block = Block::new(b(0)).with_param(v(0), refined);
    finish(module, func, block)
}

/// `fn probe(f: <callee>, x: u64) -> u64 { call_indirect f(x) }`: an indirect
/// call whose callee is a block parameter typed `Ty::Closure` (a closure
/// APPLICATION, subset structural condition 4) or, as the mutation control,
/// typed `Ty::Func` (an ordinary function-pointer call).
fn indirect_call_module(closure_callee: bool) -> Module {
    let mut module = Module::new("bridge-agreement-indirect-call");
    let apparent = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let callee_ty = if closure_callee {
        Ty::Closure(
            module
                .add_closure_type(ClosureTy {
                    func: apparent,
                    captures: vec![Ty::U64],
                })
                .expect("Module::add_closure_type: test fixture"),
        )
    } else {
        Ty::Func(apparent)
    };
    let ft = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![callee_ty.clone(), Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "probe", ft, b(0));
    let mut block = Block::new(b(0))
        .with_param(v(0), callee_ty)
        .with_param(v(1), Ty::U64);
    block.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: v(0),
            sig: apparent,
            args: vec![v(1)],
            calling_conv: Default::default(),
        })
        .with_result(v(2)),
    );
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
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
        // v3 (F-036 review): float/bool are off the Transmute scalar set on
        // BOTH sides. The `dst` rows are the Lean mistranslation control —
        // `transmute u32 -> f32` bound an integer at a float type and
        // `transmute u8 -> bool` a bool whose payload could exceed 1.
        (
            false,
            "float transmute src",
            cast_module(CastOp::Transmute, Ty::F32, Ty::U32),
        ),
        (
            false,
            "float transmute dst",
            cast_module(CastOp::Transmute, Ty::U32, Ty::F32),
        ),
        (
            false,
            "bool transmute dst",
            cast_module(CastOp::Transmute, Ty::U8, Ty::Bool),
        ),
        // Mutation control: the sanctioned int<->float reinterpret stays IN.
        (
            true,
            "int-to-float bitcast",
            cast_module(CastOp::Bitcast, Ty::U32, Ty::F32),
        ),
        (
            true,
            "ptr-to-ptr",
            cast_module(CastOp::PtrToPtr, Ty::Ptr, Ty::Ptr),
        ),
        // Review (WS2.9): the pointer member of the Transmute scalar set is
        // EXACTLY `Ty::Ptr`. A spelling that tested "pointer-like" instead
        // would admit the typed raw pointers and references, which Lean's
        // `transmuteScalarTy` refuses (they are not `.Ptr`) — so the thin
        // `ptr -> ptr` transmute is IN and every typed-pointer shape is OUT
        // on both sides.
        (
            true,
            "ptr transmute",
            cast_module(CastOp::Transmute, Ty::Ptr, Ty::Ptr),
        ),
        (
            false,
            "ptr-const transmute src",
            cast_module(CastOp::Transmute, Ty::PtrConst(Box::new(Ty::U8)), Ty::Ptr),
        ),
        (
            false,
            "ptr-mut transmute dst",
            cast_module(CastOp::Transmute, Ty::Ptr, Ty::PtrMut(Box::new(Ty::U8))),
        ),
        (
            false,
            "ref transmute src",
            cast_module(CastOp::Transmute, Ty::Ref(Box::new(Ty::U8)), Ty::Ptr),
        ),
        // Review (WS2.9): an off-set IDENTITY transmute is OUT too. The
        // condition is on the types, never on whether the reinterpretation
        // would change anything — a spelling that short-circuited
        // `src == dst` would admit `bool -> bool` while both engines refuse
        // it (`UnsupportedCast` / `unsupported.cast`).
        (
            false,
            "bool identity transmute",
            cast_module(CastOp::Transmute, Ty::Bool, Ty::Bool),
        ),
        (
            false,
            "f64 identity transmute",
            cast_module(CastOp::Transmute, Ty::F64, Ty::F64),
        ),
        // ...while an in-set identity transmute is IN (the control).
        (
            true,
            "u64 identity transmute",
            cast_module(CastOp::Transmute, Ty::U64, Ty::U64),
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
        // F-042: dropped from the subset in v2 (G18-1); the bridge admitted
        // it until v3.
        (
            false,
            "dealloc",
            inst_module(Inst::Dealloc { ptr: v(0) }, 0),
        ),
        // Crystal lane (wave-DS): `Drop` has no destructor model in either
        // engine (both refuse it). The bridge's inline-type fallthrough would
        // have admitted it, so both spellings must exclude it by name.
        (
            false,
            "drop",
            inst_module(
                Inst::Drop {
                    ty: Ty::I32,
                    ptr: v(0),
                },
                0,
            ),
        ),
        // Crystal lane (D3): the WEAK form of the allowlisted `CmpXchg` is out
        // (both engines refuse it); the STRONG form with the same operands is
        // the control that stays in.
        (
            false,
            "weak cmpxchg",
            inst_module(
                Inst::CmpXchg {
                    ty: Ty::I64,
                    ptr: v(0),
                    expected: v(0),
                    desired: v(0),
                    success: trust_ir::inst::Ordering::SeqCst,
                    failure: trust_ir::inst::Ordering::Relaxed,
                    weak: true,
                },
                2,
            ),
        ),
        (
            true,
            "strong cmpxchg",
            inst_module(
                Inst::CmpXchg {
                    ty: Ty::I64,
                    ptr: v(0),
                    expected: v(0),
                    desired: v(0),
                    success: trust_ir::inst::Ordering::SeqCst,
                    failure: trust_ir::inst::Ordering::Relaxed,
                    weak: false,
                },
                2,
            ),
        ),
        // Crystal lane (E3b): a `Const` carrying an unwritten lane is out; the
        // same aggregate with the lane written is the control that stays in.
        (
            false,
            "uninit-lane const",
            inst_module(
                Inst::Const {
                    ty: Ty::Tuple(vec![Ty::I64, Ty::I64]),
                    value: Constant::Aggregate(vec![Constant::Int(0), Constant::Uninit]),
                },
                1,
            ),
        ),
        (
            true,
            "written-lane const",
            inst_module(
                Inst::Const {
                    ty: Ty::Tuple(vec![Ty::I64, Ty::I64]),
                    value: Constant::Aggregate(vec![Constant::Int(0), Constant::Int(1)]),
                },
                1,
            ),
        ),
        // WS3.20 (F-057): the bulk-memory pair has semantics in both engines
        // but is NOT yet admitted — admission is a subset-contract bump. Both
        // spellings must refuse it by name until then.
        (
            false,
            "memcopy",
            inst_module(
                Inst::MemCopy {
                    dst: v(0),
                    src: v(0),
                    bytes: v(0),
                    overlap: false,
                },
                0,
            ),
        ),
        (
            false,
            "memset",
            inst_module(
                Inst::MemSet {
                    dst: v(0),
                    byte: v(0),
                    bytes: v(0),
                },
                0,
            ),
        ),
        // v50: the uniform array landed with wire tags and semantics but no
        // backend lowering, so it is NOT admitted — both spellings refuse the
        // instruction and a splat constant by name.
        (
            false,
            "array-splat",
            inst_module(
                Inst::ArraySplat {
                    ty: Ty::Array(TyId::new(0), 1 << 40),
                    value: v(0),
                },
                1,
            ),
        ),
        (
            false,
            "splat constant",
            inst_module(
                Inst::Const {
                    ty: Ty::Array(TyId::new(0), 1 << 40),
                    value: Constant::Splat {
                        elem: Box::new(Constant::Int(0)),
                        len: 1 << 40,
                    },
                },
                1,
            ),
        ),
        // Mutation control: the list spelling of a (non-uniform) array
        // constant stays IN.
        (
            true,
            "array constant",
            inst_module(
                Inst::Const {
                    ty: Ty::Array(TyId::new(0), 2),
                    value: Constant::Array(vec![Constant::Int(0), Constant::Int(1)]),
                },
                1,
            ),
        ),
        // v5 selects the wasm32 model for the whole module. Big-endian
        // remains outside regardless of the stored type.
        (true, "wasm32 ptr store", store_module(Ty::Ptr, wasm32())),
        (
            false,
            "big-endian i32 store",
            store_module(Ty::I32, big_endian_64()),
        ),
        // Mutation controls for condition 5: a target-free module and an
        // explicit x86_64 module with the SAME `Ptr` store both stay IN — a
        // condition that refused every pinned target would pass the rows
        // above and fail these.
        (true, "target-free ptr store", store_module(Ty::Ptr, None)),
        (true, "x86_64 ptr store", store_module(Ty::Ptr, x86_64())),
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
        // The tensor region (PKG-U13a): an integer matrix multiply. Both
        // engines execute it, but no backend lowers it, so both spellings
        // refuse the instruction (and its tensor type) by name.
        (
            false,
            "tensor-contract",
            inst_module(
                Inst::TensorContract {
                    ty: Ty::Tensor(Box::new(Ty::I32), 2),
                    lhs: v(0),
                    rhs: v(0),
                    batch: vec![],
                    contract: vec![(1, 0)],
                },
                1,
            ),
        ),
        // PKG-U13c: map, reduce and view refuse by name likewise.
        (
            false,
            "tensor-map",
            inst_module(
                Inst::TensorMap {
                    ty: Ty::Tensor(Box::new(Ty::I32), 2),
                    args: vec![v(0)],
                    body: vec![trust_ir::TensorMapNode::UnOp {
                        op: trust_ir::inst::UnOp::Neg,
                        ty: Ty::I32,
                        operand: 0,
                    }],
                },
                1,
            ),
        ),
        (
            false,
            "tensor-reduce",
            inst_module(
                Inst::TensorReduce {
                    ty: Ty::Tensor(Box::new(Ty::I32), 1),
                    src: v(0),
                    op: trust_ir::TensorReduceOp::Add,
                    axes: vec![1],
                    order: trust_ir::TensorReduceOrder::RowMajor,
                },
                1,
            ),
        ),
        (
            false,
            "tensor-view",
            inst_module(
                Inst::TensorView {
                    ty: Ty::Tensor(Box::new(Ty::I32), 1),
                    src: v(0),
                    params: vec![],
                    exprs: vec![
                        trust_ir::TensorIndexExpr::SrcExtent(0),
                        trust_ir::TensorIndexExpr::Coord(0),
                    ],
                    shape: vec![0],
                    index: vec![1],
                    fill: None,
                },
                1,
            ),
        ),
        // PKG-U13d: gather and scatter refuse by name likewise.
        (
            false,
            "tensor-gather",
            inst_module(
                Inst::TensorGather {
                    ty: Ty::Tensor(Box::new(Ty::I32), 1),
                    data: v(0),
                    coords: vec![v(0)],
                },
                1,
            ),
        ),
        (
            false,
            "tensor-scatter",
            inst_module(
                Inst::TensorScatter {
                    ty: Ty::Tensor(Box::new(Ty::I32), 1),
                    init: v(0),
                    src: v(0),
                    coords: vec![v(0)],
                },
                1,
            ),
        ),
        // PKG-U13e: a weight blob constant is outside through its tensor
        // type in both classifiers.
        (
            false,
            "tensor-weight-blob",
            inst_module(
                Inst::Const {
                    ty: Ty::Tensor(Box::new(Ty::I32), 1),
                    value: trust_ir::constant::Constant::TensorBlob {
                        digest: trust_ir::blob::BlobDigest::of(&[1, 0, 0, 0]),
                        dims: vec![1],
                    },
                },
                1,
            ),
        ),
        // WS3.5 addendum: excluded until its wire tag, backend lowering and
        // the enum/record Lean depth land — even at all-scalar lanes.
        (
            false,
            "make-aggregate",
            inst_module(
                Inst::MakeAggregate {
                    ty: Ty::Tuple(vec![Ty::Ptr]),
                    variant: None,
                    fields: vec![v(0)],
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
        // Structural condition 4: closure APPLICATION was stated outside the
        // subset since G18-2 but enforced by NEITHER checker (both said
        // `true`) until the v58 `closure_layout` golden reached the Lean
        // differential. The function-pointer call is the mutation control.
        (false, "closure application", indirect_call_module(true)),
        (
            true,
            "function-pointer indirect call",
            indirect_call_module(false),
        ),
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

/// `trust-ir-self-declared/bridge-vs-subset-dealloc-drift` (F-042), ported:
/// the archived row measured `bridge_ok = true, subset_ok = false` on
/// `inst_module(Inst::Dealloc{..}, 0)` — a producer self-gating through the
/// dependency-free in-process classifier (the path Clean is told it may use)
/// would have admitted `Dealloc` while the ratified v2 subset had dropped it.
/// PASS since v3: both spellings refuse, and the bridge names G18-1.
#[test]
fn trust_ir_self_declared_bridge_vs_subset_dealloc_drift() {
    let module = inst_module(Inst::Dealloc { ptr: v(0) }, 0);
    let violations = module
        .check_conformance_subset()
        .expect_err("the bridge refuses Dealloc in v3");
    assert_eq!(violations.len(), 1, "{violations:?}");
    assert_eq!(violations[0].site, SubsetSite::Instruction);
    assert!(
        violations[0].reason.contains("Inst::Dealloc") && violations[0].reason.contains("G18-1"),
        "{violations:?}"
    );
    let mirror = module_subset_violations(&module);
    assert!(
        mirror.iter().any(|reason| reason.contains("Inst::Dealloc")),
        "{mirror:?}"
    );
    // Negative twin (right reason): the same probe over `HeapAlloc`, the
    // four-field allocation whose origin/layout the format DOES state, is in.
    let twin = inst_module(
        Inst::HeapAlloc {
            ty: Ty::I32,
            count: None,
            align: Some(4),
            origin: trust_ir::inst::AllocOrigin::RustHeap,
        },
        1,
    );
    assert!(twin.check_conformance_subset().is_ok());
    assert!(module_subset_violations(&twin).is_empty());
}

/// Keep the whole-module refusal regression on unsupported32-bit ABIs and
/// big-endian targets, with wasm32 typed-storage and empty-module positives.
#[test]
fn crit_unex04_non_model_targets_stay_out_with_wasm32_positive_controls() {
    for (label, module) in [
        (
            "i686 ptr store",
            store_module(
                Ty::Ptr,
                target("i686-unknown-linux-gnu", 4, Endianness::Little),
            ),
        ),
        (
            "big-endian i32 store",
            store_module(Ty::I32, big_endian_64()),
        ),
        // No function at all: the condition is about the module's byte
        // model, not about any construct in it.
        ("unsupported32 empty module", {
            let mut empty = Module::new("bridge-agreement-empty");
            empty.target_info = target("i686-unknown-linux-gnu", 4, Endianness::Little);
            empty
        }),
    ] {
        let violations = module.check_conformance_subset().expect_err(label);
        assert_eq!(violations.len(), 1, "{label}: {violations:?}");
        let violation = &violations[0];
        assert_eq!(violation.site, SubsetSite::ModuleTarget, "{label}");
        assert_eq!(violation.function, None, "{label}");
        assert_eq!(violation.block, None, "{label}");
        assert_eq!(violation.instruction_index, None, "{label}");
        assert!(
            violation.reason.contains("condition 5"),
            "{label}: {violation:?}"
        );
        let mirror = module_subset_violations(&module);
        assert_eq!(mirror.len(), 1, "{label}: {mirror:?}");
        assert!(
            mirror[0].contains("structural condition 5"),
            "{label}: {mirror:?}"
        );
    }
    // Mutation control: the SAME stores unpinned and pinned to x86_64 are in.
    for (label, module) in [
        ("target-free ptr store", store_module(Ty::Ptr, None)),
        ("x86_64 ptr store", store_module(Ty::Ptr, x86_64())),
        ("wasm32 ptr store", store_module(Ty::Ptr, wasm32())),
        ("wasm32 empty module", {
            let mut empty = Module::new("wasm32-empty");
            empty.target_info = wasm32();
            empty
        }),
        ("x86_64 i32 store", store_module(Ty::I32, x86_64())),
    ] {
        assert!(module.check_conformance_subset().is_ok(), "{label}");
        assert!(module_subset_violations(&module).is_empty(), "{label}");
    }
    // Malformed pointer sizes fail closed in both spellings: `pointer_bits`
    // would have defaulted an overflowing size to 64.
    let malformed = store_module(Ty::Ptr, target("bogus", u32::MAX, Endianness::Little));
    assert!(malformed.check_conformance_subset().is_err());
    assert!(!module_subset_violations(&malformed).is_empty());
}

/// A refused big-endian target is reported once beside both independent
/// construct refusals. Target admission cannot swallow those construct rows.
#[test]
fn condition_5_is_reported_once_beside_the_construct_rows() {
    let mut module = Module::new("bridge-agreement-multi");
    module.target_info = big_endian_64();
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let ft_f32 = module
        .add_func_type(FuncTy {
            params: vec![Ty::F32],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    for (index, name) in ["clean", "frees", "reinterprets"].iter().enumerate() {
        let index = u32::try_from(index).expect("small");
        let (func_ty, param_ty) = if *name == "reinterprets" {
            (ft_f32, Ty::F32)
        } else {
            (ft, Ty::Ptr)
        };
        let mut func = Function::new(FuncId::new(index), *name, func_ty, b(0));
        let mut block = Block::new(b(0)).with_param(v(0), param_ty);
        match *name {
            "frees" => block.body.push(InstrNode::new(Inst::Dealloc { ptr: v(0) })),
            "reinterprets" => block.body.push(
                InstrNode::new(Inst::Cast {
                    op: CastOp::Transmute,
                    src_ty: Ty::F32,
                    dst_ty: Ty::U32,
                    operand: v(0),
                })
                .with_result(v(1)),
            ),
            _ => {}
        }
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
    }

    let violations = module
        .check_conformance_subset()
        .expect_err("big-endian + Dealloc + float transmute");
    assert_eq!(violations.len(), 3, "{violations:?}");
    let module_rows: Vec<_> = violations
        .iter()
        .filter(|violation| violation.site == SubsetSite::ModuleTarget)
        .collect();
    assert_eq!(module_rows.len(), 1, "{violations:?}");
    assert_eq!(module_rows[0].function, None);
    assert!(
        violations.iter().any(|violation| {
            violation.function == Some(FuncId::new(1))
                && violation.site == SubsetSite::Instruction
                && violation.reason.contains("Inst::Dealloc")
        }),
        "{violations:?}"
    );
    assert!(
        violations.iter().any(|violation| {
            violation.function == Some(FuncId::new(2))
                && violation.site == SubsetSite::Instruction
                && violation.reason.contains("scalar-to-scalar")
        }),
        "{violations:?}"
    );

    let mirror = module_subset_violations(&module);
    assert_eq!(
        mirror
            .iter()
            .filter(|reason| reason.contains("structural condition 5"))
            .count(),
        1,
        "{mirror:?}"
    );
    assert!(
        mirror
            .iter()
            .any(|reason| reason.contains("fn `frees`") && reason.contains("Inst::Dealloc")),
        "{mirror:?}"
    );
    assert!(
        mirror
            .iter()
            .any(|reason| reason.contains("fn `reinterprets`") && reason.contains("Transmute")),
        "{mirror:?}"
    );
    assert_eq!(mirror.len(), 3, "{mirror:?}");

    // Mutation control: the same three functions on x86_64 leave exactly the
    // two construct rows in both spellings — the module row is the target's.
    module.target_info = x86_64();
    let violations = module
        .check_conformance_subset()
        .expect_err("Dealloc + float transmute");
    assert_eq!(violations.len(), 2, "{violations:?}");
    assert!(
        violations
            .iter()
            .all(|violation| violation.site == SubsetSite::Instruction),
        "{violations:?}"
    );
    assert_eq!(module_subset_violations(&module).len(), 2);
}

/// `probe() -> i32 { return const 1 }` pinned to `target` (or unpinned): the
/// smallest body the reference interpreter can run, so its verdict is about
/// the TARGET alone.
fn const_module(target: Option<TargetInfo>) -> Module {
    let mut module = Module::new("bridge-agreement-const");
    module.target_info = target;
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "probe", ft, b(0));
    let mut block = Block::new(b(0));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(1),
        })
        .with_result(v(0)),
    );
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

/// Review (WS2.9): condition 5 and the reference interpreter's own target
/// gate (`require_reference_execution_layout`) must agree in the SOUND
/// direction — no differential "evidence" can exist for a byte model the
/// Lean semantics do not describe. (The converse is not pinned: the
/// interpreter additionally requires a triple in its canonical
/// scalar-layout set, so an 8-byte little-endian triple outside it —
/// `powerpc64le` — is in-subset yet unexecuted; that is a coverage gap, not
/// a soundness one, and is filed rather than asserted.)
///
/// v5 joins wasm32 execution and model admission. The unsupported target
/// negatives still exercise both classifiers and the reference interpreter.
#[test]
fn condition_5_refusals_are_never_executed_by_the_reference_interpreter() {
    use trust_ir::interpret::{InterpretErrorCode, Interpreter};
    // wasm32: admitted by v5 and executed at the selected32-bit model.
    let wasm = const_module(wasm32());
    assert!(wasm.check_conformance_subset().is_ok(), "wasm32");
    assert!(module_subset_violations(&wasm).is_empty(), "wasm32");
    Interpreter::with_module(&wasm)
        .execute_func(FuncId::new(0), [])
        .unwrap_or_else(|error| panic!("wasm32 reference execution: {error:?}"));
    for (label, target) in [
        ("big-endian 64", big_endian_64()),
        (
            "unsupported32 ABI",
            target("i686-unknown-linux-gnu", 4, Endianness::Little),
        ),
        (
            "malformed pointer size",
            target("bogus", u32::MAX, Endianness::Little),
        ),
    ] {
        let module = const_module(target);
        assert!(module.check_conformance_subset().is_err(), "{label}");
        assert!(!module_subset_violations(&module).is_empty(), "{label}");
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err(label);
        assert_eq!(
            error.code,
            InterpretErrorCode::UnsupportedMemory,
            "{label}: {error:?}"
        );
    }
    // Mutation control: the pinned byte model executes, unpinned or x86_64.
    for (label, target) in [("target-free", None), ("x86_64", x86_64())] {
        let module = const_module(target);
        assert!(module.check_conformance_subset().is_ok(), "{label}");
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .unwrap_or_else(|error| panic!("{label}: {error:?}"));
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

/// Subset v4 structural condition 6 (WS2.17, F-037): the two spellings of
/// the `Char` origin rule must agree instruction by instruction — the
/// bridge classifier (`ConformanceSubset::char_origin_excluded`) and the
/// machine-readable mirror (`char_origin_violation`). Each row is a
/// positive, a negative twin one mutation away, or an over-refusal control.
#[test]
fn char_origin_verdicts_agree() {
    let probes: Vec<(&str, Inst, bool)> = vec![
        // (what, inst, expected: is it OUT of subset by condition 6?)
        (
            "zext u8 -> char (the one admitted computed origin)",
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::U8,
                dst_ty: Ty::Char,
                operand: v(0),
            },
            false,
        ),
        (
            "bitcast u32 -> char",
            Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: Ty::U32,
                dst_ty: Ty::Char,
                operand: v(0),
            },
            true,
        ),
        (
            "trunc u32 -> char",
            Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::U32,
                dst_ty: Ty::Char,
                operand: v(0),
            },
            true,
        ),
        (
            "zext u16 -> char",
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::U16,
                dst_ty: Ty::Char,
                operand: v(0),
            },
            true,
        ),
        (
            "load char",
            Inst::Load {
                ty: Ty::Char,
                ptr: v(0),
                volatile: false,
                align: None,
            },
            true,
        ),
        (
            "load (char, i32)",
            Inst::Load {
                ty: Ty::Tuple(vec![Ty::Char, Ty::I32]),
                ptr: v(0),
                volatile: false,
                align: None,
            },
            true,
        ),
        (
            "load &char is a POINTER, not a char (no over-refusal)",
            Inst::Load {
                ty: Ty::Ref(Box::new(Ty::Char)),
                ptr: v(0),
                volatile: false,
                align: None,
            },
            false,
        ),
        (
            "zext char -> u32 (char is the SOURCE)",
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Char,
                dst_ty: Ty::U32,
                operand: v(0),
            },
            false,
        ),
    ];
    for (what, inst, expected_out) in probes {
        let bridge = ConformanceSubset::char_origin_excluded(&inst).is_some();
        let mirror = char_origin_violation(&inst).is_some();
        assert_eq!(
            bridge, mirror,
            "{what}: bridge and mirror condition-6 verdicts drifted"
        );
        assert_eq!(bridge, expected_out, "{what}: wrong condition-6 verdict");
    }
}

/// WS2.17 REVIEW — condition 6 resolves the module's MEMBER TABLES, in BOTH
/// spellings, on the same modules.
///
/// `char_origin_verdicts_agree` above pins the two classifiers on instructions
/// whose types are inline. A `load { char }` names only a `Ty::Struct`, so the
/// inline surface says nothing — yet one `ExtractField` later the program
/// holds a `Char` made out of arbitrary memory bytes. Before this fix both
/// spellings called such a module IN SUBSET, which made condition 6's rule
/// one indirection away from vacuous. The two-sided agreement matters here
/// more than anywhere else: a fix in only one spelling is silent drift.
#[test]
fn char_origin_resolves_named_aggregates_in_both_spellings() {
    // `fn f(p: ptr) { load <ty>; return }`.
    fn module_loading(name: &str, prepare: impl FnOnce(&mut Module) -> Ty) -> Module {
        let mut module = Module::new(name);
        let ty = prepare(&mut module);
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0)).with_param(v(0), Ty::Ptr);
        block.body.push(
            InstrNode::new(Inst::Load {
                ty,
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(1)),
        );
        finish(module, func, block)
    }

    let field = |name: &str, ty: Ty| trust_ir::FieldDef {
        name: name.into(),
        ty,
        offset: None,
    };

    let via_struct = module_loading("agreement-load-struct-char", |m| {
        let id = m.add_struct(trust_ir::StructDef {
            id: StructId::new(0),
            name: "S".into(),
            fields: vec![field("n", Ty::I32), field("c", Ty::Char)],
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        });
        Ty::Struct(id)
    });
    let via_array = module_loading("agreement-load-array-char", |m| {
        let elem = m
            .add_type(Ty::Char)
            .expect("Module::add_type: test fixture");
        Ty::Array(elem, 2)
    });
    // The over-refusal control: the same shape, one mutation away (the member
    // type), must stay in subset in both spellings.
    let no_char = module_loading("agreement-load-struct-nochar", |m| {
        let id = m.add_struct(trust_ir::StructDef {
            id: StructId::new(0),
            name: "S".into(),
            fields: vec![field("n", Ty::I32)],
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        });
        Ty::Struct(id)
    });

    for (what, module, expected_out) in [
        ("load { i32, char }", &via_struct, true),
        ("load [char; 2]", &via_array, true),
        ("load { i32 }", &no_char, false),
    ] {
        let bridge = module.check_conformance_subset().is_err();
        let mirror_violations = module_subset_violations(module);
        assert_eq!(
            bridge,
            !mirror_violations.is_empty(),
            "{what}: bridge and mirror module verdicts drifted ({mirror_violations:?})"
        );
        assert_eq!(bridge, expected_out, "{what}: wrong subset verdict");
        if expected_out {
            assert!(
                mirror_violations
                    .iter()
                    .any(|x| x.contains("may not be READ FROM MEMORY")),
                "{what}: the mirror must name condition 6: {mirror_violations:?}"
            );
            let Err(bridge_violations) = module.check_conformance_subset() else {
                unreachable!("verdict asserted above")
            };
            assert!(
                bridge_violations
                    .iter()
                    .any(|x| x.reason.contains("may not be READ FROM MEMORY")),
                "{what}: the bridge must name condition 6: {bridge_violations:?}"
            );
        }
    }
}

/// The same usize body is admitted at default64 and canonical wasm32,
/// but an unsupported32-bit ABI is refused by the module target, not the type.
#[test]
fn b1_scalar_module_selects_wasm32_but_refuses_unknown32_layouts() {
    let usize_id = || {
        let mut module = Module::new("usize-id");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Usize],
                returns: vec![Ty::Usize],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let func = Function::new(FuncId::new(0), "usize_id", ft, b(0));
        let block = Block::new(b(0)).with_param(v(0), Ty::Usize);
        (module, func, block)
    };

    let (module, func, block) = usize_id();
    let clean = finish(module, func, block);
    assert!(
        module_subset_violations(&clean).is_empty(),
        "a usize body is inside subset v{SUBSET_VERSION}: {:?}",
        module_subset_violations(&clean)
    );

    let (mut module, func, block) = usize_id();
    module.target_info = wasm32();
    let mut on_wasm32 = finish(module, func, block);
    assert!(module_subset_violations(&on_wasm32).is_empty());
    assert!(on_wasm32.check_conformance_subset().is_ok());
    on_wasm32.target_info.as_mut().expect("target").triple = "i686-unknown-linux-gnu".into();
    let violations = module_subset_violations(&on_wasm32);
    assert!(
        violations.iter().any(|x| x.contains("pinned byte model")),
        "an unsupported32-bit ABI must be refused by condition5: {violations:?}"
    );
    assert!(
        !violations.iter().any(|x| x.contains("Ty::Usize")),
        "`Usize` is in-subset in v{SUBSET_VERSION}; only the target refuses \
         this module: {violations:?}"
    );
}

#[path = "common/target_model.rs"]
mod target_model;

/// Every real typed32/64 case agrees between independent classifiers;
/// canonical metadata is selected per module, never inferred from a host.
#[test]
fn v5_target_models_keep_construct_exclusions_and_metadata_lanes() {
    for bits in [32, 64] {
        for &cell in target_model::CELLS {
            let (module, _) = target_model::module(cell, bits);
            assert!(
                trust_ir_build::validate_module(&module).is_empty(),
                "{bits}/{cell:?}"
            );
            assert_eq!(
                module.check_conformance_subset().is_ok(),
                cell.in_subset(),
                "{bits}/{cell:?}"
            );
            assert_eq!(
                module_subset_violations(&module).is_empty(),
                cell.in_subset(),
                "{bits}/{cell:?}"
            );
            if matches!(
                cell,
                target_model::Cell::Fat(_) | target_model::Cell::ThinParts
            ) {
                let mut wrong = module.clone();
                for function in &mut wrong.functions {
                    for block in &mut function.blocks {
                        for node in &mut block.body {
                            match &mut node.inst {
                                Inst::PtrMetadata { metadata_ty, .. }
                                | Inst::PtrFromParts { metadata_ty, .. } => {
                                    *metadata_ty = if *metadata_ty == Ty::U32 {
                                        Ty::U64
                                    } else {
                                        Ty::U32
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }
                assert!(
                    wrong.check_conformance_subset().is_err(),
                    "wrong {bits}/{cell:?}"
                );
                assert!(
                    !module_subset_violations(&wrong).is_empty(),
                    "wrong {bits}/{cell:?}"
                );
            }
        }
    }
}
