// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Fixture generators for the conformance corpus.
//
// Each `build_*` function returns a `trust-ir::Module` that exercises a
// distinct slice of the IR surface. Coverage across all fixtures is
// asserted by `tests/conformance.rs::coverage`, which walks every
// generated module and verifies that every `Ty`, `Inst`, and
// `ProofAnnotation` variant appears at least once.
//
// Fixture design rules:
//
// * Every fixture must validate cleanly under `trust-ir_build::validate_module`
//   (an untyped, well-formed structure only — the goal is wire-format
//   coverage, not end-to-end type checking).
// * Fixtures must round-trip losslessly through every enabled format
//   (binary, canonical text, serde-JSON, serde-MessagePack). If a format
//   ever cannot express a variant, the harness in `tests/conformance.rs`
//   skips that specific format for that fixture and records a reason;
//   today every fixture (including binding-frame instructions) round-trips
//   through all four formats.
// * Value numbering inside a fixture should be stable (`canonicalize`
//   is applied before goldening), so building with the normal
//   `FunctionBuilder` sequential allocator is fine.

use trust_ir::constant::Constant;
use trust_ir::dialect::{AttrValue, DialectInst};
use trust_ir::inst::{
    AllocOrigin, AtomicRMWOp, BinOp, BindingFrameDef, BindingSlot, CastOp, FCmpOp, ICmpOp, Inst,
    Ordering, OverflowOp, SwitchCase, UnOp,
};
use trust_ir::node::InstrNode;
use trust_ir::proof::{
    DiagnosticSeverity, Divergence, ObligationDiagnostic, ObligationKind, ProofAnnotation,
    ProofCertificate, ProofDigest, ProofEvidence, ProofFormula, ProofLineageId,
    ProofLineageManifest, ProofLineageNode, ProofObligation, ProofObligationSourceIdentity,
    ProofObligationSourceRange, ProofReplayIdentity, ProofStatus, ProofTransform,
    ProofTransformStage, PublicObligationIdentity,
};
use trust_ir::ty::{
    ClosureTy, EnumDef, EnumTagRepr, EnumVariant, FatPtrKind, FieldDef, FuncTy, RecordDef, SetRepr,
    StructDef, Ty,
};
use trust_ir::value::{
    BindingFrameId, BlockId, EnumId, FuncId, GlobalId, ProofId, ProofTag, RecordId, SourceSpan,
    StructId, TyId, ValueId,
};
use trust_ir::{
    Block, Endianness, Function, Global, Linkage, Module, ParamAttrs, ScopeData, StructRepr,
    TargetInfo,
};
use trust_ir::{
    CastLayoutEvidence, FieldOffsetShape, NativeAdapterInput, NativeAdtLayoutFact,
    NativeAssertionId, NativeBundleProducer, NativeBundleProvenance, NativeCastFact,
    NativeCompilerFactId, NativeCompilerFactRef, NativeCompilerFacts, NativeDiagnosticLevel,
    NativeDiagnosticsPolicy, NativeEnumLayoutFact, NativeEnumNicheFact, NativeEnumTagEncoding,
    NativeEnumVariantLayoutFact, NativeEvidenceArtifact, NativeEvidenceArtifactKind,
    NativeEvidenceBundle, NativeFatPointerFact, NativeGenericArg, NativeIntegerRange,
    NativeMonomorphizationFact, NativeMonomorphizationId, NativeObligationCause,
    NativeObligationSource, NativeReplayAtom, NativeReplayAtomId, NativeReplayContext,
    NativeRequestId, NativeRequestProvenance, NativeSourceLanguage, NativeToolIdentity,
    NativeVerificationBundle, NativeVerificationRequest, NativeVerifierSuite, PointerLayoutShape,
    PointerMetadataShape, TrustMcArithmeticModel, TrustMcChcEngine, TrustMcChcOptions,
    TrustMcInvariantSource, TrustMcMemoryModel, TrustMcNativeEvidenceBundle, TrustMcNativeRequest,
    TrustMcPdrGeneralization, TrustMcPdrOptions, TrustMcRequestOptions, TrustMcSlicingMode,
    TrustMcVerificationMode, TrustVcMemorySemantics, TrustVcNativeEvidenceBundle,
    TrustVcNativeRequest, TrustVcRequestOptions, TrustVcTrustedEvidencePolicy,
    TrustVcVerificationMode, TrustWpFramePolicy, TrustWpHeapModel, TrustWpLoopStrategy,
    TrustWpNativeEvidenceBundle, TrustWpNativeRequest, TrustWpPanicSemantics,
    TrustWpRequestOptions, TrustWpVerificationMode, TyLayoutKind, TyLayoutShape, TyShape,
};
use trust_ir_build::ModuleBuilder;
use trust_ir_build::demo::VectorDemoExt;

// ---------- ty_primitives ----------

/// Every primitive `Ty` variant appears either as a function parameter,
/// a function return type, a block parameter, or an instruction operand.
pub fn build_ty_primitives() -> Module {
    let mut mb = ModuleBuilder::new("ty_primitives");
    // Signed integers: one function per width returning a constant.
    for (name, ty) in [
        ("i8_id", Ty::I8),
        ("i16_id", Ty::I16),
        ("i32_id", Ty::I32),
        ("i64_id", Ty::I64),
        ("i128_id", Ty::I128),
    ] {
        let ft = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
        let mut fb = mb.function(name, ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, ty.clone());
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();
    }
    // Unsigned integers: use each width in an arithmetic identity.
    for (name, ty) in [
        ("u8_id", Ty::U8),
        ("u16_id", Ty::U16),
        ("u32_id", Ty::U32),
        ("u64_id", Ty::U64),
        ("u128_id", Ty::U128),
    ] {
        let ft = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
        let mut fb = mb.function(name, ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, ty.clone());
        fb.switch_to_block(entry);
        let zero = fb.iconst(ty.clone(), 0);
        let sum = fb.add(ty.clone(), x, zero);
        fb.ret(vec![sum]);
        fb.build();
    }
    // Floats.
    for (name, ty) in [
        ("f16_id", Ty::F16),
        ("f32_id", Ty::F32),
        ("f64_id", Ty::F64),
    ] {
        let ft = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
        let mut fb = mb.function(name, ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, ty.clone());
        fb.switch_to_block(entry);
        let zero = fb.fconst(ty.clone(), 0.0);
        let sum = fb.fadd(ty.clone(), x, zero);
        fb.ret(vec![sum]);
        fb.build();
    }
    // Bool.
    {
        let ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
        let mut fb = mb.function("bool_id", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::Bool);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();
    }
    // Ptr.
    {
        let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Ptr]);
        let mut fb = mb.function("ptr_id", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();
    }
    // Unit.
    {
        let ft = mb.add_func_type(vec![], vec![Ty::Unit]);
        let mut fb = mb.function("unit_value", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let u = fb.undef(Ty::Unit);
        fb.ret(vec![u]);
        fb.build();
    }
    // Never (diverging).
    {
        let ft = mb.add_func_type(vec![], vec![Ty::Never]);
        let mut fb = mb.function("diverge", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.unreachable();
        fb.build();
    }
    // Pin target triple so fixtures are target-stable.
    let mut m = mb.build();
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        // ABI pinning (v20): a non-default stable ABI id so the goldens pin
        // the extended TargetInfo wire form (policy stays the NativeC default).
        abi: Some("aapcs64".into()),
        struct_passing: Default::default(),
    });
    m
}

// ---------- ty_composite ----------

/// Every composite / reference `Ty` variant appears on a function or
/// block signature. Referenced definitions (`StructDef`, `EnumDef`,
/// `RecordDef`, `ClosureTy`) live on the module's side tables.
pub fn build_ty_composite() -> Module {
    let mut m = Module::new("ty_composite");

    // Struct: { a: i32, b: f64 }
    let point = m.add_struct(StructDef {
        id: StructId::new(0),
        name: "Point".into(),
        fields: vec![
            FieldDef {
                name: "a".into(),
                ty: Ty::I32,
                offset: Some(0),
            },
            FieldDef {
                name: "b".into(),
                ty: Ty::F64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),

        repr: Default::default(),
    });

    // Enum: Maybe { Some(i64) | None }
    let maybe = m.add_enum(EnumDef {
        id: EnumId::new(0),
        name: "Maybe".into(),
        variants: vec![
            EnumVariant {
                name: "Some".into(),
                fields: vec![Ty::I64],
                field_names: Vec::new(),
            },
            EnumVariant {
                name: "None".into(),
                fields: vec![],
                field_names: Vec::new(),
            },
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: None,
    });

    // Enum with the v19 canonical-layout fields exercised: an explicit +
    // implicit discriminant mix (including a negative value) and a tag-repr
    // hint. Guards the new wire surface across binary / text / JSON /
    // MessagePack.
    m.add_enum(
        EnumDef::new(
            EnumId::new(1),
            "Sparse",
            vec![
                EnumVariant {
                    name: "Neg".into(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Next".into(),
                    fields: vec![Ty::I16],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Big".into(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
            ],
        )
        .with_discriminants(vec![Some(-3), None, Some(1000)])
        .with_repr(EnumTagRepr::I16),
    );

    // Record: { x: i64, y: i64 }
    let rec = m.add_record(RecordDef {
        id: RecordId::new(0),
        name: "Vec2".into(),
        fields: vec![
            FieldDef {
                name: "x".into(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "y".into(),
                ty: Ty::I64,
                offset: None,
            },
        ],
    });

    // Func type used by a closure and indirectly.
    let inner_ft = m.add_func_type(FuncTy {
        params: vec![Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });

    // Closure: (I32)->I32 with captures [I64, F64]
    let closure = m.add_closure_type(ClosureTy {
        func: inner_ft,
        captures: vec![Ty::I64, Ty::F64],
    });

    // A Ty interned in `module.types` (used by validating tooling as a
    // canonical type reference — see `Ty::Array(TyId, u64)` and
    // `Ty::Sequence(TyId)` below).
    let i32_interned = m.add_type(Ty::I32);

    // The "carrier" function signature walks every composite / ref variant.
    let composite_ft = m.add_func_type(FuncTy {
        params: vec![
            Ty::Struct(point),
            Ty::Array(i32_interned, 4),
            Ty::Tuple(vec![Ty::I32, Ty::F64, Ty::Bool]),
            Ty::Enum(maybe),
            Ty::Func(inner_ft),
            Ty::Sequence(i32_interned),
            Ty::Set(i32_interned, SetRepr::Bitset),
            Ty::Set(i32_interned, SetRepr::Boxed),
            Ty::Record(rec),
            Ty::Closure(closure),
            Ty::Ref(Box::new(Ty::I64)),
            Ty::RefMut(Box::new(Ty::I64)),
            Ty::PtrConst(Box::new(Ty::U8)),
            Ty::PtrMut(Box::new(Ty::U8)),
            Ty::FatPtr(FatPtrKind::Str),
            Ty::Rc(Box::new(Ty::I32)),
        ],
        returns: vec![Ty::Unit],
        is_vararg: false,
    });

    // Minimal body: entry block accepting every composite param then returning unit.
    let mut func = Function::new(
        FuncId::new(0),
        "composite_carrier",
        composite_ft,
        BlockId::new(0),
    );
    let mut entry = Block::new(BlockId::new(0));
    for (i, ty) in [
        Ty::Struct(point),
        Ty::Array(i32_interned, 4),
        Ty::Tuple(vec![Ty::I32, Ty::F64, Ty::Bool]),
        Ty::Enum(maybe),
        Ty::Func(inner_ft),
        Ty::Sequence(i32_interned),
        Ty::Set(i32_interned, SetRepr::Bitset),
        Ty::Set(i32_interned, SetRepr::Boxed),
        Ty::Record(rec),
        Ty::Closure(closure),
        Ty::Ref(Box::new(Ty::I64)),
        Ty::RefMut(Box::new(Ty::I64)),
        Ty::PtrConst(Box::new(Ty::U8)),
        Ty::PtrMut(Box::new(Ty::U8)),
        Ty::FatPtr(FatPtrKind::Str),
        Ty::Rc(Box::new(Ty::I32)),
    ]
    .into_iter()
    .enumerate()
    {
        entry.params.push((ValueId::new(i as u32), ty));
    }
    let unit_val = ValueId::new(100);
    entry
        .body
        .push(InstrNode::new(Inst::Undef { ty: Ty::Unit }).with_result(unit_val));
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![unit_val],
    }));
    func.blocks.push(entry);
    m.add_function(func);

    // Globals referencing composite initializers (exercises `Constant::Aggregate`).
    m.globals.push(Global {
        name: "G_POINT".into(),
        ty: Ty::Struct(point),
        mutable: false,
        initializer: Some(Constant::Aggregate(vec![
            Constant::Int(1),
            Constant::Float(2.5),
        ])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });
    m.globals.push(Global {
        name: "G_SEQ".into(),
        ty: Ty::Sequence(i32_interned),
        mutable: false,
        initializer: Some(Constant::Sequence(vec![Constant::Int(1), Constant::Int(2)])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });
    m.globals.push(Global {
        name: "G_ARRAY".into(),
        ty: Ty::Array(i32_interned, 2),
        mutable: false,
        initializer: Some(Constant::Array(vec![Constant::Int(1), Constant::Int(2)])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });
    m.globals.push(Global {
        name: "G_SET".into(),
        ty: Ty::Set(i32_interned, SetRepr::Boxed),
        mutable: false,
        initializer: Some(Constant::Set(vec![Constant::Int(1), Constant::Int(2)])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });
    m.globals.push(Global {
        name: "G_REC".into(),
        ty: Ty::Record(rec),
        mutable: false,
        initializer: Some(Constant::Record(vec![
            ("x".into(), Constant::Int(1)),
            ("y".into(), Constant::Int(2)),
        ])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });
    m.globals.push(Global {
        name: "G_CLOSURE".into(),
        ty: Ty::Closure(closure),
        mutable: false,
        initializer: Some(Constant::Closure {
            func: FuncId::new(0),
            captures: vec![Constant::Int(1), Constant::Float(2.5)],
        }),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });
    m.globals.push(Global {
        name: "G_FNDEF".into(),
        ty: Ty::Func(composite_ft),
        mutable: false,
        initializer: Some(Constant::FnDef(FuncId::new(0))),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });
    m.globals.push(Global {
        name: "G_PHANTOM".into(),
        ty: Ty::Unit,
        mutable: false,
        initializer: Some(Constant::PhantomData),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });

    m
}

// ---------- inst_arithmetic ----------

/// Covers `Inst::SeqMapAddK` (the Aeneas loop forward function `for x in &mut l
/// { *x += k }`, `loopFwd`) over a `&mut Sequence<i32>`. Guards wire-format
/// coverage of the give-back loop instruction across all four formats.
pub fn build_inst_seq_map() -> Module {
    let mut m = Module::new("inst_seq_map");
    let i32_interned = m.add_type(Ty::I32);
    let seq_ty = Ty::Sequence(i32_interned);
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::RefMut(Box::new(seq_ty.clone()))],
        returns: vec![],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "seq_incr_all", ft, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry
        .params
        .push((ValueId::new(0), Ty::RefMut(Box::new(seq_ty.clone()))));
    entry.body.push(
        InstrNode::new(Inst::BorrowMut {
            ptr: ValueId::new(0),
        })
        .with_result(ValueId::new(1)),
    );
    entry.body.push(
        InstrNode::new(Inst::Load {
            ty: seq_ty.clone(),
            ptr: ValueId::new(1),
            volatile: false,
            align: None,
        })
        .with_result(ValueId::new(2)),
    );
    entry.body.push(
        InstrNode::new(Inst::SeqMapAddK {
            ty: seq_ty.clone(),
            seq: ValueId::new(2),
            k: 3,
        })
        .with_result(ValueId::new(3)),
    );
    entry.body.push(InstrNode::new(Inst::Store {
        ty: seq_ty,
        ptr: ValueId::new(1),
        value: ValueId::new(3),
        volatile: false,
        align: None,
    }));
    entry.body.push(InstrNode::new(Inst::EndBorrow {
        borrow_ptr: ValueId::new(1),
    }));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    func.blocks.push(entry);
    m.add_function(func);
    m
}

/// Covers `Inst::SeqMapNot` (the boolean-flip loop `for b in &mut l { *b = !*b }`,
/// `loopFwd` over a `&mut Sequence<bool>`) — the second element-op loop instruction.
pub fn build_inst_seq_map_not() -> Module {
    let mut m = Module::new("inst_seq_map_not");
    let bool_interned = m.add_type(Ty::Bool);
    let seq_ty = Ty::Sequence(bool_interned);
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::RefMut(Box::new(seq_ty.clone()))],
        returns: vec![],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "flip_all", ft, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry
        .params
        .push((ValueId::new(0), Ty::RefMut(Box::new(seq_ty.clone()))));
    entry.body.push(
        InstrNode::new(Inst::BorrowMut {
            ptr: ValueId::new(0),
        })
        .with_result(ValueId::new(1)),
    );
    entry.body.push(
        InstrNode::new(Inst::Load {
            ty: seq_ty.clone(),
            ptr: ValueId::new(1),
            volatile: false,
            align: None,
        })
        .with_result(ValueId::new(2)),
    );
    entry.body.push(
        InstrNode::new(Inst::SeqMapNot {
            ty: seq_ty.clone(),
            seq: ValueId::new(2),
        })
        .with_result(ValueId::new(3)),
    );
    entry.body.push(InstrNode::new(Inst::Store {
        ty: seq_ty,
        ptr: ValueId::new(1),
        value: ValueId::new(3),
        volatile: false,
        align: None,
    }));
    entry.body.push(InstrNode::new(Inst::EndBorrow {
        borrow_ptr: ValueId::new(1),
    }));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    func.blocks.push(entry);
    m.add_function(func);
    m
}

/// Covers `Inst::SeqMap` (the GENERAL element-op loop `for x in &mut l { *x =
/// fwd(x) }` with a first-class element `FuncId` — designs/2026-06-30-general-
/// seqmap-instruction.md). The module carries both the loop function and the
/// single-`&mut` element function `incr_elem(x: &mut i32) { *x += 1 }`, so the
/// fixture also exercises the FuncId operand class on a map instruction.
pub fn build_inst_seq_map_general() -> Module {
    let mut m = Module::new("inst_seq_map_general");
    let i32_interned = m.add_type(Ty::I32);
    let seq_ty = Ty::Sequence(i32_interned);
    let loop_ft = m.add_func_type(FuncTy {
        params: vec![Ty::RefMut(Box::new(seq_ty.clone()))],
        returns: vec![],
        is_vararg: false,
    });
    let elem_ft = m.add_func_type(FuncTy {
        params: vec![Ty::RefMut(Box::new(Ty::I32))],
        returns: vec![],
        is_vararg: false,
    });

    // fn incr_all(l: &mut Seq<i32>) { for x in &mut l { *x = incr_elem(x) } }
    let mut func = Function::new(FuncId::new(0), "incr_all", loop_ft, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry
        .params
        .push((ValueId::new(0), Ty::RefMut(Box::new(seq_ty.clone()))));
    entry.body.push(
        InstrNode::new(Inst::BorrowMut {
            ptr: ValueId::new(0),
        })
        .with_result(ValueId::new(1)),
    );
    entry.body.push(
        InstrNode::new(Inst::Load {
            ty: seq_ty.clone(),
            ptr: ValueId::new(1),
            volatile: false,
            align: None,
        })
        .with_result(ValueId::new(2)),
    );
    entry.body.push(
        InstrNode::new(Inst::SeqMap {
            ty: seq_ty.clone(),
            seq: ValueId::new(2),
            fwd: FuncId::new(1),
        })
        .with_result(ValueId::new(3)),
    );
    entry.body.push(InstrNode::new(Inst::Store {
        ty: seq_ty,
        ptr: ValueId::new(1),
        value: ValueId::new(3),
        volatile: false,
        align: None,
    }));
    entry.body.push(InstrNode::new(Inst::EndBorrow {
        borrow_ptr: ValueId::new(1),
    }));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    func.blocks.push(entry);
    m.add_function(func);

    // fn incr_elem(x: &mut i32) { *x += 1 }
    let mut elem = Function::new(FuncId::new(1), "incr_elem", elem_ft, BlockId::new(0));
    let mut eb = Block::new(BlockId::new(0));
    eb.params
        .push((ValueId::new(0), Ty::RefMut(Box::new(Ty::I32))));
    eb.body.push(
        InstrNode::new(Inst::BorrowMut {
            ptr: ValueId::new(0),
        })
        .with_result(ValueId::new(1)),
    );
    eb.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::I32,
            ptr: ValueId::new(1),
            volatile: false,
            align: None,
        })
        .with_result(ValueId::new(2)),
    );
    eb.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(1),
        })
        .with_result(ValueId::new(3)),
    );
    eb.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: ValueId::new(2),
            rhs: ValueId::new(3),
        })
        .with_result(ValueId::new(4)),
    );
    eb.body.push(InstrNode::new(Inst::Store {
        ty: Ty::I32,
        ptr: ValueId::new(1),
        value: ValueId::new(4),
        volatile: false,
        align: None,
    }));
    eb.body.push(InstrNode::new(Inst::EndBorrow {
        borrow_ptr: ValueId::new(1),
    }));
    eb.body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    elem.blocks.push(eb);
    m.add_function(elem);

    m
}

/// Covers every `BinOp`, every `UnOp`, every `OverflowOp`,
/// every `ICmpOp`, every `FCmpOp`, the validation-safe `CastOp`s,
/// and `Copy`/`Select`.
pub fn build_inst_arithmetic() -> Module {
    let mut mb = ModuleBuilder::new("inst_arithmetic");

    // int_ops: exercise all 18 BinOp variants, all 3 UnOp, all 3 Overflow,
    // all 10 ICmp, and validation-safe CastOps reachable from scalar types.
    let ft = mb.add_func_type(
        vec![
            Ty::I64,
            Ty::I64,
            Ty::I32,
            Ty::U32,
            Ty::F32,
            Ty::F64,
            Ty::Bool,
            Ty::Ptr,
            Ty::FatPtr(FatPtrKind::Str),
            Ty::U64,
        ],
        vec![Ty::I64],
    );
    let mut fb = mb.function("int_ops", ft);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I64);
    let b = fb.add_block_param(entry, Ty::I64);
    let a32 = fb.add_block_param(entry, Ty::I32);
    let u32v = fb.add_block_param(entry, Ty::U32);
    let f32v = fb.add_block_param(entry, Ty::F32);
    let f64v = fb.add_block_param(entry, Ty::F64);
    let cond = fb.add_block_param(entry, Ty::Bool);
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let fat_str = fb.add_block_param(entry, Ty::FatPtr(FatPtrKind::Str));
    let metadata = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);

    // 18 BinOps on (i64, i64). Some (UDiv/SDiv/URem/SRem/FAdd/...)
    // require matching types; use i64 for int ops, f64 for fp ops.
    for op in [
        BinOp::Add,
        BinOp::Sub,
        BinOp::Mul,
        BinOp::UDiv,
        BinOp::SDiv,
        BinOp::URem,
        BinOp::SRem,
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
        BinOp::Shl,
        BinOp::LShr,
        BinOp::AShr,
    ] {
        let _ = fb.binop(op, Ty::I64, a, b);
    }
    for op in [
        BinOp::FAdd,
        BinOp::FSub,
        BinOp::FMul,
        BinOp::FDiv,
        BinOp::FRem,
    ] {
        let _ = fb.binop(op, Ty::F64, f64v, f64v);
    }
    // UnOp: Neg, FNeg, Not, CtPop.
    let _ = fb.unop(UnOp::Neg, Ty::I64, a);
    let _ = fb.unop(UnOp::FNeg, Ty::F64, f64v);
    let _ = fb.unop(UnOp::Not, Ty::I64, a);
    let _ = fb.ctpop(Ty::I64, a);
    // OverflowOp x3.
    for op in [
        OverflowOp::AddOverflow,
        OverflowOp::SubOverflow,
        OverflowOp::MulOverflow,
    ] {
        let _ = fb.overflow(op, Ty::I64, a, b);
    }
    // ICmp x10.
    for op in [
        ICmpOp::Eq,
        ICmpOp::Ne,
        ICmpOp::Ult,
        ICmpOp::Ule,
        ICmpOp::Ugt,
        ICmpOp::Uge,
        ICmpOp::Slt,
        ICmpOp::Sle,
        ICmpOp::Sgt,
        ICmpOp::Sge,
    ] {
        let _ = fb.icmp(op, Ty::I64, a, b);
    }
    // FCmp x12.
    for op in [
        FCmpOp::OEq,
        FCmpOp::ONe,
        FCmpOp::OLt,
        FCmpOp::OLe,
        FCmpOp::OGt,
        FCmpOp::OGe,
        FCmpOp::UEq,
        FCmpOp::UNe,
        FCmpOp::ULt,
        FCmpOp::ULe,
        FCmpOp::UGt,
        FCmpOp::UGe,
    ] {
        let _ = fb.fcmp(op, Ty::F64, f64v, f64v);
    }
    // Validation-safe casts — pick input/output type pairs that are well-formed.
    let _ = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, a);
    let _ = fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, a32);
    let _ = fb.cast(CastOp::SExt, Ty::I32, Ty::I64, a32);
    let _ = fb.cast(CastOp::FPTrunc, Ty::F64, Ty::F32, f64v);
    let _ = fb.cast(CastOp::FPExt, Ty::F32, Ty::F64, f32v);
    let _ = fb.cast(CastOp::FPToUI, Ty::F64, Ty::U32, f64v);
    let _ = fb.cast(CastOp::FPToSI, Ty::F64, Ty::I32, f64v);
    let _ = fb.cast(CastOp::UIToFP, Ty::U32, Ty::F32, u32v);
    let _ = fb.cast(CastOp::SIToFP, Ty::I32, Ty::F64, a32);
    let _ = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, ptr);
    let _ = fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, metadata);
    let _ = fb.cast(CastOp::Bitcast, Ty::F32, Ty::I32, f32v);
    let fat_str_ty = Ty::FatPtr(FatPtrKind::Str);
    let _ = fb.ptr_data(fat_str_ty.clone(), fat_str);
    let _ = fb.ptr_metadata(fat_str_ty.clone(), Ty::U64, fat_str);
    let _ = fb.ptr_from_parts(fat_str_ty, Ty::U64, ptr, metadata);
    // Copy and Select.
    let _ = fb.copy(Ty::I64, a);
    let _ = fb.select(Ty::I64, cond, a, b);
    fb.ret(vec![a]);
    fb.build();

    mb.build()
}

// ---------- inst_vector ----------

/// Covers fixed-width vector arithmetic, vector `icmp` masks, vector
/// `select`, and vector load/store through every public conformance format.
pub fn build_inst_vector() -> Module {
    let mut mb = ModuleBuilder::new("inst_vector");
    let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
    let v4bool = Ty::Vector(Box::new(Ty::Bool), 4);

    let ft = mb.add_func_type(
        vec![Ty::Ptr, v4i32.clone(), v4i32.clone()],
        vec![v4i32.clone(), v4bool.clone()],
    );
    let mut fb = mb.function("batch_i32", ft);
    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let a = fb.add_block_param(entry, v4i32.clone());
    let b = fb.add_block_param(entry, v4i32.clone());
    fb.switch_to_block(entry);

    let loaded = fb.load_aligned(v4i32.clone(), ptr, 16);
    let add = fb.add(v4i32.clone(), a, b);
    let sub = fb.sub(v4i32.clone(), add, loaded);
    let mul = fb.mul(v4i32.clone(), sub, b);
    let and = fb.binop(BinOp::And, v4i32.clone(), mul, a);
    let or = fb.binop(BinOp::Or, v4i32.clone(), and, b);
    let xor = fb.binop(BinOp::Xor, v4i32.clone(), or, loaded);
    let mask = fb.icmp(ICmpOp::Eq, v4i32.clone(), xor, loaded);
    let selected = fb.select(v4i32.clone(), mask, xor, loaded);
    fb.store_aligned(v4i32.clone(), ptr, selected, 16);
    fb.ret(vec![selected, mask]);
    fb.build();

    mb.build()
}

// ---------- inst_vector_dialect ----------

/// Covers the portable `vector.*` dialect contract separately from the
/// generic opaque dialect fixture.
pub fn build_inst_vector_dialect() -> Module {
    let mut mb = ModuleBuilder::new("inst_vector_dialect");

    let ft = mb.add_func_type(
        vec![
            Ty::I32,
            Ty::I32,
            Ty::I32,
            Ty::I32,
            Ty::I64,
            Ty::I64,
            Ty::v4_i32(),
            Ty::I32,
            Ty::v2_i64(),
            Ty::I64,
            Ty::v8_bool(),
            Ty::v16_bool(),
        ],
        vec![
            Ty::v4_i32(),
            Ty::I32,
            Ty::v4_i32(),
            Ty::v2_i64(),
            Ty::I64,
            Ty::v2_i64(),
            Ty::I32,
            Ty::I64,
            Ty::I32,
            Ty::I32,
        ],
    );
    let mut fb = mb.function("portable_vector_dialect", ft);
    let entry = fb.create_block();
    let l0 = fb.add_block_param(entry, Ty::I32);
    let l1 = fb.add_block_param(entry, Ty::I32);
    let l2 = fb.add_block_param(entry, Ty::I32);
    let l3 = fb.add_block_param(entry, Ty::I32);
    let wide0 = fb.add_block_param(entry, Ty::I64);
    let wide1 = fb.add_block_param(entry, Ty::I64);
    let v4_seed = fb.add_block_param(entry, Ty::v4_i32());
    let v4_replacement = fb.add_block_param(entry, Ty::I32);
    let v2_seed = fb.add_block_param(entry, Ty::v2_i64());
    let v2_replacement = fb.add_block_param(entry, Ty::I64);
    let v8_mask = fb.add_block_param(entry, Ty::v8_bool());
    let v16_mask = fb.add_block_param(entry, Ty::v16_bool());
    fb.switch_to_block(entry);

    let packed_v4 = fb
        .v4_i32_pack_lanes([l0, l1, l2, l3])
        .expect("valid <4 x i32> lane pack");
    let extracted_v4 = fb
        .v4_i32_extract_lane(packed_v4, 2)
        .expect("valid <4 x i32> lane extract");
    let inserted_v4 = fb
        .v4_i32_insert_lane(v4_seed, 1, v4_replacement)
        .expect("valid <4 x i32> lane insert");

    let packed_v2 = fb
        .v2_i64_pack_lanes([wide0, wide1])
        .expect("valid <2 x i64> lane pack");
    let extracted_v2 = fb
        .v2_i64_extract_lane(packed_v2, 1)
        .expect("valid <2 x i64> lane extract");
    let inserted_v2 = fb
        .v2_i64_insert_lane(v2_seed, 0, v2_replacement)
        .expect("valid <2 x i64> lane insert");

    let v4_mask = fb.icmp(ICmpOp::Sgt, Ty::v4_i32(), inserted_v4, packed_v4);
    let v4_bits = fb
        .v4_bool_mask_to_i32_bits(v4_mask)
        .expect("valid <4 x bool> mask compaction");
    let v2_mask = fb.icmp(ICmpOp::Eq, Ty::v2_i64(), inserted_v2, packed_v2);
    let v2_bits = fb
        .v2_bool_mask_to_i64_bits(v2_mask)
        .expect("valid <2 x bool> mask compaction");
    let v8_bits = fb
        .v8_bool_mask_to_i32_bits(v8_mask)
        .expect("valid <8 x bool> mask compaction");
    let v16_bits = fb
        .v16_bool_mask_to_i32_bits(v16_mask)
        .expect("valid <16 x bool> mask compaction");

    fb.ret(vec![
        packed_v4,
        extracted_v4,
        inserted_v4,
        packed_v2,
        extracted_v2,
        inserted_v2,
        v4_bits,
        v2_bits,
        v8_bits,
        v16_bits,
    ]);
    fb.build();

    mb.build()
}

// ---------- inst_vector_crosslane ----------

/// Covers the cross-lane `vector.*` ops (`reduce` / `shuffle` / `fma`) added
/// for the fast-4 "much faster metadata" leg. These ops have no operational
/// lowering into other dialect ops: the reference interpreter executes them
/// directly and a backend selects them to horizontal-reduce / permute / FMA
/// instructions. The fixture pins their wire form so downstream consumers can
/// detect payload drift independently from the structural lane ops above.
pub fn build_inst_vector_crosslane() -> Module {
    use trust_ir::dialect::vector::ReduceKind;

    let mut mb = ModuleBuilder::new("inst_vector_crosslane");

    let ft = mb.add_func_type(
        vec![Ty::v4_i32(), Ty::v2_i64(), Ty::v4_f32(), Ty::v2_f64()],
        vec![
            Ty::I32,
            Ty::I64,
            Ty::v4_i32(),
            Ty::v2_i64(),
            Ty::v4_f32(),
            Ty::v2_f64(),
        ],
    );
    let mut fb = mb.function("portable_vector_crosslane", ft);
    let entry = fb.create_block();
    let v4 = fb.add_block_param(entry, Ty::v4_i32());
    let v2 = fb.add_block_param(entry, Ty::v2_i64());
    let v4f = fb.add_block_param(entry, Ty::v4_f32());
    let v2f = fb.add_block_param(entry, Ty::v2_f64());
    fb.switch_to_block(entry);

    let reduced_add = fb
        .vector_reduce(Ty::v4_i32(), v4, ReduceKind::Add)
        .expect("valid <4 x i32> reduce-add");
    let reduced_or = fb
        .vector_reduce(Ty::v2_i64(), v2, ReduceKind::Or)
        .expect("valid <2 x i64> reduce-or");

    let shuffled_v4 = fb
        .vector_shuffle(Ty::v4_i32(), v4, [3u8, 2, 1, 0])
        .expect("valid <4 x i32> reverse shuffle");
    let shuffled_v2 = fb
        .vector_shuffle(Ty::v2_i64(), v2, [1u8, 1])
        .expect("valid <2 x i64> broadcast shuffle");

    let fma_v4 = fb
        .vector_fma(Ty::v4_f32(), v4f, v4f, v4f)
        .expect("valid <4 x f32> fma");
    let fma_v2 = fb
        .vector_fma(Ty::v2_f64(), v2f, v2f, v2f)
        .expect("valid <2 x f64> fma");

    fb.ret(vec![
        reduced_add,
        reduced_or,
        shuffled_v4,
        shuffled_v2,
        fma_v4,
        fma_v2,
    ]);
    fb.build();

    mb.build()
}

// ---------- vector_mask_oracles ----------

/// Machine-readable oracle rows for executable vector mask semantics.
///
/// These rows deliberately live beside the structural `inst_vector_dialect`
/// fixture instead of replacing it: downstream consumers can pin concrete
/// x86-facing mask behavior without scraping prose from test code.
#[derive(Debug, Clone)]
pub struct VectorMaskOracleFixture {
    pub name: &'static str,
    pub case: VectorMaskOracleCase,
    pub mask_ty: Ty,
    pub result_ty: Ty,
    pub bit_order: &'static str,
    pub expected_compacted_integer: u64,
    pub expected_rust_output: &'static str,
    pub expected_lean_output: &'static str,
    pub lean_theorem: &'static str,
}

#[derive(Debug, Clone)]
pub enum VectorMaskOracleCase {
    LogicalMask {
        input_lanes: Vec<bool>,
    },
    CompareMask {
        compare_op: ICmpOp,
        compare_ty: Ty,
        lhs_lanes: Vec<i128>,
        rhs_lanes: Vec<i128>,
        expected_mask_lanes: Vec<bool>,
    },
}

pub fn build_vector_mask_oracles() -> Vec<VectorMaskOracleFixture> {
    vec![
        VectorMaskOracleFixture {
            name: "mask_to_bits_v16_bool_sparse_i32",
            case: VectorMaskOracleCase::LogicalMask {
                input_lanes: vec![
                    true, false, false, true, false, true, false, false, true, false, false, false,
                    false, true, false, true,
                ],
            },
            mask_ty: Ty::v16_bool(),
            result_ty: Ty::I32,
            bit_order: "lsb_lane0",
            expected_compacted_integer: 0xa129,
            expected_rust_output: "ok:return:[int32:41257]",
            expected_lean_output: "ok:value:int32:41257",
            lean_theorem: "vector_mask_oracle_v16_bool_sparse_i32_stable",
        },
        VectorMaskOracleFixture {
            name: "mask_to_bits_v8_bool_sparse_i32",
            case: VectorMaskOracleCase::LogicalMask {
                input_lanes: vec![true, false, true, true, false, false, false, true],
            },
            mask_ty: Ty::v8_bool(),
            result_ty: Ty::I32,
            bit_order: "lsb_lane0",
            expected_compacted_integer: 0x8d,
            expected_rust_output: "ok:return:[int32:141]",
            expected_lean_output: "ok:value:int32:141",
            lean_theorem: "vector_mask_oracle_v8_bool_sparse_i32_stable",
        },
        VectorMaskOracleFixture {
            name: "mask_to_bits_v4_bool_existing_i32",
            case: VectorMaskOracleCase::LogicalMask {
                input_lanes: vec![true, false, true, true],
            },
            mask_ty: Ty::v4_bool(),
            result_ty: Ty::I32,
            bit_order: "lsb_lane0",
            expected_compacted_integer: 0xd,
            expected_rust_output: "ok:return:[int32:13]",
            expected_lean_output: "ok:value:int32:13",
            lean_theorem: "vector_mask_oracle_v4_bool_existing_i32_stable",
        },
        VectorMaskOracleFixture {
            name: "mask_to_bits_v2_bool_existing_i64",
            case: VectorMaskOracleCase::LogicalMask {
                input_lanes: vec![false, true],
            },
            mask_ty: Ty::v2_bool(),
            result_ty: Ty::I64,
            bit_order: "lsb_lane0",
            expected_compacted_integer: 0x2,
            expected_rust_output: "ok:return:[int64:2]",
            expected_lean_output: "ok:value:int64:2",
            lean_theorem: "vector_mask_oracle_v2_bool_existing_i64_stable",
        },
        VectorMaskOracleFixture {
            name: "compare_slt_v16_i8_mask_to_bits_i32",
            case: VectorMaskOracleCase::CompareMask {
                compare_op: ICmpOp::Slt,
                compare_ty: Ty::Vector(Box::new(Ty::I8), 16),
                lhs_lanes: vec![
                    -1, 0, 1, 127, -128, 5, -6, 42, 100, -56, 15, 16, 17, 18, 19, 20,
                ],
                rhs_lanes: vec![
                    1, 0, 2, 126, 127, 6, -5, 40, 99, -57, 15, 10, 18, 17, 21, 20,
                ],
                expected_mask_lanes: vec![
                    true, false, true, false, true, true, true, false, false, false, false, false,
                    true, false, true, false,
                ],
            },
            mask_ty: Ty::v16_bool(),
            result_ty: Ty::I32,
            bit_order: "lsb_lane0",
            expected_compacted_integer: 0x5075,
            expected_rust_output: "ok:return:[vector[bool:true,bool:false,bool:true,bool:false,bool:true,bool:true,bool:true,bool:false,bool:false,bool:false,bool:false,bool:false,bool:true,bool:false,bool:true,bool:false],int32:20597]",
            expected_lean_output: "ok:value:int32:20597",
            lean_theorem: "vector_mask_oracle_compare_slt_v16_i8_i32_stable",
        },
        VectorMaskOracleFixture {
            name: "compare_slt_v8_i16_mask_to_bits_i32",
            case: VectorMaskOracleCase::CompareMask {
                compare_op: ICmpOp::Slt,
                compare_ty: Ty::Vector(Box::new(Ty::I16), 8),
                lhs_lanes: vec![-1, 0, 32767, -32768, 100, -25536, 7, 8],
                rhs_lanes: vec![1, 0, 32766, 32767, 101, -25537, 6, 9],
                expected_mask_lanes: vec![true, false, false, true, true, false, false, true],
            },
            mask_ty: Ty::v8_bool(),
            result_ty: Ty::I32,
            bit_order: "lsb_lane0",
            expected_compacted_integer: 0x99,
            expected_rust_output: "ok:return:[vector[bool:true,bool:false,bool:false,bool:true,bool:true,bool:false,bool:false,bool:true],int32:153]",
            expected_lean_output: "ok:value:int32:153",
            lean_theorem: "vector_mask_oracle_compare_slt_v8_i16_i32_stable",
        },
    ]
}

// ---------- inst_memory ----------

/// Covers Load, Store, Alloca, GEP, Dealloc, ExtractField, InsertField,
/// ExtractElement, InsertElement, NullPtr, Undef, Const.
pub fn build_inst_memory() -> Module {
    let mut mb = ModuleBuilder::new("inst_memory");
    // A module-level static whose address is taken by `GlobalAddr` (B1).
    // The explicit over-alignment pins Global.align across binary, canonical
    // text, JSON, and MessagePack instead of exercising only its None default.
    mb.add_global(Global {
        name: "MEM_STATIC".into(),
        ty: Ty::I32,
        mutable: false,
        initializer: Some(Constant::Int(7)),
        linkage: Linkage::Internal,
        tls: None,
        align: Some(32),
    });
    let i32_ty = mb.add_func_type(vec![Ty::Ptr, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("mem_roundtrip", i32_ty);
    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    // Alloca an i32 slot, store x, load it back, dealloc the slot.
    let slot = fb.alloca(Ty::I32);
    fb.store(Ty::I32, slot, x);
    let loaded = fb.load(Ty::I32, slot);
    // GEP into an external pointer.
    let zero = fb.iconst(Ty::I64, 0);
    let _off = fb.gep(Ty::I32, ptr, vec![zero]);
    // Non-default memory-field coverage so the cross-format golden exercises the
    // true/non-null paths (not just volatile:false / inbounds:false / align:null):
    // a volatile load, an aligned store, an inbounds GEP, an aligned alloca.
    let _vload = fb.load_volatile(Ty::I32, slot);
    fb.store_aligned(Ty::I32, slot, x, 4);
    let _ginb = fb.gep_inbounds(Ty::I32, ptr, vec![zero]);
    let _aslot = fb.alloca_aligned(Ty::I32, 8);
    fb.dealloc(_aslot);
    // NullPtr + Undef + Const.
    let _n = fb.null_ptr();
    // GlobalAddr: address of the module static MEM_STATIC (B1).
    let _g = fb.global_addr(GlobalId::new(0));
    let _u = fb.undef(Ty::I32);
    let _c = fb.iconst(Ty::I32, 7);
    // HeapAlloc: a heap i32 region from the Rust allocator, freed by Dealloc (B2).
    let heap = fb.heap_alloc(Ty::I32, None, None, AllocOrigin::RustHeap);
    fb.store(Ty::I32, heap, x);
    fb.dealloc(heap);
    fb.dealloc(slot);
    fb.ret(vec![loaded]);
    fb.build();

    // Aggregate accessors: extract/insert field, extract/insert element.
    let agg_ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("aggregates", agg_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    // Build a tuple-typed undef and poke at it.
    let tup = Ty::Tuple(vec![Ty::I32, Ty::F64, Ty::Bool]);
    let undef = fb.undef(tup.clone());
    let seven = fb.iconst(Ty::I32, 7);
    let updated = fb.insert_field(tup.clone(), undef, 0, seven);
    let got = fb.extract_field(Ty::I32, updated, 0);
    // Array aggregate. Ty::Array carries a TyId into `module.types`;
    // we intern `Ty::I32` at index 0 post-build so the reference
    // resolves. Using `TyId::new(0)` directly keeps the IR body
    // independent of the interning step.
    let arr_ty = Ty::Array(TyId::new(0), 4);
    let arr_undef = fb.undef(arr_ty.clone());
    let idx = fb.iconst(Ty::I64, 1);
    let elem = fb.iconst(Ty::I32, 42);
    let arr2 = fb.insert_element(arr_ty.clone(), arr_undef, idx, elem);
    let _got2 = fb.extract_element(Ty::I32, arr2, idx);
    fb.ret(vec![got]);
    fb.build();

    let mut m = mb.build();
    // Intern `i32` at TyId::new(0) so `Ty::Array(TyId::new(0), 4)`
    // above is well-formed when validators walk the module.
    m.types.push(Ty::I32);
    m
}

// ---------- inst_control ----------

/// Covers Br, CondBr, Switch, Return, Unreachable, Call, CallIndirect,
/// Assume, Assert.
pub fn build_inst_control() -> Module {
    let mut mb = ModuleBuilder::new("inst_control");

    // Helper used by Call.
    let helper_ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let helper_id = {
        let mut fb = mb.function("helper", helper_ft);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        fb.ret(vec![x]);
        fb.build()
    };

    // Direct + indirect dispatcher.
    let dispatch_ft = mb.add_func_type(vec![Ty::I32, Ty::Bool, Ty::Ptr], vec![Ty::I32]);
    let mut fb = mb.function("dispatch", dispatch_ft);
    let entry = fb.create_block();
    let then_bb = fb.create_block();
    let else_bb = fb.create_block();
    let switch_bb = fb.create_block();
    let case_a = fb.create_block();
    let case_b = fb.create_block();
    let default_bb = fb.create_block();
    let merge_bb = fb.create_block();
    let unreach_bb = fb.create_block();

    let x = fb.add_block_param(entry, Ty::I32);
    let cond = fb.add_block_param(entry, Ty::Bool);
    let fptr = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    // assume/assert on the bool.
    fb.assume(cond);
    fb.assert(cond);
    fb.condbr(cond, then_bb, vec![], else_bb, vec![]);

    // then: direct call.
    fb.switch_to_block(then_bb);
    let called = fb.call(helper_id, vec![x]);
    fb.br(switch_bb, vec![called]);

    // else: indirect call with a non-default ABI, so the corpus round-trips
    // CallIndirect.calling_conv through every format.
    fb.switch_to_block(else_bb);
    let ind = fb.call_indirect_cc(fptr, helper_ft, vec![x], trust_ir::CallingConv::Swift);
    fb.br(switch_bb, vec![ind]);

    // switch on the incoming value.
    let switch_param = fb.add_block_param(switch_bb, Ty::I32);
    fb.switch_to_block(switch_bb);
    fb.switch(
        switch_param,
        vec![
            SwitchCase {
                value: Constant::Int(0),
                target: case_a,
                args: vec![],
            },
            SwitchCase {
                value: Constant::Int(1),
                target: case_b,
                args: vec![],
            },
        ],
        default_bb,
        vec![],
    );

    fb.switch_to_block(case_a);
    let a_val = fb.iconst(Ty::I32, 10);
    fb.br(merge_bb, vec![a_val]);

    fb.switch_to_block(case_b);
    let b_val = fb.iconst(Ty::I32, 20);
    fb.br(merge_bb, vec![b_val]);

    fb.switch_to_block(default_bb);
    fb.br(unreach_bb, vec![]);

    fb.switch_to_block(unreach_bb);
    fb.unreachable();

    let merge_param = fb.add_block_param(merge_bb, Ty::I32);
    fb.switch_to_block(merge_bb);
    fb.ret(vec![merge_param]);
    fb.build();

    mb.build()
}

// ---------- inst_atomic ----------

/// Covers AtomicLoad, AtomicStore, AtomicRMW (all 10 RMW sub-ops), CmpXchg,
/// Fence — across every `Ordering` variant.
pub fn build_inst_atomic() -> Module {
    let mut mb = ModuleBuilder::new("inst_atomic");
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("atomic_ops", ft);
    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let v = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);

    // One fence per ordering.
    for ord in [
        Ordering::Relaxed,
        Ordering::Acquire,
        Ordering::Release,
        Ordering::AcqRel,
        Ordering::SeqCst,
    ] {
        fb.fence(ord);
    }

    // One AtomicLoad + AtomicStore per ordering.
    for ord in [
        Ordering::Relaxed,
        Ordering::Acquire,
        Ordering::Release,
        Ordering::AcqRel,
        Ordering::SeqCst,
    ] {
        let _ = fb.atomic_load(Ty::I64, ptr, ord);
        fb.atomic_store(Ty::I64, ptr, v, ord);
    }

    // One AtomicRMW per RMW op (ordering varies).
    for op in [
        AtomicRMWOp::Xchg,
        AtomicRMWOp::Add,
        AtomicRMWOp::Sub,
        AtomicRMWOp::And,
        AtomicRMWOp::Or,
        AtomicRMWOp::Xor,
        AtomicRMWOp::Max,
        AtomicRMWOp::Min,
        AtomicRMWOp::UMax,
        AtomicRMWOp::UMin,
    ] {
        let _ = fb.atomic_rmw(op, Ty::I64, ptr, v, Ordering::SeqCst);
    }

    // Compare-exchange with different success/failure orderings.
    let expected = fb.iconst(Ty::I64, 0);
    let desired = fb.iconst(Ty::I64, 1);
    let (_old, _ok) = fb.cmpxchg(
        Ty::I64,
        ptr,
        expected,
        desired,
        Ordering::AcqRel,
        Ordering::Acquire,
    );

    let zero = fb.iconst(Ty::I64, 0);
    fb.ret(vec![zero]);
    fb.build();

    mb.build()
}

// ---------- inst_borrow_arc ----------

/// Covers Borrow, BorrowMut, EndBorrow, Retain, Release, IsUnique.
pub fn build_inst_borrow_arc() -> Module {
    let mut mb = ModuleBuilder::new("inst_borrow_arc");

    // Rust borrow quartet.
    let rust_ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Bool]);
    let mut fb = mb.function("borrow_lifecycle", rust_ft);
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    let b = fb.borrow(p);
    fb.end_borrow(b);
    let bm = fb.borrow_mut(p);
    fb.end_borrow(bm);
    let t = fb.bool_const(true);
    fb.ret(vec![t]);
    fb.build();

    // Swift ARC triple.
    let arc_ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Bool]);
    let mut fb = mb.function("arc_lifecycle", arc_ft);
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    fb.retain(p);
    let uniq = fb.is_unique(p);
    fb.release(p);
    fb.ret(vec![uniq]);
    fb.build();

    // Clean Perceus RC lifecycle (P1 native ARC for Clean): a
    // `heap_alloc clean_heap` cell through the native ARC surface — pins
    // `AllocOrigin::CleanHeap` (binary origin byte 3, v22) on the wire.
    let clean_ft = mb.add_func_type(vec![], vec![Ty::Bool]);
    let mut fb = mb.function("clean_rc_lifecycle", clean_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let cell = fb.heap_alloc(Ty::I64, None, None, AllocOrigin::CleanHeap);
    fb.retain(cell);
    let uniq = fb.is_unique(cell);
    fb.release(cell);
    fb.release(cell);
    fb.ret(vec![uniq]);
    fb.build();

    mb.build()
}

// ---------- inst_binding_frames ----------

/// Covers OpenFrame, BindSlot, LoadSlot, CloseFrame — binding frame
/// quartet used by quantifier lowering (see design doc §R4).
///
/// The canonical text parser now round-trips these instructions, so this
/// fixture asserts all four goldens (binary / text / JSON / MessagePack)
/// like every other fixture.
pub fn build_inst_binding_frames() -> Module {
    let mut mb = ModuleBuilder::new("inst_binding_frames");
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("exists_in_set", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);

    // `\E i \in S : i == x` lowered: open frame, bind `i`, read it, close.
    let frame_def = BindingFrameDef::new(
        BindingFrameId::new(0),
        "exists_i",
        vec![BindingSlot::new("i", Ty::I64)],
    );
    let frame = fb.open_frame(frame_def);
    let i_val = fb.iconst(Ty::I64, 42);
    let _bound = fb.bind_slot(frame, 0, i_val);
    let loaded = fb.load_slot(frame, 0, Ty::I64);
    let sum = fb.add(Ty::I64, loaded, x);
    fb.close_frame(frame);
    fb.ret(vec![sum]);
    fb.build();

    mb.build()
}

// ---------- inst_dialect ----------

/// Covers `Inst::DialectOp` / `DialectInst` with all `AttrValue`
/// variants, exercising opaque round-trip of a dialect payload.
pub fn build_inst_dialect() -> Module {
    let mut mb = ModuleBuilder::new("inst_dialect");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("dialect_roundtrip", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    // Exercise every AttrValue variant.
    let op = DialectInst::new("verif", "bfs_step")
        .with_operand(x)
        .with_result_ty(Ty::I32)
        .with_attr("i64_attr", AttrValue::I64(-7))
        .with_attr("u64_attr", AttrValue::U64(42))
        .with_attr("f64_attr", AttrValue::F64(3.5))
        .with_attr("bool_attr", AttrValue::Bool(true))
        .with_attr("str_attr", AttrValue::Str("hello".into()))
        .with_attr("bytes_attr", AttrValue::Bytes(vec![0xDE, 0xAD, 0xBE, 0xEF]))
        .with_attr("ty_attr", AttrValue::Ty(Ty::I32))
        .with_version(1);
    let results = fb.dialect_op(op);
    fb.ret(results);
    fb.build();
    mb.build()
}

// ---------- proof_annotations ----------

/// Covers every `ProofAnnotation` variant (including every `Divergence`
/// case in `DivergenceClass`), every `ObligationKind`, every
/// `ProofStatus`, and every `ProofEvidence` variant.
pub fn build_proof_annotations() -> Module {
    let mut mb = ModuleBuilder::new("proof_annotations");

    // A single function with every proof annotation attached.
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("carrier", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    // One BinOp with arithmetic-safety proofs attached to the instruction.
    let _sum = fb.binop_proven(
        BinOp::Add,
        Ty::I64,
        x,
        x,
        vec![
            ProofAnnotation::NoOverflow,
            ProofAnnotation::NoWrap,
            ProofAnnotation::Commutative,
            ProofAnnotation::Associative,
        ],
    );
    fb.ret(vec![x]);

    // Every annotation variant attached at the function level.
    fb.add_proof(ProofAnnotation::InBounds);
    fb.add_proof(ProofAnnotation::NotNull);
    fb.add_proof(ProofAnnotation::ValidBorrow);
    fb.add_proof(ProofAnnotation::UniqueBorrow);
    fb.add_proof(ProofAnnotation::SharedBorrow);
    fb.add_proof(ProofAnnotation::ValidDealloc);
    fb.add_proof(ProofAnnotation::NoOverflow);
    fb.add_proof(ProofAnnotation::NoWrap);
    fb.add_proof(ProofAnnotation::DivNonZero);
    fb.add_proof(ProofAnnotation::ShiftInRange);
    fb.add_proof(ProofAnnotation::Wrapping);
    fb.add_proof(ProofAnnotation::BranchWeights(vec![7, 1]));
    fb.add_proof(ProofAnnotation::Pure);
    fb.add_proof(ProofAnnotation::Terminates);
    fb.add_proof(ProofAnnotation::Deterministic);
    fb.add_proof(ProofAnnotation::Associative);
    fb.add_proof(ProofAnnotation::Commutative);
    fb.add_proof(ProofAnnotation::DataRaceFree);
    fb.add_proof(ProofAnnotation::AtomicOrdering(Ordering::Relaxed));
    fb.add_proof(ProofAnnotation::AtomicOrdering(Ordering::Acquire));
    fb.add_proof(ProofAnnotation::AtomicOrdering(Ordering::Release));
    fb.add_proof(ProofAnnotation::AtomicOrdering(Ordering::AcqRel));
    fb.add_proof(ProofAnnotation::AtomicOrdering(Ordering::SeqCst));
    fb.add_proof(ProofAnnotation::BoundedOutput { lo: -1.0, hi: 1.0 });
    fb.add_proof(ProofAnnotation::Monotonic);
    fb.add_proof(ProofAnnotation::NoAlias);
    fb.add_proof(ProofAnnotation::Aligned(16));
    fb.add_proof(ProofAnnotation::NoPanic);
    fb.add_proof(ProofAnnotation::NoUndef);
    fb.add_proof(ProofAnnotation::ReadonlyTable);
    fb.add_proof(ProofAnnotation::AppendOnlyBuffer);
    fb.add_proof(ProofAnnotation::AtomicSetInsert);
    fb.add_proof(ProofAnnotation::ParallelMap);
    fb.add_proof(ProofAnnotation::BoundedLoop(1024));
    fb.add_proof(ProofAnnotation::DivergenceClass(Divergence::Uniform));
    fb.add_proof(ProofAnnotation::DivergenceClass(Divergence::Low));
    fb.add_proof(ProofAnnotation::DivergenceClass(Divergence::High));
    fb.add_proof(ProofAnnotation::Custom(ProofTag::new(42)));
    // fast-3 value facts (finding D): both i128/u128 payloads must round-trip
    // through every format, including text.
    fb.add_proof(ProofAnnotation::ValueRange {
        lo: i128::MIN,
        hi: i128::MAX,
    });
    fb.add_proof(ProofAnnotation::KnownBits {
        zeros: 0x00FF_00FF_00FF_00FF,
        ones: 0xFF00_0000_0000_0000,
    });
    fb.build();

    let mut m = mb.build();

    // `Module::add_function` (via `fb.build()`) synthesized one obligation per
    // claim-kind on the carrier (roadmap §1.1); number the explicit corpus
    // table after them so ids stay unique.
    let synth_base = m
        .proof_obligations
        .iter()
        .map(|o| o.id.index() + 1)
        .max()
        .unwrap_or(0);

    // Every ObligationKind with every ProofStatus, plus every ProofEvidence
    // variant on a matching certificate.
    let kinds = [
        ObligationKind::Precondition,
        ObligationKind::Postcondition,
        ObligationKind::LoopInvariant,
        ObligationKind::TypeInvariant,
        ObligationKind::RefinementType,
        ObligationKind::TranslationValidation,
        ObligationKind::MemorySafety,
        ObligationKind::PanicFreedom,
        ObligationKind::TemporalSafety,
        ObligationKind::Liveness,
    ];
    let statuses = [
        ProofStatus::Pending,
        ProofStatus::Discharged,
        ProofStatus::Failed,
        ProofStatus::Trusted,
    ];
    let mut next = synth_base;
    for kind in kinds {
        for status in statuses {
            m.proof_obligations.push(ProofObligation {
                id: ProofId::new(next),
                kind: kind.clone(),
                status,
                description: format!("{kind:?}/{status:?}"),
                formula: (next == synth_base).then(|| ProofFormula::smtlib2("(> x 0)", "Bool")),
                // B4: scope the first explicit obligation to the carrier
                // function so the `function <id>` text clause is exercised by
                // the corpus (finding C) together with a formula (the
                // formula-and-function-present pairing keeps the positional
                // MessagePack layout exercised end-to-end).
                function: (next == synth_base).then(|| FuncId::new(0)),
                source: None,
                site: None,
            });
            next += 1;
        }
    }
    // fast-1: proof-backed annotation referencing a Discharged obligation (the
    // second explicit entry, `Precondition/Discharged`). Attached post-build so
    // the referenced id can be computed from the synthesized base.
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(synth_base + 1)));
    // Certificates: one per ProofEvidence variant, bound to the first
    // obligation (ProofId 0) to keep things self-contained.
    let certs = [
        ProofEvidence::SmtProof(vec![0x01, 0x02, 0x03]),
        ProofEvidence::LeanProof("exact rfl".into()),
        ProofEvidence::KaniHarness("#[kani::proof] fn check() {}".into()),
        ProofEvidence::GammaCrownBound {
            epsilon: 0.001,
            verified_layers: 5,
        },
        ProofEvidence::TranslationValidation {
            rule_name: "const-fold".into(),
            smt_hash: [0xAB; 32],
        },
        ProofEvidence::Trusted("manual audit by USER".into()),
        ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(0),
            obligation: ProofId::new(0),
        },
    ];
    for (i, ev) in certs.into_iter().enumerate() {
        m.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(i as u32),
            prover: format!("prover_{i}"),
            evidence: ev,
        });
    }
    m
}

// ---------- proof_diagnostics ----------

/// Diagnostics + debug-info surface: a populated `Module::files` table,
/// spanned instructions, and the `Module::obligation_diagnostics` sidecar —
/// one located error with a machine-readable detail, one located warning in a
/// second file, and one location-less note WITH detail. The last shape is the
/// R3 #5 positional-MessagePack hazard (a skipped non-trailing `location`
/// shifted `detail` into its slot), pinned here byte-golden. Instruction
/// spans are text-lossy (the canonical text form renders no per-node span
/// clause — see `normalize_text_lossy_fields`); the binary/JSON/MessagePack
/// goldens pin them exactly.
pub fn build_proof_diagnostics() -> Module {
    let mut m = Module::new("proof_diagnostics");
    let main_rs = m.intern_file("src/main.rs");
    let lib_rs = m.intern_file("src/lib.rs");

    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "checked_incr", ft, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::I32));
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(1),
        })
        .with_result(ValueId::new(1))
        .with_span(SourceSpan {
            file: main_rs,
            line: 11,
            col: 9,
        }),
    );
    entry.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(2))
        .with_span(SourceSpan {
            file: main_rs,
            line: 12,
            col: 5,
        }),
    );
    entry.body.push(
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(2)],
        })
        .with_span(SourceSpan {
            file: lib_rs,
            line: 3,
            col: 1,
        }),
    );
    func.blocks.push(entry);
    m.add_function(func);

    // The obligation the diagnostics annotate: a failed panic-freedom proof,
    // B4-scoped to the carrier function.
    let oid = ProofId::new(0);
    m.proof_obligations.push(
        ProofObligation::new(
            oid,
            ObligationKind::PanicFreedom,
            ProofStatus::Failed,
            "i32 increment must not overflow",
        )
        .with_function(FuncId::new(0))
        .with_source(
            ProofObligationSourceIdentity::new(
                "rust:src/main.rs::checked_incr",
                "assert:i32-add-no-overflow",
            )
            .with_range(ProofObligationSourceRange {
                file: main_rs,
                start_line: 12,
                start_col: 5,
                end_line: 12,
                end_col: 10,
            })
            .with_public(PublicObligationIdentity {
                obligation_id: "vc:checked_incr:overflow:0".to_string(),
                semantic_digest: ProofDigest::sha256_domain(
                    "trust-ir.conformance.public-obligation.v1",
                    b"checked_incr:overflow:0",
                ),
            }),
        ),
    );

    m.obligation_diagnostics.push(
        ObligationDiagnostic::error(oid, "could not prove x + 1 stays in i32 range")
            .with_location(SourceSpan {
                file: main_rs,
                line: 12,
                col: 5,
            })
            .with_detail("counterexample: x = 2147483647"),
    );
    m.obligation_diagnostics.push(ObligationDiagnostic {
        obligation: oid,
        severity: DiagnosticSeverity::Warning,
        message: "caller relies on this increment staying in range".into(),
        location: Some(SourceSpan {
            file: lib_rs,
            line: 3,
            col: 1,
        }),
        detail: None,
    });
    // location: None + detail: Some — the non-trailing-skip regression shape.
    m.obligation_diagnostics.push(ObligationDiagnostic {
        obligation: oid,
        severity: DiagnosticSeverity::Note,
        message: "counterexample model available".into(),
        location: None,
        detail: Some("model: (define-fun x () Int 2147483647)".into()),
    });
    m
}

// ---------- proof lineage sidecar fixtures ----------

pub struct ProofLineageFixture {
    pub manifest: ProofLineageManifest,
    pub obligations: Vec<ProofObligation>,
    pub certificates: Vec<ProofCertificate>,
}

fn digest(seed: u8) -> ProofDigest {
    ProofDigest::sha256([seed; 32])
}

fn trust_ir_digest(domain: &str, bytes: &[u8]) -> ProofDigest {
    ProofDigest::sha256_domain(domain, bytes)
}

fn lineage_obligation(
    id: u32,
    kind: ObligationKind,
    status: ProofStatus,
    description: &str,
) -> ProofObligation {
    ProofObligation::new(ProofId::new(id), kind, status, description)
        .with_formula(ProofFormula::smtlib2(format!("obligation_{id}"), "Bool"))
}

fn lineage_certificate(id: u32, prover: &str, evidence: ProofEvidence) -> ProofCertificate {
    ProofCertificate {
        obligation: ProofId::new(id),
        prover: prover.to_string(),
        evidence,
    }
}

/// Single-stage Trust proof handoff: one verifier run discharges one
/// obligation and records a replay identity.
pub fn build_proof_lineage_single_stage() -> ProofLineageFixture {
    let obligations = vec![lineage_obligation(
        0,
        ObligationKind::MemorySafety,
        ProofStatus::Discharged,
        "Trust borrow proof implies TrustIr memory safety",
    )];
    let certificates = vec![lineage_certificate(
        0,
        "trust-kernel",
        ProofEvidence::LeanProof("exact Trust.MemorySafety.borrow_sound".into()),
    )];

    let mut node = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "trust-proof-export",
            "Trust",
            "2026.04",
        ),
        digest(0x11),
        digest(0x12),
    );
    node.obligations.push(ProofId::new(0));
    node.certificates.push(certificates[0].lineage_ref());
    node.replay = Some(
        ProofReplayIdentity::new(
            "trust-stage2",
            "trust verify --emit-trust_ir-proof src/lib.trust",
        )
        .with_transcript_digest(trust_ir_digest("trust.transcript", b"single-stage-ok")),
    );

    ProofLineageFixture {
        manifest: ProofLineageManifest {
            schema_version: ProofLineageManifest::SCHEMA_VERSION,
            nodes: vec![node],
            roots: vec![ProofLineageId::new(0)],
        },
        obligations,
        certificates,
    }
}

/// Multi-stage Trust -> TrustIr -> ay -> TrustCg composition fixture. The
/// source/target digests chain across dependencies so `validate()` rejects
/// any stale intermediate artifact.
pub fn build_proof_lineage_multi_stage() -> ProofLineageFixture {
    let obligations = vec![
        lineage_obligation(
            0,
            ObligationKind::Precondition,
            ProofStatus::Discharged,
            "Trust frontend precondition exported to TrustIr",
        ),
        lineage_obligation(
            1,
            ObligationKind::TranslationValidation,
            ProofStatus::Discharged,
            "TrustIr lowering preserves the Trust proof term",
        ),
        lineage_obligation(
            2,
            ObligationKind::PanicFreedom,
            ProofStatus::Trusted,
            "TrustCg backend panic-freedom audited for this kernel",
        ),
    ];
    let certificates = vec![
        lineage_certificate(
            0,
            "trust-kernel",
            ProofEvidence::LeanProof("exact Trust.Precondition.export_sound".into()),
        ),
        lineage_certificate(
            1,
            "trust-ir-ay",
            ProofEvidence::SmtProof(vec![0xA5, 0x5A, 0x01]),
        ),
        lineage_certificate(
            2,
            "trust_cg-audit",
            ProofEvidence::Trusted("manual audit by USER for Trust self-host seed".into()),
        ),
    ];

    let mut frontend = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "trust-proof-export",
            "Trust",
            "2026.04",
        ),
        digest(0x21),
        digest(0x22),
    );
    frontend.obligations.push(ProofId::new(0));
    frontend.certificates.push(certificates[0].lineage_ref());

    let mut lowering = ProofLineageNode::new(
        ProofLineageId::new(1),
        ProofTransform::new(
            ProofTransformStage::TrustIrLowering,
            "trust-to-trust_ir",
            "TrustIr",
            "0.1.0",
        ),
        digest(0x22),
        digest(0x23),
    );
    lowering.obligations.push(ProofId::new(1));
    lowering.certificates.push(certificates[1].lineage_ref());
    lowering.depends_on.push(ProofLineageId::new(0));
    lowering.replay = Some(
        ProofReplayIdentity::new("trust_ir-conformance", "cargo test -p trust_ir-conformance")
            .with_transcript_digest(trust_ir_digest(
                "trust_ir.transcript",
                b"multi-stage-lowering",
            )),
    );

    let mut backend = ProofLineageNode::new(
        ProofLineageId::new(2),
        ProofTransform::new(
            ProofTransformStage::Backend,
            "trust_cg-codegen",
            "TrustCg",
            "0.1.0",
        ),
        digest(0x23),
        digest(0x24),
    );
    backend.obligations.push(ProofId::new(2));
    backend.certificates.push(certificates[2].lineage_ref());
    backend.depends_on.push(ProofLineageId::new(1));

    ProofLineageFixture {
        manifest: ProofLineageManifest {
            schema_version: ProofLineageManifest::SCHEMA_VERSION,
            nodes: vec![frontend, lowering, backend],
            roots: vec![ProofLineageId::new(2)],
        },
        obligations,
        certificates,
    }
}

// ---------- native verification bundle fixtures ----------

pub struct NativeBundleFixture {
    pub bundle: NativeVerificationBundle,
}

/// tRust-produced native verification bundle. This pins the typed request
/// boundary used by TrustVc, TrustMc, and TrustWp without introducing a stringly
/// adapter registry or changing the module `.tmbc` format.
pub fn build_trust_native_request_bundle() -> NativeBundleFixture {
    let source_digest = digest(0x31);

    let mut mb = ModuleBuilder::new("trust_native_request_bundle");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    {
        let mut fb = mb.function("checked_add", ft);
        let entry = fb.create_block();
        let lhs = fb.add_block_param(entry, Ty::I32);
        let rhs = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let sum = fb.add(Ty::I32, lhs, rhs);
        fb.ret(vec![sum]);
        fb.build();
    }
    let mut module = mb.build();
    module.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let source_file = module.intern_file("crates/trust/tests/checked_add.rs");
    let u8_ty = module.add_type(Ty::U8);
    let u64_ty = module.add_type(Ty::U64);
    let pair_struct = module.add_struct(StructDef {
        id: StructId::new(0),
        name: "PairU64".into(),
        fields: vec![
            FieldDef {
                name: "lhs".into(),
                ty: Ty::U64,
                offset: Some(0),
            },
            FieldDef {
                name: "rhs".into(),
                ty: Ty::U64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),

        repr: Default::default(),
    });
    let option_ptr_enum = module.add_enum(EnumDef {
        id: EnumId::new(0),
        name: "OptionConstU8Ptr".into(),
        variants: vec![
            EnumVariant {
                name: "None".into(),
                fields: vec![],
                field_names: Vec::new(),
            },
            EnumVariant {
                name: "Some".into(),
                fields: vec![Ty::PtrConst(Box::new(Ty::U8))],
                field_names: Vec::new(),
            },
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: None,
    });
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Certified,
            "kernel-replayed native TrustVc conformance postcondition",
        )
        .with_formula(ProofFormula::smtlib2("(>= 5 0)", "Bool"))
        .with_source(
            ProofObligationSourceIdentity::new(
                "rust:crates/trust/tests/checked_add.rs::checked_add",
                "rust-assertion:1",
            )
            .with_range(ProofObligationSourceRange {
                file: source_file,
                start_line: 24,
                start_col: 9,
                end_line: 24,
                end_col: 10,
            })
            .with_public(PublicObligationIdentity {
                obligation_id: "vc:checked_add:postcondition:0".to_string(),
                semantic_digest: ProofDigest::sha256_domain(
                    "trust-ir.conformance.public-obligation.v1",
                    b"checked_add:postcondition:0",
                ),
            }),
        ),
    );
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(1),
            ObligationKind::TranslationValidation,
            ProofStatus::Pending,
            "tRust MIR to TrustIr lowering preserves checked_add",
        )
        .with_formula(ProofFormula::smtlib2(
            "(= (rust_mir.checked_add lhs rhs) (trust_ir.checked_add lhs rhs))",
            "Bool",
        ))
        .with_source(
            ProofObligationSourceIdentity::new(
                "rust:crates/trust/tests/checked_add.rs::checked_add",
                "rust-assertion:2",
            )
            .with_range(ProofObligationSourceRange {
                file: source_file,
                start_line: 28,
                start_col: 13,
                end_line: 28,
                end_col: 14,
            })
            .with_public(PublicObligationIdentity {
                obligation_id: "vc:checked_add:cast:1".to_string(),
                semantic_digest: ProofDigest::sha256_domain(
                    "trust-ir.conformance.public-obligation.v1",
                    b"checked_add:cast:1",
                ),
            }),
        ),
    );
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(2),
            ObligationKind::Precondition,
            ProofStatus::Pending,
            "checked_add arguments satisfy verifier preconditions",
        )
        .with_formula(ProofFormula::smtlib2("(and (i32 lhs) (i32 rhs))", "Bool"))
        .with_source(
            ProofObligationSourceIdentity::new(
                "rust:crates/trust/tests/checked_add.rs::checked_add",
                "rust-assertion:0",
            )
            .with_range(ProofObligationSourceRange {
                file: source_file,
                start_line: 31,
                start_col: 5,
                end_line: 31,
                end_col: 6,
            })
            .with_public(PublicObligationIdentity {
                obligation_id: "vc:checked_add:assert:2".to_string(),
                semantic_digest: ProofDigest::sha256_domain(
                    "trust-ir.conformance.public-obligation.v1",
                    b"checked_add:assert:2",
                ),
            }),
        ),
    );

    // This is an admission-valid corpus, not merely an authority-shaped wire
    // fixture. Mint a real obligation-bound CleanCic term and let bundle
    // validation replay it in-process; an opaque LeanProof string would make a
    // `Certified`/`Discharged` label non-authoritative by design.
    let trust_vc_cert = trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate(
        &module.proof_obligations[0],
        "trust_vc-clean-kernel",
    )
    .expect("ground true postcondition must produce a kernel-replayable certificate");
    module.proof_certificates.push(trust_vc_cert.clone());
    let trust_ir_module_digest = module.stable_digest();

    let mut frontend = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "rustc-mir-to-trust_ir",
            "tRust",
            "native-request-schema-v1",
        ),
        source_digest,
        trust_ir_module_digest,
    );
    frontend.obligations.push(ProofId::new(0));
    frontend.obligations.push(ProofId::new(1));
    frontend.obligations.push(ProofId::new(2));
    frontend.certificates.push(trust_vc_cert.lineage_ref());
    frontend.replay = Some(
        ProofReplayIdentity::new("trust-full-verify", "trust verify --emit-trust_ir-bundle")
            .with_transcript_digest(trust_ir_digest("trust.native.transcript", b"bundle-ok")),
    );

    let lineage = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        nodes: vec![frontend],
        roots: vec![ProofLineageId::new(0)],
    };

    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TRust,
        NativeAdapterInput::RustMir {
            body_digest: source_digest,
        },
        trust_ir_module_digest,
        module,
        lineage,
    );
    bundle.provenance = NativeBundleProvenance {
        producer_version: "trust-native-bundle@1".into(),
        source_language: NativeSourceLanguage::Rust,
        source_artifact: Some("crates/trust/tests/checked_add.rs".into()),
        source_digest: Some(source_digest),
        toolchain: vec![
            NativeToolIdentity::new("rustc")
                .with_version("1.92.0-nightly")
                .with_revision("rustc-2026-04-29"),
            NativeToolIdentity::new("tRust")
                .with_version("native-request-schema-v1")
                .with_revision("eac751770e436657fa6ee3cef0d3e3c0f37bb76c"),
        ],
    };
    bundle.diagnostics = NativeDiagnosticsPolicy {
        level: NativeDiagnosticLevel::Trace,
        emit_proof_traces: true,
        max_counterexamples: 2,
        ..NativeDiagnosticsPolicy::default()
    };
    bundle.compiler_facts = NativeCompilerFacts {
        adt_layouts: vec![
            NativeAdtLayoutFact {
                id: NativeCompilerFactId::new(0),
                ty: Ty::Struct(pair_struct),
                layout: TyLayoutShape {
                    size_bits: 128,
                    align_bits: Some(64),
                    kind: TyLayoutKind::Struct {
                        id: pair_struct,
                        fields: vec![
                            FieldOffsetShape {
                                field: 0,
                                name: "lhs".into(),
                                ty_shape: TyShape::Int {
                                    signed: false,
                                    bits: 64,
                                },
                                offset_bits: Some(0),
                            },
                            FieldOffsetShape {
                                field: 1,
                                name: "rhs".into(),
                                ty_shape: TyShape::Int {
                                    signed: false,
                                    bits: 64,
                                },
                                offset_bits: Some(64),
                            },
                        ],
                    },
                },
                enum_layout: None,
            },
            NativeAdtLayoutFact {
                id: NativeCompilerFactId::new(1),
                ty: Ty::Enum(option_ptr_enum),
                layout: TyLayoutShape {
                    size_bits: 64,
                    align_bits: Some(64),
                    kind: TyLayoutKind::Enum {
                        id: option_ptr_enum,
                        variants: 2,
                    },
                },
                enum_layout: Some(NativeEnumLayoutFact {
                    enum_id: option_ptr_enum,
                    tag_encoding: NativeEnumTagEncoding::Niche,
                    tag_bits: None,
                    discriminant_offset_bits: None,
                    niche: Some(NativeEnumNicheFact {
                        variant_index: 0,
                        field: None,
                        valid_range: NativeIntegerRange { start: 1, end: 255 },
                    }),
                    variants: vec![
                        NativeEnumVariantLayoutFact {
                            variant_index: 0,
                            name: "None".into(),
                            discriminant: Some(0),
                            fields: vec![],
                            size_bits: 0,
                            align_bits: Some(8),
                        },
                        NativeEnumVariantLayoutFact {
                            variant_index: 1,
                            name: "Some".into(),
                            discriminant: Some(1),
                            fields: vec![FieldOffsetShape {
                                field: 0,
                                name: "ptr".into(),
                                ty_shape: TyShape::PtrConst,
                                offset_bits: Some(0),
                            }],
                            size_bits: 64,
                            align_bits: Some(64),
                        },
                    ],
                }),
            },
        ],
        fat_pointers: vec![
            NativeFatPointerFact {
                id: NativeCompilerFactId::new(2),
                ty: Ty::FatPtr(FatPtrKind::Slice(u8_ty)),
                layout: PointerLayoutShape::fat(64, PointerMetadataShape::SliceLen { elem: u8_ty }),
            },
            NativeFatPointerFact {
                id: NativeCompilerFactId::new(3),
                ty: Ty::FatPtr(FatPtrKind::Str),
                layout: PointerLayoutShape::fat(64, PointerMetadataShape::StrLen),
            },
        ],
        casts: vec![NativeCastFact {
            id: NativeCompilerFactId::new(4),
            function: FuncId::new(0),
            result: None,
            op: CastOp::Transmute,
            source_ty: Ty::Struct(pair_struct),
            target_ty: Ty::Array(u64_ty, 2),
            evidence: CastLayoutEvidence::SameSize {
                size_bits: 128,
                src_align_bits: Some(64),
                dst_align_bits: Some(64),
            },
            span: Some(trust_ir::SourceSpan {
                file: 0,
                line: 28,
                col: 13,
            }),
            obligations: vec![ProofId::new(1)],
        }],
        monomorphizations: vec![NativeMonomorphizationFact {
            id: NativeMonomorphizationId::new(0),
            source_item: "crates/trust/tests/checked_add.rs::checked_add".into(),
            symbol: "_RNvCs_trust_checked_addINtB4_7PairU64ELi2_E".into(),
            generic_args: vec![
                NativeGenericArg::Ty(Ty::Struct(pair_struct)),
                NativeGenericArg::Const {
                    ty: Ty::U64,
                    value: Constant::Int(2),
                },
            ],
            function: Some(FuncId::new(0)),
            stable_digest: trust_ir_digest("trust.monomorphization", b"checked_add::<PairU64, 2>"),
        }],
        obligation_sources: vec![
            NativeObligationSource {
                obligation: ProofId::new(0),
                public_obligation_id: "vc:checked_add:postcondition:0".to_string(),
                function: Some(FuncId::new(0)),
                span: Some(trust_ir::SourceSpan {
                    file: 0,
                    line: 24,
                    col: 9,
                }),
                assertion_id: Some(NativeAssertionId::new(1)),
                cause: NativeObligationCause::Postcondition,
                monomorphization: Some(NativeMonomorphizationId::new(0)),
                facts: vec![
                    NativeCompilerFactRef::AdtLayout(NativeCompilerFactId::new(0)),
                    NativeCompilerFactRef::FatPointer(NativeCompilerFactId::new(2)),
                    NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId::new(0)),
                ],
            },
            NativeObligationSource {
                obligation: ProofId::new(1),
                public_obligation_id: "vc:checked_add:cast:1".to_string(),
                function: Some(FuncId::new(0)),
                span: Some(trust_ir::SourceSpan {
                    file: 0,
                    line: 28,
                    col: 13,
                }),
                assertion_id: Some(NativeAssertionId::new(2)),
                cause: NativeObligationCause::CastCheck,
                monomorphization: Some(NativeMonomorphizationId::new(0)),
                facts: vec![
                    NativeCompilerFactRef::AdtLayout(NativeCompilerFactId::new(0)),
                    NativeCompilerFactRef::AdtLayout(NativeCompilerFactId::new(1)),
                    NativeCompilerFactRef::Cast(NativeCompilerFactId::new(4)),
                    NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId::new(0)),
                ],
            },
            NativeObligationSource {
                obligation: ProofId::new(2),
                public_obligation_id: "vc:checked_add:assert:2".to_string(),
                function: Some(FuncId::new(0)),
                span: Some(trust_ir::SourceSpan {
                    file: 0,
                    line: 31,
                    col: 5,
                }),
                assertion_id: Some(NativeAssertionId::new(0)),
                cause: NativeObligationCause::Assert,
                monomorphization: Some(NativeMonomorphizationId::new(0)),
                facts: vec![
                    NativeCompilerFactRef::FatPointer(NativeCompilerFactId::new(2)),
                    NativeCompilerFactRef::FatPointer(NativeCompilerFactId::new(3)),
                    NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId::new(0)),
                ],
            },
        ],
        ..NativeCompilerFacts::default()
    };
    bundle
        .requests
        .push(NativeVerificationRequest::TrustVc(TrustVcNativeRequest {
            id: NativeRequestId::new(0),
            mode: TrustVcVerificationMode::ImportProofCertificates,
            obligations: vec![ProofId::new(0)],
            certificates: vec![trust_vc_cert.lineage_ref()],
            lineage_roots: vec![ProofLineageId::new(0)],
            options: TrustVcRequestOptions {
                memory_semantics: TrustVcMemorySemantics::StackedBorrows,
                trusted_evidence: TrustVcTrustedEvidencePolicy::Reject,
                ..TrustVcRequestOptions::default()
            },
            diagnostics: NativeDiagnosticsPolicy {
                emit_proof_traces: true,
                ..NativeDiagnosticsPolicy::default()
            },
            provenance: NativeRequestProvenance::new(
                NativeVerifierSuite::TrustVc,
                NativeToolIdentity::new("trust_vc")
                    .with_version("semantics-v1")
                    .with_revision("trust_vc-2026-04-29"),
            )
            .with_solver(
                NativeToolIdentity::new("lean4")
                    .with_version("4.18.0")
                    .with_revision("trust_vc-proof-kernel"),
            )
            .with_replay(
                ProofReplayIdentity::new(
                    "trust_vc",
                    "trust_vc import --native-bundle native_request_trust_bundle",
                )
                .with_transcript_digest(trust_ir_digest(
                    "trust_vc.native.transcript",
                    b"native-request-trust-bundle-trust_vc",
                )),
            ),
            // MUST stay None. A Some(_) here appends 4 bytes to the request
            // digest and MOVES both committed goldens plus the evidence
            // `request_digest` inside them — destroying the byte-identity
            // check that is the whole proof this change is digest-neutral.
            function: None,
        }));
    bundle
        .requests
        .push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
        id: NativeRequestId::new(1),
        mode: TrustMcVerificationMode::Chc,
        function: FuncId::new(0),
        obligations: vec![ProofId::new(1), ProofId::new(2)],
        lineage_roots: vec![ProofLineageId::new(0)],
        options: TrustMcRequestOptions {
            memory_model: TrustMcMemoryModel::StackedBorrows,
            arithmetic_model: TrustMcArithmeticModel::RustChecked,
            chc: TrustMcChcOptions {
                engine: TrustMcChcEngine::Spacer,
                invariant_source: TrustMcInvariantSource::TrustIrProofObligations,
                pdr: TrustMcPdrOptions {
                    enabled: true,
                    max_frames: Some(16),
                    generalization: TrustMcPdrGeneralization::Cubes,
                },
                emit_horn_clauses: true,
            },
            slicing: TrustMcSlicingMode::ObligationBackwardSlice,
            ..TrustMcRequestOptions::default()
        },
        diagnostics: NativeDiagnosticsPolicy {
            emit_counterexamples: true,
            emit_unsat_cores: true,
            max_counterexamples: 2,
            ..NativeDiagnosticsPolicy::default()
        },
        provenance: NativeRequestProvenance::new(
            NativeVerifierSuite::TrustMc,
            NativeToolIdentity::new("trust_mc")
                .with_version("chc-v1")
                .with_revision("trust_mc-2026-04-29"),
        )
        .with_solver(
            NativeToolIdentity::new("z3-spacer")
                .with_version("4.13.0")
                .with_revision("spacer"),
        )
        .with_replay(
            ProofReplayIdentity::new(
                "trust_mc",
                "trust_mc chc --native-bundle native_request_trust_bundle --function checked_add",
            )
            .with_transcript_digest(trust_ir_digest(
                "trust_mc.native.transcript",
                b"native-request-trust-bundle-trust_mc-chc",
            )),
        ),
    }));
    bundle
        .requests
        .push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
        id: NativeRequestId::new(2),
        mode: TrustMcVerificationMode::Pdr,
        function: FuncId::new(0),
        obligations: vec![ProofId::new(1), ProofId::new(2)],
        lineage_roots: vec![ProofLineageId::new(0)],
        options: TrustMcRequestOptions {
            memory_model: TrustMcMemoryModel::StackedBorrows,
            arithmetic_model: TrustMcArithmeticModel::RustChecked,
            chc: TrustMcChcOptions {
                engine: TrustMcChcEngine::NativePdr,
                invariant_source: TrustMcInvariantSource::TrustIrProofObligations,
                pdr: TrustMcPdrOptions {
                    enabled: true,
                    max_frames: Some(32),
                    generalization: TrustMcPdrGeneralization::Interpolants,
                },
                emit_horn_clauses: true,
            },
            slicing: TrustMcSlicingMode::ConstraintIndependence,
            ..TrustMcRequestOptions::default()
        },
        diagnostics: NativeDiagnosticsPolicy {
            emit_counterexamples: true,
            emit_unsat_cores: true,
            max_counterexamples: 2,
            ..NativeDiagnosticsPolicy::default()
        },
        provenance: NativeRequestProvenance::new(
            NativeVerifierSuite::TrustMc,
            NativeToolIdentity::new("trust_mc")
                .with_version("chc-pdr-v1")
                .with_revision("trust_mc-2026-04-29"),
        )
        .with_solver(NativeToolIdentity::new("trust_mc-native-pdr").with_version("pdr-v1"))
        .with_replay(
            ProofReplayIdentity::new(
                "trust_mc",
                "trust_mc pdr --native-bundle native_request_trust_bundle --function checked_add",
            )
            .with_transcript_digest(trust_ir_digest(
                "trust_mc.native.transcript",
                b"native-request-trust-bundle-trust_mc-pdr",
            )),
        ),
    }));
    bundle
        .requests
        .push(NativeVerificationRequest::TrustWp(TrustWpNativeRequest {
        id: NativeRequestId::new(3),
        mode: TrustWpVerificationMode::WeakestPrecondition,
        function: FuncId::new(0),
        obligations: vec![ProofId::new(1), ProofId::new(2)],
        lineage_roots: vec![ProofLineageId::new(0)],
        options: TrustWpRequestOptions {
            heap_model: TrustWpHeapModel::RustBorrowGraph,
            loop_strategy: TrustWpLoopStrategy::RequireInvariants,
            frame_policy: TrustWpFramePolicy::BorrowRegions,
            panic_semantics: TrustWpPanicSemantics::PanicFreeRequired,
            max_abduced_preconditions: 8,
            emit_verification_conditions: true,
        },
        diagnostics: NativeDiagnosticsPolicy {
            emit_proof_traces: true,
            ..NativeDiagnosticsPolicy::default()
        },
        provenance: NativeRequestProvenance::new(
            NativeVerifierSuite::TrustWp,
            NativeToolIdentity::new("trust_wp")
                .with_version("wp-v1")
                .with_revision("trust_wp-2026-04-29"),
        )
        .with_solver(NativeToolIdentity::new("trust_wp-vcgen").with_version("wp-v1"))
        .with_replay(
            ProofReplayIdentity::new(
                "trust_wp",
                "trust_wp wp --native-bundle native_request_trust_bundle --function checked_add",
            )
            .with_transcript_digest(trust_ir_digest(
                "trust_wp.native.transcript",
                b"native-request-trust-bundle-trust_wp-wp",
            )),
        ),
    }));
    bundle
        .requests
        .push(NativeVerificationRequest::TrustWp(TrustWpNativeRequest {
        id: NativeRequestId::new(4),
        mode: TrustWpVerificationMode::StrongestPostcondition,
        function: FuncId::new(0),
        obligations: vec![ProofId::new(1), ProofId::new(2)],
        lineage_roots: vec![ProofLineageId::new(0)],
        options: TrustWpRequestOptions {
            heap_model: TrustWpHeapModel::TrustIrMemory,
            loop_strategy: TrustWpLoopStrategy::RequireInvariants,
            frame_policy: TrustWpFramePolicy::Minimal,
            panic_semantics: TrustWpPanicSemantics::PanicFreeRequired,
            max_abduced_preconditions: 8,
            emit_verification_conditions: true,
        },
        diagnostics: NativeDiagnosticsPolicy {
            emit_proof_traces: true,
            ..NativeDiagnosticsPolicy::default()
        },
        provenance: NativeRequestProvenance::new(
            NativeVerifierSuite::TrustWp,
            NativeToolIdentity::new("trust_wp")
                .with_version("sp-v1")
                .with_revision("trust_wp-2026-04-29"),
        )
        .with_solver(NativeToolIdentity::new("trust_wp-vcgen").with_version("sp-v1"))
        .with_replay(
            ProofReplayIdentity::new(
                "trust_wp",
                "trust_wp sp --native-bundle native_request_trust_bundle --function checked_add",
            )
            .with_transcript_digest(trust_ir_digest(
                "trust_wp.native.transcript",
                b"native-request-trust-bundle-trust_wp-sp",
            )),
        )
        .with_replay_context(
            NativeReplayContext::default()
                .with_atom(
                    NativeReplayAtom::assumption(
                        NativeReplayAtomId::new(0),
                        ProofFormula::smtlib2("(i32 lhs)", "Bool"),
                    )
                    .with_obligation(ProofId::new(2))
                    .with_span(trust_ir::SourceSpan {
                        file: 0,
                        line: 31,
                        col: 5,
                    }),
                )
                .with_atom(
                    NativeReplayAtom::assumption(
                        NativeReplayAtomId::new(1),
                        ProofFormula::smtlib2("(i32 rhs)", "Bool"),
                    )
                    .with_obligation(ProofId::new(2))
                    .with_span(trust_ir::SourceSpan {
                        file: 0,
                        line: 31,
                        col: 5,
                    }),
                )
                .with_atom(
                    NativeReplayAtom::assertion(
                        NativeReplayAtomId::new(2),
                        ProofFormula::smtlib2("(and (i32 lhs) (i32 rhs))", "Bool"),
                    )
                    .with_obligation(ProofId::new(2))
                    .with_assertion_id(NativeAssertionId::new(0))
                    .with_span(trust_ir::SourceSpan {
                        file: 0,
                        line: 31,
                        col: 5,
                    }),
                ),
        ),
    }));
    bundle
        .requests
        .push(NativeVerificationRequest::TrustWp(TrustWpNativeRequest {
        id: NativeRequestId::new(5),
        mode: TrustWpVerificationMode::Abduction,
        function: FuncId::new(0),
        obligations: vec![ProofId::new(1), ProofId::new(2)],
        lineage_roots: vec![ProofLineageId::new(0)],
        options: TrustWpRequestOptions {
            heap_model: TrustWpHeapModel::SeparationLogic,
            loop_strategy: TrustWpLoopStrategy::InferInvariants,
            frame_policy: TrustWpFramePolicy::BorrowRegions,
            panic_semantics: TrustWpPanicSemantics::EncodePanicsAsErrors,
            max_abduced_preconditions: 4,
            emit_verification_conditions: true,
        },
        diagnostics: NativeDiagnosticsPolicy {
            emit_proof_traces: true,
            ..NativeDiagnosticsPolicy::default()
        },
        provenance: NativeRequestProvenance::new(
            NativeVerifierSuite::TrustWp,
            NativeToolIdentity::new("trust_wp")
                .with_version("abduction-v1")
                .with_revision("trust_wp-2026-04-29"),
        )
        .with_solver(NativeToolIdentity::new("trust_wp-vcgen").with_version("abduction-v1"))
        .with_replay(
            ProofReplayIdentity::new(
                "trust_wp",
                "trust_wp abduce --native-bundle native_request_trust_bundle --function checked_add",
            )
            .with_transcript_digest(trust_ir_digest(
                "trust_wp.native.transcript",
                b"native-request-trust-bundle-trust_wp-abduction",
            )),
        ),
    }));

    bundle.evidence_bundles = native_request_evidence_bundles(&bundle);

    NativeBundleFixture { bundle }
}

fn native_request_evidence_bundles(bundle: &NativeVerificationBundle) -> Vec<NativeEvidenceBundle> {
    bundle
        .requests
        .iter()
        .map(|request| match request {
            NativeVerificationRequest::TrustVc(request) => {
                NativeEvidenceBundle::TrustVc(TrustVcNativeEvidenceBundle {
                    request: request.id,
                    mode: request.mode,
                    obligations: request.obligations.clone(),
                    verifier: request.provenance.expected_verifier.clone(),
                    solvers: request.provenance.solvers.clone(),
                    replay: request.provenance.replay.clone().expect("TrustVc replay"),
                    trust_ir_module_digest: bundle.trust_ir_module_digest,
                    request_digest: bundle
                        .requests
                        .iter()
                        .find(|candidate| candidate.id() == request.id)
                        .expect("TrustVc request")
                        .stable_digest(),
                    artifacts: vec![NativeEvidenceArtifact::new(
                        "trust_vc-place-projection.import.lean",
                        NativeEvidenceArtifactKind::TrustVcCertificateImport,
                        trust_ir_digest(
                            "trust_vc.native.artifact",
                            b"native-request-trust-bundle-trust_vc-import",
                        ),
                    )],
                })
            }
            NativeVerificationRequest::TrustMc(request) => {
                let artifacts = match request.mode {
                    TrustMcVerificationMode::Chc => vec![NativeEvidenceArtifact::new(
                        "trust_mc-checked-add.chc.smt2",
                        NativeEvidenceArtifactKind::TrustMcHornClauses,
                        trust_ir_digest(
                            "trust_mc.native.artifact",
                            b"native-request-trust-bundle-trust_mc-chc-horn-clauses",
                        ),
                    )],
                    TrustMcVerificationMode::Pdr => vec![
                        NativeEvidenceArtifact::new(
                            "trust_mc-checked-add.pdr.smt2",
                            NativeEvidenceArtifactKind::TrustMcHornClauses,
                            trust_ir_digest(
                                "trust_mc.native.artifact",
                                b"native-request-trust-bundle-trust_mc-pdr-horn-clauses",
                            ),
                        ),
                        NativeEvidenceArtifact::new(
                            "trust_mc-checked-add.pdr.trace",
                            NativeEvidenceArtifactKind::TrustMcPdrTrace,
                            trust_ir_digest(
                                "trust_mc.native.artifact",
                                b"native-request-trust-bundle-trust_mc-pdr-trace",
                            ),
                        ),
                    ],
                    TrustMcVerificationMode::BoundedModelCheck => {
                        vec![NativeEvidenceArtifact::new(
                            "trust_mc-checked-add.bmc.model",
                            NativeEvidenceArtifactKind::TrustMcModel,
                            trust_ir_digest(
                                "trust_mc.native.artifact",
                                b"native-request-trust-bundle-trust_mc-bmc-model",
                            ),
                        )]
                    }
                };
                NativeEvidenceBundle::TrustMc(TrustMcNativeEvidenceBundle {
                    request: request.id,
                    mode: request.mode,
                    obligations: request.obligations.clone(),
                    verifier: request.provenance.expected_verifier.clone(),
                    solvers: request.provenance.solvers.clone(),
                    replay: request.provenance.replay.clone().expect("TrustMc replay"),
                    trust_ir_module_digest: bundle.trust_ir_module_digest,
                    request_digest: bundle
                        .requests
                        .iter()
                        .find(|candidate| candidate.id() == request.id)
                        .expect("TrustMc request")
                        .stable_digest(),
                    artifacts,
                })
            }
            NativeVerificationRequest::TrustWp(request) => {
                let artifacts = match request.mode {
                    TrustWpVerificationMode::WeakestPrecondition => {
                        vec![NativeEvidenceArtifact::new(
                            "trust_wp-checked-add.wp.vc",
                            NativeEvidenceArtifactKind::TrustWpVerificationCondition,
                            trust_ir_digest(
                                "trust_wp.native.artifact",
                                b"native-request-trust-bundle-trust_wp-wp-vc",
                            ),
                        )]
                    }
                    TrustWpVerificationMode::StrongestPostcondition => vec![
                        NativeEvidenceArtifact::new(
                            "trust_wp-checked-add.sp.vc",
                            NativeEvidenceArtifactKind::TrustWpVerificationCondition,
                            trust_ir_digest(
                                "trust_wp.native.artifact",
                                b"native-request-trust-bundle-trust_wp-sp-vc",
                            ),
                        ),
                        NativeEvidenceArtifact::new(
                            "trust_wp-checked-add.sp.replay",
                            NativeEvidenceArtifactKind::TrustWpReplayTrace,
                            trust_ir_digest(
                                "trust_wp.native.artifact",
                                b"native-request-trust-bundle-trust_wp-sp-replay",
                            ),
                        ),
                    ],
                    TrustWpVerificationMode::Abduction => vec![
                        NativeEvidenceArtifact::new(
                            "trust_wp-checked-add.abduction.vc",
                            NativeEvidenceArtifactKind::TrustWpVerificationCondition,
                            trust_ir_digest(
                                "trust_wp.native.artifact",
                                b"native-request-trust-bundle-trust_wp-abduction-vc",
                            ),
                        ),
                        NativeEvidenceArtifact::new(
                            "trust_wp-checked-add.abduced-preconditions",
                            NativeEvidenceArtifactKind::TrustWpAbducedPrecondition,
                            trust_ir_digest(
                                "trust_wp.native.artifact",
                                b"native-request-trust-bundle-trust_wp-abduced-preconditions",
                            ),
                        ),
                    ],
                };
                NativeEvidenceBundle::TrustWp(TrustWpNativeEvidenceBundle {
                    request: request.id,
                    mode: request.mode,
                    obligations: request.obligations.clone(),
                    verifier: request.provenance.expected_verifier.clone(),
                    solvers: request.provenance.solvers.clone(),
                    replay: request.provenance.replay.clone().expect("TrustWp replay"),
                    trust_ir_module_digest: bundle.trust_ir_module_digest,
                    request_digest: bundle
                        .requests
                        .iter()
                        .find(|candidate| candidate.id() == request.id)
                        .expect("TrustWp request")
                        .stable_digest(),
                    artifacts,
                })
            }
        })
        .collect()
}

// ---------- func_param_abi ----------

/// ABI-pinning parameter attributes (abi-pinning.md): the v20 `byval`/`sret`
/// aggregate-passing classification, alongside the fast-2 hint attributes they
/// share `ParamAttrs` with. A `repr(C)` struct crosses the call edge through
/// memory: param 0 is the caller-allocated `sret` return slot, param 1 the
/// caller-made `byval` argument copy. Pins the wire form across binary /
/// canonical text / JSON / MessagePack.
pub fn build_func_param_abi() -> Module {
    let mut module = Module::new("func_param_abi");
    // Pin the target with the non-default AlwaysMemory policy + a stable ABI
    // id: the module-wide contract the byval/sret classification below obeys.
    module.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("sysv64".into()),
        struct_passing: trust_ir::StructPassingPolicy::AlwaysMemory,
    });
    module.add_struct(StructDef {
        id: StructId::new(0),
        name: "BigPair".into(),
        fields: vec![
            FieldDef {
                name: "lo".into(),
                ty: Ty::U64,
                offset: Some(0),
            },
            FieldDef {
                name: "hi".into(),
                ty: Ty::U64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::C,
    });

    // fn copy_pair(out: Ptr [sret noalias], src: Ptr [byval readonly ...]) -> ()
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr],
        returns: vec![],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "copy_pair", ft, BlockId::new(0));
    func.attrs.params = vec![
        ParamAttrs {
            noalias: true,
            sret: true,
            ..Default::default()
        },
        ParamAttrs {
            dereferenceable: Some(16),
            align: Some(8),
            readonly: true,
            byval: true,
            ..Default::default()
        },
    ];
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::Ptr));
    block.params.push((ValueId::new(1), Ty::Ptr));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    func.blocks.push(block);
    module.add_function(func);
    module
}

// ---------- chc_batch ----------

/// x86 CHC Batch JIT TrustIr Contract Plan fixture.
/// Separate-compilation contract fixture: a module that carries a body-less,
/// contract-only declaration (`FunctionSummary` with requires/ensures/params/proved)
/// alongside a defined function. Exercises the v18 `Function.summary` wire codec
/// across binary / JSON / MessagePack. The canonical text form intentionally does
/// not render the verifier-facing contract (`text_supported: false`), so this is
/// not round-tripped through `.trust_ir` — the lossless paths guard it.
pub fn build_composition() -> Module {
    use trust_ir::value::FuncTyId;
    use trust_ir::{FunctionSummary, ProofFormula};

    let mut module = Module::new("composition");

    // Signature shared by the declaration and the caller: fn(i32) -> i32.
    let ft: FuncTyId = module.add_func_type(FuncTy {
        params: vec![Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });

    // The trusted-prelude contract for `reciprocal`: requires a non-zero argument,
    // guarantees a non-zero result. A body-less, contract-only declaration — the
    // IR-level "body None ⇒ summary" state a caller is verified against.
    let summary = FunctionSummary::new()
        .with_params(vec!["x".to_string()])
        .requiring(ProofFormula::trust_types_json(
            "{\"Ne\":[{\"Var\":[\"x\",\"Int\"]},{\"Int\":0}]}",
            "(not (= x 0))",
            "Bool",
        ))
        .ensuring(ProofFormula::smtlib2("(not (= result 0))", "Bool"))
        .proved();
    module.add_function(Function::declaration(
        FuncId::new(0),
        "reciprocal",
        ft,
        summary,
    ));

    // A defined sibling function that also publishes its own (trivial) contract,
    // proving body + summary coexist on the wire.
    let mut caller = Function::new(FuncId::new(1), "passthrough", ft, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::I32));
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    caller.blocks.push(block);
    caller.summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(ProofFormula::smtlib2("(= result x)", "Bool"))
            .proved(),
    );
    module.add_function(caller);

    module
}

pub fn build_chc_batch_fixture() -> Module {
    let mut mb = ModuleBuilder::new("chc_batch");

    // fn ay_chc_batch_eval(
    //     model_values: Ptr,
    //     model_len: U64,
    //     batch_meta: Ptr,
    //     batch_meta_len: U64,
    //     output: Ptr,
    //     output_len: U64,
    //     status: Ptr,
    // ) -> U32
    let ft = mb.add_func_type(
        vec![
            Ty::Ptr,
            Ty::U64,
            Ty::Ptr,
            Ty::U64,
            Ty::Ptr,
            Ty::U64,
            Ty::Ptr,
        ],
        vec![Ty::U32],
    );

    let mut fb = mb.function("ay_chc_batch_eval", ft);
    let entry = fb.create_block();
    fb.add_block_param(entry, Ty::Ptr); // model_values
    fb.add_block_param(entry, Ty::U64); // model_len
    fb.add_block_param(entry, Ty::Ptr); // batch_meta
    fb.add_block_param(entry, Ty::U64); // batch_meta_len
    fb.add_block_param(entry, Ty::Ptr); // output
    fb.add_block_param(entry, Ty::U64); // output_len
    fb.add_block_param(entry, Ty::Ptr); // status

    fb.switch_to_block(entry);
    let res = fb.iconst(Ty::U32, 0);
    fb.ret(vec![res]);

    // Annotations.
    //
    // #25 (soundness): `ay_chc_batch_eval` writes results through its `output`
    // and `status` pointer parameters, so it is NOT `Pure`. TrustIr defines
    // `Pure` as "no side effects" (see `Function::is_safe_for_gpu`), and a
    // function that mutates caller memory has a side effect. Annotating it
    // `Pure` would falsely make it pass `is_safe_for_gpu()`
    // (`Pure + NoPanic + Deterministic`), so the `Pure` claim is deliberately
    // omitted to keep the contract honest until the ay-side protocol decision
    // is made (see the design plan §"Proof Annotations"): whether the helper is
    // modelled as pure-modulo-its-declared-output-buffer (which would require a
    // new annotation expressing that scoped effect) or simply as an effectful
    // helper. The output-buffer write is instead flagged with
    // `AppendOnlyBuffer` (a memory-role hint, no purity guarantee).
    //
    // `Deterministic`/`Terminates`/`NoPanic`/`NoUndef` remain: none of those
    // claims is contradicted by writing to a declared output buffer.
    fb.add_proof(ProofAnnotation::Deterministic);
    fb.add_proof(ProofAnnotation::Terminates);
    fb.add_proof(ProofAnnotation::NoPanic);
    fb.add_proof(ProofAnnotation::NoUndef);
    fb.add_proof(ProofAnnotation::AppendOnlyBuffer);

    // Custom proof tags (mapped to unique indices for the fixture)
    fb.add_proof(ProofAnnotation::Custom(ProofTag::new(1001))); // ay.chc.batch.v1
    fb.add_proof(ProofAnnotation::Custom(ProofTag::new(1002))); // ay.chc.scalar_oracle
    fb.add_proof(ProofAnnotation::Custom(ProofTag::new(1003))); // ay.chc.layout_hash
    fb.add_proof(ProofAnnotation::Custom(ProofTag::new(1004))); // ay.chc.generation_domain
    fb.add_proof(ProofAnnotation::Custom(ProofTag::new(1005))); // ay.chc.batch_shape_version

    fb.build();

    mb.build()
}

// ---------- frontend_emission_subset ----------

/// The `integration-frontend-emission` worked example: a tiny two-function
/// "frontend" emission that stays entirely inside the v1 lowering-target
/// conformance subset (`lowering-target-subset.md`, repo root), with source spans
/// threaded through the builder (`intern_file` + `set_span`) and the
/// function-level ABI set through the builder pass-throughs
/// (`set_calling_conv` / `set_attrs`).
///
/// The `lowering_subset` gate test additionally asserts this module
/// validates cleanly, produces zero subset violations, and that every
/// emitted instruction carries a span.
pub fn build_frontend_emission_subset() -> Module {
    use trust_ir::{CallingConv, FuncAttrs};

    let mut mb = ModuleBuilder::new("frontend_emission_subset");
    let file = mb.intern_file("examples/mini_frontend.rs");
    let span = |line: u32, col: u32| SourceSpan { file, line, col };

    // fn checked_add(a: i32, b: i32) -> i32 — overflow-checked add that
    // traps (Unreachable) on overflow, per the ratified panic=abort policy.
    let bin_ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let checked_add = {
        let mut fb = mb.function("checked_add", bin_ft);
        fb.set_calling_conv(CallingConv::Rust);
        fb.set_attrs(FuncAttrs {
            inlinehint: true,
            ..Default::default()
        });
        fb.add_proof(ProofAnnotation::Terminates);
        fb.add_proof(ProofAnnotation::Deterministic);
        let entry = fb.create_block();
        let ok_bb = fb.create_block();
        let trap_bb = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I32);
        let b = fb.add_block_param(entry, Ty::I32);
        let sum_param = fb.add_block_param(ok_bb, Ty::I32);
        fb.switch_to_block(entry);
        fb.set_span(span(3, 5));
        let (sum, overflowed) = fb.overflow(OverflowOp::AddOverflow, Ty::I32, a, b);
        fb.set_span(span(3, 9));
        fb.condbr(overflowed, trap_bb, vec![], ok_bb, vec![sum]);
        fb.switch_to_block(ok_bb);
        fb.set_span(span(4, 5));
        fb.ret(vec![sum_param]);
        fb.switch_to_block(trap_bb);
        fb.set_span(span(5, 5));
        fb.unreachable();
        fb.build()
    };

    // fn sum3(x: i32) -> i32 { checked_add(checked_add(x, 1), 2) }
    let un_ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    {
        let mut fb = mb.function("sum3", un_ft);
        fb.set_calling_conv(CallingConv::Rust);
        fb.add_proof(ProofAnnotation::Terminates);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.set_span(span(9, 24));
        let one = fb.iconst(Ty::I32, 1);
        fb.set_span(span(9, 27));
        let two = fb.iconst(Ty::I32, 2);
        fb.set_span(span(9, 17));
        let inner = fb.call(checked_add, vec![x, one]);
        fb.set_span(span(9, 5));
        let outer = fb.call(checked_add, vec![inner, two]);
        fb.set_span(span(10, 1));
        fb.ret(vec![outer]);
        fb.build();
    }

    mb.build()
}

/// PANIC-CLASS OBLIGATIONS the Rust frontend records from rustc MIR `Assert`
/// terminators (`trust-ir-frontend/mir-assert@1`). Closes a measured wire-format
/// gap: before this fixture, `ObligationKind::BoundsCheck` and
/// `ObligationKind::ArithmeticSafety` appeared in NO byte-golden fixture — their
/// binary tags were covered only by a unit test, so nothing guarded them across
/// canonical text / JSON / MessagePack.
///
/// Shape mirrors the producer exactly: every row is `Pending` (a RECORDED,
/// UNPROVED claim), B4-scoped with `function`, and identified by
/// `ProofObligationSourceIdentity` — with a resolved source range where the
/// span mapped, and WITHOUT one on the dummy-span degradation path. No
/// `PublicObligationIdentity` (there is no semantic digest to compute) and no
/// on-node `ProofRef` (the validator rejects a ProofRef to a non-discharged
/// obligation — the source identity IS the linkage). Built through
/// `ModuleBuilder::add_proof_obligation`, the surface the frontend uses.
pub fn build_frontend_panic_obligations() -> Module {
    const SOURCE_ID: &str = "trust-ir-frontend/mir-assert@1";

    let mut mb = ModuleBuilder::new("frontend_panic_obligations");
    let file = mb.intern_file("examples/panic_checks.rs");

    // fn checked_index(slice_len: u64, index: u64, acc: i32) -> i32
    // — the body stands in for a bounds check + an overflow check + a
    // coroutine-resume check, all lowered to explicit control flow.
    let ft = mb.add_func_type(vec![Ty::U64, Ty::U64, Ty::I32], vec![Ty::I32]);
    let fid = mb.peek_next_func_id();
    {
        let mut fb = mb.function("checked_index", ft);
        let entry = fb.create_block();
        let bounds_ok_bb = fb.create_block();
        let ret_bb = fb.create_block();
        let trap_bb = fb.create_block();
        let len = fb.add_block_param(entry, Ty::U64);
        let index = fb.add_block_param(entry, Ty::U64);
        let acc = fb.add_block_param(entry, Ty::I32);
        let sum_param = fb.add_block_param(ret_bb, Ty::I32);
        fb.switch_to_block(entry);
        fb.set_span(SourceSpan {
            file,
            line: 7,
            col: 13,
        });
        let in_bounds = fb.icmp(ICmpOp::Ult, Ty::U64, index, len);
        fb.condbr(in_bounds, bounds_ok_bb, vec![], trap_bb, vec![]);
        fb.switch_to_block(bounds_ok_bb);
        fb.set_span(SourceSpan {
            file,
            line: 8,
            col: 9,
        });
        let one = fb.iconst(Ty::I32, 1);
        let (sum, overflowed) = fb.overflow(OverflowOp::AddOverflow, Ty::I32, acc, one);
        fb.condbr(overflowed, trap_bb, vec![], ret_bb, vec![sum]);
        fb.switch_to_block(ret_bb);
        fb.set_span(SourceSpan {
            file,
            line: 9,
            col: 5,
        });
        fb.ret(vec![sum_param]);
        fb.switch_to_block(trap_bb);
        fb.unreachable();
        fb.build();
    }

    // (a) bounds check, with a full source range.
    mb.add_proof_obligation(|id| {
        ProofObligation::new(
            id,
            ObligationKind::BoundsCheck,
            ProofStatus::Pending,
            "rustc MIR Assert (bounds_check) at bb0 of `checked_index`: index is in bounds. \
             RECORDED BY THE FRONTEND, NOT PROVED.",
        )
        .with_function(fid)
        .with_source(
            ProofObligationSourceIdentity::new(SOURCE_ID, "checked_index#bb0#bounds_check")
                .with_range(ProofObligationSourceRange {
                    file,
                    start_line: 7,
                    start_col: 13,
                    end_line: 7,
                    end_col: 26,
                }),
        )
        // v34 site backref: the `condbr` in bb0 that IS the lowered bounds
        // check (index 1: the `icmp` producing the condition is index 0).
        .with_site(trust_ir::ObligationSite::new(fid, BlockId::new(0), 1))
    });

    // (b) arithmetic safety (overflow), with a MULTI-LINE source range.
    mb.add_proof_obligation(|id| {
        ProofObligation::new(
            id,
            ObligationKind::ArithmeticSafety,
            ProofStatus::Pending,
            "rustc MIR Assert (overflow) at bb1 of `checked_index`: arithmetic does not \
             overflow. RECORDED BY THE FRONTEND, NOT PROVED.",
        )
        .with_function(fid)
        .with_source(
            ProofObligationSourceIdentity::new(SOURCE_ID, "checked_index#bb1#overflow").with_range(
                ProofObligationSourceRange {
                    file,
                    start_line: 8,
                    start_col: 9,
                    end_line: 9,
                    end_col: 4,
                },
            ),
        )
        // v34 site backref: the `condbr` in bb1 on the overflow flag
        // (index 2: `iconst` is 0, the checked `add` is 1).
        .with_site(trust_ir::ObligationSite::new(fid, BlockId::new(1), 2))
    });

    // (c) panic freedom WITHOUT a range — the dummy/unmapped-span degradation
    // path the frontend takes when a span resolves to no interned file.
    mb.add_proof_obligation(|id| {
        ProofObligation::new(
            id,
            ObligationKind::PanicFreedom,
            ProofStatus::Pending,
            "rustc MIR Assert (resumed_after_return) at bb2 of `checked_index`: coroutine is \
             not resumed after returning. RECORDED BY THE FRONTEND, NOT PROVED.",
        )
        .with_function(fid)
        .with_source(ProofObligationSourceIdentity::new(
            SOURCE_ID,
            "checked_index#bb2#resumed_after_return",
        ))
    });

    mb.build()
}

/// v23 producer provenance (Program CK1 contract ladder): one function per
/// producer wire tag — `TRust`(0), `Clean`(1), `TrustIr`(2), the deprecated
/// `TSwift`(3)/`TC`(4), and the `Other`(5) string escape — plus one untagged
/// function (producer = None). Built through the builder surface:
/// `ModuleBuilder::set_default_producer` stamps the module-wide default,
/// `FunctionBuilder::set_producer` overrides it per function, and
/// `FunctionBuilder::clear_producer` clears it back to `None` — which is
/// exactly the frontend usage pattern. Also carries the `; #producer:`
/// canonical-text clause through the `.trust_ir` golden.
pub fn build_producer_provenance() -> Module {
    use trust_ir::Producer;

    let mut mb = ModuleBuilder::new("producer_provenance");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    // Module-wide default: everything below is Clean-emitted unless
    // overridden per function.
    mb.set_default_producer(Producer::Clean);

    let mut identity = |name: &str, producer: Option<Producer>| {
        let mut fb = mb.function(name, ft);
        if let Some(producer) = producer {
            fb.set_producer(producer);
        }
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();
    };

    // Inherits the Clean default (wire tag 1).
    identity("from_clean_default", None);
    // Per-function overrides covering the rest of the stable vocabulary.
    identity("from_trust", Some(Producer::TRust));
    identity("from_trust_ir", Some(Producer::TrustIr));
    identity("from_tswift_deprecated", Some(Producer::TSwift));
    identity("from_tc_deprecated", Some(Producer::TC));
    // The Other escape: free-form tool identifier with characters that
    // exercise the quoted-string text form and the string pool.
    identity(
        "from_other_escape",
        Some(Producer::Other("custom \"exotic\" frontend v1".to_string())),
    );

    // One genuinely untagged function (None on the wire): `clear_producer`
    // overrides the module-wide Clean default back to None.
    {
        let mut fb = mb.function("untagged", ft);
        fb.clear_producer();
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();
    }

    mb.build()
}

/// v32/v33 debug metadata: a producer-stamped function with sparse SSA names,
/// a two-level lexical-scope tree, and exact per-node scope indices. Keeping
/// producer provenance in the same fixture pins the complete trailing
/// Function record order (`producer`, `value_names`, `scopes`).
pub fn build_debug_metadata_v33() -> Module {
    use trust_ir::Producer;

    let mut m = Module::new("debug_metadata_v33");
    let file = m.intern_file("src/debug.rs");
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "named_increment", ft, BlockId::new(0));
    func.producer = Some(Producer::TRust);
    func.value_names = Some(vec![
        (ValueId::new(9), "input".to_string()),
        (ValueId::new(42), "incremented, value".to_string()),
    ]);
    func.scopes = Some(vec![
        ScopeData {
            parent: None,
            span: Some(SourceSpan {
                file,
                line: 1,
                col: 0,
            }),
        },
        ScopeData {
            parent: Some(0),
            span: Some(SourceSpan {
                file,
                line: 2,
                col: 4,
            }),
        },
    ]);

    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(9), Ty::I32));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(1),
        })
        .with_result(ValueId::new(41))
        .with_span(SourceSpan {
            file,
            line: 2,
            col: 8,
        })
        .with_scope(1),
    );
    block.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: ValueId::new(9),
            rhs: ValueId::new(41),
        })
        .with_result(ValueId::new(42))
        .with_span(SourceSpan {
            file,
            line: 2,
            col: 4,
        })
        .with_scope(1),
    );
    block.body.push(
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(42)],
        })
        .with_span(SourceSpan {
            file,
            line: 3,
            col: 0,
        })
        .with_scope(0),
    );
    func.blocks.push(block);
    m.add_function(func);
    m
}

/// v24: the 128-bit-faithful integer carrier. Pins `Constant::U128` (wire
/// tag 13) across all four formats at BOTH canonical boundaries — the first
/// value i128 cannot carry (i128::MAX + 1) and u128::MAX — as an
/// `Inst::Const` result AND a global initializer. Values at or below
/// i128::MAX stay `Constant::Int` (the one-spelling rule); `boundary_int`
/// pins the Int side of the boundary in the same module.
pub fn build_u128_constants() -> Module {
    use trust_ir::{Constant, Global, Linkage};

    let mut mb = ModuleBuilder::new("u128_constants");
    let ft = mb.add_func_type(vec![], vec![Ty::U128]);

    let ret_const = |mb: &mut ModuleBuilder, name: &str, value: u128| {
        let mut fb = mb.function(name, ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let v = fb.uconst(Ty::U128, value);
        fb.ret(vec![v]);
        fb.build();
    };

    ret_const(&mut mb, "first_above_i128_max", i128::MAX as u128 + 1);
    ret_const(&mut mb, "u128_max", u128::MAX);

    // The Int side of the canonical boundary: `Constant::u128(i128::MAX)`
    // must spell as Int (proving the smart constructor's split in the wire).
    let ft_i = mb.add_func_type(vec![], vec![Ty::I128]);
    {
        let mut fb = mb.function("boundary_int", ft_i);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let v = fb.uconst(Ty::I128, i128::MAX as u128);
        fb.ret(vec![v]);
        fb.build();
    }

    mb.add_global(Global {
        name: "U128_GLOBAL".to_string(),
        ty: Ty::U128,
        mutable: false,
        initializer: Some(Constant::U128(u128::MAX - 1)),
        linkage: Linkage::External,
        tls: None,
        align: None,
    });

    mb.build()
}

/// v25: the byte-array constant carrier. Pins `Constant::Bytes` (wire tag
/// 14) across all four formats: a raw payload (with a 0x00 and a 0xFF), a
/// utf8-claimed payload (multibyte character included), and the empty
/// payload — each as a `[u8; N]` global initializer plus one `Inst::Const`
/// use.
pub fn build_bytes_constants() -> Module {
    use trust_ir::{Constant, Global, Linkage};

    let mut mb = ModuleBuilder::new("bytes_constants");

    let add_global = |mb: &mut ModuleBuilder, name: &str, c: Constant| {
        let len = match &c {
            Constant::Bytes { data, .. } => data.len() as u64,
            _ => unreachable!("bytes fixture"),
        };
        let tid = mb.add_type(Ty::U8);
        mb.add_global(Global {
            name: name.to_string(),
            ty: Ty::Array(tid, len),
            mutable: false,
            initializer: Some(c),
            linkage: Linkage::External,
            tls: None,
            align: None,
        });
    };

    add_global(
        &mut mb,
        "RAW_BYTES",
        Constant::bytes(vec![0u8, 0xde, 0xad, 0xff]),
    );
    add_global(&mut mb, "UTF8_BYTES", Constant::str_bytes("héllo"));
    add_global(&mut mb, "EMPTY_BYTES", Constant::bytes(Vec::new()));

    // One in-body use: a [u8; 2] constant materialized and returned.
    let tid = mb.add_type(Ty::U8);
    let arr_ty = Ty::Array(tid, 2);
    let ft = mb.add_func_type(vec![], vec![arr_ty.clone()]);
    {
        let mut fb = mb.function("ret_bytes", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let v = fb.const_value(arr_ty, Constant::str_bytes("ok"));
        fb.ret(vec![v]);
        fb.build();
    }

    mb.build()
}

/// v25 B1 scalars: `Ty::Isize` / `Ty::Usize` / `Ty::Char` (wire tags 33-35)
/// exercised in signatures, block params, arithmetic, and constants.
/// (`Ty::Error` is deliberately absent — producer-internal, unencodable.)
pub fn build_b1_scalars() -> Module {
    use trust_ir::inst::BinOp;

    let mut mb = ModuleBuilder::new("b1_scalars");

    // isize passthrough-with-arithmetic: fn(isize) -> isize { x + 1 }
    let ft_i = mb.add_func_type(vec![Ty::Isize], vec![Ty::Isize]);
    {
        let mut fb = mb.function("isize_add_one", ft_i);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::Isize);
        fb.switch_to_block(entry);
        let one = fb.iconst(Ty::Isize, 1);
        let sum = fb.binop(BinOp::Add, Ty::Isize, x, one);
        fb.ret(vec![sum]);
        fb.build();
    }

    // usize passthrough: fn(usize) -> usize { x }
    let ft_u = mb.add_func_type(vec![Ty::Usize], vec![Ty::Usize]);
    {
        let mut fb = mb.function("usize_id", ft_u);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::Usize);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();
    }

    // char constant: fn() -> char { 'A' }
    let ft_c = mb.add_func_type(vec![], vec![Ty::Char]);
    {
        let mut fb = mb.function("char_a", ft_c);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let c = fb.iconst(Ty::Char, 65);
        fb.ret(vec![c]);
        fb.build();
    }

    mb.build()
}

// ---------- mixed_producer_module ----------

/// The WS3-M1 seed (Program CK1, designs/2026-07-07): ONE module legally
/// carrying functions from BOTH producers, with cross-producer calls in BOTH
/// directions — trust-ir as the single target for tRust and Clean alike.
///
/// Layout (all bodies are simple lowering-target-subset arithmetic, so the
/// `lowering_subset` gate stays exemption-free):
///
/// | function            | producer | body                          |
/// |---------------------|----------|-------------------------------|
/// | `clean_double`      | Clean    | `x * 2`                       |
/// | `trust_inc`         | TRust    | `x + 1`                       |
/// | `trust_calls_clean` | TRust    | `clean_double(x) + 1`         |
/// | `clean_calls_trust` | Clean    | `trust_inc(x) * 2`            |
///
/// `tests/mixed_producer.rs` holds the acceptance tests over this module
/// (validate_module 0 errors, both call directions present, interpreter
/// execution) and the negative-first FuncTy-mismatch rejection; the
/// byte-golden corpus pins its four-format wire form.
pub fn build_mixed_producer_module() -> Module {
    use trust_ir::Producer;

    let mut mb = ModuleBuilder::new("mixed_producer_module");
    let unary = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    // Leaf functions, one per producer.
    // fn clean_double(x: i32) -> i32 { x * 2 }   [Clean]
    let clean_double = {
        let mut fb = mb.function("clean_double", unary);
        fb.set_producer(Producer::Clean);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let two = fb.iconst(Ty::I32, 2);
        let doubled = fb.mul(Ty::I32, x, two);
        fb.ret(vec![doubled]);
        fb.build()
    };

    // fn trust_inc(x: i32) -> i32 { x + 1 }   [TRust]
    let trust_inc = {
        let mut fb = mb.function("trust_inc", unary);
        fb.set_producer(Producer::TRust);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let one = fb.iconst(Ty::I32, 1);
        let inc = fb.add(Ty::I32, x, one);
        fb.ret(vec![inc]);
        fb.build()
    };

    // Cross-call direction 1: tRust caller -> Clean callee.
    // fn trust_calls_clean(x: i32) -> i32 { clean_double(x) + 1 }   [TRust]
    {
        let mut fb = mb.function("trust_calls_clean", unary);
        fb.set_producer(Producer::TRust);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let doubled = fb.call(clean_double, vec![x]);
        let one = fb.iconst(Ty::I32, 1);
        let out = fb.add(Ty::I32, doubled, one);
        fb.ret(vec![out]);
        fb.build();
    }

    // Cross-call direction 2: Clean caller -> tRust callee.
    // fn clean_calls_trust(x: i32) -> i32 { trust_inc(x) * 2 }   [Clean]
    {
        let mut fb = mb.function("clean_calls_trust", unary);
        fb.set_producer(Producer::Clean);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let inc = fb.call(trust_inc, vec![x]);
        let two = fb.iconst(Ty::I32, 2);
        let out = fb.mul(Ty::I32, inc, two);
        fb.ret(vec![out]);
        fb.build();
    }

    mb.build()
}

/// NEGATIVE variant of [`build_mixed_producer_module`] (WS3-M1
/// negative-test-first): both cross-producer call edges are skewed against
/// the callee's declared `FuncTy`, modelling a producer compiled against a
/// stale signature of the other producer's function.
///
/// * `trust_calls_clean_bad` (TRust) passes an `i64` where `clean_double`
///   (Clean) declares `fn(i32) -> i32` — an argument-TYPE mismatch;
/// * `clean_calls_trust_bad` (Clean) passes two arguments where `trust_inc`
///   (TRust) declares one — an argument-COUNT mismatch.
///
/// This module must be REJECTED by `validate_module`, and each diagnostic
/// must attribute BOTH sides of the broken edge by producer (see
/// `tests/mixed_producer.rs`). Never registered in the byte-golden corpus:
/// invalid modules are not wire-format contracts.
#[allow(dead_code)] // Used by the sibling mixed_producer integration target.
pub fn build_mixed_producer_cross_functy_mismatch() -> Module {
    use trust_ir::Producer;

    let mut mb = ModuleBuilder::new("mixed_producer_cross_functy_mismatch");
    let unary = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    // Same leaves as the valid fixture.
    let clean_double = {
        let mut fb = mb.function("clean_double", unary);
        fb.set_producer(Producer::Clean);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let two = fb.iconst(Ty::I32, 2);
        let doubled = fb.mul(Ty::I32, x, two);
        fb.ret(vec![doubled]);
        fb.build()
    };
    let trust_inc = {
        let mut fb = mb.function("trust_inc", unary);
        fb.set_producer(Producer::TRust);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let one = fb.iconst(Ty::I32, 1);
        let inc = fb.add(Ty::I32, x, one);
        fb.ret(vec![inc]);
        fb.build()
    };

    // tRust caller believes clean_double takes i64: arg-TYPE mismatch.
    {
        let mut fb = mb.function("trust_calls_clean_bad", unary);
        fb.set_producer(Producer::TRust);
        let entry = fb.create_block();
        let _x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let wide = fb.iconst(Ty::I64, 7);
        let out = fb.call(clean_double, vec![wide]);
        fb.ret(vec![out]);
        fb.build();
    }

    // Clean caller believes trust_inc takes two args: arg-COUNT mismatch.
    {
        let mut fb = mb.function("clean_calls_trust_bad", unary);
        fb.set_producer(Producer::Clean);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let extra = fb.iconst(Ty::I32, 3);
        let out = fb.call(trust_inc, vec![x, extra]);
        fb.ret(vec![out]);
        fb.build();
    }

    mb.build()
}
