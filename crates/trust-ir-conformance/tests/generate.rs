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

use std::collections::BTreeSet;
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
    BindingFrameId, BlockId, EnumId, FreshIds, FuncId, GlobalId, ProofId, ProofTag, RecordId,
    SourceSpan, StructId, TyId, ValueId,
};
use trust_ir::{
    Block, Endianness, Function, Global, Linkage, Module, ParamAttrs, Producer, ScopeData,
    StructRepr, TargetInfo,
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
    PointerMetadataShape, TrustMcArithmeticModel, TrustMcBmcOptions, TrustMcChcEngine,
    TrustMcChcOptions, TrustMcInvariantSource, TrustMcMemoryModel, TrustMcNativeEvidenceBundle,
    TrustMcNativeRequest, TrustMcPdrGeneralization, TrustMcPdrOptions, TrustMcRequestOptions,
    TrustMcSlicingMode, TrustMcVerificationMode, TrustVcMemorySemantics,
    TrustVcNativeEvidenceBundle, TrustVcNativeRequest, TrustVcRequestOptions,
    TrustVcTrustedEvidencePolicy, TrustVcVerificationMode, TrustWpFramePolicy, TrustWpHeapModel,
    TrustWpLoopStrategy, TrustWpNativeEvidenceBundle, TrustWpNativeRequest, TrustWpPanicSemantics,
    TrustWpRequestOptions, TrustWpVerificationMode, TyLayoutKind, TyLayoutShape, TyShape,
};
use trust_ir_build::ModuleBuilder;
use trust_ir_build::demo::VectorDemoExt;

#[path = "generate/call_unwind_boundary.rs"]
mod call_unwind_boundary;
pub use call_unwind_boundary::build_call_unwind_boundary;

#[path = "generate/signature_abi.rs"]
pub(crate) mod signature_abi_fixture;

/// A valid source-to-lowered placement record, pinned in all four formats.
pub fn build_typed_signature_abi() -> Result<Module, FixtureError> {
    signature_abi_fixture::module().or_fixture("the typed signature fixture module")
}

/// Both declaration selectors retain the same nominal empty payload type.
pub fn build_single_inhabited_enums() -> Result<Module, FixtureError> {
    let mut module = Module::new("single_inhabited_enums");
    module.add_enum(EnumDef::new(EnumId::new(0), "NominalVoid", vec![]));
    for selected in [0u32, 1] {
        let payload = EnumVariant {
            name: "Value".into(),
            fields: vec![Ty::U32],
            field_names: vec![],
        };
        let absent = EnumVariant {
            name: "Absent".into(),
            fields: vec![Ty::Enum(EnumId::new(0))],
            field_names: vec![],
        };
        let mut definition = EnumDef::new(
            EnumId::new(1 + selected),
            format!("Selected{selected}"),
            if selected == 0 {
                vec![payload, absent]
            } else {
                vec![absent, payload]
            },
        );
        definition.discriminants = vec![Some(7), Some(23)];
        definition.layout = Some(trust_ir::EnumLayoutDescriptor {
            encoding: trust_ir::EnumTagEncoding::SingleInhabited { variant: selected },
            size: 4,
            align: 4,
            variant_field_offsets: if selected == 0 {
                vec![vec![0], vec![]]
            } else {
                vec![vec![], vec![0]]
            },
        });
        module.add_enum(definition);
    }
    Ok(module)
}

/// Why a fixture builder could not build its artifact.
///
/// Every `build_*` fixture (and every `build_refuse_*` KIND 4 builder) is
/// TOTAL: it returns this instead of panicking, and the TEST that calls it
/// decides (`.expect(..)` there, where a panic is a test failure). The
/// builders are compiled into the library under `all`, the surface the
/// verified survey examines, so a designed panic here would be a refutation
/// the lane calls TRUE (r11 item 7).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixtureError {
    /// What the builder was doing.
    pub context: &'static str,
    /// Why it could not.
    pub message: String,
}

impl std::fmt::Display for FixtureError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fixture: {}: {}", self.context, self.message)
    }
}

impl std::error::Error for FixtureError {}

/// Turn a callee's typed refusal (or an absent value) into a
/// [`FixtureError`] naming the step, for `?`.
pub trait OrFixture<T> {
    /// The value, or the refusal as a [`FixtureError`] naming `context`.
    fn or_fixture(self, context: &'static str) -> Result<T, FixtureError>;
}

impl<T, E: std::fmt::Display> OrFixture<T> for Result<T, E> {
    fn or_fixture(self, context: &'static str) -> Result<T, FixtureError> {
        self.map_err(|error| FixtureError {
            context,
            message: error.to_string(),
        })
    }
}

impl<T> OrFixture<T> for Option<T> {
    fn or_fixture(self, context: &'static str) -> Result<T, FixtureError> {
        self.ok_or_else(|| FixtureError {
            context,
            message: "absent".to_string(),
        })
    }
}

/// A fixture invariant that does not hold: the builder refuses, never panics.
pub fn fixture_invariant(holds: bool, context: &'static str) -> Result<(), FixtureError> {
    if holds {
        Ok(())
    } else {
        Err(FixtureError {
            context,
            message: "the fixture's own invariant does not hold".to_string(),
        })
    }
}

// ---------- ty_primitives ----------

/// Every primitive `Ty` variant appears either as a function parameter,
/// a function return type, a block parameter, or an instruction operand.
pub fn build_ty_primitives() -> Result<Module, FixtureError> {
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
    let mut m = mb.build().or_fixture("ModuleBuilder::build")?;
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        // ABI pinning (v20): a non-default stable ABI id so the goldens pin
        // the extended TargetInfo wire form (policy stays the NativeC default).
        abi: Some("aapcs64".into()),
        struct_passing: Default::default(),
    });
    Ok(m)
}

// ---------- ty_container_vtable ----------

/// v40 `FatPtrKind::ContainerVtable` (fat-pointer-kind tag 4) beside its v38
/// sibling `ContainerLen` (tag 3): both container-tail fat pointers appear as
/// struct fields, function-type parameters/returns, and block parameters, so
/// exactly one golden in the corpus carries the v40 header word and sub-tag 4
/// through binary, text (`fatptr<container_vtable>`), JSON, and MessagePack.
/// Every other golden keeps its minimum lossless writer version (v38, or v39
/// for nominal dialect types); this is the only fixture the v40 selection
/// rule may raise.
pub fn build_ty_container_vtable() -> Result<Module, FixtureError> {
    let mut m = Module::new("ty_container_vtable");
    let dyn_tail = Ty::FatPtr(FatPtrKind::ContainerVtable);
    let len_tail = Ty::FatPtr(FatPtrKind::ContainerLen);

    // struct ArcTails { any: *const ArcInner<dyn Any>, text: *const ArcInner<str> }
    // Both kinds lay out as 16-byte / 8-aligned fat pointers.
    let tails = m.add_struct(StructDef {
        id: StructId::new(0),
        name: "ArcTails".into(),
        fields: vec![
            FieldDef {
                name: "any".into(),
                ty: dyn_tail.clone(),
                offset: Some(0),
            },
            FieldDef {
                name: "text".into(),
                ty: len_tail.clone(),
                offset: Some(16),
            },
        ],
        size: Some(32),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    });

    let ft = m
        .add_func_type(FuncTy {
            params: vec![dyn_tail.clone(), len_tail.clone(), Ty::Struct(tails)],
            returns: vec![dyn_tail.clone()],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let mut func = Function::new(FuncId::new(0), "container_tails", ft, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), dyn_tail));
    entry.params.push((ValueId::new(1), len_tail));
    entry.params.push((ValueId::new(2), Ty::Struct(tails)));
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    func.blocks.push(entry);
    m.try_add_function(func)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

// ---------- ty_dialect_v39 ----------

/// A v39 nominal dialect type on a signature, a block parameter and an
/// exact-typed `Copy` (the transport the validator permits). Header 39.
pub fn build_ty_dialect() -> Result<Module, FixtureError> {
    let nominal = Ty::Dialect(Box::new(trust_ir::DialectTy::new("example", "value", 1)));
    let mut m = Module::new("ty_dialect_v39");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![nominal.clone()],
            returns: vec![nominal.clone()],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let mut func = Function::new(FuncId::new(0), "nominal_identity", ft, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), nominal.clone()));
    entry.body.push(
        InstrNode::new(Inst::Copy {
            ty: nominal,
            operand: ValueId::new(0),
        })
        .with_result(ValueId::new(1)),
    );
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    func.blocks.push(entry);
    m.try_add_function(func)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

// ---------- import_scheme ----------

/// The v44 import-identity scheme (WS4.10): a module whose import table mixes
/// a legacy row recorded under the V2 identity (`trust_ir.module.v2`, the
/// decode default of every pre-v44 row) with a row recorded under the
/// portable V3 identity (`trust_ir.module.v3`, `Module.files` strings
/// projected out). The V3 row is what selects header 44; the V2 row proves a
/// v44 table spells BOTH tags (`0` and `1`), since every row of a v44 table
/// carries one. A debug file table and a span on the body make the projected
/// field visible in the golden. The `.trust_ir` golden pins the text
/// spelling: ` scheme v3`, V2 by omission. The ONLY golden whose header word
/// is 44.
pub fn build_import_scheme() -> Result<Module, FixtureError> {
    use trust_ir::{IdentityScheme, ModuleImport};

    let mut m = Module::new("import_scheme");
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: Default::default(),
    });
    let file = m
        .intern_file("src/lib.rs")
        .or_fixture("Module::intern_file")?;
    m.intern_import(
        ModuleImport::new("legacy_dep", ProofDigest::sha256([0x22; 32]))
            .with_producer(Producer::TRust)
            .with_scheme(IdentityScheme::V2),
    )
    .or_fixture("Module::intern_import")?;
    m.intern_import(
        ModuleImport::new("portable_dep", ProofDigest::sha256([0x33; 32]))
            .with_producer(Producer::Clean),
    )
    .or_fixture("Module::intern_import")?;
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let mut func = Function::new(FuncId::new(0), "identity", ft, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::I32));
    entry.body.push(
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        })
        .with_span(SourceSpan {
            file,
            line: 3,
            col: 5,
        }),
    );
    func.blocks.push(entry);
    m.try_add_function(func)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

// ---------- abi_function_symbol ----------

/// The v45 function symbol attributes (WS3.10, F-053): an `(External,
/// Hidden)` definition — rustc's default for a non-exported cross-CGU
/// function — placed in an explicit section and retained; a bodyless
/// `Protected` import (the visibility the import requests); and a plain
/// function that keeps every default, proving a v45 function record spells
/// the defaults too. The ONLY golden whose function records carry the v45
/// symbol triple.
pub fn build_abi_function_symbol() -> Result<Module, FixtureError> {
    use trust_ir::Visibility;

    let mut m = Module::new("abi_function_symbol");
    m.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("sysv64".into()),
        struct_passing: Default::default(),
    });
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;

    let mut import = Function::new(FuncId::new(0), "imported_protected", ft, BlockId::new(0));
    import.visibility = Visibility::Protected;
    m.try_add_function(import)
        .or_fixture("Module::try_add_function")?;

    let mut hidden = Function::new(FuncId::new(1), "hidden_helper", ft, BlockId::new(0));
    hidden.visibility = Visibility::Hidden;
    hidden.section = Some("__TEXT,__text_hidden".into());
    hidden.retained = true;
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::I32));
    entry.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![ValueId::new(0)],
        })
        .with_results(vec![ValueId::new(1)]),
    );
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    hidden.blocks.push(entry);
    m.try_add_function(hidden)
        .or_fixture("Module::try_add_function")?;

    let mut plain = Function::new(FuncId::new(2), "plain", ft, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::I32));
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    plain.blocks.push(entry);
    m.try_add_function(plain)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

// ---------- abi_calling_conv ----------

/// The v45 calling conventions (WS3.12, F-059): every convention added in
/// v45 on a declaration, plus a `CallIndirect` site carrying one. `CUnwind`
/// is RECORDED, not given unwind semantics (panic=abort, ub-numerics-policy
/// §4). The ONLY golden whose function records carry a v45 convention.
pub fn build_abi_calling_conv() -> Result<Module, FixtureError> {
    use trust_ir::CallingConv;

    let mut m = Module::new("abi_calling_conv");
    m.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("sysv64".into()),
        struct_passing: Default::default(),
    });
    let ft = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    // Function ids by the core's one fresh-id rule (r11 sibling h2).
    let mut func_ids = FreshIds::<FuncId>::new();
    for conv in CallingConv::ALL.into_iter().filter(|c| c.is_abi_surface()) {
        let mut decl = Function::new(
            func_ids.take().or_fixture("a fresh FuncId")?,
            format!("foreign_{conv}"),
            ft,
            BlockId::new(0),
        );
        decl.calling_conv = conv;
        m.try_add_function(decl)
            .or_fixture("a claim-free declaration is added")?;
    }

    let mut caller = Function::new(
        func_ids.take().or_fixture("a fresh FuncId")?,
        "caller",
        ft,
        BlockId::new(0),
    );
    caller.calling_conv = CallingConv::Rust;
    let mut entry = Block::new(BlockId::new(0));
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Ptr,
            value: Constant::FnDef(FuncId::new(0)),
        })
        .with_result(ValueId::new(0)),
    );
    entry.body.push(InstrNode::new(Inst::CallIndirect {
        callee: ValueId::new(0),
        sig: ft,
        args: vec![],
        calling_conv: CallingConv::CUnwind,
    }));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    caller.blocks.push(entry);
    m.try_add_function(caller)
        .or_fixture("a claim-free caller is added")?;
    Ok(m)
}

// ---------- abi_enum_tag_repr ----------

/// The v45 128-bit enum tag lanes (WS3.14(b) / WS2.22, F-056): a
/// `#[repr(u128)]` enum and a `#[repr(i128)]` one, with explicit
/// discriminants a 64-bit lane could not hold at their declared repr.
/// Inference keeps the 64-bit cap, so only the explicit hint selects these.
/// The ONLY golden whose enum table carries a 128-bit tag repr.
pub fn build_abi_enum_tag_repr() -> Result<Module, FixtureError> {
    let mut m = Module::new("abi_enum_tag_repr");
    m.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("sysv64".into()),
        struct_passing: Default::default(),
    });
    let variant = |name: &str| EnumVariant {
        name: name.into(),
        fields: vec![],
        field_names: Vec::new(),
    };
    // 2^64: one past the widest 64-bit unsigned tag. Constants, so the value
    // is fixed at compile time and the builder carries no arithmetic.
    const WIDE: i128 = 1 << 64;
    const NEG_WIDE: i128 = -WIDE;
    let unsigned = EnumDef::new(EnumId::new(0), "WideU", vec![variant("A"), variant("B")])
        .with_discriminants(vec![Some(0), Some(WIDE)])
        .with_repr(EnumTagRepr::U128);
    let signed = EnumDef::new(
        EnumId::new(1),
        "WideI",
        vec![variant("Neg"), variant("Pos")],
    )
    .with_discriminants(vec![Some(NEG_WIDE), Some(WIDE)])
    .with_repr(EnumTagRepr::I128);
    m.enums.push(unsigned);
    m.enums.push(signed);
    m.add_type(Ty::Enum(EnumId::new(0)))
        .or_fixture("Module::add_type")?;
    m.add_type(Ty::Enum(EnumId::new(1)))
        .or_fixture("Module::add_type")?;

    let ft = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let mut func = Function::new(FuncId::new(0), "wide_tags", ft, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    func.blocks.push(entry);
    m.try_add_function(func)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

// ---------- closure_layout ----------

/// The v58 declared closure environment frame (WS3.13): a two-capture
/// `(U64) -> U64` closure whose declared image puts capture 1 FIRST — the
/// `repr(Rust)` upvar reordering that is the whole reason the table exists.
///
/// The body applies the closure, so the module also exercises the v58
/// codegen-refusal lift: with this row the `CallIndirect` over a `Ty::Closure`
/// callee is lowerable; without it the refusal is unchanged.
pub fn build_closure_layout() -> Result<Module, FixtureError> {
    let mut m = Module::new("closure_layout");
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: Default::default(),
    });
    // The closure's PHYSICAL signature: captures spread as leading arguments
    // (`lowering-target-subset.md` §G18-2), then the apparent parameters.
    let physical = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::U8, Ty::U64, Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let apparent = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let nullary = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let closure = m
        .add_closure_type(ClosureTy {
            func: apparent,
            captures: vec![Ty::U8, Ty::U64],
        })
        .or_fixture("Module::add_closure_type")?;
    m.closure_layouts.push(trust_ir::ClosureLayoutDescriptor {
        origin: None,
        closure,
        size: 16,
        align: 8,
        capture_offsets: vec![8, 0],
    });

    let mut body = Function::new(FuncId::new(0), "add_lo_hi", physical, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::U8));
    entry.params.push((ValueId::new(1), Ty::U64));
    entry.params.push((ValueId::new(2), Ty::U64));
    entry.body.push(
        InstrNode::new(Inst::Cast {
            op: trust_ir::inst::CastOp::ZExt,
            src_ty: Ty::U8,
            dst_ty: Ty::U64,
            operand: ValueId::new(0),
        })
        .with_result(ValueId::new(3)),
    );
    entry.body.push(
        InstrNode::new(Inst::BinOp {
            op: trust_ir::inst::BinOp::Add,
            ty: Ty::U64,
            lhs: ValueId::new(3),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(4)),
    );
    entry.body.push(
        InstrNode::new(Inst::BinOp {
            op: trust_ir::inst::BinOp::Add,
            ty: Ty::U64,
            lhs: ValueId::new(4),
            rhs: ValueId::new(2),
        })
        .with_result(ValueId::new(5)),
    );
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(5)],
    }));
    body.blocks.push(entry);
    // A v41+ producer stamps the codegen license (the v41 producer rule,
    // `producer_rule_census`): a NEW golden never joins the bodied tag-0 set.
    body.body_gate = Some(trust_ir::BodyGate::Gated {
        authority: "conformance-fixture".into(),
        evidence: None,
    });
    m.try_add_function(body)
        .or_fixture("Module::try_add_function")?;

    let mut program = Function::new(FuncId::new(1), "program", nullary, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Closure(closure),
            value: Constant::Closure {
                func: FuncId::new(0),
                captures: vec![Constant::Int(3), Constant::Int(5)],
            },
        })
        .with_result(ValueId::new(0)),
    );
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(16),
        })
        .with_result(ValueId::new(1)),
    );
    entry.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: ValueId::new(0),
            sig: apparent,
            args: vec![ValueId::new(1)],
            calling_conv: Default::default(),
        })
        .with_result(ValueId::new(2)),
    );
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    program.blocks.push(entry);
    // A v41+ producer stamps the codegen license (the v41 producer rule,
    // `producer_rule_census`): a NEW golden never joins the bodied tag-0 set.
    program.body_gate = Some(trust_ir::BodyGate::Gated {
        authority: "conformance-fixture".into(),
        evidence: None,
    });
    m.try_add_function(program)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

/// Runtime capture construction over the existing declared two-capture frame.
/// The older closure_layout goldens remain unchanged; this fixture selects v63.
pub fn build_make_closure() -> Result<Module, FixtureError> {
    let mut m = build_closure_layout()?;
    m.name = "make_closure".into();
    let constant = m
        .functions
        .get(1)
        .and_then(|f| f.blocks.first())
        .and_then(|b| b.body.first())
        .or_fixture("the declared closure fixture's original constant")?;
    let (ty, func, low, high) = match &constant.inst {
        Inst::Const {
            ty: Ty::Closure(ty),
            value: Constant::Closure { func, captures },
        } => {
            let [low, high] = captures.as_slice() else {
                return Err(FixtureError {
                    context: "runtime closure fixture",
                    message: "expected two original captures".into(),
                });
            };
            (*ty, *func, low.clone(), high.clone())
        }
        _ => {
            return Err(FixtureError {
                context: "runtime closure fixture",
                message: "expected the original typed closure constant".into(),
            });
        }
    };
    let apparent = m
        .closure_type(ty)
        .or_fixture("the declared closure signature")?
        .func;
    let entry = m
        .functions
        .get_mut(1)
        .and_then(|f| f.blocks.first_mut())
        .or_fixture("the runtime closure entry block")?;
    entry.body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::U8,
            value: low,
        })
        .with_result(ValueId::new(0)),
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: high,
        })
        .with_result(ValueId::new(1)),
        InstrNode::new(Inst::MakeClosure {
            ty,
            func,
            captures: vec![ValueId::new(0), ValueId::new(1)],
        })
        .with_result(ValueId::new(2)),
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(16),
        })
        .with_result(ValueId::new(3)),
        InstrNode::new(Inst::CallIndirect {
            callee: ValueId::new(2),
            sig: apparent,
            args: vec![ValueId::new(3)],
            calling_conv: Default::default(),
        })
        .with_result(ValueId::new(4)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(4)],
        }),
    ];
    Ok(m)
}

// ---------- tensor_contract ----------

/// The tensor region's first slice (PKG-U13a): `fn matmul(a: tensor<i32, 2>,
/// b: tensor<i32, 2>) -> tensor<i32, 2>`, whose one value is the integer
/// matrix multiply `tensor_contract tensor<i32, 2> %a, %b batch [] contract
/// [1:0]`. The tensor type sits in the signature, the entry block's
/// parameters and inline on the instruction, so every type walk meets it.
/// The only golden that selects `TENSOR_FORMAT_VERSION`.
pub fn build_tensor_contract() -> Result<Module, FixtureError> {
    let matrix = Ty::Tensor(Box::new(Ty::I32), 2);
    let mut m = Module::new("tensor_contract");
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    });
    let sig = m
        .add_func_type(FuncTy {
            params: vec![matrix.clone(), matrix.clone()],
            returns: vec![matrix.clone()],
            is_vararg: false,
            abi: None,
        })
        .or_fixture("the tensor contraction signature")?;
    let mut f = Function::new(FuncId::new(0), "matmul", sig, BlockId::new(0));
    // The v41 producer rule: a bodied function at v41+ states its codegen
    // license; this golden is affirmatively ungated.
    f.body_gate = Some(trust_ir::BodyGate::Ungated);
    let mut entry = Block::new(BlockId::new(0))
        .with_param(ValueId::new(0), matrix.clone())
        .with_param(ValueId::new(1), matrix.clone());
    entry.body = vec![
        InstrNode::new(Inst::TensorContract {
            ty: matrix,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
            batch: vec![],
            contract: vec![(1, 0)],
        })
        .with_result(ValueId::new(2)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(2)],
        }),
    ];
    f.blocks.push(entry);
    m.try_add_function(f)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

// ---------- tensor_map_reduce_view ----------

/// The tensor region's map, reduce and view (PKG-U13c), chained in one
/// function `fn mrv(a: tensor<i32, 2>, b: tensor<i32, 2>, p: usize, f: i32)
/// -> tensor<i32, 1>`:
///
/// * `%5 = tensor_map tensor<i32, 2> (%0, %1, %4) { add i32 $0, $1; neg i32
///   $3; icmp sgt i32 $4, $2; select i32 $5, $4, $2; trunc i32 $6 to i8;
///   sext i8 $7 to i32 }` with `%4 = const i32 0`: every node kind, a scalar
///   operand, the element `sext(trunc(relu(-(a + b))))`;
/// * `%6 = tensor_reduce add tensor<i32, 1> %5 axes [1] order row_major`:
///   the row sums;
/// * `%7 = tensor_view tensor<i32, 1> %6 params [%2] exprs [src_extent(0),
///   param(0), add($0, $1), coord(0), sub($3, $1)] shape [$2] index [$4] fill
///   %3`: the sums padded on the left by `p` copies of `f`.
///
/// The only golden that selects `TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION`.
pub fn build_tensor_map_reduce_view() -> Result<Module, FixtureError> {
    use trust_ir::{TensorIndexExpr as E, TensorMapNode as N, TensorReduceOp, TensorReduceOrder};
    let matrix = Ty::Tensor(Box::new(Ty::I32), 2);
    let row = Ty::Tensor(Box::new(Ty::I32), 1);
    let mut m = Module::new("tensor_map_reduce_view");
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    });
    let sig = m
        .add_func_type(FuncTy {
            params: vec![matrix.clone(), matrix.clone(), Ty::Usize, Ty::I32],
            returns: vec![row.clone()],
            is_vararg: false,
            abi: None,
        })
        .or_fixture("the tensor map/reduce/view signature")?;
    let mut f = Function::new(FuncId::new(0), "mrv", sig, BlockId::new(0));
    // The v41 producer rule: a bodied function at v41+ states its codegen
    // license; this golden is affirmatively ungated.
    f.body_gate = Some(trust_ir::BodyGate::Ungated);
    let mut entry = Block::new(BlockId::new(0))
        .with_param(ValueId::new(0), matrix.clone())
        .with_param(ValueId::new(1), matrix.clone())
        .with_param(ValueId::new(2), Ty::Usize)
        .with_param(ValueId::new(3), Ty::I32);
    entry.body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(0),
        })
        .with_result(ValueId::new(4)),
        InstrNode::new(Inst::TensorMap {
            ty: matrix,
            args: vec![ValueId::new(0), ValueId::new(1), ValueId::new(4)],
            body: vec![
                N::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I32,
                    lhs: 0,
                    rhs: 1,
                },
                N::UnOp {
                    op: UnOp::Neg,
                    ty: Ty::I32,
                    operand: 3,
                },
                N::ICmp {
                    op: ICmpOp::Sgt,
                    ty: Ty::I32,
                    lhs: 4,
                    rhs: 2,
                },
                N::Select {
                    ty: Ty::I32,
                    cond: 5,
                    then_lane: 4,
                    else_lane: 2,
                },
                N::Cast {
                    op: CastOp::Trunc,
                    src_ty: Ty::I32,
                    dst_ty: Ty::I8,
                    operand: 6,
                },
                N::Cast {
                    op: CastOp::SExt,
                    src_ty: Ty::I8,
                    dst_ty: Ty::I32,
                    operand: 7,
                },
            ],
        })
        .with_result(ValueId::new(5)),
        InstrNode::new(Inst::TensorReduce {
            ty: row.clone(),
            src: ValueId::new(5),
            op: TensorReduceOp::Add,
            axes: vec![1],
            order: TensorReduceOrder::RowMajor,
        })
        .with_result(ValueId::new(6)),
        InstrNode::new(Inst::TensorView {
            ty: row,
            src: ValueId::new(6),
            params: vec![ValueId::new(2)],
            exprs: vec![
                E::SrcExtent(0),
                E::Param(0),
                E::Add(0, 1),
                E::Coord(0),
                E::Sub(3, 1),
            ],
            shape: vec![2],
            index: vec![4],
            fill: Some(ValueId::new(3)),
        })
        .with_result(ValueId::new(7)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(7)],
        }),
    ];
    f.blocks.push(entry);
    m.try_add_function(f)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

// ---------- tensor_gather_scatter ----------

/// The tensor region's gather and scatter (PKG-U13d), chained in one
/// function `fn gs(data: tensor<i32, 2>, rows: tensor<i64, 1>, cols:
/// tensor<u8, 1>, init: tensor<i32, 1>, at: tensor<usize, 1>) ->
/// tensor<i32, 1>`:
///
/// * `%5 = tensor_gather tensor<i32, 1> %0 coords [%1, %2]`: `data` at the
///   `(rows[p], cols[p])` pairs, the two coordinate tensors of different
///   integer element types (one signed, one unsigned);
/// * `%6 = tensor_scatter tensor<i32, 1> %3, %5 coords [%4]`: the gathered
///   values written over a copy of `init` at `at` (`usize`), the
///   row-major-last write winning at a repeated coordinate.
///
/// The only golden that selects `TENSOR_GATHER_SCATTER_FORMAT_VERSION`.
pub fn build_tensor_gather_scatter() -> Result<Module, FixtureError> {
    let tensor = |elem: Ty, rank: u32| Ty::Tensor(Box::new(elem), rank);
    let row = tensor(Ty::I32, 1);
    let mut m = Module::new("tensor_gather_scatter");
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    });
    let params = vec![
        tensor(Ty::I32, 2),
        tensor(Ty::I64, 1),
        tensor(Ty::U8, 1),
        row.clone(),
        tensor(Ty::Usize, 1),
    ];
    let sig = m
        .add_func_type(FuncTy {
            params: params.clone(),
            returns: vec![row.clone()],
            is_vararg: false,
            abi: None,
        })
        .or_fixture("the tensor gather/scatter signature")?;
    let mut f = Function::new(FuncId::new(0), "gs", sig, BlockId::new(0));
    // The v41 producer rule: a bodied function at v41+ states its codegen
    // license; this golden is affirmatively ungated.
    f.body_gate = Some(trust_ir::BodyGate::Ungated);
    let mut entry = Block::new(BlockId::new(0));
    for (i, ty) in (0u32..).zip(params) {
        entry = entry.with_param(ValueId::new(i), ty);
    }
    entry.body = vec![
        InstrNode::new(Inst::TensorGather {
            ty: row.clone(),
            data: ValueId::new(0),
            coords: vec![ValueId::new(1), ValueId::new(2)],
        })
        .with_result(ValueId::new(5)),
        InstrNode::new(Inst::TensorScatter {
            ty: row,
            init: ValueId::new(3),
            src: ValueId::new(5),
            coords: vec![ValueId::new(4)],
        })
        .with_result(ValueId::new(6)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(6)],
        }),
    ];
    f.blocks.push(entry);
    m.try_add_function(f)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

// ---------- tensor_weight_blob ----------

/// Content-addressed weight blobs (PKG-U13e, wire v70, SPEC_RATIFICATIONS
/// §27): two functions over one blob table on an aarch64 target.
///
/// * `fn dot(x: tensor<i32, 1>) -> tensor<i32, 0>`: `%1 = const tensor<i32,
///   1> tensor_blob<W>[3]`, the weights `[1, 2, -1]` named by the SHA-256 of
///   their twelve little-endian bytes, then `%2 = tensor_contract tensor<i32,
///   0> %0, %1 contract [(0, 0)]`, the dot product `x · w`;
/// * `fn raw() -> tensor<u8, 1>`: the SAME twelve bytes as `u8`, named by the
///   same digest, so the table holds them once;
/// * `fn none() -> tensor<i64, 1>`: zero `i64`, named by the digest of the
///   empty byte string (an empty row).
///
/// The only golden that selects `TENSOR_BLOB_FORMAT_VERSION`.
pub fn build_tensor_weight_blob() -> Result<Module, FixtureError> {
    let tensor = |elem: Ty, rank: u32| Ty::Tensor(Box::new(elem), rank);
    let mut m = Module::new("tensor_weight_blob");
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    });
    let weights = m.intern_blob([1i32, 2, -1].iter().flat_map(|w| w.to_le_bytes()).collect());
    let empty = m.intern_blob(Vec::new());
    let blob = |digest, dims: &[u64]| Constant::TensorBlob {
        digest,
        dims: dims.to_vec(),
    };
    let functions: [(&str, Vec<Ty>, Ty, Vec<InstrNode>); 3] = [
        (
            "dot",
            vec![tensor(Ty::I32, 1)],
            tensor(Ty::I32, 0),
            vec![
                InstrNode::new(Inst::Const {
                    ty: tensor(Ty::I32, 1),
                    value: blob(weights, &[3]),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::TensorContract {
                    ty: tensor(Ty::I32, 0),
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                    batch: vec![],
                    contract: vec![(0, 0)],
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(2)],
                }),
            ],
        ),
        (
            "raw",
            vec![],
            tensor(Ty::U8, 1),
            vec![
                InstrNode::new(Inst::Const {
                    ty: tensor(Ty::U8, 1),
                    value: blob(weights, &[12]),
                })
                .with_result(ValueId::new(0)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(0)],
                }),
            ],
        ),
        (
            "none",
            vec![],
            tensor(Ty::I64, 1),
            vec![
                InstrNode::new(Inst::Const {
                    ty: tensor(Ty::I64, 1),
                    value: blob(empty, &[0]),
                })
                .with_result(ValueId::new(0)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(0)],
                }),
            ],
        ),
    ];
    for (i, (name, params, result, body)) in (0u32..).zip(functions) {
        let sig = m
            .add_func_type(FuncTy {
                params: params.clone(),
                returns: vec![result],
                is_vararg: false,
                abi: None,
            })
            .or_fixture("the tensor weight blob signature")?;
        let mut f = Function::new(FuncId::new(i), name, sig, BlockId::new(0));
        // The v41 producer rule: a bodied function at v41+ states its codegen
        // license; this golden is affirmatively ungated.
        f.body_gate = Some(trust_ir::BodyGate::Ungated);
        let mut entry = Block::new(BlockId::new(0));
        for (j, ty) in (0u32..).zip(params) {
            entry = entry.with_param(ValueId::new(j), ty);
        }
        entry.body = body;
        f.blocks.push(entry);
        m.try_add_function(f)
            .or_fixture("Module::try_add_function")?;
    }
    Ok(m)
}

// ---------- nominal_type_origin ----------

/// The v58 nominal identity key (WS3.9): one module carrying BOTH
/// `TypeOrigin` spellings, so a v58 table pins both tags.
///
/// * `Nat` is a Rust ENUM that MIRRORS a Clean inductive, so it carries the
///   **Clean** key — the paired-carrier rule, and the reason the field exists
///   at all;
/// * `Span` is an ordinary Rust STRUCT keyed by its rustc `DefPathHash` plus a
///   digest over the concrete generic arguments (empty here, digested rather
///   than omitted so "no arguments" and "arguments not recorded" cannot
///   collide);
/// * `Unkeyed` carries NO key, which is not a wildcard and not an error: it
///   is what every pre-v58 definition decodes to, and the golden pins that
///   the absent case still costs exactly one byte.
///
/// With `closure_layout`, one of the two goldens whose header word is 58.
pub fn build_nominal_type_origin() -> Result<Module, FixtureError> {
    use trust_ir::ty::TypeOrigin;

    let mut m = Module::new("nominal_type_origin");
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: Default::default(),
    });
    m.add_enum(
        EnumDef::new(
            EnumId::new(0),
            "Nat",
            vec![
                EnumVariant {
                    name: "Zero".into(),
                    fields: vec![],
                    field_names: vec![],
                },
                EnumVariant {
                    name: "Succ".into(),
                    fields: vec![Ty::U64],
                    field_names: vec![],
                },
            ],
        )
        .with_origin(TypeOrigin::Clean {
            decl: "Trust.Nat".into(),
            env_digest: ProofDigest::sha256([0x51; 32]),
        }),
    );
    // Positional fields (no names, no offsets): the text format carries
    // neither until WS4.5, and this fixture pins the ORIGIN clause, so it
    // stays loss-free rather than earning a `TEXT_LOSS_RATCHET` row.
    m.add_struct(
        StructDef {
            id: StructId::new(0),
            name: "Span".into(),
            fields: vec![
                FieldDef {
                    name: String::new(),
                    ty: Ty::U32,
                    offset: None,
                },
                FieldDef {
                    name: String::new(),
                    ty: Ty::U32,
                    offset: None,
                },
            ],
            size: Some(8),
            align: Some(4),
            repr: Default::default(),
            origin: None,
        }
        .with_origin(TypeOrigin::Rust {
            stable_crate_id: 0x0123_4567_89ab_cdef,
            def_path_hash: [
                0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
                0xee, 0xff,
            ],
            args_digest: ProofDigest::sha256([0x62; 32]),
        }),
    );
    m.add_struct(StructDef {
        id: StructId::new(1),
        name: "Unkeyed".into(),
        fields: vec![FieldDef {
            name: String::new(),
            ty: Ty::U8,
            offset: None,
        }],
        size: Some(1),
        align: Some(1),
        repr: Default::default(),
        origin: None,
    });
    let ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![Ty::U32],
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let mut func = Function::new(FuncId::new(0), "span_lo", ft, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(0)),
    );
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    func.blocks.push(entry);
    // A v41+ producer stamps the codegen license (the v41 producer rule,
    // `producer_rule_census`): a NEW golden never joins the bodied tag-0 set.
    func.body_gate = Some(trust_ir::BodyGate::Gated {
        authority: "conformance-fixture".into(),
        evidence: None,
    });
    m.try_add_function(func)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

// ---------- abi_param_facts ----------

/// The v45 per-slot ABI facts (WS3.11, F-054): a C-ABI declaration whose
/// `u8` return carries `zeroext`, whose `(u64, u64)` struct parameter is
/// passed as a `Pair`, plus a `Cast` lane list, an `Ignore` on a `Unit`
/// slot and an `Indirect` `byval` pointer — every `PassMode` tag on the
/// wire, and the return slot record. The ONLY golden whose `FuncAttrs`
/// carries a return slot.
pub fn build_abi_param_facts() -> Result<Module, FixtureError> {
    use trust_ir::{ArgExt, PassMode};

    let mut m = Module::new("abi_param_facts");
    m.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("sysv64".into()),
        struct_passing: Default::default(),
    });
    // The two-lane aggregate is a TUPLE, not a struct: the fixture is about
    // the SLOT facts, and struct field names / offsets are text-lossy until
    // WS4.5 carries them — a loss-free golden is what lets `#ret_attrs`
    // round-trip through the corpus
    // (`every_text_directive_round_trips_through_the_corpus`).
    let pair = Ty::Tuple(vec![Ty::U64, Ty::U64]);
    let pair_ty = m.add_type(pair.clone()).or_fixture("Module::add_type")?;
    m.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
        tuple_type: pair_ty,
        size: 16,
        align: 8,
        field_offsets: vec![0, 8],
    });
    let ft = m
        .add_func_type(FuncTy {
            params: vec![pair.clone(), Ty::Unit, Ty::Ptr],
            returns: vec![Ty::U8],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let mut decl = Function::new(FuncId::new(0), "c_abi_decl", ft, BlockId::new(0));
    decl.attrs.params = vec![
        ParamAttrs {
            pass: Some(PassMode::Pair),
            ..ParamAttrs::default()
        },
        ParamAttrs {
            pass: Some(PassMode::Ignore),
            ..ParamAttrs::default()
        },
        ParamAttrs {
            byval: true,
            pass: Some(PassMode::Indirect { on_stack: true }),
            ..ParamAttrs::default()
        },
    ];
    decl.attrs.ret = ParamAttrs {
        ext: ArgExt::ZeroExt,
        ..ParamAttrs::default()
    };
    m.try_add_function(decl)
        .or_fixture("Module::try_add_function")?;

    let cast_ft = m
        .add_func_type(FuncTy {
            params: vec![pair, Ty::I16],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let mut cast = Function::new(FuncId::new(1), "coerced", cast_ft, BlockId::new(0));
    cast.attrs.params = vec![
        ParamAttrs {
            pass: Some(PassMode::Cast {
                pieces: vec![Ty::U64, Ty::U64],
            }),
            ..ParamAttrs::default()
        },
        ParamAttrs {
            ext: ArgExt::SignExt,
            pass: Some(PassMode::Direct),
            ..ParamAttrs::default()
        },
    ];
    m.try_add_function(cast)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

// ---------- effect_summaries ----------

/// The v59 typed effect summaries and world epochs (WS1.14, F-013): a writer
/// `set(p, q)` whose summary lists exactly `*param0` and the global `COUNTER`
/// and whose (unproved) ensures clause relates the world at EXIT to the world
/// at ENTRY (`WorldPost` / `WorldPre`); a pure `add`; and a `caller` of an
/// unsummarized external declaration, whose honest summary is the top one.
/// The ONLY golden whose header word is the effect-summary version; validates
/// clean (every body honours its summary). Text carries all of it (the
/// `; #effects:` directive and the `world_pre` / `world_post` places).
pub fn build_effect_summaries() -> Result<Module, FixtureError> {
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
    use trust_ir::{EffectPlace, EffectSet, EffectSummary, FunctionSummary};

    let ptr = || Ty::PtrMut(Box::new(Ty::U64));
    let mut m = Module::new("effect_summaries");
    // A body-less external declaration is a native-code boundary: the
    // validator requires the target it binds against.
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    m.globals.push(Global {
        name: "COUNTER".into(),
        ty: Ty::U64,
        mutable: true,
        initializer: Some(Constant::Int(0)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    let two_ptrs = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![ptr(), ptr()],
            returns: vec![],
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let binary = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::U64, Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let one_ptr = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![ptr()],
            returns: vec![],
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;

    // set(p, q) { *p = 7; COUNTER = 7 }
    let heap = || {
        ClauseSort::Array(
            Box::new(ClauseSort::BitVec(64)),
            Box::new(ClauseSort::BitVec(64)),
        )
    };
    let mut frame = ProofFormula::smtlib2(
        "(= (select after #x0000000000000000) (select before #x0000000000000000))",
        "Bool",
    );
    frame.bindings = vec![
        (
            "before".to_string(),
            ClauseBinding {
                sort: heap(),
                place: ClausePlace::WorldPre,
            },
        ),
        (
            "after".to_string(),
            ClauseBinding {
                sort: heap(),
                place: ClausePlace::WorldPost,
            },
        ),
    ];
    let mut set = Function::new(FuncId::new(0), "set", two_ptrs, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), ptr()));
    entry.params.push((ValueId::new(1), ptr()));
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(2)),
    );
    entry.body.push(InstrNode::new(Inst::Store {
        ty: Ty::U64,
        ptr: ValueId::new(0),
        value: ValueId::new(2),
        volatile: false,
        align: None,
    }));
    entry.body.push(
        InstrNode::new(Inst::GlobalAddr {
            global: GlobalId::new(0),
        })
        .with_result(ValueId::new(3)),
    );
    entry.body.push(InstrNode::new(Inst::Store {
        ty: Ty::U64,
        ptr: ValueId::new(3),
        value: ValueId::new(2),
        volatile: false,
        align: None,
    }));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    set.blocks.push(entry);
    set.body_gate = Some(trust_ir::BodyGate::Ungated);
    set.summary = Some(
        FunctionSummary::new()
            .with_params(vec!["p".to_string(), "q".to_string()])
            .ensuring(frame)
            .with_effects(EffectSummary::pure().writing(EffectSet::of([
                EffectPlace::ParamPointee { index: 0 },
                EffectPlace::Global(GlobalId::new(0)),
            ]))),
    );
    m.try_add_function(set)
        .or_fixture("Module::try_add_function")?;

    // add(x, y) = x + y, pure.
    let mut add = Function::new(FuncId::new(1), "add", binary, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::U64));
    entry.params.push((ValueId::new(1), Ty::U64));
    entry.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U64,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(2)),
    );
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    add.blocks.push(entry);
    add.body_gate = Some(trust_ir::BodyGate::Ungated);
    add.summary = Some(FunctionSummary::new().with_effects(EffectSummary::pure()));
    m.try_add_function(add)
        .or_fixture("Module::try_add_function")?;

    // ext(p): an external declaration with NO summary — havoc at a call.
    m.try_add_function(Function::new(
        FuncId::new(2),
        "ext",
        one_ptr,
        BlockId::new(0),
    ))
    .or_fixture("Module::try_add_function")?;

    // caller(p) { ext(p) }: the only honest summary is the top one.
    let mut caller = Function::new(FuncId::new(3), "caller", one_ptr, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), ptr()));
    entry.body.push(InstrNode::new(Inst::Call {
        callee: FuncId::new(2),
        args: vec![ValueId::new(0)],
    }));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    caller.blocks.push(entry);
    caller.body_gate = Some(trust_ir::BodyGate::Ungated);
    caller.summary = Some(FunctionSummary::new().with_effects(EffectSummary::top()));
    m.try_add_function(caller)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

// ---------- spec_carrier ----------

/// The v46 typed spec carrier (WS4.14, F-014): the `ring` machine with
/// `SpecVar.sort` on every variable, a typed `BoundedSeq` invariant, the five
/// `TemporalForm`s (an `Always`, an `Eventually`, a `LeadsTo`, a `WeakFair`
/// with a primed action relation, a `StrongFair` with none), a
/// `clean-theorem` proof binding, and a `Liveness` obligation whose typed
/// bindings name the machine's state and whose `spec` backref names the
/// property it discharges. The ONLY golden whose header word is 46. Design-only
/// (a Linked machine would need anchors, which are not what this pins) and
/// validates clean. Text is `#lossy` (the carrier has no text spelling; WS4.4).
pub fn build_spec_carrier() -> Result<Module, FixtureError> {
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort, SpecObligationRef};
    use trust_ir::{
        ProofKind, SpecInvariant, SpecModule, SpecProof, SpecTemporal, SpecVar, TemporalForm,
    };

    let bind = |name: &str, sort: ClauseSort, place: ClausePlace| {
        (name.to_string(), ClauseBinding { sort, place })
    };
    let seq = |place: ClausePlace| bind("seq", ClauseSort::Int, place);
    let clause = |text: &str, bindings: Vec<(String, ClauseBinding)>| {
        let mut f = ProofFormula::smtlib2(text, "Bool");
        f.bindings = bindings;
        f
    };
    let bounded = || clause("(<= seq 7)", vec![seq(ClausePlace::SpecVar { index: 0 })]);
    let full = || clause("(= seq 7)", vec![seq(ClausePlace::SpecVar { index: 0 })]);
    let nonempty = || {
        clause(
            "(not empty)",
            vec![bind(
                "empty",
                ClauseSort::Bool,
                ClausePlace::SpecVar { index: 1 },
            )],
        )
    };
    let push = || {
        clause(
            "(= seq_next (+ seq 1))",
            vec![
                seq(ClausePlace::SpecVar { index: 0 }),
                bind(
                    "seq_next",
                    ClauseSort::Int,
                    ClausePlace::SpecVarNext { index: 0 },
                ),
            ],
        )
    };

    let mut m = Module::new("spec_carrier");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let mut func = Function::new(FuncId::new(0), "identity", ft, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::I32));
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    func.blocks.push(entry);
    m.try_add_function(func)
        .or_fixture("Module::try_add_function")?;

    let mut ring = SpecModule::design_only("ring");
    ring.vars = vec![
        SpecVar::new("seq", "0..7").with_sort(ClauseSort::Int),
        SpecVar::new("empty", "Bool").with_sort(ClauseSort::Bool),
    ];
    ring.actions = vec!["Push".to_string(), "Pop".to_string()];
    ring.invariants = vec![
        SpecInvariant::new("BoundedSeq", "(<= seq 7)").with_typed(bounded()),
        // An invariant with the surface text only: `typed` NOT RECORDED.
        SpecInvariant::new("Untyped", "(>= seq 0)"),
    ];
    ring.temporal = vec![
        SpecTemporal::new("AlwaysBounded", TemporalForm::Always(bounded())),
        SpecTemporal::new("EventuallyFull", TemporalForm::Eventually(full())),
        SpecTemporal::new(
            "NonEmptyLeadsToFull",
            TemporalForm::LeadsTo(nonempty(), full()),
        ),
        SpecTemporal::new(
            "PushFair",
            TemporalForm::WeakFair {
                action: "Push".to_string(),
                relation: Some(push()),
            },
        ),
        SpecTemporal::new(
            "PopFair",
            TemporalForm::StrongFair {
                action: "Pop".to_string(),
                relation: None,
            },
        ),
    ];
    ring.proofs = vec![
        SpecProof {
            machine: "ring".to_string(),
            action: "Push".to_string(),
            proof_name: "ring_push_refines".to_string(),
            kind: ProofKind::CleanTheorem {
                name: "Ring.push_refines".to_string(),
            },
        },
        SpecProof {
            machine: "ring".to_string(),
            action: "Pop".to_string(),
            proof_name: "ring_pop_refines".to_string(),
            kind: ProofKind::Kani,
        },
    ];
    m.spec_modules.push(ring);

    let mut liveness = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Liveness,
        ProofStatus::Pending,
        "eventually the ring is full",
    )
    .with_formula(full());
    liveness.spec = Some(SpecObligationRef::new("ring", "EventuallyFull"));
    m.proof_obligations.push(liveness);
    Ok(m)
}

// ---------- ty_handle ----------

/// The v43 nominal opaque runtime handle as a producer would actually emit
/// it: the `trust_bignum::Nat` entry points this body CALLS, declared through
/// `ModuleBuilder::declare_handle_runtime_roles` (bodyless C `External`, exact
/// pinned signatures, `display_path` def-paths) and one transport body,
/// `pred(x) = if is_zero(x) { x } else { sub(x, from_u64(1)) }` — a call
/// result copied across a branch edge and returned, never cast, loaded,
/// stored or compared. Header 43; validates clean under the pinned registry.
///
/// The role list is EXPLICIT, not `declare_handle_runtime`, and that is
/// load-bearing for this golden: the pinned row grew a fifth `drop` entry
/// point when the release entry point was ratified, and declaring the whole
/// row would have added a fifth `External` declaration plus a void `FuncTy`
/// to these bytes. A producer declares the symbols it calls, this body calls
/// four, and the fixture's bytes are therefore unchanged by a pin-table
/// addition that this module does not use. `drop`'s validator rules are
/// covered by `trust-ir-build/tests/handle_types.rs`; the release call
/// introduces no wire construct a `Call` to a void-returning declaration does
/// not already exercise.
pub fn build_ty_handle() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new_with_target_info(
        // FROZEN GOLDEN CONTENT, not a file name: this string is inside the
        // `ty_handle.*` golden bytes. The goldens were renamed to a feature name
        // (wire-allocations.toml: names, not numbers); the bytes were not touched.
        "ty_handle_v43",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: Default::default(),
        },
    );
    let pin = trust_ir_build::TRUSTED_HANDLE_RUNTIMES
        .iter()
        .find(|pin| pin.runtime == "trust_bignum::Nat")
        .or_fixture("the v1 Nat row is pinned")?;
    let decls = mb
        .declare_handle_runtime_roles(pin, &["from_u64", "add", "sub", "is_zero"])
        .or_fixture("fresh module has no conflicting declaration")?;
    let h = decls.handle.clone();
    let from_u64 = decls
        .entry("from_u64")
        .or_fixture("the pinned Nat row declares `from_u64`")?;
    let sub = decls
        .entry("sub")
        .or_fixture("the pinned Nat row declares `sub`")?;
    let is_zero = decls
        .entry("is_zero")
        .or_fixture("the pinned Nat row declares `is_zero`")?;
    let unop = mb.add_func_type(vec![h.clone()], vec![h.clone()]);
    let mut m = mb.build().or_fixture("ModuleBuilder::build")?;

    let mut pred = Function::new(FuncId::new(4), "pred", unop, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), h.clone()));
    entry.body.push(
        InstrNode::new(Inst::Call {
            callee: is_zero,
            args: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(1)),
    );
    entry.body.push(InstrNode::new(Inst::CondBr {
        cond: ValueId::new(1),
        then_target: BlockId::new(1),
        then_args: vec![],
        else_target: BlockId::new(2),
        else_args: vec![],
    }));
    let mut zero = Block::new(BlockId::new(1));
    zero.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    let mut step = Block::new(BlockId::new(2));
    step.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(1),
        })
        .with_result(ValueId::new(2)),
    );
    step.body.push(
        InstrNode::new(Inst::Call {
            callee: from_u64,
            args: vec![ValueId::new(2)],
        })
        .with_result(ValueId::new(3)),
    );
    step.body.push(
        InstrNode::new(Inst::Call {
            callee: sub,
            args: vec![ValueId::new(0), ValueId::new(3)],
        })
        .with_result(ValueId::new(4)),
    );
    step.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(4)],
    }));
    pred.blocks = vec![entry, zero, step];
    pred.body_gate = Some(trust_ir::BodyGate::Gated {
        authority: "conformance-fixture".into(),
        evidence: None,
    });
    m.try_add_function(pred)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

// ---------- ty_composite ----------

/// Every composite / reference `Ty` variant appears on a function or
/// block signature. Referenced definitions (`StructDef`, `EnumDef`,
/// `RecordDef`, `ClosureTy`) live on the module's side tables.
pub fn build_ty_composite() -> Result<Module, FixtureError> {
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
        origin: None,
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
        origin: None,
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
    let inner_ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;

    // Closure: (I32)->I32 with captures [I64, F64]
    let closure = m
        .add_closure_type(ClosureTy {
            func: inner_ft,
            captures: vec![Ty::I64, Ty::F64],
        })
        .or_fixture("Module::add_closure_type")?;

    // A Ty interned in `module.types` (used by validating tooling as a
    // canonical type reference — see `Ty::Array(TyId, u64)` and
    // `Ty::Sequence(TyId)` below).
    let i32_interned = m.add_type(Ty::I32).or_fixture("Module::add_type")?;

    // The "carrier" function signature walks every composite / ref variant.
    let composite_ft = m
        .add_func_type(FuncTy {
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
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;

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
    m.try_add_function(func)
        .or_fixture("Module::try_add_function")?;

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
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    m.globals.push(Global {
        name: "G_SEQ".into(),
        ty: Ty::Sequence(i32_interned),
        mutable: false,
        initializer: Some(Constant::Sequence(vec![Constant::Int(1), Constant::Int(2)])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    m.globals.push(Global {
        name: "G_ARRAY".into(),
        ty: Ty::Array(i32_interned, 2),
        mutable: false,
        initializer: Some(Constant::Array(vec![Constant::Int(1), Constant::Int(2)])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    m.globals.push(Global {
        name: "G_SET".into(),
        ty: Ty::Set(i32_interned, SetRepr::Boxed),
        mutable: false,
        initializer: Some(Constant::Set(vec![Constant::Int(1), Constant::Int(2)])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
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
        section: None,
        visibility: Default::default(),
        retained: false,
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
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    m.globals.push(Global {
        name: "G_FNDEF".into(),
        ty: Ty::Func(composite_ft),
        mutable: false,
        initializer: Some(Constant::FnDef(FuncId::new(0))),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    m.globals.push(Global {
        name: "G_PHANTOM".into(),
        ty: Ty::Unit,
        mutable: false,
        initializer: Some(Constant::PhantomData),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });

    Ok(m)
}

// ---------- inst_arithmetic ----------

/// Covers `Inst::SeqMapAddK` (the Aeneas loop forward function `for x in &mut l
/// { *x += k }`, `loopFwd`) over a `&mut Sequence<i32>`. Guards wire-format
/// coverage of the give-back loop instruction across all four formats.
pub fn build_inst_seq_map() -> Result<Module, FixtureError> {
    let mut m = Module::new("inst_seq_map");
    let i32_interned = m.add_type(Ty::I32).or_fixture("Module::add_type")?;
    let seq_ty = Ty::Sequence(i32_interned);
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::RefMut(Box::new(seq_ty.clone()))],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
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
    m.try_add_function(func)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

/// Covers `Inst::SeqMapNot` (the boolean-flip loop `for b in &mut l { *b = !*b }`,
/// `loopFwd` over a `&mut Sequence<bool>`) — the second element-op loop instruction.
pub fn build_inst_seq_map_not() -> Result<Module, FixtureError> {
    let mut m = Module::new("inst_seq_map_not");
    let bool_interned = m.add_type(Ty::Bool).or_fixture("Module::add_type")?;
    let seq_ty = Ty::Sequence(bool_interned);
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::RefMut(Box::new(seq_ty.clone()))],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
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
    m.try_add_function(func)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

/// Covers `Inst::SeqMap` (the GENERAL element-op loop `for x in &mut l { *x =
/// fwd(x) }` with a first-class element `FuncId` — designs/2026-06-30-general-
/// seqmap-instruction.md). The module carries both the loop function and the
/// single-`&mut` element function `incr_elem(x: &mut i32) { *x += 1 }`, so the
/// fixture also exercises the FuncId operand class on a map instruction.
pub fn build_inst_seq_map_general() -> Result<Module, FixtureError> {
    let mut m = Module::new("inst_seq_map_general");
    let i32_interned = m.add_type(Ty::I32).or_fixture("Module::add_type")?;
    let seq_ty = Ty::Sequence(i32_interned);
    let loop_ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::RefMut(Box::new(seq_ty.clone()))],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let elem_ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::RefMut(Box::new(Ty::I32))],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;

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
    m.try_add_function(func)
        .or_fixture("Module::try_add_function")?;

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
    m.try_add_function(elem)
        .or_fixture("Module::try_add_function")?;

    Ok(m)
}

/// Covers every `BinOp`, every `UnOp`, every `OverflowOp`,
/// every `ICmpOp`, every `FCmpOp`, the validation-safe `CastOp`s,
/// and `Copy`/`Select`.
pub fn build_inst_arithmetic() -> Result<Module, FixtureError> {
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

    mb.build().or_fixture("ModuleBuilder::build")
}

// ---------- inst_vector ----------

/// Covers fixed-width vector arithmetic, vector `icmp` masks, vector
/// `select`, and vector load/store through every public conformance format.
pub fn build_inst_vector() -> Result<Module, FixtureError> {
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

    mb.build().or_fixture("ModuleBuilder::build")
}

// ---------- inst_vector_dialect ----------

/// Covers the portable `vector.*` dialect contract separately from the
/// generic opaque dialect fixture.
pub fn build_inst_vector_dialect() -> Result<Module, FixtureError> {
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
        .or_fixture("valid <4 x i32> lane pack")?;
    let extracted_v4 = fb
        .v4_i32_extract_lane(packed_v4, 2)
        .or_fixture("valid <4 x i32> lane extract")?;
    let inserted_v4 = fb
        .v4_i32_insert_lane(v4_seed, 1, v4_replacement)
        .or_fixture("valid <4 x i32> lane insert")?;

    let packed_v2 = fb
        .v2_i64_pack_lanes([wide0, wide1])
        .or_fixture("valid <2 x i64> lane pack")?;
    let extracted_v2 = fb
        .v2_i64_extract_lane(packed_v2, 1)
        .or_fixture("valid <2 x i64> lane extract")?;
    let inserted_v2 = fb
        .v2_i64_insert_lane(v2_seed, 0, v2_replacement)
        .or_fixture("valid <2 x i64> lane insert")?;

    let v4_mask = fb.icmp(ICmpOp::Sgt, Ty::v4_i32(), inserted_v4, packed_v4);
    let v4_bits = fb
        .v4_bool_mask_to_i32_bits(v4_mask)
        .or_fixture("valid <4 x bool> mask compaction")?;
    let v2_mask = fb.icmp(ICmpOp::Eq, Ty::v2_i64(), inserted_v2, packed_v2);
    let v2_bits = fb
        .v2_bool_mask_to_i64_bits(v2_mask)
        .or_fixture("valid <2 x bool> mask compaction")?;
    let v8_bits = fb
        .v8_bool_mask_to_i32_bits(v8_mask)
        .or_fixture("valid <8 x bool> mask compaction")?;
    let v16_bits = fb
        .v16_bool_mask_to_i32_bits(v16_mask)
        .or_fixture("valid <16 x bool> mask compaction")?;

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

    mb.build().or_fixture("ModuleBuilder::build")
}

// ---------- inst_vector_crosslane ----------

/// Covers the cross-lane `vector.*` ops (`reduce` / `shuffle` / `fma`) added
/// for the fast-4 "much faster metadata" leg. These ops have no operational
/// lowering into other dialect ops: the reference interpreter executes them
/// directly and a backend selects them to horizontal-reduce / permute / FMA
/// instructions. The fixture pins their wire form so downstream consumers can
/// detect payload drift independently from the structural lane ops above.
pub fn build_inst_vector_crosslane() -> Result<Module, FixtureError> {
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
        .or_fixture("valid <4 x i32> reduce-add")?;
    let reduced_or = fb
        .vector_reduce(Ty::v2_i64(), v2, ReduceKind::Or)
        .or_fixture("valid <2 x i64> reduce-or")?;

    let shuffled_v4 = fb
        .vector_shuffle(Ty::v4_i32(), v4, [3u8, 2, 1, 0])
        .or_fixture("valid <4 x i32> reverse shuffle")?;
    let shuffled_v2 = fb
        .vector_shuffle(Ty::v2_i64(), v2, [1u8, 1])
        .or_fixture("valid <2 x i64> broadcast shuffle")?;

    let fma_v4 = fb
        .vector_fma(Ty::v4_f32(), v4f, v4f, v4f)
        .or_fixture("valid <4 x f32> fma")?;
    let fma_v2 = fb
        .vector_fma(Ty::v2_f64(), v2f, v2f, v2f)
        .or_fixture("valid <2 x f64> fma")?;

    fb.ret(vec![
        reduced_add,
        reduced_or,
        shuffled_v4,
        shuffled_v2,
        fma_v4,
        fma_v2,
    ]);
    fb.build();

    mb.build().or_fixture("ModuleBuilder::build")
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

pub fn build_vector_mask_oracles() -> Result<Vec<VectorMaskOracleFixture>, FixtureError> {
    Ok(vec![
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
    ])
}

// ---------- inst_memory ----------

/// Covers Load, Store, Alloca, GEP, Dealloc, ExtractField, InsertField,
/// ExtractElement, InsertElement, NullPtr, Undef, Const.
pub fn build_inst_memory() -> Result<Module, FixtureError> {
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
        section: None,
        visibility: Default::default(),
        retained: false,
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

    let mut m = mb.build().or_fixture("ModuleBuilder::build")?;
    // Intern `i32` at TyId::new(0) so `Ty::Array(TyId::new(0), 4)`
    // above is well-formed when validators walk the module.
    m.types.push(Ty::I32);
    Ok(m)
}

// ---------- inst_control ----------

/// Covers Br, CondBr, Switch, Return, Unreachable, Call, CallIndirect,
/// Assume, Assert.
pub fn build_inst_control() -> Result<Module, FixtureError> {
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

    mb.build().or_fixture("ModuleBuilder::build")
}

// ---------- inst_atomic ----------

/// Covers AtomicLoad, AtomicStore, AtomicRMW (all 10 RMW sub-ops), CmpXchg,
/// Fence. Every `Ordering` variant appears (the `Fence` sweep carries all
/// five); the load/store sweeps carry only the orderings LEGAL for their
/// operation, for the reason spelled out at the sweep itself.
pub fn build_inst_atomic() -> Result<Module, FixtureError> {
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

    // One AtomicLoad per LEGAL load ordering, one AtomicStore per LEGAL store
    // ordering.
    //
    // Deliberately not the same five-ordering sweep as the fences above: an
    // acquire constrains a READ and a release constrains a WRITE, so
    // `AtomicLoad { Release | AcqRel }` and `AtomicStore { Acquire | AcqRel }`
    // name a fence half the instruction does not have. The Lean model
    // (`isValidLoadOrdering` / `isValidStoreOrdering`), trust-cg's adapter, and
    // now `validate_module` each refuse them independently — and an invalid
    // module is not a wire-format contract, so the corpus must not pin one.
    // Every `Ordering` wire tag stays covered by the fence sweep above.
    for ord in [Ordering::Relaxed, Ordering::Acquire, Ordering::SeqCst] {
        let _ = fb.atomic_load(Ty::I64, ptr, ord);
    }
    for ord in [Ordering::Relaxed, Ordering::Release, Ordering::SeqCst] {
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

    mb.build().or_fixture("ModuleBuilder::build")
}

// ---------- inst_borrow_arc ----------

/// Covers Borrow, BorrowMut, EndBorrow, Retain, Release, IsUnique.
pub fn build_inst_borrow_arc() -> Result<Module, FixtureError> {
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

    mb.build().or_fixture("ModuleBuilder::build")
}

// ---------- inst_binding_frames ----------

/// Covers OpenFrame, BindSlot, LoadSlot, CloseFrame — binding frame
/// quartet used by quantifier lowering (see design doc §R4).
///
/// The canonical text parser now round-trips these instructions, so this
/// fixture asserts all four goldens (binary / text / JSON / MessagePack)
/// like every other fixture.
pub fn build_inst_binding_frames() -> Result<Module, FixtureError> {
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

    mb.build().or_fixture("ModuleBuilder::build")
}

// ---------- inst_dialect ----------

/// Covers `Inst::DialectOp` / `DialectInst` with all `AttrValue`
/// variants, exercising opaque round-trip of a dialect payload.
pub fn build_inst_dialect() -> Result<Module, FixtureError> {
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
    mb.build().or_fixture("ModuleBuilder::build")
}

// ---------- proof_annotations ----------

/// Covers every `ProofAnnotation` variant (including every `Divergence`
/// case in `DivergenceClass`), every `ObligationKind`, every
/// `ProofStatus`, and every `ProofEvidence` variant.
pub fn build_proof_annotations() -> Result<Module, FixtureError> {
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
    fb.add_function_proof(ProofAnnotation::InBounds);
    fb.add_function_proof(ProofAnnotation::NotNull);
    fb.add_function_proof(ProofAnnotation::ValidBorrow);
    fb.add_function_proof(ProofAnnotation::UniqueBorrow);
    fb.add_function_proof(ProofAnnotation::SharedBorrow);
    fb.add_function_proof(ProofAnnotation::ValidDealloc);
    fb.add_function_proof(ProofAnnotation::NoOverflow);
    fb.add_function_proof(ProofAnnotation::NoWrap);
    fb.add_function_proof(ProofAnnotation::DivNonZero);
    fb.add_function_proof(ProofAnnotation::ShiftInRange);
    fb.add_function_proof(ProofAnnotation::Wrapping);
    fb.add_function_proof(ProofAnnotation::BranchWeights(vec![7, 1]));
    fb.add_function_proof(ProofAnnotation::Pure);
    fb.add_function_proof(ProofAnnotation::Terminates);
    fb.add_function_proof(ProofAnnotation::Deterministic);
    fb.add_function_proof(ProofAnnotation::Associative);
    fb.add_function_proof(ProofAnnotation::Commutative);
    fb.add_function_proof(ProofAnnotation::DataRaceFree);
    fb.add_function_proof(ProofAnnotation::AtomicOrdering(Ordering::Relaxed));
    fb.add_function_proof(ProofAnnotation::AtomicOrdering(Ordering::Acquire));
    fb.add_function_proof(ProofAnnotation::AtomicOrdering(Ordering::Release));
    fb.add_function_proof(ProofAnnotation::AtomicOrdering(Ordering::AcqRel));
    fb.add_function_proof(ProofAnnotation::AtomicOrdering(Ordering::SeqCst));
    fb.add_function_proof(ProofAnnotation::BoundedOutput { lo: -1.0, hi: 1.0 });
    fb.add_function_proof(ProofAnnotation::Monotonic);
    fb.add_function_proof(ProofAnnotation::NoAlias);
    fb.add_function_proof(ProofAnnotation::Aligned(16));
    fb.add_function_proof(ProofAnnotation::NoPanic);
    fb.add_function_proof(ProofAnnotation::NoUndef);
    fb.add_function_proof(ProofAnnotation::ReadonlyTable);
    fb.add_function_proof(ProofAnnotation::AppendOnlyBuffer);
    fb.add_function_proof(ProofAnnotation::AtomicSetInsert);
    fb.add_function_proof(ProofAnnotation::ParallelMap);
    fb.add_function_proof(ProofAnnotation::BoundedLoop(1024));
    fb.add_function_proof(ProofAnnotation::DivergenceClass(Divergence::Uniform));
    fb.add_function_proof(ProofAnnotation::DivergenceClass(Divergence::Low));
    fb.add_function_proof(ProofAnnotation::DivergenceClass(Divergence::High));
    fb.add_function_proof(ProofAnnotation::Custom(ProofTag::new(42)));
    // fast-3 value facts (finding D): both i128/u128 payloads must round-trip
    // through every format, including text.
    fb.add_function_proof(ProofAnnotation::ValueRange {
        lo: i128::MIN,
        hi: i128::MAX,
    });
    fb.add_function_proof(ProofAnnotation::KnownBits {
        zeros: 0x00FF_00FF_00FF_00FF,
        ones: 0xFF00_0000_0000_0000,
    });
    fb.build();

    let mut m = mb.build().or_fixture("ModuleBuilder::build")?;

    // `Module::add_function` (via `fb.build()`) synthesized one obligation per
    // claim-kind on the carrier (roadmap §1.1); number the explicit corpus
    // table after them so ids stay unique. The ids come from the core's one
    // fresh-id rule (`Module::fresh_obligation_ids`: one past the highest,
    // refused — never wrapped — at `u32::MAX`); the first one taken is the
    // base the old code called `synth_base`, so every id and golden byte is
    // unchanged (r11 item 8).
    let mut ids = m.fresh_obligation_ids();
    let synth_base = ids
        .peek()
        .or_fixture("the obligation table leaves a fresh ProofId")?;
    let mut second_explicit = None;

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
    for kind in kinds {
        for status in statuses {
            let id = ids
                .take()
                .or_fixture("the explicit table fits the ProofId space")?;
            if second_explicit.is_none() && id != synth_base {
                second_explicit = Some(id);
            }
            m.proof_obligations.push(ProofObligation {
                id,
                kind: kind.clone(),
                status,
                description: format!("{kind:?}/{status:?}"),
                formula: (id == synth_base).then(|| ProofFormula::smtlib2("(> x 0)", "Bool")),
                // B4: scope the first explicit obligation to the carrier
                // function so the `function <id>` text clause is exercised by
                // the corpus (finding C) together with a formula (the
                // formula-and-function-present pairing keeps the positional
                // MessagePack layout exercised end-to-end).
                function: (id == synth_base).then(|| FuncId::new(0)),
                source: None,
                site: None,
                spec: None,
            });
        }
    }
    // fast-1: proof-backed annotation referencing a Discharged obligation (the
    // second explicit entry, `Precondition/Discharged`). Attached post-build so
    // the referenced id can be computed from the synthesized base.
    let carrier = m
        .functions
        .first_mut()
        .or_fixture("the proof-annotation carrier function")?;
    carrier.proofs.push(ProofAnnotation::ProofRef(
        second_explicit.or_fixture("the explicit table has more than one row")?,
    ));
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
            // v41: the LOCAL form. Its wire encoding (tag 6, two varints) is
            // byte-identical to the pre-v41 spelling, which is what keeps this
            // fixture's binary golden stable across the widening.
            external: None,
        },
    ];
    for (i, ev) in certs.into_iter().enumerate() {
        m.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(i as u32),
            prover: format!("prover_{i}"),
            evidence: ev,
            assurance: None,
        });
    }
    Ok(m)
}

// ---------- proof_diagnostics ----------

/// Diagnostics + debug-info surface: a populated `Module::files` table,
/// spanned instructions, and the `Module::obligation_diagnostics` sidecar —
/// one located error with a machine-readable detail, one located warning in a
/// second file, and one location-less note WITH detail. The last shape is the
/// R3 #5 positional-MessagePack hazard (a skipped non-trailing `location`
/// shifted `detail` into its slot), pinned here byte-golden. Instruction
/// spans ride the per-node `; #loc:` clause in text (the corpus harness's
/// old `normalize_text_lossy_fields` erasure is gone); the
/// binary/JSON/MessagePack goldens pin them exactly.
pub fn build_proof_diagnostics() -> Result<Module, FixtureError> {
    let mut m = Module::new("proof_diagnostics");
    let main_rs = m
        .intern_file("src/main.rs")
        .or_fixture("Module::intern_file")?;
    let lib_rs = m
        .intern_file("src/lib.rs")
        .or_fixture("Module::intern_file")?;

    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
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
    m.try_add_function(func)
        .or_fixture("Module::try_add_function")?;

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
    Ok(m)
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
        assurance: None,
    }
}

/// Single-stage Trust proof handoff: one verifier run discharges one
/// obligation and records a replay identity.
pub fn build_proof_lineage_single_stage() -> Result<ProofLineageFixture, FixtureError> {
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
    node.certificates.push(
        certificates
            .first()
            .or_fixture("the stage certificate")?
            .lineage_ref(),
    );
    node.replay = Some(
        ProofReplayIdentity::new(
            "trust-stage2",
            "trust verify --emit-trust_ir-proof src/lib.trust",
        )
        .with_transcript_digest(trust_ir_digest("trust.transcript", b"single-stage-ok")),
    );

    Ok(ProofLineageFixture {
        manifest: ProofLineageManifest {
            schema_version: ProofLineageManifest::SCHEMA_VERSION,
            nodes: vec![node],
            roots: vec![ProofLineageId::new(0)],
        },
        obligations,
        certificates,
    })
}

/// Multi-stage Trust -> TrustIr -> ay -> TrustCg composition fixture. The
/// source/target digests chain across dependencies so `validate()` rejects
/// any stale intermediate artifact.
pub fn build_proof_lineage_multi_stage() -> Result<ProofLineageFixture, FixtureError> {
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
    frontend.certificates.push(
        certificates
            .first()
            .or_fixture("the frontend certificate")?
            .lineage_ref(),
    );

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
    lowering.certificates.push(
        certificates
            .get(1)
            .or_fixture("the lowering certificate")?
            .lineage_ref(),
    );
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
    backend.certificates.push(
        certificates
            .get(2)
            .or_fixture("the backend certificate")?
            .lineage_ref(),
    );
    backend.depends_on.push(ProofLineageId::new(1));

    Ok(ProofLineageFixture {
        manifest: ProofLineageManifest {
            schema_version: ProofLineageManifest::SCHEMA_VERSION,
            nodes: vec![frontend, lowering, backend],
            roots: vec![ProofLineageId::new(2)],
        },
        obligations,
        certificates,
    })
}

// ---------- native verification bundle fixtures ----------

pub struct NativeBundleFixture {
    pub bundle: NativeVerificationBundle,
}

/// tRust-produced native verification bundle. This pins the typed request
/// boundary used by TrustVc, TrustMc, and TrustWp without introducing a stringly
/// adapter registry or changing the module `.tmbc` format.
pub fn build_trust_native_request_bundle() -> Result<NativeBundleFixture, FixtureError> {
    let source_digest = digest(0x31);

    let mut mb = ModuleBuilder::new("trust_native_request_bundle");
    // Stamped as the shipping tRust producer stamps: schema 8 requires the
    // bundle's language set (`{Rust}` below) to cover every function.
    mb.set_default_producer(Producer::TRust);
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
    let mut module = mb.build().or_fixture("ModuleBuilder::build")?;
    module.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let source_file = module
        .intern_file("crates/trust/tests/checked_add.rs")
        .or_fixture("Module::intern_file")?;
    let u8_ty = module.add_type(Ty::U8).or_fixture("Module::add_type")?;
    let u64_ty = module.add_type(Ty::U64).or_fixture("Module::add_type")?;
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
        origin: None,
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
        origin: None,
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
        module
            .proof_obligations
            .first()
            .or_fixture("the TrustVc obligation")?,
        "trust_vc-clean-kernel",
    )
    .or_fixture("ground true postcondition must produce a kernel-replayable certificate")?;
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
        source_languages: BTreeSet::from([NativeSourceLanguage::Rust]),
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

    bundle.evidence_bundles = native_request_evidence_bundles(&bundle)?;

    Ok(NativeBundleFixture { bundle })
}

/// WS4.16 (F-080): a COMPLETE, validating schema-8 bundle over `module`, so a
/// language-set test that expects `Ok(())` or exactly ONE refusal is testing
/// the language rule and nothing else. The module gets one `Pending`
/// panic-freedom obligation sited at `f0/bb0#0` with an embedded source and
/// public identity; the bundle gets a compiler-facts sidecar row for it, one
/// frontend lineage node (non-zero source digest) rooting it, and the THREE
/// typed request lanes the design names — TrustVc (discharge, scoped to
/// `f0`), TrustMc (BMC) and TrustWp (WP) — each with a solver identity and a
/// replay identity carrying a transcript digest. The language set is
/// `languages`; its first entry is the primary `source_language`.
///
/// `function 0` must exist and have a body (the discharge request is sited
/// in it). The two-producer fixture (`build_mixed_producer_module`) and the
/// `b1_mixed` module both satisfy that.
#[allow(dead_code)] // Used by the mixed_producer and two_language_b1 targets.
pub fn build_language_set_bundle(
    mut module: Module,
    producer: NativeBundleProducer,
    languages: &[NativeSourceLanguage],
) -> Result<NativeVerificationBundle, FixtureError> {
    use trust_ir::ObligationSite;

    // The bundle's primary source language is the first of the set: an empty
    // set has none, so the builder refuses rather than indexing past it.
    let Some(&primary_language) = languages.first() else {
        return Err(FixtureError {
            context: "build_language_set_bundle",
            message: "the source-language set is empty".to_string(),
        });
    };
    let f0 = FuncId::new(0);
    // The fixtures this is used over carry no obligations of their own.
    let obligation = ProofId::new(0);
    fixture_invariant(
        module
            .function_by_id(f0)
            .is_some_and(|f| !f.blocks.is_empty()),
        "build_language_set_bundle: function 0 must be a definition",
    )?;
    let source_file = module
        .intern_file("two_language/package.src")
        .or_fixture("Module::intern_file")?;
    let source_digest = digest(0x80);
    let public_id = "vc:f0:panic_freedom:0";
    module.proof_obligations.push(
        ProofObligation::new(
            obligation,
            ObligationKind::PanicFreedom,
            ProofStatus::Pending,
            "two-language package: the requests' obligation",
        )
        .with_function(f0)
        .with_site(ObligationSite {
            function: f0,
            block: BlockId::new(0),
            inst_index: 0,
        })
        .with_source(
            ProofObligationSourceIdentity::new("two-language:f0", "assertion:0")
                .with_range(ProofObligationSourceRange {
                    file: source_file,
                    start_line: 1,
                    start_col: 1,
                    end_line: 1,
                    end_col: 2,
                })
                .with_public(PublicObligationIdentity {
                    obligation_id: public_id.to_string(),
                    semantic_digest: trust_ir_digest(
                        "trust-ir.conformance.public-obligation.v1",
                        public_id.as_bytes(),
                    ),
                }),
        ),
    );
    let trust_ir_module_digest = module.stable_digest();

    let mut frontend = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "two-language-lowering",
            "two-language-package",
            "ws4.16",
        ),
        source_digest,
        trust_ir_module_digest,
    );
    frontend.obligations.push(obligation);
    let lineage = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        nodes: vec![frontend],
        roots: vec![ProofLineageId::new(0)],
    };

    let mut bundle = NativeVerificationBundle::new(
        producer,
        NativeAdapterInput::TrustIrModule,
        trust_ir_module_digest,
        module,
        lineage,
    );
    bundle.provenance = NativeBundleProvenance {
        producer_version: "two-language-package@ws4.16".into(),
        source_language: primary_language,
        source_languages: languages.iter().copied().collect(),
        source_artifact: Some("app/{lib.rs,App.clean}".into()),
        source_digest: Some(source_digest),
        // G8: pinned compiler, kernel, solver and runtime identities.
        toolchain: vec![
            NativeToolIdentity::new("rustc-trust")
                .with_version("1.99.0-dev")
                .with_revision("1979a7b8546279af0b88c3a7f10e0df4809eb2a9"),
            NativeToolIdentity::new("clean-kernel")
                .with_revision("55a85e998d428606ec9745bf6ba65fd1888ea149"),
            NativeToolIdentity::new("ay").with_revision("849c19fa0382085174a6a4827739681f059b4615"),
            NativeToolIdentity::new("trust-bignum").with_digest(digest(0x5a)),
        ],
    };
    bundle.compiler_facts = NativeCompilerFacts {
        obligation_sources: vec![NativeObligationSource {
            obligation,
            public_obligation_id: public_id.to_string(),
            function: Some(f0),
            span: Some(SourceSpan {
                file: source_file,
                line: 1,
                col: 1,
            }),
            assertion_id: Some(NativeAssertionId::new(0)),
            cause: NativeObligationCause::Assert,
            monomorphization: None,
            facts: Vec::new(),
        }],
        ..NativeCompilerFacts::default()
    };
    let replay = |engine: &str| {
        ProofReplayIdentity::new(engine, format!("{engine} --bundle two-language-package"))
            .with_transcript_digest(trust_ir_digest(
                "two-language.transcript",
                engine.as_bytes(),
            ))
    };
    bundle
        .requests
        .push(NativeVerificationRequest::TrustVc(TrustVcNativeRequest {
            id: NativeRequestId::new(0),
            mode: TrustVcVerificationMode::DischargeProofObligations,
            obligations: vec![obligation],
            certificates: Vec::new(),
            lineage_roots: vec![ProofLineageId::new(0)],
            options: TrustVcRequestOptions::default(),
            diagnostics: NativeDiagnosticsPolicy::default(),
            provenance: NativeRequestProvenance::new(
                NativeVerifierSuite::TrustVc,
                NativeToolIdentity::new("trust_vc").with_version("vc-v1"),
            )
            .with_solver(NativeToolIdentity::new("ay").with_version("0.26.0"))
            .with_replay(replay("trust_vc")),
            function: Some(f0),
        }));
    bundle
        .requests
        .push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
            id: NativeRequestId::new(1),
            mode: TrustMcVerificationMode::BoundedModelCheck,
            function: f0,
            obligations: vec![obligation],
            lineage_roots: vec![ProofLineageId::new(0)],
            options: TrustMcRequestOptions {
                bmc: TrustMcBmcOptions {
                    unwind_limit: 1,
                    unwinding_assertions: true,
                },
                ..TrustMcRequestOptions::default()
            },
            diagnostics: NativeDiagnosticsPolicy::default(),
            provenance: NativeRequestProvenance::new(
                NativeVerifierSuite::TrustMc,
                NativeToolIdentity::new("trust_mc").with_version("bmc-v1"),
            )
            .with_solver(NativeToolIdentity::new("ay").with_version("0.26.0"))
            .with_replay(replay("trust_mc")),
        }));
    bundle
        .requests
        .push(NativeVerificationRequest::TrustWp(TrustWpNativeRequest {
            id: NativeRequestId::new(2),
            mode: TrustWpVerificationMode::WeakestPrecondition,
            function: f0,
            obligations: vec![obligation],
            lineage_roots: vec![ProofLineageId::new(0)],
            options: TrustWpRequestOptions::default(),
            diagnostics: NativeDiagnosticsPolicy::default(),
            provenance: NativeRequestProvenance::new(
                NativeVerifierSuite::TrustWp,
                NativeToolIdentity::new("trust_wp").with_version("wp-v1"),
            )
            .with_solver(NativeToolIdentity::new("ay").with_version("0.26.0"))
            .with_replay(replay("trust_wp")),
        }));
    Ok(bundle)
}

fn native_request_evidence_bundles(
    bundle: &NativeVerificationBundle,
) -> Result<Vec<NativeEvidenceBundle>, FixtureError> {
    bundle
        .requests
        .iter()
        .map(|request| -> Result<NativeEvidenceBundle, FixtureError> {
            Ok(match request {
                NativeVerificationRequest::TrustVc(request) => {
                    NativeEvidenceBundle::TrustVc(TrustVcNativeEvidenceBundle {
                        request: request.id,
                        mode: request.mode,
                        obligations: request.obligations.clone(),
                        verifier: request.provenance.expected_verifier.clone(),
                        solvers: request.provenance.solvers.clone(),
                        replay: request
                            .provenance
                            .replay
                            .clone()
                            .or_fixture("TrustVc replay")?,
                        trust_ir_module_digest: bundle.trust_ir_module_digest,
                        request_digest: bundle
                            .requests
                            .iter()
                            .find(|candidate| candidate.id() == request.id)
                            .or_fixture("TrustVc request")?
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
                        replay: request
                            .provenance
                            .replay
                            .clone()
                            .or_fixture("TrustMc replay")?,
                        trust_ir_module_digest: bundle.trust_ir_module_digest,
                        request_digest: bundle
                            .requests
                            .iter()
                            .find(|candidate| candidate.id() == request.id)
                            .or_fixture("TrustMc request")?
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
                        replay: request
                            .provenance
                            .replay
                            .clone()
                            .or_fixture("TrustWp replay")?,
                        trust_ir_module_digest: bundle.trust_ir_module_digest,
                        request_digest: bundle
                            .requests
                            .iter()
                            .find(|candidate| candidate.id() == request.id)
                            .or_fixture("TrustWp request")?
                            .stable_digest(),
                        artifacts,
                    })
                }
            })
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
pub fn build_func_param_abi() -> Result<Module, FixtureError> {
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
        origin: None,
    });

    // fn copy_pair(out: Ptr [sret noalias], src: Ptr [byval readonly ...]) -> ()
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
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
    module
        .try_add_function(func)
        .or_fixture("Module::try_add_function")?;
    Ok(module)
}

// ---------- text_directives ----------

/// Roadmap WS4.2: the LOSS-FREE golden that spells every text directive the
/// rest of the corpus only spells inside a lossy fixture (or not at all) —
/// `#param_attrs`, `#target_features`, `#proof_ctx`, `#source-provenance`,
/// `#source-loop`, `#source-binding` — so
/// `every_text_directive_round_trips_through_the_corpus` proves each entry of
/// the shared `TEXT_DIRECTIVES` vocabulary parses back exactly.
pub fn build_text_directives() -> Result<Module, FixtureError> {
    use trust_ir::proof::ProofContext;
    use trust_ir::{SourceBindingProvenance, SourceLoopProvenance, SourcePlace, SourceProvenance};

    let mut module = Module::new("text_directives");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;

    // fn sink(p: ptr [nonnull]) — target features + parameter attributes.
    let mut sink = Function::new(FuncId::new(0), "sink", ft, BlockId::new(0));
    sink.attrs.params = vec![ParamAttrs {
        nonnull: true,
        ..Default::default()
    }];
    sink.attrs.target_features = vec!["neon".into(), "crc".into()];
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::Ptr));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    sink.blocks.push(block);
    module
        .try_add_function(sink)
        .or_fixture("Module::try_add_function")?;

    // fn spin(p: ptr) — a call carrying a per-call proof context, then a
    // self-loop whose header parameter is bound to a source local.
    let mut spin = Function::new(FuncId::new(1), "spin", ft, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::Ptr));
    let mut call = InstrNode::new(Inst::Call {
        callee: FuncId::new(0),
        args: vec![ValueId::new(0)],
    });
    call.proof_context = Some(ProofContext {
        assumes: vec![],
        establishes: vec![ProofId::new(0), ProofId::new(1)],
    });
    entry.body.push(call);
    entry.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(1),
        args: vec![ValueId::new(0)],
    }));
    let mut header = Block::new(BlockId::new(1));
    header.params.push((ValueId::new(1), Ty::Ptr));
    header.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(1),
        args: vec![ValueId::new(1)],
    }));
    spin.blocks.extend([entry, header]);
    module
        .try_add_function(spin)
        .or_fixture("Module::try_add_function")?;

    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Precondition,
            ProofStatus::Pending,
            "sink: p is non-null",
        )
        .with_function(FuncId::new(0)),
    );
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(1),
            ObligationKind::Precondition,
            ProofStatus::Pending,
            "sink: p is aligned",
        )
        .with_function(FuncId::new(0)),
    );

    // Sealed last: the semantic digest covers the finished module image.
    let semantic = module
        .source_provenance_semantic_digest(FuncId::new(1))
        .or_fixture("spin is unique")?;
    module
        .functions
        .get_mut(1)
        .or_fixture("the spin function")?
        .source_provenance = Some(SourceProvenance::new(
        ProofDigest::sha256([0x11; 32]),
        semantic,
        vec![SourceLoopProvenance {
            source_loop_id: 0,
            hir_local_id: 71,
            header: BlockId::new(1),
            bindings: vec![SourceBindingProvenance {
                name: "cursor".into(),
                hir_local_id: 72,
                place: SourcePlace::LoopParameter { index: 0 },
            }],
        }],
    ));
    Ok(module)
}

// ---------- chc_batch ----------

/// x86 CHC Batch JIT TrustIr Contract Plan fixture.
/// Separate-compilation contract fixture: a module that carries a body-less,
/// contract-only declaration (`FunctionSummary` with requires/ensures/params/proved)
/// alongside a defined function. Exercises the v18 `Function.summary` wire codec
/// across binary / JSON / MessagePack. The canonical text form does not yet
/// render the verifier-facing contract, so its `.trust_ir` golden is the
/// `#lossy`-marked dump the parser refuses (roadmap WS4.2; `TEXT_LOSS_RATCHET`
/// row `FunctionSummary`) — the lossless paths guard the contract.
///
/// Since v41 it is also the corpus's ONLY byte-golden of the cross-crate
/// carrier — `Module::imports` (a content-interned [`trust_ir::ModuleImport`]
/// pinned by digest) and the [`trust_ir::ExternRef`] that cites it from
/// `FunctionSummary::backed_by`. The two are what make `proved` checkable on a
/// body-less declaration, so the fixture pins them together with the bit they
/// authenticate.
///
/// The two summaries deliberately sit at DIFFERENT rungs, because those are the
/// two states the format can honestly spell here:
///
/// * `reciprocal` is a body-less declaration, so it holds no local obligation
///   and the only thing that can authenticate its `proved` bit is the v41
///   `backed_by` citation into a declared import. It carries one.
/// * `passthrough` HAS a body, so a cross-crate citation would be a falsehood —
///   its `(= result x)` postcondition is about the body right here. The honest
///   local backing would be a `Discharged`/`Certified` `Postcondition`
///   obligation, and neither is constructible in a wire-format fixture:
///   structural `validate_module` supplies a rejecting proof authority, so a
///   `Discharged` row without a replayed certificate is itself an error
///   (`DischargedWithoutCertificate`), and `Certified` needs a kernel-recheckable
///   `CleanCic` payload. So its summary carries the clause with `proved` FALSE —
///   the accurate "published, not yet backed" state — and the fixture pins both
///   values of the bit rather than asserting one it cannot support.
pub fn build_composition() -> Result<Module, FixtureError> {
    use trust_ir::proof::ProofDigest;
    use trust_ir::value::{FuncTyId, ProofId};
    use trust_ir::{ExternRef, FunctionSummary, ModuleImport, ProofFormula};

    let mut module = Module::new("composition");

    // A body-less `External` declaration is a hard cross-object ABI boundary,
    // and byte-level ABI agreement is only well-defined against a pinned target.
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: Default::default(),
    });

    // The crate whose verification established `reciprocal`'s contract, pinned
    // by `Module::stable_digest` — the digest is what makes the citation below
    // checkable rather than asserted, since module NAMES collide. Interned (not
    // pushed) so a second reference to the same artifact reuses this `ImportId`.
    let prelude = module
        .intern_import(
            ModuleImport::new("trusted_prelude", ProofDigest::sha256([0x11; 32]))
                .with_producer(Producer::Clean)
                // FROZEN GOLDEN CONTENT: a v41 row, recorded under the legacy V2
                // identity. A V3 row would raise these bytes to v44; the v44
                // spelling is the `import_scheme` golden.
                .with_scheme(trust_ir::IdentityScheme::V2),
        )
        .or_fixture("Module::intern_import")?;

    // Signature shared by the declaration and the caller: fn(i32) -> i32.
    let ft: FuncTyId = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;

    // The trusted-prelude contract for `reciprocal`: requires a non-zero argument,
    // guarantees a non-zero result. A body-less, contract-only declaration — the
    // IR-level "body None ⇒ summary" state a caller is verified against.
    //
    // `proved` is backed by obligation #3 of the imported module. The id lives in
    // the IMPORTED module's `proof_obligations` id space, so a consumer resolves
    // it only after authenticating that module against the import digest above;
    // `ExternRef::obligation == None` would name the entity while making no proof
    // claim at all, and would not authenticate `proved`.
    let summary = FunctionSummary::new()
        .with_params(vec!["x".to_string()])
        .requiring(ProofFormula::trust_types_json(
            "{\"Ne\":[{\"Var\":[\"x\",\"Int\"]},{\"Int\":0}]}",
            "(not (= x 0))",
            "Bool",
        ))
        .ensuring(ProofFormula::smtlib2("(not (= result 0))", "Bool"))
        .backed_by(ExternRef::new(prelude, "reciprocal").relying_on(ProofId::new(3)))
        .proved();
    module
        .try_add_function(Function::declaration(
            FuncId::new(0),
            "reciprocal",
            ft,
            summary,
        ))
        .or_fixture("Module::try_add_function")?;

    // A defined sibling function that also publishes its own (trivial) contract,
    // proving body + summary coexist on the wire. `proved` is deliberately NOT
    // set — see this function's doc comment.
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
            .ensuring(ProofFormula::smtlib2("(= result x)", "Bool")),
    );
    module
        .try_add_function(caller)
        .or_fixture("Module::try_add_function")?;

    Ok(module)
}

/// Roadmap WS4.4 (F-064, F-070, F-071): the proof surface the TEXT format
/// carries, in one loss-free fixture whose `.trust_ir` golden spells every
/// piece of it and round-trips EXACTLY.
///
/// * `bump(x: u64, p: &mut u64) -> u64` carries a summary with EVERY clause
///   kind — `params`, `requires`, `ensures`, `decreases` — and bindings of
///   every FUNCTION `ClausePlace` (`param`, `result`, `mut_exit`, `world`,
///   `unwind`, `value`), each sort a faithful reading of its place's IR type.
///   `proved` is false: no local row can back it in a wire fixture (see
///   [`build_composition`]).
/// * `reciprocal` is a body-less declaration whose `proved` summary is
///   `backed_by` an import (the `; #backed-by:` directive).
/// * One `Pending` obligation per v41 kind (`termination`, `ownership`,
///   `custom("trust.contract", ..)`), each scoped and bound.
/// * One `Trusted` row per [`trust_ir::proof::CoverageBound`], each with a
///   justified `Trusted` certificate carrying that bound as its `assurance`.
///
/// The spec-variable places are the `spec_carrier` fixture's, and a
/// kernel-Certified `clean_cic` certificate with its `recheck` directive is
/// the `lean_library_envelope` fixture's — both loss-free in text since WS4.4.
pub fn build_proof_surface() -> Result<Module, FixtureError> {
    use trust_ir::proof::{
        ClauseBinding, ClausePlace, ClauseSort, CoverageAssurance, CoverageBound,
    };
    use trust_ir::{ExternRef, FunctionSummary, ModuleImport};

    let bound = |text: &str, sort: &str, bindings: Vec<(&str, ClauseSort, ClausePlace)>| {
        let mut formula = ProofFormula::smtlib2(text, sort);
        formula.bindings = bindings
            .into_iter()
            .map(|(name, sort, place)| (name.to_string(), ClauseBinding { sort, place }))
            .collect();
        formula
    };
    let x = || ("x", ClauseSort::BitVec(64), ClausePlace::Param { index: 0 });

    let mut module = Module::new("proof_surface");
    // `reciprocal` is a body-less `External` declaration: a cross-object ABI
    // boundary, well-defined only against a pinned target (the fixture must
    // VALIDATE, so its text image can re-validate with the same empty verdict).
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: Default::default(),
    });
    let dep = module
        .intern_import(
            ModuleImport::new("proof_surface_dep", ProofDigest::sha256([0x44; 32]))
                .with_producer(Producer::Clean)
                .with_scheme(trust_ir::IdentityScheme::V2),
        )
        .or_fixture("Module::intern_import")?;
    let bump_ty = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::U64, Ty::RefMut(Box::new(Ty::U64))],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let unary = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;

    let mut bump = Function::new(FuncId::new(0), "bump", bump_ty, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::U64));
    block
        .params
        .push((ValueId::new(1), Ty::RefMut(Box::new(Ty::U64))));
    block.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U64,
            lhs: ValueId::new(0),
            rhs: ValueId::new(0),
        })
        .with_result(ValueId::new(2)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    bump.blocks.push(block);
    bump.summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".to_string(), "p".to_string()])
            .requiring(bound("(bvult x #x8000000000000000)", "Bool", vec![x()]))
            .ensuring(bound(
                "(and (= result sum) (= p_exit p_exit) heap (not unwinding))",
                "Bool",
                vec![
                    (
                        "result",
                        ClauseSort::BitVec(64),
                        ClausePlace::ResultSlot { index: 0 },
                    ),
                    (
                        "p_exit",
                        ClauseSort::BitVec(64),
                        ClausePlace::MutParamExit { index: 1 },
                    ),
                    (
                        "sum",
                        ClauseSort::BitVec(64),
                        ClausePlace::Value(ValueId::new(2)),
                    ),
                    ("heap", ClauseSort::Bool, ClausePlace::World),
                    ("unwinding", ClauseSort::Bool, ClausePlace::Unwind),
                ],
            ))
            .decreasing(bound("x", "(_ BitVec 64)", vec![x()])),
    );
    // The v41 producer rule (`producer_rule_census.rs`): this blob is written
    // at v41+, so its one bodied function states its codegen license rather
    // than the grandfather `None`. `Ungated` is the true claim — no gate ran
    // on a wire fixture's body — and `validate_module` accepts a module that
    // CARRIES it (only `validate_module_for_codegen` refuses to consume it).
    bump.body_gate = Some(trust_ir::BodyGate::Ungated);
    module
        .try_add_function(bump)
        .or_fixture("Module::try_add_function")?;

    module
        .try_add_function(Function::declaration(
            FuncId::new(1),
            "reciprocal",
            unary,
            FunctionSummary::new()
                .with_params(vec!["x".to_string()])
                .ensuring(ProofFormula::smtlib2("(not (= result 0))", "Bool"))
                .backed_by(ExternRef::new(dep, "reciprocal").relying_on(ProofId::new(2)))
                .proved(),
        ))
        .or_fixture("Module::try_add_function")?;

    let kinds = [
        (ObligationKind::Termination, "bump terminates"),
        (ObligationKind::Ownership, "bump's &mut is exclusive"),
        (
            ObligationKind::Custom {
                namespace: "trust.contract".to_string(),
                name: "unlowered \"old(x)\" clause".to_string(),
            },
            "a source clause the compiler could not lower",
        ),
    ];
    for (id, (kind, description)) in kinds.into_iter().enumerate() {
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(id as u32),
                kind,
                ProofStatus::Pending,
                description,
            )
            .with_function(FuncId::new(0))
            .with_formula(bound("(bvule x x)", "Bool", vec![x()])),
        );
    }
    // (obligation id, bound, request-digest byte): spelled out, so the
    // builder does no arithmetic (it is total — see [`FixtureError`]).
    let bounds = [
        (3, CoverageBound::Unbounded, 0x50),
        (4, CoverageBound::UnwindBounded { depth: 8 }, 0x51),
        (5, CoverageBound::ModelBounded { size: 3 }, 0x52),
        (6, CoverageBound::Unrecorded, 0x53),
    ];
    for (offset, (id, bound, digest_byte)) in bounds.into_iter().enumerate() {
        let id = ProofId::new(id);
        module.proof_obligations.push(
            ProofObligation::new(
                id,
                ObligationKind::Postcondition,
                ProofStatus::Trusted,
                "an audited postcondition",
            )
            .with_function(FuncId::new(0))
            .with_formula(ProofFormula::smtlib2("(= 1 1)", "Bool")),
        );
        module.proof_certificates.push(ProofCertificate {
            obligation: id,
            prover: "manual-audit".to_string(),
            evidence: ProofEvidence::Trusted(format!("reviewed; coverage row {offset}")),
            assurance: Some(CoverageAssurance {
                bound,
                request_digest: ProofDigest::sha256([digest_byte; 32]),
            }),
        });
    }
    Ok(module)
}

pub fn build_chc_batch_fixture() -> Result<Module, FixtureError> {
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
    fb.add_function_proof(ProofAnnotation::Deterministic);
    fb.add_function_proof(ProofAnnotation::Terminates);
    fb.add_function_proof(ProofAnnotation::NoPanic);
    fb.add_function_proof(ProofAnnotation::NoUndef);
    fb.add_function_proof(ProofAnnotation::AppendOnlyBuffer);

    // Custom proof tags (mapped to unique indices for the fixture)
    fb.add_function_proof(ProofAnnotation::Custom(ProofTag::new(1001))); // ay.chc.batch.v1
    fb.add_function_proof(ProofAnnotation::Custom(ProofTag::new(1002))); // ay.chc.scalar_oracle
    fb.add_function_proof(ProofAnnotation::Custom(ProofTag::new(1003))); // ay.chc.layout_hash
    fb.add_function_proof(ProofAnnotation::Custom(ProofTag::new(1004))); // ay.chc.generation_domain
    fb.add_function_proof(ProofAnnotation::Custom(ProofTag::new(1005))); // ay.chc.batch_shape_version

    fb.build();

    mb.build().or_fixture("ModuleBuilder::build")
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
pub fn build_frontend_emission_subset() -> Result<Module, FixtureError> {
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
        fb.add_function_proof(ProofAnnotation::Terminates);
        fb.add_function_proof(ProofAnnotation::Deterministic);
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
        fb.add_function_proof(ProofAnnotation::Terminates);
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

    mb.build().or_fixture("ModuleBuilder::build")
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
pub fn build_frontend_panic_obligations() -> Result<Module, FixtureError> {
    const SOURCE_ID: &str = "trust-ir-frontend/mir-assert@1";

    let mut mb = ModuleBuilder::new("frontend_panic_obligations");
    let file = mb.intern_file("examples/panic_checks.rs");

    // fn checked_index(slice_len: u64, index: u64, acc: i32) -> i32
    // — the body stands in for a bounds check + an overflow check + a
    // coroutine-resume check, all lowered to explicit control flow.
    let ft = mb.add_func_type(vec![Ty::U64, Ty::U64, Ty::I32], vec![Ty::I32]);
    let fid = mb.peek_next_func_id().or_fixture("peek_next_func_id")?;
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
    })
    .or_fixture("a fresh obligation id")?;

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
    })
    .or_fixture("a fresh obligation id")?;

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
    })
    .or_fixture("a fresh obligation id")?;

    mb.build().or_fixture("ModuleBuilder::build")
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
/// v41 codegen license (`Function.body_gate`) + display path.
///
/// Covers ALL THREE states in one module, because the whole point of the
/// three-valued wire tag is that `None` and `Ungated` are DIFFERENT: a
/// consumer permits the first (it is the pre-v41 grandfather state) and must
/// refuse the second. A fixture carrying only the two `Some` states would
/// round-trip happily under a two-tag encoding that silently rewrote `None`.
pub fn build_body_gate() -> Result<Module, FixtureError> {
    use trust_ir::BodyGate;

    // FROZEN GOLDEN CONTENT, not a file name: this string is inside the
    // `body_gate.*` golden bytes (and the pinned `v41-reader-compat` copies).
    // The goldens were renamed to a feature name; the bytes were not touched.
    let mut mb = ModuleBuilder::new("body_gate_v41");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    let mut identity = |name: &str, gate: Option<BodyGate>, path: Option<&str>| {
        let mut fb = mb.function(name, ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        if let Some(gate) = gate {
            fb.set_body_gate(gate);
        }
        if let Some(path) = path {
            fb.set_display_path(path);
        }
        fb.build();
    };

    // No licensing claim: what every pre-v41 blob decodes to.
    identity("no_claim", None, None);
    // An affirmative "not gated" — codegen must refuse this one.
    identity("ungated_body", Some(BodyGate::Ungated), None);
    // Gated, with the display path carrying generics/colons/spaces that force
    // the quoted text form and exercise the string pool.
    identity(
        "gated_body",
        Some(BodyGate::Gated {
            authority: "clean-kernel-tv".to_string(),
            evidence: None,
        }),
        Some("core::ptr::drop_in_place::<alloc::string::String>"),
    );

    mb.build().or_fixture("ModuleBuilder::build")
}

pub fn build_producer_provenance() -> Result<Module, FixtureError> {
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

    mb.build().or_fixture("ModuleBuilder::build")
}

/// v32/v33 debug metadata: a producer-stamped function with sparse SSA names,
/// a two-level lexical-scope tree, and exact per-node scope indices. Keeping
/// producer provenance in the same fixture pins the complete trailing
/// Function record order (`producer`, `value_names`, `scopes`).
pub fn build_debug_metadata_v33() -> Result<Module, FixtureError> {
    let mut m = Module::new("debug_metadata_v33");
    let file = m
        .intern_file("src/debug.rs")
        .or_fixture("Module::intern_file")?;
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
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
            inlined_at: None,
        },
        ScopeData {
            parent: Some(0),
            span: Some(SourceSpan {
                file,
                line: 2,
                col: 4,
            }),
            inlined_at: None,
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
    m.try_add_function(func)
        .or_fixture("Module::try_add_function")?;
    Ok(m)
}

/// v24: the 128-bit-faithful integer carrier. Pins `Constant::U128` (wire
/// tag 13) across all four formats at BOTH canonical boundaries — the first
/// value i128 cannot carry (i128::MAX + 1) and u128::MAX — as an
/// `Inst::Const` result AND a global initializer. Values at or below
/// i128::MAX stay `Constant::Int` (the one-spelling rule); `boundary_int`
/// pins the Int side of the boundary in the same module.
pub fn build_u128_constants() -> Result<Module, FixtureError> {
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
        section: None,
        visibility: Default::default(),
        retained: false,
    });

    mb.build().or_fixture("ModuleBuilder::build")
}

/// v25: the byte-array constant carrier. Pins `Constant::Bytes` (wire tag
/// 14) across all four formats: a raw payload (with a 0x00 and a 0xFF), a
/// utf8-claimed payload (multibyte character included), and the empty
/// payload — each as a `[u8; N]` global initializer plus one `Inst::Const`
/// use.
pub fn build_bytes_constants() -> Result<Module, FixtureError> {
    use trust_ir::{Constant, Global, Linkage};

    let mut mb = ModuleBuilder::new("bytes_constants");

    // Typed on the BYTES, so no non-bytes constant can reach it (the old
    // closure took any `Constant` and had an unreachable arm).
    let add_global = |mb: &mut ModuleBuilder,
                      name: &str,
                      data: Vec<u8>,
                      utf8: bool|
     -> Result<(), FixtureError> {
        let len = u64::try_from(data.len()).or_fixture("bytes fixture length")?;
        let c = Constant::Bytes { data, utf8 };
        let tid = mb.add_type(Ty::U8);
        mb.add_global(Global {
            name: name.to_string(),
            ty: Ty::Array(tid, len),
            mutable: false,
            initializer: Some(c),
            linkage: Linkage::External,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        Ok(())
    };

    add_global(&mut mb, "RAW_BYTES", vec![0u8, 0xde, 0xad, 0xff], false)?;
    // The utf8 claim is true by construction: the bytes come from a `&str`.
    add_global(&mut mb, "UTF8_BYTES", "héllo".as_bytes().to_vec(), true)?;
    add_global(&mut mb, "EMPTY_BYTES", Vec::new(), false)?;

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

    mb.build().or_fixture("ModuleBuilder::build")
}

/// v50: the constant-size uniform array. Pins `Constant::Splat` (Constant
/// tag 16) and `Inst::ArraySplat` (Inst tag 59) across all four formats, at
/// u64-scale lengths — the goldens are a few hundred bytes whatever the
/// lengths, which is the point:
///
/// * `ZEROS: [u8 x 2^32] = splat[ 0; 4294967296 ]` and a nested
///   `GRID: [[i32 x 2^20] x 2^20] = splat[ splat[ 7; 1048576 ]; 1048576 ]`
///   as global initializers (the `static` case no instruction can express);
/// * `fill(x: i64) -> [i64 x 2^40]` = `array_splat` of its parameter (the
///   register case, a Rust `[x; N]` with a runtime `x`);
/// * `pick(i: u64) -> i64` = `extract_element` at a runtime index out of an
///   in-body `Const` splat of 2^40 elements.
pub fn build_array_splat() -> Result<Module, FixtureError> {
    use trust_ir::{Global, Linkage};

    let mut mb = ModuleBuilder::new("array_splat");
    let add_global = |mb: &mut ModuleBuilder, name: &str, ty: Ty, c: Constant| {
        mb.add_global(Global {
            name: name.to_string(),
            ty,
            mutable: false,
            initializer: Some(c),
            linkage: Linkage::External,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
    };

    let u8_id = mb.add_type(Ty::U8);
    add_global(
        &mut mb,
        "ZEROS",
        Ty::Array(u8_id, 1 << 32),
        Constant::splat(Constant::Int(0), 1 << 32),
    );
    let i32_id = mb.add_type(Ty::I32);
    let row_id = mb.add_type(Ty::Array(i32_id, 1 << 20));
    add_global(
        &mut mb,
        "GRID",
        Ty::Array(row_id, 1 << 20),
        Constant::splat(Constant::splat(Constant::Int(7), 1 << 20), 1 << 20),
    );

    let i64_id = mb.add_type(Ty::I64);
    let big = Ty::Array(i64_id, 1 << 40);
    let ft = mb.add_func_type(vec![Ty::I64], vec![big.clone()]);
    {
        let mut fb = mb.function("fill", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let array = fb.uniform_array(big.clone(), x);
        fb.ret(vec![array]);
        // The v41 producer rule: a bodied function at v41+ states its
        // codegen license; this golden is affirmatively ungated.
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        fb.build();
    }

    let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::I64]);
    {
        let mut fb = mb.function("pick", ft);
        let entry = fb.create_block();
        let index = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let array = fb.const_value(big.clone(), Constant::splat(Constant::Int(-3), 1 << 40));
        let element = fb.extract_element(Ty::I64, array, index);
        fb.ret(vec![element]);
        // The v41 producer rule: a bodied function at v41+ states its
        // codegen license; this golden is affirmatively ungated.
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        fb.build();
    }

    mb.build().or_fixture("ModuleBuilder::build")
}

/// The location record of the panic-site goldens: an immutable, non-TLS
/// `u64` with a plain integer initializer (no `SymbolAddr`), so the Lean
/// executable model can materialize it when a caller takes its address.
/// The panic-site goldens' target: a bodyless C declaration (the entry) is
/// an FFI boundary, which the validator admits only on a known target.
fn panic_site_target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

fn panic_location_global(name: &str) -> trust_ir::Global {
    trust_ir::Global {
        name: name.to_string(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(Constant::Int(7)),
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    }
}

/// Amendment P (wire v54): sited `Inst::Assert`s (Inst tag 66), carried by
/// all four formats, inside the lowering-target subset. Every function takes
/// and returns integers only, so both executable engines run it and the
/// Lean-execution differential compares (message, entry, location):
///
/// * `panic_bounds_check(usize, usize, ptr)`, `panic_const_add_overflow(ptr)`
///   and `panic_resumed(ptr)` are the bodyless entries (functions 0..=2);
///   `loc.0` (global 0) is the location record;
/// * `bounds(i: usize, n: usize) -> usize` asserts `i < n` as a bounds check
///   sited on `panic_bounds_check` at `@global.0`;
/// * `add(a: u8) -> u8` asserts `a != 255` as `overflow add` sited on the
///   location-only `panic_const_add_overflow`;
/// * `resumed(c: bool) -> bool` asserts `c` with NO kind, sited on the
///   location-only `panic_resumed` (MIR's coroutine-resume shape);
/// * `tracked(i: usize, n: usize, loc: ptr) -> usize` is the
///   `#[track_caller]` shape: its bounds check reports the location its
///   caller passed (`PanicLocation::Value`);
/// * `caller(i: usize, n: usize) -> usize` passes `global_addr @global.0`.
pub fn build_assert_panic_site() -> Result<Module, FixtureError> {
    use trust_ir::{AssertKind, AssertOverflowOp, PanicLocation, PanicSite};

    let mut mb = ModuleBuilder::new_with_target_info("assert_panic_site", panic_site_target());
    let bounds_ft = mb.add_func_type(vec![Ty::Usize, Ty::Usize, Ty::Ptr], vec![]);
    let panic_bounds_check = mb.declare_function("panic_bounds_check", bounds_ft);
    let loc_ft = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let panic_add = mb.declare_function("panic_const_add_overflow", loc_ft);
    let loc_ft = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let panic_resumed = mb.declare_function("panic_resumed", loc_ft);
    mb.add_global(panic_location_global("loc.0"));
    let loc = PanicLocation::Global(GlobalId::new(0));

    let ft = mb.add_func_type(vec![Ty::Usize, Ty::Usize], vec![Ty::Usize]);
    {
        let mut fb = mb.function("bounds", ft);
        let entry = fb.create_block();
        let i = fb.add_block_param(entry, Ty::Usize);
        let n = fb.add_block_param(entry, Ty::Usize);
        fb.switch_to_block(entry);
        let ok = fb.icmp(ICmpOp::Ult, Ty::Usize, i, n);
        fb.assert_sited(
            ok,
            AssertKind::BoundsCheck { index: i, len: n },
            PanicSite {
                entry: panic_bounds_check,
                location: loc,
            },
        );
        fb.ret(vec![i]);
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        fb.build();
    }
    let ft = mb.add_func_type(vec![Ty::U8], vec![Ty::U8]);
    {
        let mut fb = mb.function("add", ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U8);
        fb.switch_to_block(entry);
        let max = fb.uconst(Ty::U8, 255);
        let ok = fb.icmp(ICmpOp::Ne, Ty::U8, a, max);
        fb.assert_sited(
            ok,
            AssertKind::Overflow(AssertOverflowOp::Add),
            PanicSite {
                entry: panic_add,
                location: loc,
            },
        );
        fb.ret(vec![a]);
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        fb.build();
    }
    let ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
    {
        let mut fb = mb.function("resumed", ft);
        let entry = fb.create_block();
        let c = fb.add_block_param(entry, Ty::Bool);
        fb.switch_to_block(entry);
        fb.assert_sited(
            c,
            AssertKind::Unspecified,
            PanicSite {
                entry: panic_resumed,
                location: loc,
            },
        );
        fb.ret(vec![c]);
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        fb.build();
    }
    let tracked_ft = mb.add_func_type(vec![Ty::Usize, Ty::Usize, Ty::Ptr], vec![Ty::Usize]);
    let tracked = {
        let mut fb = mb.function("tracked", tracked_ft);
        let entry = fb.create_block();
        let i = fb.add_block_param(entry, Ty::Usize);
        let n = fb.add_block_param(entry, Ty::Usize);
        let location = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        let ok = fb.icmp(ICmpOp::Ult, Ty::Usize, i, n);
        fb.assert_sited(
            ok,
            AssertKind::BoundsCheck { index: i, len: n },
            PanicSite {
                entry: panic_bounds_check,
                location: PanicLocation::Value(location),
            },
        );
        fb.ret(vec![i]);
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        fb.build()
    };
    let ft = mb.add_func_type(vec![Ty::Usize, Ty::Usize], vec![Ty::Usize]);
    {
        let mut fb = mb.function("caller", ft);
        let entry = fb.create_block();
        let i = fb.add_block_param(entry, Ty::Usize);
        let n = fb.add_block_param(entry, Ty::Usize);
        fb.switch_to_block(entry);
        let p = fb.global_addr(GlobalId::new(0));
        let r = fb.call(tracked, vec![i, n, p]);
        fb.ret(vec![r]);
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        fb.build();
    }
    mb.build().or_fixture("ModuleBuilder::build")
}

/// Amendment P (wire v54): `Inst::AssertInvoke` (Inst tag 67), carried by all
/// four formats, OUTSIDE the lowering-target subset (no consumer lowers its
/// unwind edge yet; `AssertInvoke`, `LandingPad` and `Resume` are excluded
/// by name). `guarded(c: bool, x: usize) -> usize` is `assert_invoke %c,
/// div_by_zero, panic @func.0 at @global.0 to bb1(%x) unwind bb2`; bb1
/// returns its parameter and bb2 is a cleanup pad that resumes.
pub fn build_assert_invoke() -> Result<Module, FixtureError> {
    use trust_ir::{AssertKind, PanicLocation, PanicSite};

    let mut mb = ModuleBuilder::new_with_target_info("assert_invoke", panic_site_target());
    let loc_ft = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let entry_fn = mb.declare_function("panic_const_div_by_zero", loc_ft);
    mb.add_global(panic_location_global("loc.0"));
    let ft = mb.add_func_type(vec![Ty::Bool, Ty::Usize], vec![Ty::Usize]);
    let mut fb = mb.function("guarded", ft);
    let bb0 = fb.create_block();
    let bb1 = fb.create_block();
    let bb2 = fb.create_block();
    let c = fb.add_block_param(bb0, Ty::Bool);
    let x = fb.add_block_param(bb0, Ty::Usize);
    let y = fb.add_block_param(bb1, Ty::Usize);
    fb.switch_to_block(bb0);
    fb.assert_invoke(
        c,
        AssertKind::DivByZero,
        PanicSite {
            entry: entry_fn,
            location: PanicLocation::Global(GlobalId::new(0)),
        },
        bb1,
        vec![x],
        bb2,
    );
    fb.switch_to_block(bb1);
    fb.ret(vec![y]);
    fb.switch_to_block(bb2);
    let (exn, _) = fb.landingpad(true, vec![]);
    fb.resume(exn);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    fb.build();
    mb.build().or_fixture("ModuleBuilder::build")
}

/// Amendment D (wire v55, `docs/SPEC_RATIFICATIONS.md` §20): the module
/// drop-glue table and `Inst::DropInvoke` (Inst tag 68), carried by all four
/// formats (the only golden at header 55), OUTSIDE the lowering-target
/// subset (no backend lowers a drop yet; `Drop`, `DropInvoke`, `LandingPad`
/// and `Resume` are excluded by name). Executable on its normal paths in both
/// engines:
///
/// * `Resource` (a counter cell) has glue `drop_resource(p)`, which adds 1
///   to the `i64` at its place;
/// * `Pair` has glue `drop_pair(p)`, a NESTED drop: it drops a `Resource`
///   at the same place;
/// * `Node` has glue `drop_node(p)`, RECURSIVE through the table: it drops
///   the `Node` its place points to, unless that pointer is null;
/// * `run(flag: bool) -> i64` drops a `Resource` and a `Pair` over a cell
///   holding 0, drops another `Resource` under a DROP FLAG (an ordinary
///   `CondBr` on `flag`), then `drop_invoke`s a `Pair` into a cleanup pad
///   that resumes, and returns the cell: 4 with the flag, 3 without;
/// * `run_list() -> i64` drops a two-node list and returns 0.
pub fn build_drop_glue() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new_with_target_info("drop_glue", panic_site_target());
    let structs = [("Resource", Ty::I64), ("Pair", Ty::I64), ("Node", Ty::Ptr)];
    let mut tys = Vec::new();
    for (index, (name, field)) in structs.into_iter().enumerate() {
        tys.push(Ty::Struct(mb.add_struct(StructDef {
            id: StructId::new(u32::try_from(index).or_fixture("struct id")?),
            name: name.into(),
            fields: vec![FieldDef {
                name: "field".into(),
                ty: field,
                offset: Some(0),
            }],
            size: Some(8),
            align: Some(8),
            repr: Default::default(),
            origin: None,
        })));
    }
    let [resource, pair, node] = <[Ty; 3]>::try_from(tys)
        .ok()
        .or_fixture("three struct types")?;
    let glue_ty = mb.add_func_type(vec![Ty::Ptr], vec![]);

    // drop_resource(p): *p += 1
    let mut fb = mb.function("drop_resource", glue_ty);
    let bb0 = fb.create_block();
    let p = fb.add_block_param(bb0, Ty::Ptr);
    fb.switch_to_block(bb0);
    let x = fb.load(Ty::I64, p);
    let one = fb.iconst(Ty::I64, 1);
    let y = fb.add(Ty::I64, x, one);
    fb.store(Ty::I64, p, y);
    fb.ret(vec![]);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    let drop_resource = fb.build();

    // drop_pair(p): drop Resource, p (a nested drop)
    let mut fb = mb.function("drop_pair", glue_ty);
    let bb0 = fb.create_block();
    let p = fb.add_block_param(bb0, Ty::Ptr);
    fb.switch_to_block(bb0);
    fb.drop(resource.clone(), p);
    fb.ret(vec![]);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    let drop_pair = fb.build();

    // drop_node(p): let n = *p; if n != null { drop Node, n }
    let mut fb = mb.function("drop_node", glue_ty);
    let bb0 = fb.create_block();
    let bb1 = fb.create_block();
    let bb2 = fb.create_block();
    let p = fb.add_block_param(bb0, Ty::Ptr);
    fb.switch_to_block(bb0);
    let next = fb.load(Ty::Ptr, p);
    let addr = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, next);
    let zero = fb.iconst(Ty::U64, 0);
    let is_null = fb.icmp(ICmpOp::Eq, Ty::U64, addr, zero);
    fb.condbr(is_null, bb2, vec![], bb1, vec![]);
    fb.switch_to_block(bb1);
    fb.drop(node.clone(), next);
    fb.ret(vec![]);
    fb.switch_to_block(bb2);
    fb.ret(vec![]);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    let drop_node = fb.build();

    // run(flag) -> i64
    let run_ty = mb.add_func_type(vec![Ty::Bool], vec![Ty::I64]);
    let mut fb = mb.function("run", run_ty);
    let bb0 = fb.create_block();
    let bb1 = fb.create_block();
    let bb2 = fb.create_block();
    let bb3 = fb.create_block();
    let bb4 = fb.create_block();
    let flag = fb.add_block_param(bb0, Ty::Bool);
    fb.switch_to_block(bb0);
    let cell = fb.alloca(Ty::I64);
    let zero = fb.iconst(Ty::I64, 0);
    fb.store(Ty::I64, cell, zero);
    fb.drop(resource.clone(), cell);
    fb.drop(pair.clone(), cell);
    fb.condbr(flag, bb1, vec![], bb2, vec![]);
    fb.switch_to_block(bb1);
    fb.drop(resource.clone(), cell);
    fb.br(bb2, vec![]);
    fb.switch_to_block(bb2);
    fb.drop_invoke(pair.clone(), cell, bb3, vec![], bb4);
    fb.switch_to_block(bb3);
    let out = fb.load(Ty::I64, cell);
    fb.ret(vec![out]);
    fb.switch_to_block(bb4);
    let (exn, _) = fb.landingpad(true, vec![]);
    fb.resume(exn);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    fb.build();

    // run_list() -> i64: head -> second -> null
    let list_ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("run_list", list_ty);
    let bb0 = fb.create_block();
    fb.switch_to_block(bb0);
    let null = fb.null_ptr();
    let second = fb.alloca(Ty::Ptr);
    fb.store(Ty::Ptr, second, null);
    let head = fb.alloca(Ty::Ptr);
    fb.store(Ty::Ptr, head, second);
    fb.drop(node.clone(), head);
    let done = fb.iconst(Ty::I64, 0);
    fb.ret(vec![done]);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    fb.build();

    for (ty, glue) in [
        (resource, drop_resource),
        (pair, drop_pair),
        (node, drop_node),
    ] {
        mb.set_drop_glue(ty, glue)
            .or_fixture("one drop-glue row per type")?;
    }
    mb.build().or_fixture("ModuleBuilder::build")
}

/// Amendment D, Part 2 (wire v56, `docs/SPEC_RATIFICATIONS.md` §21):
/// `Inst::InvokeIndirect` (Inst tag 69), carried by all four formats (the only
/// golden at header 56), OUTSIDE the lowering-target subset (no backend lowers
/// it; `LandingPad` is excluded by name too). Executable in the reference
/// interpreter under both panic strategies:
///
/// * `seven() -> i64` returns 7; `boom() -> i64` fails a `div_by_zero`
///   check (an unsited kinded assert) before it returns;
/// * `run_ok() -> i64` and `run_boom() -> i64` each `invoke_indirect` one of
///   them through its `fn` item (a `FnDef` constant at `fn() -> i64`); the
///   normal edge returns the call's result and the unwind edge enters a
///   CATCH-ALL pad (clause 0) that returns -1.
///
/// Under `PanicStrategy::Abort` (the default) `run_ok` returns 7 and
/// `run_boom` is the `div_by_zero` panic; under `PanicStrategy::Unwind`
/// `run_boom`'s raise is caught by the pad and it returns -1.
pub fn build_unwind_twins() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new_with_target_info("unwind_twins", panic_site_target());
    let thunk_ty = mb.add_func_type(vec![], vec![Ty::I64]);

    let mut fb = mb.function("seven", thunk_ty);
    let bb0 = fb.create_block();
    fb.switch_to_block(bb0);
    let seven = fb.iconst(Ty::I64, 7);
    fb.ret(vec![seven]);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    let seven_fn = fb.build();

    let mut fb = mb.function("boom", thunk_ty);
    let bb0 = fb.create_block();
    fb.switch_to_block(bb0);
    let fails = fb.const_value(Ty::Bool, Constant::Bool(false));
    fb.assert_kind(fails, trust_ir::AssertKind::DivByZero);
    let zero = fb.iconst(Ty::I64, 0);
    fb.ret(vec![zero]);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    let boom_fn = fb.build();

    for (name, target) in [("run_ok", seven_fn), ("run_boom", boom_fn)] {
        let mut fb = mb.function(name, thunk_ty);
        let bb0 = fb.create_block();
        let bb1 = fb.create_block();
        let bb2 = fb.create_block();
        fb.switch_to_block(bb0);
        let callee = fb.const_value(Ty::Func(thunk_ty), Constant::FnDef(target));
        let result = fb.invoke_indirect(callee, thunk_ty, vec![], bb1, vec![], bb2);
        fb.switch_to_block(bb1);
        fb.ret(vec![result]);
        fb.switch_to_block(bb2);
        let _ = fb.landingpad(false, vec![0]);
        let caught = fb.iconst(Ty::I64, -1);
        fb.ret(vec![caught]);
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        fb.build();
    }
    mb.build().or_fixture("ModuleBuilder::build")
}

/// Roadmap DG-63 (wire v62, the trust-ir prerequisite of WS5.5): the
/// entry-state pointee clause place `ClausePlace::ParamPointeeEntry`, carried
/// by all four formats (the only golden at header 62; binary clause-place
/// tag 10, text `pointee_entry(N)`).
///
/// `bump(limit: &u64, p: &mut u64) -> u64` increments `*p` and returns
/// `*limit`. Its summary states, over the values behind both references AT
/// ENTRY:
///
/// * `requires (bvult p_entry limit)` — `*p < *limit` before the call;
/// * `ensures (and (= p_exit (bvadd p_entry #x..01)) (= result limit))` —
///   the `&mut`'s exit value is its entry value plus one (`old(*p) + 1`, with
///   `MutParamExit`), and the result is `*limit`.
///
/// Each clause is restated by one `Pending` obligation scoped to `bump`, so
/// the place rides an obligation formula as well as a summary clause. Every
/// binding reads `u64` at `BitVec(64)`, a faithful reading of the pointee, so
/// the module validates. `proved` is false: no local row backs it in a wire
/// fixture.
pub fn build_param_pointee_place() -> Result<Module, FixtureError> {
    use trust_ir::FunctionSummary;
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};

    let bound = |text: &str, bindings: Vec<(&str, ClausePlace)>| {
        let mut formula = ProofFormula::smtlib2(text, "Bool");
        formula.bindings = bindings
            .into_iter()
            .map(|(name, place)| {
                (
                    name.to_string(),
                    ClauseBinding {
                        sort: ClauseSort::BitVec(64),
                        place,
                    },
                )
            })
            .collect();
        formula
    };
    let limit = ("limit", ClausePlace::ParamPointeeEntry { index: 0 });
    let p_entry = ("p_entry", ClausePlace::ParamPointeeEntry { index: 1 });
    let requires = bound("(bvult p_entry limit)", vec![p_entry, limit]);
    let ensures = bound(
        "(and (= p_exit (bvadd p_entry #x0000000000000001)) (= result limit))",
        vec![
            ("p_exit", ClausePlace::MutParamExit { index: 1 }),
            p_entry,
            ("result", ClausePlace::ResultSlot { index: 0 }),
            limit,
        ],
    );

    let mut mb = ModuleBuilder::new_with_target_info("param_pointee_place", panic_site_target());
    let ref_u64 = Ty::Ref(Box::new(Ty::U64));
    let mut_u64 = Ty::RefMut(Box::new(Ty::U64));
    let bump_ty = mb.add_func_type(vec![ref_u64.clone(), mut_u64.clone()], vec![Ty::U64]);
    let mut fb = mb.function("bump", bump_ty);
    let bb0 = fb.create_block();
    let limit_ref = fb.add_block_param(bb0, ref_u64);
    let p = fb.add_block_param(bb0, mut_u64);
    fb.switch_to_block(bb0);
    let old = fb.load(Ty::U64, p);
    let one = fb.uconst(Ty::U64, 1);
    let new = fb.add(Ty::U64, old, one);
    fb.store(Ty::U64, p, new);
    let result = fb.load(Ty::U64, limit_ref);
    fb.ret(vec![result]);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    let bump = fb.build();

    let mut module = mb.build().or_fixture("ModuleBuilder::build")?;
    module
        .functions
        .first_mut()
        .or_fixture("the bump function")?
        .summary = Some(
        FunctionSummary::new()
            .with_params(vec!["limit".to_string(), "p".to_string()])
            .requiring(requires.clone())
            .ensuring(ensures.clone()),
    );
    for (id, kind, description, formula) in [
        (
            0,
            ObligationKind::Precondition,
            "requires clause 0 of 'bump': *p < *limit at entry",
            requires,
        ),
        (
            1,
            ObligationKind::Postcondition,
            "ensures clause 0 of 'bump': *p is incremented and *limit returned",
            ensures,
        ),
    ] {
        module.proof_obligations.push(
            ProofObligation::new(ProofId::new(id), kind, ProofStatus::Pending, description)
                .with_function(bump)
                .with_formula(formula),
        );
    }
    Ok(module)
}

/// Plan item P (wire v52): an `Inst::Assert` of every kind, carried by all
/// four formats (the only goldens at header 52). Every function takes and
/// returns integers only, so both executable engines run it, and their panic
/// MESSAGES are compared (`lean_exec_differential.rs`):
///
/// * `bounds(i: usize, n: usize) -> usize` asserts `i < n` as
///   `bounds_check %i, %n` (Inst tag 63, AssertKind 3 with two operands);
/// * `misaligned(addr: usize, align: usize) -> usize` asserts `addr < align`
///   as `misaligned_ptr %align, %addr` (AssertKind 4);
/// * `divide(a: u32, b: u32) -> u32` / `remainder(..)` assert `b != 0` as
///   `div_by_zero` / `rem_by_zero` before the division;
/// * `null(p: usize) -> usize` asserts `p != 0` as `null_ptr`;
/// * `overflow(a: u8) -> u8` asserts `a != k` as `overflow OP_k` for the
///   eight ops in wire order, so `a = k` panics with op k's message;
/// * `legacy(c: bool) -> bool` asserts `c` with NO kind (`Unspecified`,
///   Inst tag 29), beside the kinded ones in the same v52 blob.
pub fn build_assert_kind() -> Result<Module, FixtureError> {
    use trust_ir::{AssertKind, AssertOverflowOp};

    let mut mb = ModuleBuilder::new("assert_kind");
    let pair =
        |mb: &mut ModuleBuilder, ty: Ty| mb.add_func_type(vec![ty.clone(), ty.clone()], vec![ty]);

    let ft = pair(&mut mb, Ty::Usize);
    {
        let mut fb = mb.function("bounds", ft);
        let entry = fb.create_block();
        let i = fb.add_block_param(entry, Ty::Usize);
        let n = fb.add_block_param(entry, Ty::Usize);
        fb.switch_to_block(entry);
        let ok = fb.icmp(ICmpOp::Ult, Ty::Usize, i, n);
        fb.assert_kind(ok, AssertKind::BoundsCheck { index: i, len: n });
        fb.ret(vec![i]);
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        fb.build();
    }
    let ft = pair(&mut mb, Ty::Usize);
    {
        let mut fb = mb.function("misaligned", ft);
        let entry = fb.create_block();
        let addr = fb.add_block_param(entry, Ty::Usize);
        let align = fb.add_block_param(entry, Ty::Usize);
        fb.switch_to_block(entry);
        let ok = fb.icmp(ICmpOp::Ult, Ty::Usize, addr, align);
        fb.assert_kind(
            ok,
            AssertKind::MisalignedPtr {
                required: align,
                found: addr,
            },
        );
        fb.ret(vec![addr]);
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        fb.build();
    }
    for (name, kind, op) in [
        ("divide", AssertKind::DivByZero, BinOp::UDiv),
        ("remainder", AssertKind::RemByZero, BinOp::URem),
    ] {
        let ft = pair(&mut mb, Ty::U32);
        let mut fb = mb.function(name, ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U32);
        let b = fb.add_block_param(entry, Ty::U32);
        fb.switch_to_block(entry);
        let zero = fb.uconst(Ty::U32, 0);
        let nonzero = fb.icmp(ICmpOp::Ne, Ty::U32, b, zero);
        fb.assert_kind(nonzero, kind);
        let q = fb.binop(op, Ty::U32, a, b);
        fb.ret(vec![q]);
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        fb.build();
    }
    let ft = mb.add_func_type(vec![Ty::Usize], vec![Ty::Usize]);
    {
        let mut fb = mb.function("null", ft);
        let entry = fb.create_block();
        let p = fb.add_block_param(entry, Ty::Usize);
        fb.switch_to_block(entry);
        let zero = fb.uconst(Ty::Usize, 0);
        let nonnull = fb.icmp(ICmpOp::Ne, Ty::Usize, p, zero);
        fb.assert_kind(nonnull, AssertKind::NullPtr);
        fb.ret(vec![p]);
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        fb.build();
    }
    let ft = mb.add_func_type(vec![Ty::U8], vec![Ty::U8]);
    {
        let mut fb = mb.function("overflow", ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U8);
        fb.switch_to_block(entry);
        for (k, op) in AssertOverflowOp::ALL.into_iter().enumerate() {
            let at = fb.uconst(Ty::U8, k as u128);
            let ok = fb.icmp(ICmpOp::Ne, Ty::U8, a, at);
            fb.assert_kind(ok, AssertKind::Overflow(op));
        }
        fb.ret(vec![a]);
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        fb.build();
    }
    let ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
    {
        let mut fb = mb.function("legacy", ft);
        let entry = fb.create_block();
        let c = fb.add_block_param(entry, Ty::Bool);
        fb.switch_to_block(entry);
        fb.assert(c);
        fb.ret(vec![c]);
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        fb.build();
    }
    mb.build().or_fixture("ModuleBuilder::build")
}

/// v51, the INST wire batch: every instruction and sub-op that existed in the
/// enums ahead of its wire tag, now carried by all four formats (the only
/// goldens at header 51):
///
/// * `make(x: i32, b: bool) -> (E, (i32, bool), E)` = `Inst::MakeAggregate`
///   (Inst tag 60) as an enum variant with a payload, a payload-free variant
///   and a tuple (the variant clause is a presence byte on the wire);
/// * `copy(dst, src, n: u64, byte: u8)` = `Inst::MemCopy` (Inst tag 61) in
///   both `overlap` spellings and `Inst::MemSet` (Inst tag 62);
/// * `bits(x: u32, k: u32) -> u32` = the four bit intrinsics (UnOp tags
///   9..=12) and the two rotates (BinOp tags 23, 24) chained;
/// * `sign(a: f64, b: f64) -> f64` = `BinOp::FCopySign` (BinOp tag 25).
pub fn build_inst_wire_batch() -> Result<Module, FixtureError> {
    use trust_ir::inst::{BinOp, UnOp};
    use trust_ir::ty::{EnumDef, EnumVariant};

    let mut mb = ModuleBuilder::new("inst_wire_batch");
    let e = Ty::Enum(mb.add_enum(EnumDef::new(
        trust_ir::EnumId::new(0),
        "E",
        vec![
            EnumVariant {
                name: "A".into(),
                fields: vec![Ty::I32, Ty::Bool],
                field_names: vec![],
            },
            EnumVariant {
                name: "B".into(),
                fields: vec![],
                field_names: vec![],
            },
        ],
    )));
    let pair = Ty::Tuple(vec![Ty::I32, Ty::Bool]);

    let ft = mb.add_func_type(
        vec![Ty::I32, Ty::Bool],
        vec![e.clone(), pair.clone(), e.clone()],
    );
    {
        let mut fb = mb.function("make", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        let b = fb.add_block_param(entry, Ty::Bool);
        fb.switch_to_block(entry);
        let a = fb.make_enum_variant(e.clone(), 0, vec![x, b]);
        let t = fb.make_aggregate(pair, vec![x, b]);
        let none = fb.make_enum_variant(e.clone(), 1, vec![]);
        fb.ret(vec![a, t, none]);
        // The v41 producer rule: a bodied function at v41+ states its
        // codegen license; this golden is affirmatively ungated.
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        fb.build();
    }

    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::U64, Ty::U8], vec![]);
    {
        let mut fb = mb.function("copy", ft);
        let entry = fb.create_block();
        let dst = fb.add_block_param(entry, Ty::Ptr);
        let src = fb.add_block_param(entry, Ty::Ptr);
        let n = fb.add_block_param(entry, Ty::U64);
        let byte = fb.add_block_param(entry, Ty::U8);
        fb.switch_to_block(entry);
        fb.memcopy(dst, src, n, false);
        fb.memcopy(dst, src, n, true);
        fb.memset(dst, byte, n);
        fb.ret(vec![]);
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        fb.build();
    }

    let ft = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![Ty::U32]);
    {
        let mut fb = mb.function("bits", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U32);
        let k = fb.add_block_param(entry, Ty::U32);
        fb.switch_to_block(entry);
        let mut last = x;
        for op in [UnOp::CtLz, UnOp::CtTz, UnOp::BSwap, UnOp::BitReverse] {
            last = fb.unop(op, Ty::U32, last);
        }
        for op in [BinOp::RotL, BinOp::RotR] {
            last = fb.binop(op, Ty::U32, last, k);
        }
        fb.ret(vec![last]);
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        fb.build();
    }

    let ft = mb.add_func_type(vec![Ty::F64, Ty::F64], vec![Ty::F64]);
    {
        let mut fb = mb.function("sign", ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::F64);
        let b = fb.add_block_param(entry, Ty::F64);
        fb.switch_to_block(entry);
        let r = fb.binop(BinOp::FCopySign, Ty::F64, a, b);
        fb.ret(vec![r]);
        fb.set_body_gate(trust_ir::BodyGate::Ungated);
        fb.build();
    }

    mb.build().or_fixture("ModuleBuilder::build")
}

/// v25 B1 scalars: `Ty::Isize` / `Ty::Usize` / `Ty::Char` (wire tags 33-35)
/// exercised in signatures, block params, arithmetic, and constants.
/// (`Ty::Error` is deliberately absent — producer-internal, unencodable.)
pub fn build_b1_scalars() -> Result<Module, FixtureError> {
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

    mb.build().or_fixture("ModuleBuilder::build")
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
pub fn build_mixed_producer_module() -> Result<Module, FixtureError> {
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

    mb.build().or_fixture("ModuleBuilder::build")
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
pub fn build_mixed_producer_cross_functy_mismatch() -> Result<Module, FixtureError> {
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

    mb.build().or_fixture("ModuleBuilder::build")
}

// ---------- fixture design rule: goldened fixtures must be VALID ----------

/// A declared non-C tuple byte image in a module whose function remains ungated.
/// The golden tests serialization and interpretation, not source refinement or
/// a claim that this layout applies to another language or target.
pub fn build_declared_tuple_v42() -> Result<Module, FixtureError> {
    let mut module = Module::new("declared_tuple_v42");
    module.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    });
    let tuple = Ty::Tuple(vec![Ty::U8, Ty::U64, Ty::U8]);
    let tuple_type = module
        .add_type(tuple.clone())
        .or_fixture("Module::add_type")?;
    module.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
        tuple_type,
        size: 16,
        align: 8,
        field_offsets: vec![8, 0, 9],
    });
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let mut function = Function::new(
        FuncId::new(0),
        "read_declared_image",
        signature,
        BlockId::new(0),
    );
    function.body_gate = Some(trust_ir::BodyGate::Ungated);
    let mut block = Block::new(BlockId::new(0));
    let v = ValueId::new;
    let ops = [
        (
            Some(v(0)),
            Inst::Alloca {
                ty: tuple.clone(),
                count: None,
                align: None,
            },
        ),
        (
            Some(v(1)),
            Inst::Const {
                ty: tuple.clone(),
                value: Constant::Aggregate(vec![
                    Constant::Int(17),
                    Constant::Int(0x1122334455667788),
                    Constant::Int(34),
                ]),
            },
        ),
        (
            None,
            Inst::Store {
                ty: tuple,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: None,
            },
        ),
        (
            Some(v(2)),
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            },
        ),
        (
            Some(v(3)),
            Inst::GEP {
                pointee_ty: Ty::U8,
                base: v(0),
                indices: vec![v(2)],
                inbounds: true,
            },
        ),
        (
            Some(v(4)),
            Inst::Load {
                ty: Ty::U64,
                ptr: v(3),
                volatile: false,
                align: None,
            },
        ),
        (None, Inst::Return { values: vec![v(4)] }),
    ];
    for (value, inst) in ops {
        let node = InstrNode::new(inst);
        block.body.push(if let Some(value) = value {
            node.with_result(value)
        } else {
            node
        });
    }
    function.blocks.push(block);
    module
        .try_add_function(function)
        .or_fixture("Module::try_add_function")?;
    Ok(module)
}

/// The first fixture-design rule stated at the top of this file — "every
/// fixture must validate cleanly under `trust_ir_build::validate_module`" — had
/// no enforcement anywhere: `conformance.rs::corpus_roundtrip` goldens the
/// bytes without validating the module, and both fixtures below had drifted
/// into invalidity unnoticed (`composition` asserted `proved` with nothing
/// behind it and pinned no target across its FFI boundary; `inst_atomic` swept
/// AtomicLoad/AtomicStore over orderings that are illegal for them).
///
/// This module is the guard for the two fixtures that regression covers. It
/// lives beside the generators rather than in one test target because the rule
/// is a property of the GENERATOR: it runs with the library's unit tests (this
/// file is the lib's `fixtures` module) and in every target that
/// `#[path]`-includes the file.
#[cfg(test)]
mod fixture_validity {
    /// `build_composition` exercises the v41 cross-crate carrier: a `proved`
    /// summary on a body-less declaration, authenticated by a `backed_by`
    /// `ExternRef` into a declared `ModuleImport`. Drop either half — the
    /// import or the `ExternRef::obligation` — and the `proved` bit is
    /// unbacked, which is exactly what `validate_module` now refuses.
    #[test]
    fn composition_fixture_is_a_valid_module() {
        let errors = trust_ir_build::validate_module(
            &super::build_composition().expect("the fixture builds"),
        );
        assert!(
            errors.is_empty(),
            "the composition fixture must validate: {errors:#?}"
        );
    }

    /// `build_text_directives` (roadmap WS4.2) is a well-formed module, so the
    /// directives it pins are pinned on IR a consumer would accept.
    #[test]
    fn text_directives_fixture_is_a_valid_module() {
        let errors = trust_ir_build::validate_module(
            &super::build_text_directives().expect("the fixture builds"),
        );
        assert!(
            errors.is_empty(),
            "the text_directives fixture must validate: {errors:#?}"
        );
    }

    /// `build_inst_atomic` must carry only orderings that are LEGAL for the
    /// operation carrying them.
    #[test]
    fn inst_atomic_fixture_is_a_valid_module() {
        let errors = trust_ir_build::validate_module(
            &super::build_inst_atomic().expect("the fixture builds"),
        );
        assert!(
            errors.is_empty(),
            "the inst_atomic fixture must validate: {errors:#?}"
        );
    }
}

// ---------- lean_library_envelope ----------

/// The Lean library envelope's source file, as `sources[]` records it. The
/// authoritative text stays in the envelope sidecar (NOT identity); the module
/// carries only its path, in `Module.files` (debug metadata).
pub const LEAN_ENVELOPE_SOURCE_PATH: &str = "Envelope.lean";

/// The envelope's `source_closure_sha256` for this fixture (a FIXTURE VALUE:
/// trust-ir never recomputes it), spelled into the module NAME exactly as the
/// standalone Lean lane names its module today
/// (`lean-library:<source_closure_sha256>`). A name is not an identity row:
/// the closure digest's in-format home is WS1/F-008's source-definition digest
/// on `CleanCicKernelRecheck` (not yet on the wire) plus the digest of the
/// module's `imports` rows (`docs/SPEC_RATIFICATIONS.md` §9).
pub const LEAN_ENVELOPE_SOURCE_CLOSURE_SHA256: &str =
    "5a0b1c2d3e4f5061728394a5b6c7d8e9f00112233445566778899aabbccddeef";

/// The authority string the Clean producer stamps on a body it certified.
pub const LEAN_ENVELOPE_TV_AUTHORITY: &str = "clean-kernel-tv";

/// `bodies[].carrier` / `bodies[].method`, carried as the TV obligation's
/// `ProofFormula` schema and payload (lineage-bound: `clean_cic_lineage_digest`
/// hashes the formula).
pub const LEAN_ENVELOPE_TV_BINDING_SCHEMA: &str = "clean.tv-binding/v1";
pub const LEAN_ENVELOPE_TV_BINDING_PAYLOAD: &str = "carrier=UInt64;method=definitional-equality";

/// A `kernel_only_declarations` row, carried as a schema-tagged REFERENCE:
/// trust-ir never parses or evaluates it, and the theorem STATEMENT lives only
/// in the sidecar / a `CleanCic` certificate (no CIC statement in a trust-ir
/// field — `docs/SPEC_RATIFICATIONS.md` §8, §9). Payload grammar:
/// `decl=<Clean declaration name>;source_sha256=<64 lowercase hex>`, the digest
/// being the declaration's source digest as the envelope records it (a FIXTURE
/// VALUE here) until WS1.12 lands F-008's source-definition digest.
pub const LEAN_ENVELOPE_THEOREM_REF_SCHEMA: &str = "clean.theorem-ref/v1";

/// The kernel-term vocabulary for the `addmul` translation-validation
/// certificate. The comparand is the SOURCE term
/// `fun a b : Nat => ((a*b) % 2^64 + a) % 2^64`, built by hand — never read
/// back from trust-ir's own denotation of the emitted body.
pub mod lean_envelope_terms {
    use trust_ir_build::clean_kernel::{BinderInfo, Expr, Level, Name};

    fn nat() -> Expr {
        Expr::const_str("Nat")
    }

    fn app2(f: &str, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str(f), [a, b])
    }

    fn wmod64(e: Expr) -> Expr {
        app2("Nat.mod", e, Expr::nat_lit_u128(1u128 << 64))
    }

    fn lam2(body: Expr) -> Expr {
        (0..2).fold(body, |acc, _| Expr::lam(BinderInfo::Default, nat(), acc))
    }

    fn refl_nat(e: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [nat(), e],
        )
    }

    /// `((a*b) % 2^64 + a) % 2^64` (a = bvar 1, b = bvar 0) — `a * b + a` at
    /// `UInt64`, read at `Nat`.
    pub fn addmul_body() -> Expr {
        let a = || Expr::bvar(1);
        let b = || Expr::bvar(0);
        wmod64(app2("Nat.add", wmod64(app2("Nat.mul", a(), b())), a()))
    }

    /// `((a+b) % 2^64 + a) % 2^64` — the body after a `Mul -> Add` miscompile.
    /// Used by the `b3.envelope.gap.*` F-008 ratchet (two_language_b3) and the
    /// proof-of-another-body refusal in `conformance.rs`, not by the corpus.
    pub fn add_add_body() -> Expr {
        let a = || Expr::bvar(1);
        let b = || Expr::bvar(0);
        wmod64(app2("Nat.add", wmod64(app2("Nat.add", a(), b())), a()))
    }

    /// `(comparand, proof)` = `(fun a b => body, fun a b => Eq.refl Nat body)`.
    pub fn comparand_and_proof(body: Expr) -> (Expr, Expr) {
        (lam2(body.clone()), lam2(refl_nat(body)))
    }
}

/// The `clean_backend_tv` certificate for the TV obligation `obligation`,
/// whose comparand/proof are `fun a b => body` / `fun a b => Eq.refl Nat body`.
pub fn lean_envelope_tv_certificate(
    obligation: &ProofObligation,
    body: trust_ir_build::clean_kernel::Expr,
) -> Result<ProofCertificate, FixtureError> {
    lean_envelope_tv_certificate_for(obligation, body, "addmul")
}

/// [`lean_envelope_tv_certificate`] for the envelope body whose link-time
/// symbol is `decl`: the directive cites `CleanTV.<decl>.denotes`, the theorem
/// the validator re-derives from the function the obligation is scoped to.
pub fn lean_envelope_tv_certificate_for(
    obligation: &ProofObligation,
    body: trust_ir_build::clean_kernel::Expr,
    decl: &str,
) -> Result<ProofCertificate, FixtureError> {
    use trust_ir::proof::{
        CleanCicKernelRecheck, KERNEL_ANCHOR_CLEAN_BACKEND_TV, clean_cic_lineage_digest,
        encode_clean_expr_v1,
    };
    let (comparand, proof) = lean_envelope_terms::comparand_and_proof(body);
    Ok(ProofCertificate {
        obligation: obligation.id,
        prover: "clean-backend-tv".to_string(),
        evidence: ProofEvidence::CleanCic {
            term: encode_clean_expr_v1(&proof).or_fixture("proof term encodes")?,
            context: encode_clean_expr_v1(&comparand).or_fixture("comparand encodes")?,
            lineage: clean_cic_lineage_digest(obligation),
            kernel_recheck: Some(CleanCicKernelRecheck {
                module: "CleanCompiler.BackendTV".to_string(),
                theorems: vec![format!("CleanTV.{decl}.denotes")],
                anchor: KERNEL_ANCHOR_CLEAN_BACKEND_TV.to_string(),
                allowed_axioms: vec![],
                binding: None,
            }),
        },
        assurance: None,
    })
}

/// The TV obligation the envelope's `bodies[addmul]` row becomes: function-
/// scoped, `Certified`, carrying `carrier`/`method` as its formula.
pub fn lean_envelope_tv_obligation(id: u32, addmul: FuncId) -> ProofObligation {
    ProofObligation::new(
        ProofId::new(id),
        ObligationKind::TranslationValidation,
        ProofStatus::Certified,
        "backend translation validation: 'addmul' denotes its Clean definition \
         (mod 2^64, kernel-decided)",
    )
    .with_function(addmul)
    .with_formula(ProofFormula::new(
        LEAN_ENVELOPE_TV_BINDING_SCHEMA,
        LEAN_ENVELOPE_TV_BINDING_PAYLOAD,
    ))
}

/// The Lean library envelope (`trust.lean.ir-library/v1`, written by
/// ~/trust `targo-trust/src/lean_build.rs`) with every load-bearing fact in
/// its in-format home — `docs/SPEC_RATIFICATIONS.md` §9, roadmap WS4.15:
///
/// * the module is named `lean-library:<source_closure_sha256>`;
/// * `sources[]` is the `Module.files` table (debug only; spans point into it);
/// * `bodies[addmul]` is a `Producer::Clean` function with
///   `body_gate: Gated{"clean-kernel-tv"}` and a function-scoped, `Certified`
///   `TranslationValidation` obligation (id 1) whose `CleanCic` certificate the
///   validator re-checks IN-PROCESS with the Clean kernel
///   (`clean_backend_tv`); `carrier`/`method` are that obligation's formula;
/// * `kernel_only_declarations[addmul_def]` is a `Pending`
///   `Custom{"trust.proof_item", "addmul_def"}` obligation (id 0) whose formula
///   is a `clean.theorem-ref/v1` REFERENCE (declaration name plus the
///   declaration's source digest as the envelope records it) — never the
///   statement.
///
/// The TV obligation is deliberately the LAST row so the WS4.15 mutation
/// control can drop it (with its certificate) without renumbering anything.
pub fn build_lean_library_envelope() -> Result<Module, FixtureError> {
    use trust_ir::BodyGate;

    let mut mb = ModuleBuilder::new(format!(
        "lean-library:{LEAN_ENVELOPE_SOURCE_CLOSURE_SHA256}"
    ));
    mb.set_default_producer(Producer::Clean);
    let source = mb.intern_file(LEAN_ENVELOPE_SOURCE_PATH);
    let binary = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let addmul = {
        let mut fb = mb.function("addmul", binary);
        fb.set_producer(Producer::Clean);
        fb.set_display_path("Envelope.addmul");
        fb.set_body_gate(BodyGate::Gated {
            authority: LEAN_ENVELOPE_TV_AUTHORITY.to_string(),
            evidence: None,
        });
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        fb.set_span(SourceSpan {
            file: source,
            line: 1,
            col: 42,
        });
        let ab = fb.mul(Ty::U64, a, b);
        let out = fb.add(Ty::U64, ab, a);
        fb.ret(vec![out]);
        fb.build()
    };
    let mut module = mb.build().or_fixture("ModuleBuilder::build")?;

    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Custom {
                namespace: "trust.proof_item".to_string(),
                name: "addmul_def".to_string(),
            },
            ProofStatus::Pending,
            "kernel-only Lean theorem 'addmul_def': statement and proof live in the \
             envelope sidecar; trust-ir carries a reference only",
        )
        .with_function(addmul)
        .with_formula(ProofFormula::new(
            LEAN_ENVELOPE_THEOREM_REF_SCHEMA,
            "decl=addmul_def;source_sha256=\
             3f6c1a0e9b2d4c5f60718293a4b5c6d7e8f90a1b2c3d4e5f60718293a4b5c6d7",
        )),
    );

    let tv = lean_envelope_tv_obligation(1, addmul);
    let certificate = lean_envelope_tv_certificate(&tv, lean_envelope_terms::addmul_body())?;
    module.proof_obligations.push(tv);
    module.proof_certificates.push(certificate);
    Ok(module)
}

// ---------- certificate_binding ----------

/// The proof-surface identity carrier (`CERTIFICATE_BINDING_FORMAT_VERSION`, the
/// wire half WS1.12 deferred; roadmap WS6.7(b)): two Clean functions,
/// `double(a) = a + a` and `quad(a) = double(a) + double(a)`, each licensed
/// `Gated { clean-kernel-tv }` and certified by a BOUND `clean_backend_tv`
/// certificate (`certify_identity_lineage_rung_bound`: the anchor
/// environment and re-derived statement digests, the name-sorted callee
/// symbols). Every optional binding field but one is populated —
/// `origin_module` names the module's one declared import, `source` a
/// declaration and its closure digest — and each lineage is re-keyed to the
/// symbol-keyed v8 form over the final binding. The exception is WS1.13's
/// island (`environment`): a PRESENT island is re-checked on every lane and
/// needs a real clean-kernel declaration encoding, so its bytes are pinned by
/// `binary::tests::certificate_binding_carries_its_island_losslessly_and_verbatim`
/// and the real-island round trip in `island_theorem.rs`
/// (`the_binary_writer_never_narrows_an_island_bound_certificate`), not here. `quad` composes `double` through one
/// `InheritedFromCallee` row. Each license carries `GateEvidence` naming its
/// TV obligation and `Module::function_body_digest` of its body (tag 3).
/// Validates clean, bound and evidence policies included. The
/// ONLY golden whose header word is the carrier's version; its text is lossy
/// (the kernel-recheck directive has no text spelling, F-070 / WS4.4).
pub fn build_certificate_binding() -> Result<Module, FixtureError> {
    use trust_ir::proof::{
        SourceDefinitionRef, clean_cic_lineage_digest_v8, module_symbol_resolver,
    };
    use trust_ir::{BodyGate, IdentityScheme, ModuleImport};

    let mut mb = ModuleBuilder::new("certificate_binding");
    mb.set_default_producer(Producer::Clean);
    let unary = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let gate = || BodyGate::Gated {
        authority: "clean-kernel-tv".to_string(),
        evidence: None,
    };
    let double = {
        let mut fb = mb.function("double", unary);
        fb.set_body_gate(gate());
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let out = fb.add(Ty::U64, a, a);
        fb.ret(vec![out]);
        fb.build()
    };
    let quad = {
        let mut fb = mb.function("quad", unary);
        fb.set_body_gate(gate());
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let d1 = fb.call(double, vec![a]);
        let d2 = fb.call(double, vec![a]);
        let out = fb.add(Ty::U64, d1, d2);
        fb.ret(vec![out]);
        fb.build()
    };
    let mut module = mb.build().or_fixture("ModuleBuilder::build")?;
    let origin = ProofDigest::sha256([0x0b; 32]);
    module.imports.push(ModuleImport {
        name: "certificate_binding_origin".to_string(),
        digest: origin,
        producer: Some(Producer::Clean),
        scheme: IdentityScheme::CURRENT,
    });

    let transform = || {
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "identity",
            "certificate-binding-golden",
            "1.0.0",
        )
    };
    // The two rows are #0 (`double`) and #1 (`quad`), in mint order.
    let oblig_ids = [ProofId::new(0), ProofId::new(1)];
    for (index, (function, decl)) in [(double, "Demo.double"), (quad, "Demo.quad")]
        .into_iter()
        .enumerate()
    {
        let id = ProofId::new(u32::try_from(index).or_fixture("two rows")?);
        let (_node, obligation, mut certificate) =
            trust_ir_build::certify_identity_lineage_rung_bound(
                &module,
                ProofLineageId::new(id.index()),
                id,
                transform(),
                function,
            )
            .or_fixture("both bodies are in the TV fragment")?;
        let ProofEvidence::CleanCic {
            lineage,
            kernel_recheck: Some(recheck),
            ..
        } = &mut certificate.evidence
        else {
            return Err(FixtureError {
                context: "certificate_binding",
                message: "the bound rung mints a CleanCic directive".to_string(),
            });
        };
        let binding = recheck.binding.as_mut().or_fixture("the rung is bound")?;
        binding.origin_module = Some(origin);
        binding.source = Some(SourceDefinitionRef {
            decl: decl.to_string(),
            closure_digest: ProofDigest::sha256(
                [0x0c + u8::try_from(index).or_fixture("two")?; 32],
            ),
        });
        *lineage = {
            let resolve = module_symbol_resolver(&module);
            clean_cic_lineage_digest_v8(&obligation, &resolve, Some(binding))
                .or_fixture("both functions resolve by symbol")?
        };
        module.proof_obligations.push(obligation);
        module.proof_certificates.push(certificate);
    }
    for (function, obligation) in [(double, oblig_ids[0]), (quad, oblig_ids[1])] {
        let body_digest = module
            .function_body_digest(function)
            .or_fixture("both bodies have a digest")?;
        module
            .function_by_id_mut(function)
            .or_fixture("built above")?
            .body_gate = Some(BodyGate::Gated {
            authority: "clean-kernel-tv".to_string(),
            evidence: Some(trust_ir::GateEvidence {
                obligation,
                body_digest,
            }),
        });
    }
    module.proof_certificates.push(ProofCertificate {
        obligation: oblig_ids[1],
        prover: "clean-backend-tv-compose".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: double,
            obligation: oblig_ids[0],
            external: None,
        },
        assurance: None,
    });
    Ok(module)
}

/// Storage is addressable geometry, never a whole initialized aggregate value.
/// The parent retains all explicit offsets, size and alignment.
pub fn build_storage_only() -> Result<Module, FixtureError> {
    let mut mb = ModuleBuilder::new("storage_only");
    let parent = mb.add_struct(StructDef {
        id: StructId::new(0),
        name: "StorageParent".into(),
        fields: vec![
            FieldDef {
                name: "head".into(),
                ty: Ty::U64,
                offset: Some(0),
            },
            FieldDef {
                name: "backing".into(),
                ty: Ty::Storage(trust_ir::StorageLayout::new(80, 8)),
                offset: Some(8),
            },
            FieldDef {
                name: "tail".into(),
                ty: Ty::U64,
                offset: Some(88),
            },
        ],
        size: Some(96),
        align: Some(8),
        repr: StructRepr::Rust,
        origin: None,
    });
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let root = mb.declare_function("root", sig);
    {
        let mut b = mb
            .define_function(root)
            .or_fixture("storage fixture definition")?;
        let entry = b.create_block();
        b.switch_to_block(entry);
        let slot = b.alloca(Ty::Struct(parent));
        let tail = b.gep_byte_offset(slot, 88);
        let value = b.uconst(Ty::U64, 7);
        b.store(Ty::U64, tail, value);
        let loaded = b.load(Ty::U64, tail);
        b.ret(vec![loaded]);
        b.build();
    }
    let mut m = mb.build().or_fixture("storage fixture module")?;
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    });
    Ok(m)
}

/// Nominal closure-frame data alone requires the origin wire tail. It grants
/// no callable target, source authentication, codegen license or proof status.
pub fn build_closure_frame_origin() -> Result<Module, FixtureError> {
    let mut module = Module::new("closure_frame_origin");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
            abi: None,
        })
        .or_fixture("closure origin signature")?;
    let closure = module
        .add_closure_type(ClosureTy {
            func: signature,
            captures: vec![],
        })
        .or_fixture("closure origin type")?;
    let stable_crate_id = 7u64;
    let mut def_path_hash = [0; 16];
    def_path_hash[..8].copy_from_slice(&stable_crate_id.to_le_bytes());
    def_path_hash[8..].copy_from_slice(&11u64.to_le_bytes());
    // The existing canonical argument encoding: version 1, empty argument list.
    let mut arguments = vec![1];
    arguments.extend_from_slice(&0u64.to_le_bytes());
    module
        .closure_layouts
        .push(trust_ir::ClosureLayoutDescriptor {
            origin: Some(trust_ir::ty::TypeOrigin::Rust {
                stable_crate_id,
                def_path_hash,
                args_digest: ProofDigest::sha256_domain(
                    trust_ir::ty::RUST_TYPE_ARGS_DOMAIN,
                    &arguments,
                ),
            }),
            closure,
            size: 0,
            align: 1,
            capture_offsets: vec![],
        });
    Ok(module)
}
