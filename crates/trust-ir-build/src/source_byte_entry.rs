// Copyright 2026 Andrew Yates | Apache-2.0
//! Closed byte-entry source/body equations. A pointer signature supplies no
//! pointee layout. The access roster below is reconstructed from every actual
//! instruction; only the original pinned source-family replay can export it.
//! Physical memory, lowering, machine bytes and callability are separate owners.

use std::collections::BTreeMap;
use trust_ir::{CallingConv, Constant, FuncId, Function, Inst, Module, Ty, ValueId};

/// The original entry's ordered input role, not a host pointer permission.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ByteEntryRole {
    Context,
    Output,
}

/// A derived original pointer, including dead GEPs whose checked arithmetic
/// may fault before a later access. Consumers must cover these addresses too.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByteEntryAddress<R = ByteEntryRole> {
    instruction: usize,
    role: R,
    base_offset: u64,
    offset: u64,
    inbounds: bool,
}
impl<R: Copy> ByteEntryAddress<R> {
    pub fn instruction(&self) -> usize {
        self.instruction
    }
    pub fn role(&self) -> R {
        self.role
    }
    pub fn base_offset(&self) -> u64 {
        self.base_offset
    }
    pub fn offset(&self) -> u64 {
        self.offset
    }
    pub fn is_inbounds(&self) -> bool {
        self.inbounds
    }
}

/// One actual typed, nonvolatile eight-byte access in source order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByteEntryAccess<R = ByteEntryRole> {
    instruction: usize,
    role: R,
    offset: u64,
    ty: Ty,
    alignment: u64,
    write: bool,
}
impl<R: Copy> ByteEntryAccess<R> {
    pub fn instruction(&self) -> usize {
        self.instruction
    }
    pub fn role(&self) -> R {
        self.role
    }
    pub fn offset(&self) -> u64 {
        self.offset
    }
    pub fn ty(&self) -> &Ty {
        &self.ty
    }
    pub fn alignment(&self) -> u64 {
        self.alignment
    }
    pub fn is_write(&self) -> bool {
        self.write
    }
}

impl<R> ByteEntryAccess<R> {
    fn map_role<S>(self, f: impl FnOnce(R) -> S) -> ByteEntryAccess<S> {
        ByteEntryAccess {
            instruction: self.instruction,
            role: f(self.role),
            offset: self.offset,
            ty: self.ty,
            alignment: self.alignment,
            write: self.write,
        }
    }
}
impl<R> ByteEntryAddress<R> {
    fn map_role<S>(self, f: impl FnOnce(R) -> S) -> ByteEntryAddress<S> {
        ByteEntryAddress {
            instruction: self.instruction,
            role: f(self.role),
            base_offset: self.base_offset,
            offset: self.offset,
            inbounds: self.inbounds,
        }
    }
}

#[derive(Clone)]
struct Value {
    ty: Ty,
    pointer: Option<(usize, u64)>,
    literal: Option<u64>,
}

pub(crate) struct Plan<'m> {
    pub(crate) function: &'m Function,
    pub(crate) accesses: Vec<ByteEntryAccess<usize>>,
    pub(crate) addresses: Vec<ByteEntryAddress<usize>>,
}

/// Separate source families share this canonical operation/type walk. The
/// original two-pointer/void family retains its exact signature and roles.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Profile {
    ContextOutput,
    FourPointerStatus,
}
impl Profile {
    fn arguments(self) -> usize {
        match self {
            Self::ContextOutput => 2,
            Self::FourPointerStatus => 4,
        }
    }
    fn inputs(self) -> usize {
        match self {
            Self::ContextOutput => 1,
            Self::FourPointerStatus => 2,
        }
    }
    fn returns(self) -> Vec<Ty> {
        match self {
            Self::ContextOutput => vec![],
            Self::FourPointerStatus => vec![Ty::U64],
        }
    }
}

pub(crate) fn plan_profile<'m>(
    module: &'m Module,
    function: &'m Function,
    profile: Profile,
) -> Result<Plan<'m>, String> {
    let target = module
        .target_info
        .as_ref()
        .ok_or("byte entry needs an explicit target")?;
    if target.pointer_size != 8
        || target.endianness != trust_ir::Endianness::Little
        || !module.target_has_canonical_scalar_layout()
        || module.functions.len() != 1
        || module.func_types.len() != 1
        || module.types.len() > 5
        || module
            .types
            .iter()
            .any(|ty| !matches!(ty, Ty::Ptr | Ty::I8 | Ty::U8 | Ty::I64 | Ty::U64))
        || !std::ptr::eq(&module.functions[0], function)
        || !module.imports.is_empty()
        || !module.globals.is_empty()
        || !module.structs.is_empty()
        || !module.enums.is_empty()
        || !module.records.is_empty()
        || !module.closure_types.is_empty()
        || !module.spec_modules.is_empty()
        || !module.predicates.is_empty()
        || !module.universes.is_empty()
        || !module.global_asm.is_empty()
        || !module.tuple_layouts.is_empty()
        || !module.drop_glue.is_empty()
        || !module.closure_layouts.is_empty()
        || !module.blobs.is_empty()
    {
        return Err("byte entry requires the complete closed primitive 64LE module".into());
    }
    let sig = module
        .func_type(function.ty)
        .ok_or("byte entry missing signature")?;
    if function.calling_conv != CallingConv::C
        || !function.attrs.is_empty()
        || !function.proofs.is_empty()
        || function.summary.is_some()
        || function.source_provenance.is_some()
        || sig.abi.is_some()
        || sig.is_vararg
        || sig.params != vec![Ty::Ptr; profile.arguments()]
        || sig.returns != profile.returns()
        || function.blocks.len() != 1
        || function.blocks[0].id != function.entry
        || !matches!(
            function.linkage,
            trust_ir::Linkage::External | trust_ir::Linkage::Internal | trust_ir::Linkage::Private
        )
    {
        return Err(match profile {
            Profile::ContextOutput => {
                "byte entry requires an unadorned C(Ptr,Ptr)->void definition"
            }
            Profile::FourPointerStatus => {
                "word status entry requires an unadorned C(Ptr,Ptr,Ptr,Ptr)->U64 definition"
            }
        }
        .into());
    }
    let block = &function.blocks[0];
    if block.params.len() != profile.arguments()
        || block.params.iter().any(|(_, ty)| *ty != Ty::Ptr)
    {
        return Err("byte entry original pointer formals differ".into());
    }
    if block.body.is_empty() || block.body.len() > 256 {
        return Err("byte entry needs 1..=256 actual instructions".into());
    }
    let mut values = BTreeMap::new();
    for (role, (id, _)) in block.params.iter().enumerate() {
        if values
            .insert(
                *id,
                Value {
                    ty: Ty::Ptr,
                    pointer: Some((role, 0)),
                    literal: None,
                },
            )
            .is_some()
        {
            return Err("byte entry needs distinct original pointer formals".into());
        }
    }
    let mut accesses = Vec::new();
    let mut addresses = Vec::new();
    for (instruction, node) in block.body.iter().enumerate() {
        if !node.proofs.is_empty() || node.proof_context.is_some() {
            return Err("byte entry refuses hidden instruction proof assumptions".into());
        }
        let get = |id: &ValueId| {
            values
                .get(id)
                .ok_or("byte entry uses an absent/forward SSA value")
        };
        let result = match &node.inst {
            Inst::Const {
                ty,
                value: Constant::Int(n),
            } if matches!(ty, Ty::I64 | Ty::U64) => {
                let fits = if *ty == Ty::I64 {
                    i64::try_from(*n).is_ok()
                } else {
                    u64::try_from(*n).is_ok()
                };
                if !fits {
                    return Err("byte entry integer literal is outside its actual type".into());
                }
                Some(Value {
                    ty: ty.clone(),
                    pointer: None,
                    literal: Some(*n as u64),
                })
            }
            Inst::Copy { ty, operand } => {
                let source = get(operand)?;
                if ty != &source.ty {
                    return Err("byte entry Copy type differs".into());
                }
                Some(source.clone())
            }
            Inst::GEP {
                pointee_ty: Ty::I8 | Ty::U8,
                base,
                indices,
                inbounds,
            } => {
                let [index] = indices.as_slice() else {
                    return Err("byte entry needs one constant byte index".into());
                };
                let index = get(index)?;
                let delta = index
                    .literal
                    .filter(|n| *n < (1_u64 << 63))
                    .ok_or("byte entry index is not a nonnegative constant i64")?;
                if index.ty != Ty::I64 {
                    return Err("byte entry index type must be exactly I64".into());
                }
                let base = get(base)?;
                let (role, offset) = base
                    .pointer
                    .ok_or("byte entry GEP is not rooted in an original pointer formal")?;
                let base_offset = offset;
                let offset = offset
                    .checked_add(delta)
                    .filter(|n| *n <= i64::MAX as u64)
                    .ok_or("byte entry offset overflow")?;
                addresses.push(ByteEntryAddress {
                    instruction,
                    role,
                    base_offset,
                    offset,
                    inbounds: *inbounds,
                });
                Some(Value {
                    ty: Ty::Ptr,
                    pointer: Some((role, offset)),
                    literal: None,
                })
            }
            Inst::Load {
                ty,
                ptr,
                volatile: false,
                align,
            } if word_ty(ty) => {
                let (role, offset) = get(ptr)?
                    .pointer
                    .ok_or("byte entry read address has no original role")?;
                if role >= profile.inputs() {
                    return Err("byte entry reads only original context storage".into());
                }
                access(&mut accesses, instruction, role, offset, ty, *align, false)?;
                Some(Value {
                    ty: ty.clone(),
                    pointer: None,
                    literal: None,
                })
            }
            Inst::Store {
                ty,
                ptr,
                value,
                volatile: false,
                align,
            } if word_ty(ty) => {
                let (role, offset) = get(ptr)?
                    .pointer
                    .ok_or("byte entry write address has no original role")?;
                if role < profile.inputs() || &get(value)?.ty != ty {
                    return Err(
                        "byte entry stores exact-typed values only to original output storage"
                            .into(),
                    );
                }
                access(&mut accesses, instruction, role, offset, ty, *align, true)?;
                None
            }
            Inst::Return { values: returned }
                if instruction + 1 == block.body.len()
                    && match profile {
                        Profile::ContextOutput => returned.is_empty(),
                        Profile::FourPointerStatus => {
                            returned.len() == 1 && get(&returned[0]).is_ok_and(|v| v.ty == Ty::U64)
                        }
                    } =>
            {
                None
            }
            _ => {
                return Err(
                    "byte entry refuses an instruction outside its complete closed effect profile"
                        .into(),
                );
            }
        };
        match (result, node.results.as_slice()) {
            (Some(value), [id]) if !values.contains_key(id) => {
                values.insert(*id, value);
            }
            (None, []) => {}
            _ => return Err("byte entry result arity/SSA identity differs".into()),
        }
    }
    if !matches!(&block.body.last().unwrap().inst, Inst::Return { .. }) {
        return Err("byte entry is missing its actual void return".into());
    }
    Ok(Plan {
        function,
        accesses,
        addresses,
    })
}

fn word_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::U64 | Ty::I64 | Ty::Ptr)
}
fn access(
    out: &mut Vec<ByteEntryAccess<usize>>,
    instruction: usize,
    role: usize,
    offset: u64,
    ty: &Ty,
    alignment: Option<u64>,
    write: bool,
) -> Result<(), String> {
    let alignment = alignment.unwrap_or(8);
    if alignment != 8 || offset % 8 != 0 || offset.checked_add(8).is_none() {
        return Err("byte entry requires complete naturally aligned word accesses".into());
    }
    out.push(ByteEntryAccess {
        instruction,
        role,
        offset,
        ty: ty.clone(),
        alignment,
        write,
    });
    Ok(())
}

/// Custody of a replayed whole-effect source equation and its independently
/// derived complete footprint. No public descriptor can construct this owner.
pub struct CheckedByteEntrySource<'m, R = ByteEntryRole> {
    report: &'m crate::ModuleValidationReport<'m>,
    module: &'m Module,
    function: FuncId,
    source: trust_ir::proof::SourceDefinitionRef,
    accesses: Vec<ByteEntryAccess<R>>,
    addresses: Vec<ByteEntryAddress<R>>,
}
impl<'m, R: Copy> CheckedByteEntrySource<'m, R> {
    pub fn module(&self) -> &'m Module {
        self.module
    }
    pub fn function(&self) -> FuncId {
        self.function
    }
    /// Select only in the same original allocation, not an equal module clone.
    pub fn function_in(&self, module: &Module) -> Result<FuncId, String> {
        if !std::ptr::eq(module, self.module) {
            return Err("byte entry source belongs to another original module".into());
        }
        Ok(self.function)
    }
    pub fn source(&self) -> &trust_ir::proof::SourceDefinitionRef {
        &self.source
    }
    pub fn accesses(&self) -> &[ByteEntryAccess<R>] {
        &self.accesses
    }
    pub fn addresses(&self) -> &[ByteEntryAddress<R>] {
        &self.addresses
    }
    pub fn validation_report(&self) -> &'m crate::ModuleValidationReport<'m> {
        self.report
    }
}

pub fn check_byte_entry_source<'m>(
    report: &'m crate::ModuleValidationReport<'m>,
) -> Result<CheckedByteEntrySource<'m>, String> {
    let p = check_source_profile(
        report,
        Profile::ContextOutput,
        trust_ir::proof::KERNEL_ANCHOR_CLEAN_BACKEND_BYTE_ENTRY_V1,
    )?;
    Ok(CheckedByteEntrySource {
        report: p.report,
        module: p.module,
        function: p.function,
        source: p.source,
        accesses: p
            .accesses
            .into_iter()
            .map(|a| {
                a.map_role(|i| {
                    if i == 0 {
                        ByteEntryRole::Context
                    } else {
                        ByteEntryRole::Output
                    }
                })
            })
            .collect(),
        addresses: p
            .addresses
            .into_iter()
            .map(|a| {
                a.map_role(|i| {
                    if i == 0 {
                        ByteEntryRole::Context
                    } else {
                        ByteEntryRole::Output
                    }
                })
            })
            .collect(),
    })
}
pub(crate) fn check_source_profile<'m>(
    report: &'m crate::ModuleValidationReport<'m>,
    profile: Profile,
    anchor: &str,
) -> Result<CheckedByteEntrySource<'m, usize>, String> {
    let module = report
        .validated_module()
        .ok_or("byte entry needs original successful validation")?;
    if !report.handle_registry_is_pinned() || !crate::codegen_license_errors_with(report).is_empty()
    {
        return Err(
            "byte entry requires pinned replay and current default body-license evidence".into(),
        );
    }
    let [function] = module.functions.as_slice() else {
        return Err("byte entry needs one original definition".into());
    };
    let derived = plan_profile(module, function, profile)?;
    let replayed = report
        .replayed_certificate_refs()
        .ok_or("byte entry lost replayed certificates")?;
    let certificates = module
        .proof_certificates
        .iter()
        .filter(|c| {
            replayed.contains(&c.lineage_ref())
                && c.evidence
                    .clean_cic_kernel_recheck()
                    .is_some_and(|r| r.anchor == anchor)
                && module
                    .proof_obligations
                    .iter()
                    .any(|o| o.id == c.obligation && o.function == Some(function.id))
        })
        .collect::<Vec<_>>();
    let [certificate] = certificates.as_slice() else {
        return Err("byte entry requires exactly its actual replayed source equation".into());
    };
    if !matches!(&function.body_gate, Some(trust_ir::BodyGate::Gated { authority, .. }) if authority == "clean-kernel-tv")
    {
        return Err("byte entry requires the original recognized source body gate".into());
    }
    let source = certificate
        .evidence
        .clean_cic_kernel_recheck()
        .and_then(|r| r.binding.as_deref())
        .and_then(|b| b.source.clone())
        .ok_or("byte entry certificate lost its source definition")?;
    Ok(CheckedByteEntrySource {
        report,
        module,
        function: function.id,
        source,
        accesses: derived.accesses,
        addresses: derived.addresses,
    })
}

/// Reflection retains the SAME original proof-bearing module and pinned pass.
#[cfg(feature = "source-value-operational")]
pub fn reflect_byte_entry_source_core_module_v1<'m>(
    source: &'m CheckedByteEntrySource<'m>,
    addresses: &[(FuncId, u64)],
) -> Result<crate::core_reflection::ReflectedCoreModuleV1<'m>, String> {
    crate::core_reflection::reflect_validated_source_module_v1(
        source.validation_report(),
        addresses,
    )
    .map_err(|e| e.to_string())
}

#[cfg(feature = "clean-tv-anchor")]
#[path = "source_byte_entry/denotation.rs"]
mod denotation;
#[cfg(feature = "clean-tv-anchor")]
pub(crate) use denotation::{denote, denote_profile};
