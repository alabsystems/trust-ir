// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual-module data reflection for Clean's versioned byte-addressed EvalIR.
//!
//! This is a semantic reconstruction boundary, NOT a proof or native admission
//! API. It reflects the actual CFG, calls, result lanes, layouts and imports;
//! it does not accept a certificate's proposed interpretation. The Rust
//! reflector and layout implementation remain part of the semantic TCB.
//! Function addresses are explicit execution-environment inputs, not guessed
//! from function IDs. Relating them to a native image is a separate obligation.
//! The first profile requires an explicit canonical 64-bit little-endian
//! target. Unsupported instructions, semantic annotations and representations
//! are refused, never erased into an executable-looking empty program.

use clean_kernel::{Expr, Name};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use trust_ir::{
    Block, BlockId, CallingConv, Constant, FuncId, Function, Inst, InstrNode, Module, Ty, ValueId,
};

mod instructions;
mod runtime_fields;
use runtime_fields::OperationalModuleFields;
#[cfg(test)]
mod tests;
mod type_profile;

#[cfg(test)]
#[path = "core_reflection/cast_tests.rs"]
mod cast_tests;

#[cfg(test)]
#[path = "core_reflection/pointer_tests.rs"]
mod pointer_tests;

#[cfg(test)]
#[path = "core_reflection/atomic_layout_tests.rs"]
mod atomic_layout_tests;

#[cfg(test)]
#[path = "core_reflection/usize_tests.rs"]
mod usize_tests;

#[cfg(test)]
#[path = "core_reflection/rust_layout_tests.rs"]
mod rust_layout_tests;

#[cfg(test)]
#[path = "core_reflection/fat_pointer_tests.rs"]
mod fat_pointer_tests;

#[cfg(test)]
#[path = "core_reflection/rust_fat_layout_tests.rs"]
mod rust_fat_layout_tests;

#[cfg(test)]
#[path = "core_reflection/memory_index_profile_tests.rs"]
mod memory_index_profile_tests;

#[cfg(test)]
#[path = "core_reflection/typed_integer_gep_profile_tests.rs"]
mod typed_integer_gep_profile_tests;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoreReflectionError(String);

impl std::fmt::Display for CoreReflectionError {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        out.write_str(&self.0)
    }
}
impl std::error::Error for CoreReflectionError {}
type Result<T> = std::result::Result<T, CoreReflectionError>;

fn reject(reason: &str) -> CoreReflectionError {
    CoreReflectionError(reason.chars().take(1024).collect())
}
fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(c(name), Expr::app)
}
fn nat(value: u64) -> Expr {
    Expr::nat_lit(value)
}
fn boolean(value: bool) -> Expr {
    c(if value { "Bool.true" } else { "Bool.false" })
}
fn list(ty: &str, values: impl IntoIterator<Item = Expr>) -> Expr {
    let values: Vec<_> = values.into_iter().collect();
    values
        .into_iter()
        .rev()
        .fold(app("IRList.nil", [c(ty)]), |tail, head| {
            app("IRList.cons", [c(ty), head, tail])
        })
}
fn ids(values: &[ValueId]) -> Expr {
    list("Nat", values.iter().map(|id| nat(u64::from(id.index()))))
}
fn cc(value: CallingConv) -> u64 {
    match value {
        CallingConv::C => 0,
        CallingConv::Fast => 1,
        CallingConv::Cold => 2,
        CallingConv::Rust => 3,
        CallingConv::Swift => 4,
        // v45 (WS3.12): the reflected code is the WIRE tag, so the reflected
        // term and the binary encoding cannot drift.
        CallingConv::CUnwind => 5,
        CallingConv::SysV64 => 6,
        CallingConv::Win64 => 7,
        CallingConv::Aapcs => 8,
        CallingConv::EfiApi => 9,
        CallingConv::VectorCall => 10,
        CallingConv::RustCold => 11,
    }
}

/// A structural non-applicability check, not an inferred aggregate ABI.
/// Without calls, declarations, ABI attributes (checked by the common gate),
/// or by-value aggregates in ANY signature, this profile's execution needs no
/// aggregate-passing classification. Typed pointer pointees are not passed by
/// value; their full nominal types/layouts still undergo the common checks.
/// This establishes no Rust-source or native calling-convention refinement.
fn unclassified_scalar_leaf(module: &Module) -> Result<()> {
    if !module.global_asm.is_empty() || !module.imports.is_empty() {
        return Err(reject(
            "Unclassified byte-profile leaf module cannot contain assembly or imports",
        ));
    }
    let scalar_or_thin_pointer = |ty: &Ty| {
        matches!(
            ty,
            Ty::Bool
                | Ty::I8
                | Ty::I16
                | Ty::I32
                | Ty::I64
                | Ty::I128
                | Ty::U8
                | Ty::U16
                | Ty::U32
                | Ty::U64
                | Ty::U128
                | Ty::Usize
                | Ty::Unit
                | Ty::Ptr
                | Ty::Ref(_)
                | Ty::RefMut(_)
                | Ty::PtrConst(_)
                | Ty::PtrMut(_)
                | Ty::Func(_)
        )
    };
    // Include unused and indirectly referenced signatures, not just the types
    // of reachable functions. No table row is an exception to the ABI boundary.
    for signature in &module.func_types {
        if signature.is_vararg
            || !signature
                .params
                .iter()
                .chain(&signature.returns)
                .all(scalar_or_thin_pointer)
        {
            return Err(reject(
                "Unclassified byte-profile signatures must be nonvariadic scalar/thin-pointer only",
            ));
        }
    }
    for function in &module.functions {
        if function.blocks.is_empty() {
            return Err(reject(
                "Unclassified byte-profile leaf module cannot contain declarations",
            ));
        }
        for node in function.blocks.iter().flat_map(|block| &block.body) {
            if matches!(
                node.inst,
                Inst::Call { .. }
                    | Inst::CallIndirect { .. }
                    | Inst::CallCannotUnwind { .. }
                    | Inst::CallIndirectCannotUnwind { .. }
                    | Inst::Invoke { .. }
                    | Inst::SeqMap { .. }
            ) {
                return Err(reject(
                    "Unclassified byte-profile leaf module cannot contain calls",
                ));
            }
        }
    }
    Ok(())
}

/// The nominal index/count types admitted by actual-module reflection.
///
/// This selects reflected data, not a checked execution or native-admission
/// policy. Existing profiles retain their exact ByteV1 memory semantics;
/// the explicit typed-integer profile selects nominal GEP decoding only.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CoreMemoryIndexProfileV1 {
    /// Preserve the original profile: GEP indices and explicit allocation
    /// counts must have actual SSA type I64.
    StrictI64,
    /// Admit actual I64 and U64 operands and retain their nominal types in
    /// the memory site's operand catalog. ByteV1 still requires the resolved
    /// carrier to be below 2^63: negative I64 and high-half U64 values remain
    /// unmodelled. That runtime bound and all other memory premises must be
    /// established in the complete independently replayed execution claim.
    TypedI64U64BoundedV1,
    /// Retain actual signed/unsigned 8/16/32/64-bit GEP indices in an `mki`
    /// site. Clean's checked decoder admits nonnegative signed and canonical
    /// unsigned narrow words; both 64-bit types retain the bound below 2^63.
    /// Explicit allocation counts remain I64/U64 and keep their old `mkt`
    /// semantics. Every actual SSA/catalog, arithmetic and memory premise
    /// remains part of the independently replayed execution claim.
    TypedIntegerGepBoundedV1,
}

impl CoreMemoryIndexProfileV1 {
    fn admits_gep(self, ty: Option<&Ty>) -> bool {
        match self {
            Self::StrictI64 => ty == Some(&Ty::I64),
            Self::TypedI64U64BoundedV1 => matches!(ty, Some(Ty::I64 | Ty::U64)),
            Self::TypedIntegerGepBoundedV1 => matches!(
                ty,
                Some(Ty::I8 | Ty::U8 | Ty::I16 | Ty::U16 | Ty::I32 | Ty::U32 | Ty::I64 | Ty::U64)
            ),
        }
    }

    fn admits_count(self, ty: Option<&Ty>) -> bool {
        match self {
            Self::StrictI64 => ty == Some(&Ty::I64),
            Self::TypedI64U64BoundedV1 | Self::TypedIntegerGepBoundedV1 => {
                matches!(ty, Some(Ty::I64 | Ty::U64))
            }
        }
    }
}

/// Reflected data tied to the exact borrowed module. No field confers
/// checked semantics; a consumer must use the reviewed byte-profile vocabulary
/// and reconstruct/replay its complete endpoint proposition. Borrowed indexes
/// retain O(F + B) entries for F functions and B blocks, built once within the
/// existing reflection limits. They do not allocate a per-instruction index.
/// Named logical entry interpretation; neither profile asserts a native ABI.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CoreLogicalEntryProfileV1 {
    /// The original ByteV1 C/Fast entry and calling-convention refusals.
    CFastV1,
    /// Closed U64 -> U64 Rust leaf data for the separate Rust logical entry.
    /// Actual Rust convention is retained as wire tag 3, never relabelled C.
    RustU64LeafV1,
    /// Exact typed Const/Add/Return data; distinct from the identity leaf witness.
    RustU64AddLiteralV1,
}

/// Fixed interpretation of signature catalogs, independent of value admission.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CoreSignatureDescriptorProfileV1 {
    /// Existing strict reflection: every signature uses admitted value types.
    StrictValuesV1,
    /// Retain scalar float descriptors and actual vararg bits in signatures.
    /// Float values and variadic activation retain their existing model errors.
    RuntimeDeclarationsV1,
}

#[derive(Clone, Copy)]
enum ProofTableInterpretation<'m> {
    Strict(std::marker::PhantomData<&'m ()>),
    #[cfg(feature = "source-value-operational")]
    PriorSourceValidation(&'m crate::ModuleValidationReport<'m>),
}

impl ProofTableInterpretation<'_> {
    fn is_validated_runtime_context(self) -> bool {
        match self {
            Self::Strict(_) => false,
            #[cfg(feature = "source-value-operational")]
            Self::PriorSourceValidation(_) => true,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum TypeRole {
    Value,
    Descriptor,
}

#[derive(Debug)]
pub struct ReflectedCoreModuleV1<'module> {
    module: &'module Module,
    memory_index_profile: CoreMemoryIndexProfileV1,
    logical_entry_profile: CoreLogicalEntryProfileV1,
    signature_descriptor_profile: CoreSignatureDescriptorProfileV1,
    context: Expr,
    functions: BTreeMap<FuncId, &'module Function>,
    blocks: BTreeMap<(FuncId, BlockId), &'module Block>,
}
impl<'module> ReflectedCoreModuleV1<'module> {
    pub fn module(&self) -> &'module Module {
        self.module
    }
    pub fn context_term(&self) -> &Expr {
        &self.context
    }

    /// The immutable construction profile. It is not a proof that runtime
    /// operands satisfy ByteV1's bounds or that any memory access is permitted.
    pub fn logical_entry_profile(&self) -> CoreLogicalEntryProfileV1 {
        self.logical_entry_profile
    }

    /// Records catalog construction only; it grants no activation or ABI rule.
    pub fn signature_descriptor_profile(&self) -> CoreSignatureDescriptorProfileV1 {
        self.signature_descriptor_profile
    }

    pub fn memory_index_profile(&self) -> CoreMemoryIndexProfileV1 {
        self.memory_index_profile
    }

    /// Borrow the exact declaration by nominal ID in O(log F) time, including
    /// imports. This is raw target data, not a checked call/semantic summary.
    pub fn function(&self, id: FuncId) -> Option<&'module Function> {
        self.functions.get(&id).copied()
    }

    /// Borrow a block in O(log B) time. Block IDs are function-local keys, not
    /// vector positions. Imports, missing functions and absent blocks yield None.
    pub fn block(&self, function: FuncId, block: BlockId) -> Option<&'module Block> {
        self.blocks.get(&(function, block)).copied()
    }

    /// Borrow the actual node at a zero-based block-local PC. There is no node
    /// map or ID-sized allocation: after the indexed block lookup this uses get.
    /// The normal fetched-rule/kernel obligations remain necessary; lookup is
    /// not evidence that an execution has reached this coordinate.
    pub fn node(&self, function: FuncId, block: BlockId, pc: usize) -> Option<&'module InstrNode> {
        self.block(function, block)?.body.get(pc)
    }
}

/// Reflect a complete actual module, not a producer-supplied instruction census.
///
/// `addresses` must assign every declared function exactly one distinct nonzero
/// address. It is a parameter of the modeled execution environment; even a
/// well-formed assignment is not evidence of native symbol resolution.
/// Fixed structural caps bound this constructor's graph size, not total kernel
/// conversion work or byte usage of the whole compiler.
pub fn reflect_core_module_v1<'module>(
    module: &'module Module,
    addresses: &[(FuncId, u64)],
) -> Result<ReflectedCoreModuleV1<'module>> {
    reflect_core_module_v1_with_memory_profile(
        module,
        addresses,
        CoreMemoryIndexProfileV1::StrictI64,
    )
}

/// Reflect a complete actual module with an explicit nominal memory profile.
///
/// The target, metadata, structural limits and exact address-assignment checks
/// are identical to [`reflect_core_module_v1`]. The bounded typed profile adds
/// nominal GEP-index and explicit-allocation-count catalog rows; it does not
/// relabel operands or grant a runtime bound. Only `TypedIntegerGepBoundedV1`
/// constructs `mki` GEP sites, selecting the checked nominal integer decoder.
/// Legacy sites and all allocation-count evaluation remain unchanged. In
/// particular, reflection can retain a high-half U64 constant as data while
/// execution of that index/count remains unmodelled. A consumer must
/// replay the complete fetched execution claim, including the actual SSA
/// resolution, carrier bound, memory and ownership premises.
pub fn reflect_core_module_v1_with_memory_profile<'module>(
    module: &'module Module,
    addresses: &[(FuncId, u64)],
    memory_index_profile: CoreMemoryIndexProfileV1,
) -> Result<ReflectedCoreModuleV1<'module>> {
    reflect_with_entry_profile(
        module,
        addresses,
        memory_index_profile,
        CoreLogicalEntryProfileV1::CFastV1,
    )
}

/// Reflect actual closed U64 Rust leaf bodies through the SAME complete module
/// reflector. Calls, imports, by-value aggregates and recorded ABI claims remain
/// refused. This selects a logical interpretation only; execution still needs
/// the separate named Rust entry and complete kernel recheck.
pub fn reflect_core_rust_u64_leaf_v1<'module>(
    module: &'module Module,
    addresses: &[(FuncId, u64)],
) -> Result<ReflectedCoreModuleV1<'module>> {
    unclassified_scalar_leaf(module)?;
    if module
        .func_types
        .iter()
        .any(|sig| sig.params != [Ty::U64] || sig.returns != [Ty::U64])
    {
        return Err(reject(
            "Rust logical U64 leaf requires exact U64 -> U64 signatures",
        ));
    }
    reflect_with_entry_profile(
        module,
        addresses,
        CoreMemoryIndexProfileV1::StrictI64,
        CoreLogicalEntryProfileV1::RustU64LeafV1,
    )
}

/// Named logical arithmetic data profile. The complete original module passes
/// the same common reflector/validator; no body is reconstructed from source.
/// Exact Const/Add/Return shape is separately sealed by RustU64AdditionModule.
pub fn reflect_core_rust_u64_add_literal_v1<'m>(
    module: &'m Module,
    addresses: &[(FuncId, u64)],
) -> Result<ReflectedCoreModuleV1<'m>> {
    let mut reflected = reflect_core_rust_u64_leaf_v1(module, addresses)?;
    reflected.logical_entry_profile = CoreLogicalEntryProfileV1::RustU64AddLiteralV1;
    Ok(reflected)
}

/// Fixed opt-in C/Fast LE64 catalog interpretation for retained runtime declarations.
///
/// Every original signature/function ID, order, convention, import bit and
/// explicit address is retained, including float descriptors and the actual
/// vararg flag. Executable SSA types remain strict: descriptor cache entries
/// cannot authorize float values. All existing ABI, layout, metadata, identity
/// and structural bounds still apply. No proof-table or Release admission, body
/// permission, provider fidelity or native ABI adequacy follows.
pub fn reflect_core_module_with_runtime_signature_descriptors_v1<'module>(
    module: &'module Module,
    addresses: &[(FuncId, u64)],
) -> Result<ReflectedCoreModuleV1<'module>> {
    reflect_with_profiles(
        module,
        addresses,
        CoreMemoryIndexProfileV1::StrictI64,
        CoreLogicalEntryProfileV1::CFastV1,
        CoreSignatureDescriptorProfileV1::RuntimeDeclarationsV1,
    )
}

fn reflect_with_entry_profile<'module>(
    module: &'module Module,
    addresses: &[(FuncId, u64)],
    memory_index_profile: CoreMemoryIndexProfileV1,
    logical_entry_profile: CoreLogicalEntryProfileV1,
) -> Result<ReflectedCoreModuleV1<'module>> {
    reflect_with_profiles(
        module,
        addresses,
        memory_index_profile,
        logical_entry_profile,
        CoreSignatureDescriptorProfileV1::StrictValuesV1,
    )
}

fn reflect_with_profiles<'module>(
    module: &'module Module,
    addresses: &[(FuncId, u64)],
    memory_index_profile: CoreMemoryIndexProfileV1,
    logical_entry_profile: CoreLogicalEntryProfileV1,
    signature_descriptor_profile: CoreSignatureDescriptorProfileV1,
) -> Result<ReflectedCoreModuleV1<'module>> {
    reflect_with_table_interpretation(
        module,
        addresses,
        memory_index_profile,
        logical_entry_profile,
        signature_descriptor_profile,
        ProofTableInterpretation::Strict(std::marker::PhantomData),
    )
}

/// Crate-private fixed caller: the original SourceEq check, not a raw module or
/// caller-supplied evidence, supplies the successful PINNED admission report.
#[cfg(feature = "source-value-operational")]
pub(crate) fn reflect_checked_source_runtime_context_v1<'m>(
    source: &'m crate::CheckedSourceValueEquation<'m>,
    addresses: &[(FuncId, u64)],
) -> Result<ReflectedCoreModuleV1<'m>> {
    reflect_with_table_interpretation(
        source.module(),
        addresses,
        CoreMemoryIndexProfileV1::StrictI64,
        CoreLogicalEntryProfileV1::CFastV1,
        CoreSignatureDescriptorProfileV1::RuntimeDeclarationsV1,
        ProofTableInterpretation::PriorSourceValidation(source.validation_report()),
    )
}

/// Fixed checked-source caller for strict-value catalogs. This retains the
/// original proof fields by borrow and changes no default raw reflection gate.
#[cfg(feature = "source-value-operational")]
pub(crate) fn reflect_validated_source_module_v1<'m>(
    report: &'m crate::ModuleValidationReport<'m>,
    addresses: &[(FuncId, u64)],
) -> Result<ReflectedCoreModuleV1<'m>> {
    let module = report
        .validated_module()
        .ok_or_else(|| reject("source reflection requires a successful original-module report"))?;
    reflect_with_table_interpretation(
        module,
        addresses,
        CoreMemoryIndexProfileV1::StrictI64,
        CoreLogicalEntryProfileV1::CFastV1,
        CoreSignatureDescriptorProfileV1::StrictValuesV1,
        ProofTableInterpretation::PriorSourceValidation(report),
    )
}

fn reflect_with_table_interpretation<'module>(
    module: &'module Module,
    addresses: &[(FuncId, u64)],
    memory_index_profile: CoreMemoryIndexProfileV1,
    logical_entry_profile: CoreLogicalEntryProfileV1,
    signature_descriptor_profile: CoreSignatureDescriptorProfileV1,
    proof_tables: ProofTableInterpretation<'module>,
) -> Result<ReflectedCoreModuleV1<'module>> {
    const MAX_NODES: usize = 262_144;
    const MAX_ROWS: usize = 65_536;
    let (fields, retained_proofs) = OperationalModuleFields::partition(module);
    // Even fields without an emitted slot retain original object identity.
    if !fields.borrows(module) || !retained_proofs.borrows(module) {
        return Err(reject(
            "reflection partition changed original module identity",
        ));
    }
    #[cfg(feature = "source-value-operational")]
    if let ProofTableInterpretation::PriorSourceValidation(report) = proof_tables
        && (!report.handle_registry_is_pinned()
            || !report
                .validated_module()
                .is_some_and(|m| std::ptr::eq(m, module))
            || report.replayed_certificate_refs().is_none())
    {
        return Err(reject(
            "runtime context needs the same original pinned validation report",
        ));
    }
    let target = fields
        .target_info
        .as_ref()
        .ok_or_else(|| reject("byte profile needs an explicit target"))?;
    if target.pointer_size != 8
        || target.endianness != trust_ir::Endianness::Little
        || !module.target_has_canonical_scalar_layout()
        || !matches!(
            target.struct_passing,
            trust_ir::StructPassingPolicy::NativeC | trust_ir::StructPassingPolicy::Unclassified
        )
    {
        return Err(reject(
            "unsupported byte-profile target layout or aggregate passing policy",
        ));
    }
    if fields.functions.len() > MAX_ROWS
        || fields.func_types.len() > MAX_ROWS
        || fields.types.len() > MAX_ROWS
        || fields.structs.len() > MAX_ROWS
        || fields.tuple_layouts.len() > MAX_ROWS
        || addresses.len() > MAX_ROWS
    {
        return Err(reject("byte-profile table limit"));
    }
    let mut nodes = 0usize;
    let mut entries = 0usize;
    let mut charge = |count: usize| -> Result<()> {
        entries = entries
            .checked_add(count)
            .ok_or_else(|| reject("structural entry count overflow"))?;
        if entries > MAX_NODES {
            return Err(reject("byte-profile structural entry limit"));
        }
        Ok(())
    };
    for signature in fields.func_types {
        // ByteV1 currently records only logical carrier types. It has no
        // semantics for typed ABI entry/call transport (fresh by-value copies,
        // extension, hidden results or source-to-carrier bindings). Refusing
        // every table row prevents unused/FnPtr-only metadata from being
        // silently erased into an apparently exact reflected context.
        if signature.abi.is_some() {
            return Err(reject(
                "typed signature ABI transport requires an explicit byte-profile interpretation",
            ));
        }
        charge(signature.params.len())?;
        charge(signature.returns.len())?;
    }
    for definition in fields.structs {
        charge(definition.fields.len())?;
    }
    for layout in fields.tuple_layouts {
        charge(layout.field_offsets.len())?;
    }
    for function in fields.functions {
        charge(function.blocks.len())?;
        if function.blocks.len() > MAX_ROWS {
            return Err(reject("byte-profile block limit"));
        }
        for block in &function.blocks {
            charge(block.params.len())?;
            charge(block.body.len())?;
            for node in &block.body {
                charge(node.results.len())?;
                if let std::ops::ControlFlow::Break(error) =
                    node.inst.try_visit_value_operands(|_| match charge(1) {
                        Ok(()) => std::ops::ControlFlow::Continue(()),
                        Err(error) => std::ops::ControlFlow::Break(error),
                    })
                {
                    return Err(error);
                }
            }
            nodes = nodes
                .checked_add(block.body.len())
                .ok_or_else(|| reject("node count overflow"))?;
            if nodes > MAX_NODES || block.params.len() > MAX_ROWS {
                return Err(reject("byte-profile graph limit"));
            }
        }
    }
    if !fields.globals.is_empty()
        || !fields.enums.is_empty()
        || !fields.records.is_empty()
        || !fields.closure_types.is_empty()
        || !fields.spec_modules.is_empty()
        || !fields.predicates.is_empty()
        || !fields.universes.is_empty()
        || (!retained_proofs.certificates.is_empty()
            && !proof_tables.is_validated_runtime_context())
    {
        return Err(reject(
            "module table requires an explicit byte-profile interpretation",
        ));
    }
    for function in fields.functions {
        if !function.attrs.is_empty()
            || !function.proofs.is_empty()
            || function.summary.is_some()
            || function.source_provenance.is_some()
            || !match logical_entry_profile {
                CoreLogicalEntryProfileV1::CFastV1 => matches!(function.calling_conv, CallingConv::C | CallingConv::Fast),
                CoreLogicalEntryProfileV1::RustU64LeafV1 | CoreLogicalEntryProfileV1::RustU64AddLiteralV1 => function.calling_conv == CallingConv::Rust,
            }
            // "Replaceable" here is `{Weak, LinkOnce}`, NOT the proved table
            // `Linkage::is_interposable`, which also counts `ExternalWeak`.
            // Whether this profile should admit an `ExternalWeak` function is
            // an open owner question (2026-09-29); until it is ruled, the
            // spelling stays as it was, and gate 13's
            // `trust-ir-neighbour-spellings` mutant is exactly this set.
            || matches!(
                function.linkage,
                trust_ir::Linkage::Weak | trust_ir::Linkage::LinkOnce
            )
        {
            return Err(reject(
                "function claims, convention or replaceable linkage require a rule",
            ));
        }
        for node in function.blocks.iter().flat_map(|block| &block.body) {
            // InBounds is already an operational premise of the actual GEP.
            // Retain and check the flag; this annotation does not prove it.
            let only_gep_bounds = matches!(node.inst, Inst::GEP { inbounds: true, .. })
                && node
                    .proofs
                    .iter()
                    .all(|p| matches!(p, trust_ir::ProofAnnotation::InBounds));
            if (!node.proofs.is_empty() && !only_gep_bounds) || node.proof_context.is_some() {
                return Err(reject(
                    "instruction annotation requires an explicit semantic rule",
                ));
            }
        }
    }
    match signature_descriptor_profile {
        CoreSignatureDescriptorProfileV1::StrictValuesV1 => type_profile::check(module, MAX_NODES)?,
        CoreSignatureDescriptorProfileV1::RuntimeDeclarationsV1 => {
            type_profile::check_with_runtime_signature_descriptors(module, MAX_NODES)?;
        }
    }
    if target.struct_passing == trust_ir::StructPassingPolicy::Unclassified {
        unclassified_scalar_leaf(module)?;
    }
    // Opaque global assembly has no ByteV1 context slot or effect rule. This
    // shared new refusal closes the prior NativeC omission; no instruction or
    // runtime-counterexample claim follows from the source-derived finding.
    if !fields.global_asm.is_empty() {
        return Err(reject("global assembly has no byte-profile interpretation"));
    }
    // validate.rs:14254/14258 routes validate_module through the IDENTICAL
    // validate_module_with_config(module, &ValidationConfig::pinned()) call
    // used by validate_source_value.rs:112. The checked path reuses that actual
    // successful original report (private provenance + same-pointer/pinned
    // checks above), never a status-only substitute or another module's pass.
    // Raw/default paths keep the unchanged real validation call.
    if !proof_tables.is_validated_runtime_context()
        && let Some(error) = crate::validate_module(module).first()
    {
        return Err(reject(&format!("invalid actual Core module: {error:?}")));
    }
    let functions: BTreeMap<_, _> = fields.functions.iter().map(|f| (f.id, f)).collect();
    let mut address_map = BTreeMap::new();
    let mut used = BTreeSet::new();
    for &(function, address) in addresses {
        if address == 0
            || !functions.contains_key(&function)
            || !used.insert(address)
            || address_map.insert(function, address).is_some()
        {
            return Err(reject(
                "function address assignment is not exact and injective",
            ));
        }
    }
    if address_map.len() != functions.len() {
        return Err(reject("missing function address"));
    }
    let mut reflection = Reflection {
        module,
        fields,
        retains_release: proof_tables.is_validated_runtime_context(),
        memory_index_profile,
        layout_table: module.layout_table(),
        functions,
        types: HashMap::new(),
        visiting: HashSet::new(),
        layouts: Vec::new(),
        layout_terms: HashMap::new(),
    };
    let descriptor_role = match signature_descriptor_profile {
        CoreSignatureDescriptorProfileV1::StrictValuesV1 => TypeRole::Value,
        CoreSignatureDescriptorProfileV1::RuntimeDeclarationsV1 => TypeRole::Descriptor,
    };
    let mut signatures = Vec::with_capacity(fields.func_types.len());
    for (id, signature) in fields.func_types.iter().enumerate() {
        signatures.push(reflection.signature(id, signature, descriptor_role)?);
    }
    for ty in fields.types {
        let _ = reflection.ty_with_role(ty, descriptor_role)?;
    }
    for definition in fields.structs {
        let _ = reflection.ty_with_role(&Ty::Struct(definition.id), descriptor_role)?;
    }
    let mut bodies = Vec::with_capacity(fields.functions.len());
    let mut declared = Vec::with_capacity(fields.functions.len());
    let mut sites = Vec::with_capacity(nodes);
    let mut blocks = BTreeMap::new();
    for function in fields.functions {
        // Existing complete-module preflight and validation have already run.
        // Keep one borrowed block table, with explicit no-overwrite refusal.
        for block in &function.blocks {
            match blocks.entry((function.id, block.id)) {
                std::collections::btree_map::Entry::Vacant(entry) => {
                    entry.insert(block);
                }
                std::collections::btree_map::Entry::Occupied(_) => {
                    return Err(reject("duplicate actual block identity"));
                }
            }
        }
        bodies.push(reflection.function(function, &mut sites)?);
        declared.push(app(
            "IRByteFunctionV1.mk",
            [
                nat(u64::from(function.id.index())),
                nat(u64::from(function.ty.index())),
                nat(address_map[&function.id]),
                nat(cc(function.calling_conv)),
                boolean(function.blocks.is_empty()),
            ],
        ));
    }
    let program = app(
        "IRModule.mk",
        [list("IRFunc", bodies), list("IRGlobal", [])],
    );
    let context = app(
        "IRByteContextV1.mk",
        [
            program,
            list("IRByteLayoutV1", reflection.layouts),
            list("IRByteSignatureV1", signatures),
            list("IRByteFunctionV1", declared),
            list("IRByteSiteV1", sites),
        ],
    );
    Ok(ReflectedCoreModuleV1 {
        module,
        memory_index_profile,
        logical_entry_profile,
        signature_descriptor_profile,
        context,
        // Move the already constructed function index; do not rebuild it for
        // each execution catalog, callback, branch arm or call edge.
        functions: reflection.functions,
        blocks,
    })
}

struct Reflection<'module> {
    // Shared type/result/layout queries still accept the complete original
    // Module. This explicit Rust TCB escape is not a runtime noninterference
    // theorem; direct context construction uses the exhaustive borrowed fields.
    module: &'module Module,
    fields: OperationalModuleFields<'module>,
    retains_release: bool,
    memory_index_profile: CoreMemoryIndexProfileV1,
    /// The module's layouts, each type laid out once for the reflection.
    layout_table: trust_ir::LayoutTable<'module>,
    functions: BTreeMap<FuncId, &'module Function>,
    types: HashMap<(Ty, TypeRole), Expr>,
    visiting: HashSet<(Ty, TypeRole)>,
    layouts: Vec<Expr>,
    layout_terms: HashMap<Expr, Expr>,
}

impl Reflection<'_> {
    /// This profile never resolves a pointer-width integer from the host or
    /// the format's targetless default. Keep the resolved width in its own
    /// nominal constructor, even where its byte layout equals U64's.
    fn usize_bits(&self) -> Result<u32> {
        let target = self
            .fields
            .target_info
            .as_ref()
            .ok_or_else(|| reject("usize reflection needs an explicit target"))?;
        let bits = target
            .pointer_size
            .checked_mul(8)
            .ok_or_else(|| reject("usize target width overflow"))?;
        if bits != 64 {
            return Err(reject(
                "only target-indexed usize64 has byte-profile semantics",
            ));
        }
        Ok(bits)
    }

    fn signature(
        &mut self,
        id: usize,
        signature: &trust_ir::FuncTy,
        role: TypeRole,
    ) -> Result<Expr> {
        if signature.is_vararg && role == TypeRole::Value {
            return Err(reject("variadic byte-profile signature"));
        }
        Ok(app(
            "IRByteSignatureV1.mk",
            [
                nat(id as u64),
                self.types_with_role(&signature.params, role)?,
                self.types_with_role(&signature.returns, role)?,
                boolean(signature.is_vararg),
            ],
        ))
    }

    fn types(&mut self, types: &[Ty]) -> Result<Expr> {
        self.types_with_role(types, TypeRole::Value)
    }

    fn types_with_role(&mut self, types: &[Ty], role: TypeRole) -> Result<Expr> {
        Ok(list(
            "IRTy",
            types
                .iter()
                .map(|ty| self.value_type_with_role(ty, role))
                .collect::<Result<Vec<_>>>()?,
        ))
    }

    fn value_type(&mut self, ty: &Ty) -> Result<Expr> {
        self.value_type_with_role(ty, TypeRole::Value)
    }

    fn value_type_with_role(&mut self, ty: &Ty, role: TypeRole) -> Result<Expr> {
        if matches!(ty, Ty::Array(_, _) | Ty::Tuple(_)) {
            return Err(reject(
                "arrays and tuples have allocation layouts, not SSA value semantics in this profile",
            ));
        }
        self.ty_with_role(ty, role)
    }

    fn ty(&mut self, ty: &Ty) -> Result<Expr> {
        self.ty_with_role(ty, TypeRole::Value)
    }

    fn ty_with_role(&mut self, ty: &Ty, role: TypeRole) -> Result<Expr> {
        // All stored inline trees were bounded before validation. Table-ID
        // recursion is independently bounded by `visiting` below.
        if !(type_profile::supported(ty)
            || role == TypeRole::Descriptor && matches!(ty, Ty::F16 | Ty::F32 | Ty::F64))
        {
            return Err(reject("unsupported byte-profile type"));
        }
        let key = (ty.clone(), role);
        if let Some(result) = self.types.get(&key) {
            return Ok(result.clone());
        }
        if self.visiting.len() >= 128 || !self.visiting.insert(key.clone()) {
            return Err(reject("cyclic or over-depth byte-profile type"));
        }
        let mut fields = Vec::new();
        let term = match ty {
            Ty::Bool => c("IRTy.bool_"),
            Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128 => app(
                "IRTy.int_",
                [nat(u64::from(ty.bit_width().expect("integer width")))],
            ),
            Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 => app(
                "IRTy.uint_",
                [nat(u64::from(ty.bit_width().expect("integer width")))],
            ),
            Ty::F16 | Ty::F32 | Ty::F64 => app(
                "IRTy.float_",
                [nat(u64::from(ty.bit_width().expect("float width")))],
            ),
            Ty::Usize => app("IRTy.usize_", [nat(u64::from(self.usize_bits()?))]),
            Ty::Ptr => c("IRTy.ptr_"),
            Ty::Ref(inner) => app("IRTy.ref_", [self.ty_with_role(inner, role)?]),
            Ty::RefMut(inner) => app("IRTy.refmut_", [self.ty_with_role(inner, role)?]),
            Ty::PtrConst(inner) => app("IRTy.rawconst_", [self.ty_with_role(inner, role)?]),
            Ty::PtrMut(inner) => app("IRTy.rawmut_", [self.ty_with_role(inner, role)?]),
            Ty::FatPtr(kind) => match kind {
                trust_ir::FatPtrKind::Str => c("IRTy.fatstr_"),
                trust_ir::FatPtrKind::Slice(element) => {
                    let element = self
                        .fields
                        .types
                        .get(element.index() as usize)
                        .ok_or_else(|| reject("missing fat-slice element type"))?;
                    app("IRTy.fatslice_", [self.ty_with_role(element, role)?])
                }
                trust_ir::FatPtrKind::TraitObject { trait_id } => {
                    app("IRTy.fatdyn_", [nat(u64::from(*trait_id))])
                }
                // A container pointer addresses its header, not the tail's
                // string/slice/object contents. No invented pointee or trait
                // identity may collapse this distinction.
                trust_ir::FatPtrKind::ContainerLen => c("IRTy.containerlen_"),
                trust_ir::FatPtrKind::ContainerVtable => c("IRTy.containervtable_"),
            },
            Ty::Unit => c("IRTy.unit_"),
            Ty::Func(id) => {
                if self.fields.func_types.get(id.as_usize()).is_none() {
                    return Err(reject("missing function type"));
                }
                app("IRTy.func_", [nat(u64::from(id.index()))])
            }
            Ty::Array(element, count) => {
                let element = self
                    .fields
                    .types
                    .get(element.index() as usize)
                    .ok_or_else(|| reject("missing array element type"))?;
                app(
                    "IRTy.array_",
                    [self.ty_with_role(element, role)?, nat(*count)],
                )
            }
            Ty::Struct(id) => {
                let definition = self
                    .fields
                    .structs
                    .iter()
                    .find(|d| d.id == *id)
                    .ok_or_else(|| reject("missing struct type"))?;
                match definition.repr {
                    trust_ir::StructRepr::Rust => {
                        // A Rust descriptor is actual layout data, not a request
                        // to infer Rust layout or pass an aggregate by a guessed
                        // ABI. Even ZST placement must be explicit: the shared
                        // shape helper otherwise canonicalizes a missing offset
                        // to zero, losing this profile's exact-data boundary.
                        if definition.size.is_none()
                            || definition.align.is_none()
                            || definition.fields.iter().any(|field| field.offset.is_none())
                        {
                            return Err(reject(
                                "repr(Rust) byte profile requires explicit size, alignment and every field offset",
                            ));
                        }
                    }
                    trust_ir::StructRepr::C | trust_ir::StructRepr::Transparent => {}
                    trust_ir::StructRepr::Packed(_) => {
                        return Err(reject("packed nominal structs lack byte-profile admission"));
                    }
                }
                // Transparent remains its own nominal IRTy.struct_ row. The
                // shared ty_layout_shape below checks its exact carrier size,
                // alignment and zero offset; never flatten it to that carrier
                // or relabel its representation to gain admission.
                for field in &definition.fields {
                    fields.push(self.value_type_with_role(&field.ty, role)?);
                }
                app("IRTy.struct_", [nat(u64::from(id.index()))])
            }
            Ty::Tuple(elements) => {
                let descriptor = self
                    .module
                    .tuple_layout_descriptor(ty)
                    .map_err(|_| reject("incoherent actual tuple layout"))?
                    .ok_or_else(|| reject("missing actual tuple layout descriptor"))?;
                // The actual descriptor names a module type-table ID. Reuse
                // that nominal identity; neither arity nor inferred offsets
                // can identify a tuple's representation.
                let id = descriptor.tuple_type.index();
                for field in elements {
                    fields.push(self.ty_with_role(field, role)?);
                }
                app("IRTy.tuple_", [nat(u64::from(id))])
            }
            _ => return Err(reject("unsupported byte-profile type")),
        };
        let shape = self
            .layout_table
            .ty_layout(ty)
            .map_err(|_| reject("unresolved actual type layout"))?;
        let align = shape
            .align_bits
            .ok_or_else(|| reject("missing actual alignment"))?;
        if shape.size_bits % 8 != 0 || align % 8 != 0 || !(align / 8).is_power_of_two() {
            return Err(reject("non-byte or invalid actual layout"));
        }
        let offsets = match &shape.kind {
            trust_ir::TyLayoutKind::Struct { fields, .. }
            | trust_ir::TyLayoutKind::Tuple { fields } => fields
                .iter()
                .map(|field| {
                    let bits = field
                        .offset_bits
                        .ok_or_else(|| reject("missing actual field offset"))?;
                    if bits % 8 != 0 {
                        return Err(reject("non-byte actual field offset"));
                    }
                    Ok(nat(bits / 8))
                })
                .collect::<Result<Vec<_>>>()?,
            _ => Vec::new(),
        };
        let row = app(
            "IRByteLayoutV1.mk",
            [
                term.clone(),
                nat(shape.size_bits / 8),
                nat(align / 8),
                list("IRTy", fields),
                list("Nat", offsets),
            ],
        );
        // Distinct type-table IDs can name the same structural array type.
        // The semantic catalog has one row per reflected type, not one per
        // source spelling. A conflicting layout is never first-row-wins.
        if let Some(previous) = self.layout_terms.get(&term) {
            if previous != &row {
                return Err(reject("conflicting layouts for one reflected type"));
            }
        } else {
            self.layout_terms.insert(term.clone(), row.clone());
            self.layouts.push(row);
        }
        self.visiting.remove(&key);
        self.types.insert(key, term.clone());
        Ok(term)
    }

    fn constant(&mut self, ty: &Ty, value: &Constant) -> Result<Expr> {
        match value {
            Constant::Int(value) if ty.is_integer() => {
                let width = if *ty == Ty::Usize {
                    self.usize_bits()?
                } else {
                    ty.bit_width()
                        .ok_or_else(|| reject("integer literal width"))?
                };
                let bits = if width == 128 {
                    *value as u128
                } else {
                    (*value as u128) & ((1u128 << width) - 1)
                };
                Ok(app("IRConst.int_", [Expr::nat_lit_u128(bits)]))
            }
            Constant::U128(value) if *ty == Ty::U128 => {
                Ok(app("IRConst.int_", [Expr::nat_lit_u128(*value)]))
            }
            Constant::Bool(value) if *ty == Ty::Bool => Ok(app("IRConst.bool_", [boolean(*value)])),
            Constant::FnDef(function) => {
                let target = self
                    .functions
                    .get(function)
                    .ok_or_else(|| reject("unresolved function constant"))?;
                if *ty != Ty::Func(target.ty) {
                    return Err(reject("function constant type mismatch"));
                }
                Ok(app("IRConst.func_", [nat(u64::from(function.index()))]))
            }
            _ => Err(reject("unsupported byte-profile constant")),
        }
    }

    fn result_types(&self, node: &trust_ir::InstrNode) -> Result<Vec<Ty>> {
        if let Inst::Call { callee, .. } = node.inst {
            let function = self
                .functions
                .get(&callee)
                .ok_or_else(|| reject("missing call target"))?;
            Ok(self
                .fields
                .func_types
                .get(function.ty.as_usize())
                .ok_or_else(|| reject("missing call signature"))?
                .returns
                .clone())
        } else {
            Ok(node.result_tys(self.module))
        }
    }

    /// The nominal SSA operand catalog of a field site, or of a memory-index
    /// site in the explicitly selected bounded typed profile.
    ///
    /// Clean's ByteV1 `extractfield` (Clean `ee4dff170`) evaluates
    /// `ir_byte_extract_field_v1`, which takes the aggregate's NOMINAL type
    /// from this catalog: an old `IRByteSiteV1.mk` site has no catalog and the
    /// step halts `unmodelled` instead of reading the lane. Each row is an
    /// actual operand ID with its actual SSA type from this function's own
    /// value typing (block parameters and instruction results), never a type
    /// inferred from the runtime value; a missing type is refused. The catalog
    /// is reflected data, not an authentication of it: Clean's evaluator still
    /// checks the aggregate's admission, the lane's nominal type and the
    /// site's result lane. `InsertField` additionally retains the replacement's
    /// actual ID and nominal type; its result type is the aggregate's type.
    /// GEP/count catalogs retain nominal source identity. Only an explicitly
    /// selected `mki` GEP site reads the
    /// nominal index types; legacy `mk`/`mkt` memory evaluation remains erased.
    /// The selected decoder's complete bounds and accesses still need replay.
    fn operand_catalog(
        &mut self,
        node: &trust_ir::InstrNode,
        value_types: &HashMap<ValueId, Ty>,
    ) -> Result<Option<Expr>> {
        let inserted_operands;
        let operands: &[ValueId] = match &node.inst {
            Inst::ExtractField { aggregate, .. } => std::slice::from_ref(aggregate),
            Inst::InsertField {
                aggregate, value, ..
            } => {
                inserted_operands = [*aggregate, *value];
                &inserted_operands
            }
            Inst::GEP { indices, .. }
                if self.memory_index_profile != CoreMemoryIndexProfileV1::StrictI64 =>
            {
                indices.as_slice()
            }
            Inst::Alloca {
                count: Some(count), ..
            } if self.memory_index_profile != CoreMemoryIndexProfileV1::StrictI64 => {
                std::slice::from_ref(count)
            }
            _ => return Ok(None),
        };
        let mut seen = HashSet::with_capacity(operands.len());
        let mut rows = Vec::with_capacity(operands.len());
        for id in operands {
            // Clean requires unique operand IDs; a repeated operand is one row.
            if !seen.insert(*id) {
                continue;
            }
            let ty = value_types.get(id).ok_or_else(|| {
                reject(
                    if matches!(
                        node.inst,
                        Inst::ExtractField { .. } | Inst::InsertField { .. }
                    ) {
                        "field operand has no actual SSA type"
                    } else {
                        "memory index operand has no actual SSA type"
                    },
                )
            })?;
            rows.push(app(
                "IRByteOperandV1.mk",
                [nat(u64::from(id.index())), self.value_type(ty)?],
            ));
        }
        Ok(Some(list("IRByteOperandV1", rows)))
    }

    fn function(&mut self, function: &Function, sites: &mut Vec<Expr>) -> Result<Expr> {
        let mut value_types = HashMap::new();
        for block in &function.blocks {
            for (id, ty) in &block.params {
                value_types.insert(*id, ty.clone());
                let _ = self.value_type(ty)?;
            }
            for node in &block.body {
                let types = self.result_types(node)?;
                if types.len() != node.results.len() {
                    return Err(reject("result arity mismatch"));
                }
                for (id, ty) in node.results.iter().zip(types) {
                    value_types.insert(*id, ty);
                }
            }
        }
        let mut blocks = Vec::with_capacity(function.blocks.len());
        for block in &function.blocks {
            let mut body = Vec::with_capacity(block.body.len());
            for (index, node) in block.body.iter().enumerate() {
                if let Inst::GEP { indices, .. } = &node.inst
                    && indices
                        .iter()
                        .any(|id| !self.memory_index_profile.admits_gep(value_types.get(id)))
                {
                    return Err(reject(match self.memory_index_profile {
                        CoreMemoryIndexProfileV1::StrictI64 => {
                            "byte profile requires typed I64 GEP indices"
                        }
                        CoreMemoryIndexProfileV1::TypedI64U64BoundedV1 => {
                            "bounded typed byte profile requires I64/U64 GEP indices"
                        }
                        CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1 => {
                            "typed integer GEP profile requires signed/unsigned 8/16/32/64 indices"
                        }
                    }));
                }
                if let Inst::Alloca {
                    count: Some(count), ..
                } = &node.inst
                    && !self
                        .memory_index_profile
                        .admits_count(value_types.get(count))
                {
                    return Err(reject(match self.memory_index_profile {
                        CoreMemoryIndexProfileV1::StrictI64 => {
                            "byte profile requires typed I64 allocation count"
                        }
                        CoreMemoryIndexProfileV1::TypedI64U64BoundedV1
                        | CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1 => {
                            "bounded typed byte profile requires I64/U64 allocation count"
                        }
                    }));
                }
                let align = match &node.inst {
                    Inst::Load { align, .. }
                    | Inst::Store { align, .. }
                    | Inst::Alloca { align, .. } => {
                        if align.is_some_and(|a| !a.is_power_of_two()) {
                            return Err(reject("invalid explicit alignment"));
                        }
                        align.unwrap_or(0)
                    }
                    _ => 0,
                };
                let convention = match &node.inst {
                    Inst::Call { callee, .. } => {
                        self.functions
                            .get(callee)
                            .ok_or_else(|| reject("missing call target"))?
                            .calling_conv
                    }
                    Inst::CallIndirect { calling_conv, .. } => *calling_conv,
                    _ => function.calling_conv,
                };
                let results = self.result_types(node)?;
                let mut site = vec![
                    nat(u64::from(function.id.index())),
                    nat(u64::from(block.id.index())),
                    nat(index as u64),
                    nat(align),
                    nat(cc(convention)),
                    self.types(&results)?,
                ];
                // Only the explicit typed-integer GEP profile selects `mki`.
                // Fields and allocation counts retain `mkt`; other sites
                // keep `mk`. No catalog supplies runtime/access authority.
                let constructor = match self.operand_catalog(node, &value_types)? {
                    Some(operands) => {
                        site.push(operands);
                        if self.memory_index_profile
                            == CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1
                            && matches!(node.inst, Inst::GEP { .. })
                        {
                            "IRByteSiteV1.mki"
                        } else {
                            "IRByteSiteV1.mkt"
                        }
                    }
                    None => "IRByteSiteV1.mk",
                };
                sites.push(app(constructor, site));
                body.push(app(
                    "IRNode.mk",
                    [self.instruction(&node.inst)?, ids(&node.results)],
                ));
            }
            blocks.push(app(
                "IRBlock.mk",
                [
                    nat(u64::from(block.id.index())),
                    list(
                        "Nat",
                        block
                            .params
                            .iter()
                            .map(|(id, _)| nat(u64::from(id.index()))),
                    ),
                    list("IRNode", body),
                ],
            ));
        }
        let params = function
            .blocks
            .iter()
            .find(|b| b.id == function.entry)
            .map(|block| {
                list(
                    "Nat",
                    block
                        .params
                        .iter()
                        .map(|(id, _)| nat(u64::from(id.index()))),
                )
            })
            .unwrap_or_else(|| list("Nat", []));
        Ok(app(
            "IRFunc.mk",
            [
                nat(u64::from(function.id.index())),
                params,
                nat(u64::from(function.entry.index())),
                list("IRBlock", blocks),
            ],
        ))
    }
}

#[cfg(test)]
#[path = "core_reflection/runtime_signature_descriptor_tests.rs"]
mod runtime_signature_descriptor_tests;
