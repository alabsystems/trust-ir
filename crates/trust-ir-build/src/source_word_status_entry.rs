// Copyright 2026 Andrew Yates | Apache-2.0
//! Closed C(Ptr,Ptr,Ptr,Ptr)->U64 whole-effect source authority. The first two
//! original arguments are read inputs and the last two are write outputs.
//! Every access remains a canonical ByteV1 word operation; load-derived
//! addresses, calls, branches, allocation and nested regions remain refused.
//! Numeric argument roles supply no physical memory or invocation authority.

/// Same-module custody of the independently replayed whole source equation.
pub type CheckedWordStatusEntrySource<'m> =
    crate::source_byte_entry::CheckedByteEntrySource<'m, usize>;
/// Original word demand, indexed by its actual pointer argument (0 through 3).
pub type WordStatusEntryAccess = crate::source_byte_entry::ByteEntryAccess<usize>;
/// Original constant-offset address, indexed by its actual pointer argument.
pub type WordStatusEntryAddress = crate::source_byte_entry::ByteEntryAddress<usize>;

/// Requires the original successful pinned replay, exact new-family source
/// equation and current default body licence, preserving allocation identity.
pub fn check_word_status_entry_source<'m>(
    report: &'m crate::ModuleValidationReport<'m>,
) -> Result<CheckedWordStatusEntrySource<'m>, String> {
    crate::source_byte_entry::check_source_profile(
        report,
        crate::source_byte_entry::Profile::FourPointerStatus,
        trust_ir::proof::KERNEL_ANCHOR_CLEAN_BACKEND_WORD_STATUS_ENTRY_V1,
    )
}

#[cfg(feature = "clean-tv-anchor")]
pub(crate) fn denote(
    module: &trust_ir::Module,
    function: &trust_ir::Function,
) -> Result<(clean_kernel::Expr, clean_kernel::Expr), String> {
    crate::source_byte_entry::denote_profile(
        module,
        function,
        crate::source_byte_entry::Profile::FourPointerStatus,
    )
}

/// Reflect only the same original proof-bearing module from this pinned
/// pass; this constructs no entry proof, physical address or native authority.
#[cfg(feature = "source-value-operational")]
pub fn reflect_word_status_entry_source_core_module_v1<'m>(
    source: &'m CheckedWordStatusEntrySource<'m>,
    addresses: &[(trust_ir::FuncId, u64)],
) -> Result<crate::core_reflection::ReflectedCoreModuleV1<'m>, String> {
    crate::core_reflection::reflect_validated_source_module_v1(
        source.validation_report(),
        addresses,
    )
    .map_err(|e| e.to_string())
}
