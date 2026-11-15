// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Exhaustive borrowed classification for the model reflection boundary.
//!
//! No owned/cleared Module, Deref or as_module escape is constructed. All
//! Function fields remain inside the unchanged original function slice. Shared
//! layout/result-type queries still use the original Module and are an explicit
//! Rust reflection TCB; this is not a structural interpreter noninterference
//! theorem. Host callbacks can inspect the original Function, including gates.

use trust_ir::Module;

#[derive(Clone, Copy)]
pub(super) struct OperationalModuleFields<'m> {
    pub(super) name: &'m String,
    pub(super) functions: &'m Vec<trust_ir::Function>,
    pub(super) structs: &'m Vec<trust_ir::StructDef>,
    pub(super) enums: &'m Vec<trust_ir::EnumDef>,
    pub(super) records: &'m Vec<trust_ir::RecordDef>,
    pub(super) closure_types: &'m Vec<trust_ir::ClosureTy>,
    pub(super) globals: &'m Vec<trust_ir::Global>,
    pub(super) func_types: &'m Vec<trust_ir::FuncTy>,
    pub(super) types: &'m Vec<trust_ir::Ty>,
    pub(super) target_info: &'m Option<trust_ir::TargetInfo>,
    pub(super) files: &'m Vec<String>,
    pub(super) obligation_diagnostics: &'m Vec<trust_ir::ObligationDiagnostic>,
    pub(super) spec_modules: &'m Vec<trust_ir::SpecModule>,
    pub(super) universes: &'m Vec<trust_ir::Universe>,
    pub(super) predicates: &'m Vec<trust_ir::Pred>,
    pub(super) global_asm: &'m Vec<String>,
    pub(super) imports: &'m Vec<trust_ir::ModuleImport>,
    pub(super) tuple_layouts: &'m Vec<trust_ir::TupleLayoutDescriptor>,
    pub(super) completeness: &'m Option<trust_ir::ModuleCompleteness>,
    pub(super) drop_glue: &'m Vec<trust_ir::DropGlueEntry>,
    pub(super) closure_layouts: &'m Vec<trust_ir::ClosureLayoutDescriptor>,
    /// Operational: a `Constant::TensorBlob` executes by reading its row.
    pub(super) blobs: &'m Vec<trust_ir::blob::Blob>,
}

#[derive(Clone, Copy)]
pub(super) struct RetainedProofTables<'m> {
    pub(super) obligations: &'m Vec<trust_ir::ProofObligation>,
    pub(super) certificates: &'m Vec<trust_ir::ProofCertificate>,
}

impl<'m> OperationalModuleFields<'m> {
    /// No `..`: a new Module field must be classified before this compiles.
    pub(super) fn partition(module: &'m Module) -> (Self, RetainedProofTables<'m>) {
        let Module {
            name,
            functions,
            structs,
            enums,
            records,
            closure_types,
            globals,
            func_types,
            types,
            proof_obligations,
            proof_certificates,
            target_info,
            files,
            obligation_diagnostics,
            spec_modules,
            universes,
            predicates,
            global_asm,
            imports,
            tuple_layouts,
            completeness,
            drop_glue,
            closure_layouts,
            blobs,
        } = module;
        (
            Self {
                name,
                functions,
                structs,
                enums,
                records,
                closure_types,
                globals,
                func_types,
                types,
                target_info,
                files,
                obligation_diagnostics,
                spec_modules,
                universes,
                predicates,
                global_asm,
                imports,
                tuple_layouts,
                completeness,
                drop_glue,
                closure_layouts,
                blobs,
            },
            RetainedProofTables {
                obligations: proof_obligations,
                certificates: proof_certificates,
            },
        )
    }

    /// Every operational borrow must belong to the SAME admitted object, even
    /// for fields with no emitted ByteV1 slot. This is identity, not a partial
    /// equality that silently forgets a function field or unsupported table.
    pub(super) fn borrows(&self, module: &'m Module) -> bool {
        let (other, _) = Self::partition(module);
        std::ptr::eq(self.name, other.name)
            && std::ptr::eq(self.functions, other.functions)
            && std::ptr::eq(self.structs, other.structs)
            && std::ptr::eq(self.enums, other.enums)
            && std::ptr::eq(self.records, other.records)
            && std::ptr::eq(self.closure_types, other.closure_types)
            && std::ptr::eq(self.globals, other.globals)
            && std::ptr::eq(self.func_types, other.func_types)
            && std::ptr::eq(self.types, other.types)
            && std::ptr::eq(self.target_info, other.target_info)
            && std::ptr::eq(self.files, other.files)
            && std::ptr::eq(self.obligation_diagnostics, other.obligation_diagnostics)
            && std::ptr::eq(self.spec_modules, other.spec_modules)
            && std::ptr::eq(self.universes, other.universes)
            && std::ptr::eq(self.predicates, other.predicates)
            && std::ptr::eq(self.global_asm, other.global_asm)
            && std::ptr::eq(self.imports, other.imports)
            && std::ptr::eq(self.tuple_layouts, other.tuple_layouts)
            && std::ptr::eq(self.completeness, other.completeness)
            && std::ptr::eq(self.drop_glue, other.drop_glue)
            && std::ptr::eq(self.closure_layouts, other.closure_layouts)
            && std::ptr::eq(self.blobs, other.blobs)
    }
}

impl RetainedProofTables<'_> {
    pub(super) fn borrows(&self, module: &Module) -> bool {
        std::ptr::eq(self.obligations, &module.proof_obligations)
            && std::ptr::eq(self.certificates, &module.proof_certificates)
    }
}
