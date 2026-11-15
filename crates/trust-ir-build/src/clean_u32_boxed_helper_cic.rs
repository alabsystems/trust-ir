// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Checked typed-domain execution of the complete original tagged helper.
//!
//! This is a distinct CIC target, not extension of PrefixV1's absorbing run.
//! The original module/report/source equation and all seven wrapper nodes are
//! retained. Scalar execution is derived in its actual caller frame. No native,
//! Rust heap/ghost-frame, ARC, ABI, body-license or raw-total authority follows.
use crate::{
    clean_u32_boxed_prefix::prepare_tagged_u32_boxed_prefix,
    core_execution::Limits,
    source_value_operational::{
        CheckedSourceValueOperational, import_source_closure, strict_replay,
    },
};
use clean_kernel::{Environment, Expr};
use trust_ir::{FuncId, clean_boxed_u32::RuntimeSources};
mod proof;
mod syntax;

/// A closed receipt is minted only after the SAME strong replay for every
/// initialized proper-prefix claim and the quantified halted endpoint.
pub struct CheckedFullTaggedU32Helper<'receipt, 'source> {
    source: &'receipt CheckedSourceValueOperational<'source>,
    wrapper: FuncId,
    environment: Environment,
    steps: usize,
    prefixes: Vec<(Expr, Expr)>,
    complete: (Expr, Expr),
}
impl<'source> CheckedFullTaggedU32Helper<'_, 'source> {
    pub fn source(&self) -> &CheckedSourceValueOperational<'source> {
        self.source
    }
    pub fn wrapper(&self) -> FuncId {
        self.wrapper
    }
    pub fn environment(&self) -> &Environment {
        &self.environment
    }
    pub fn instruction_count(&self) -> usize {
        self.steps
    }
    pub fn prefix_claim(&self, budget: usize) -> Option<&Expr> {
        self.prefixes.get(budget).map(|p| &p.0)
    }
    pub fn prefix_proof(&self, budget: usize) -> Option<&Expr> {
        self.prefixes.get(budget).map(|p| &p.1)
    }
    pub fn complete_claim(&self) -> &Expr {
        &self.complete.0
    }
    pub fn complete_proof(&self) -> &Expr {
        &self.complete.1
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum FullHelperCicError {
    Subject(String),
    Replay(String),
}
impl core::fmt::Display for FullHelperCicError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "checked full tagged-helper refusal: {self:?}")
    }
}
impl std::error::Error for FullHelperCicError {}

/// Construct typed-domain whole-helper laws. Inputs are arbitrary UInt32 terms,
/// memory/host remain quantified with actual canonical admission. One ledger
/// covers all phases. The budget is node fuel, not native/provider work.
/// No raw-total claim, arbitrary context/provider or successful endpoint is an
/// argument. Lookup and construction limits retain their existing scope.
pub fn check_full_tagged_u32_boxed_helper_law<'receipt, 'source>(
    source: &'receipt CheckedSourceValueOperational<'source>,
    wrapper: FuncId,
    runtime_sources: &RuntimeSources<'_>,
    limits: Limits,
) -> Result<CheckedFullTaggedU32Helper<'receipt, 'source>, FullHelperCicError> {
    runtime_sources
        .bind()
        .map_err(|e| FullHelperCicError::Subject(format!("{e:?}")))?;
    let prepared = prepare_tagged_u32_boxed_prefix(source, wrapper)
        .map_err(|e| FullHelperCicError::Subject(e.to_string()))?;
    if prepared.unbox_id() == prepared.box_id() {
        return Err(FullHelperCicError::Subject(
            "box and unbox identities must be distinct".into(),
        ));
    }
    // Preparation checks original names AND C/nonvararg Ptr->U32/U32->Ptr
    // descriptors and the exact graph. The complete provider additionally
    // requires original imported declarations, never a name-only association.
    // Reflection emits IRByteFunctionV1.import exactly as blocks.is_empty();
    // Module.imports is a separate retained metadata table.
    for id in [prepared.unbox_id(), prepared.box_id()] {
        let declaration = source
            .source_value()
            .module()
            .functions
            .iter()
            .find(|f| f.id == id)
            .ok_or_else(|| FullHelperCicError::Subject("missing original import".into()))?;
        if !declaration.is_declaration() {
            return Err(FullHelperCicError::Subject(
                "tagged provider requires actual imported declarations".into(),
            ));
        }
    }
    let mut environment =
        clean_verify::eval_ir_tagged_u32_helper::build_tagged_u32_helper_spec_v1_with_stack()
            .map_err(|e| FullHelperCicError::Replay(e.to_string()))?
            .into_environment();
    import_source_closure(
        &mut environment,
        source.source_value().environment(),
        source.source_value(),
    )
    .map_err(FullHelperCicError::Replay)?;
    if environment
        .closure_digest(source.source_value().source())
        .map_err(|e| FullHelperCicError::Replay(e.to_string()))?
        != *source.source_value().source_closure_digest()
    {
        return Err(FullHelperCicError::Subject("source closure changed".into()));
    }
    let candidates =
        proof::derive(source, wrapper, &environment, limits).map_err(FullHelperCicError::Replay)?;
    for (i, (claim, term)) in candidates
        .prefixes
        .iter()
        .chain(core::iter::once(&candidates.complete))
        .enumerate()
    {
        strict_replay(&environment, claim, term)
            .map_err(|e| FullHelperCicError::Replay(format!("whole-helper claim {i}: {e}")))?;
    }
    Ok(CheckedFullTaggedU32Helper {
        source,
        wrapper,
        environment,
        steps: candidates.steps,
        prefixes: candidates.prefixes,
        complete: candidates.complete,
    })
}
