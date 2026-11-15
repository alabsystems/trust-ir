// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A narrowly observed inner constituent of full module validation.
//!
//! Catalog construction is observed within its actual loop. The remaining
//! layout, authority, SSA/type/proof passes still run their original complete
//! validators and remain opaque to interior cancellation. This entry point is
//! not a fully observed preflight, a resource exemption, or new admission.

use super::*;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};

/// Run the unchanged pinned full validator using a function catalog constructed
/// under the caller's existing original session. A stopped operation returns
/// no report and therefore no validated-module/certificate capability.
///
/// Only catalog construction has inner observation today. Other validation
/// constituents remain explicitly unpriced/opaque and must be completed before
/// a consumer claims whole-preflight bounded cancellation or allocation.
pub fn validate_module_report_with_observed_catalog<'m, O: ExecutionObserver>(
    module: &'m Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Result<ModuleValidationReport<'m>, ObservedValueError> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::ModuleLookup,
        site,
        work: 1,
        copy_bytes: core::mem::size_of::<ModuleValidationReport<'m>>(),
    })?;
    let catalog = ModuleFunctionCatalog::new_observed(module, session, site)?;
    let report =
        validate_module_with_config_filtered_catalog(None, &ValidationConfig::pinned(), catalog);
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Publication,
        site,
        work: 0,
        copy_bytes: 0,
    })?;
    Ok(report)
}

#[cfg(test)]
mod tests;
