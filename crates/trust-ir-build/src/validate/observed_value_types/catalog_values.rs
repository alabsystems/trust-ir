// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Duplicate-aware original switch-selector type-map context, data only.
use super::*;
/// Original switch literal inference differs from Module::function lookup:
/// direct calls must resolve through this actual duplicate-aware catalog.
/// Reuse the complete actual observed map/borrow correction/retirement engine;
/// only direct-call return inference changes in this separately named context.
/// No candidate callback/map/source authority or original owner is introduced.
/// Existing standalone/module contexts retain their original exact behavior.
pub(in crate::validate) fn build_catalog_value_types_observed<O: ExecutionObserver>(
    function: &Function,
    catalog: &ModuleFunctionCatalog<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<ObservedValueTypes> {
    build(function, Context::Catalog(catalog), session, site)
}
