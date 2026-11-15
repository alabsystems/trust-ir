// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'c, 'm> State<'c, 'm> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        layouts: &trust_ir::LayoutTable<'m>,
        catalog: &'c ModuleFunctionCatalog<'m>,
        physical_function: usize,
        census: NominalCensus,
        nominal: Option<&ObservedNominalTypeReachability<'m>>,
        schemas: Option<&DialectSchemaRegistry>,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(6, 3 * size_of::<bool>() + size_of::<&Module>())?;
        let module = catalog.source_module();
        if !core::ptr::eq(module, layouts.module())
            || nominal.is_some() != (census.handle || census.dialect)
            || nominal.is_some_and(|n| !core::ptr::eq(module, n.source_module()))
        {
            return Err(ObservedValueError::InvalidRange);
        }
        let function = w
            .at(&module.functions, physical_function)?
            .ok_or(ObservedValueError::InvalidRange)?;
        w.admit(1, size_of::<Option<Result<&FuncTy, ValidationError>>>())?;
        self.getter = Some(observed_returns::function_signature_observed(
            module, function, w.session, w.site,
        )?);
        // A returned semantic error stays parent-owned during reserve/admission.
        w.admit(1, 0)?;
        if matches!(&self.getter, Some(Err(_))) {
            w.reserve(&mut self.errors)?;
        }
        w.admit(
            2,
            size_of::<Option<&FuncTy>>() + size_of::<ValidationError>(),
        )?;
        match self.getter.take().ok_or(ObservedValueError::InvalidRange)? {
            Ok(signature) => self.signature = Some(signature),
            Err(error) => self.errors.push(error),
        }
        w.admit(1, size_of::<Option<ObservedValueTypes>>())?;
        self.values = Some(build_module_value_types_observed(
            function, module, w.session, w.site,
        )?);
        if census.handle
            && let Some(nominal) = nominal
        {
            if ObservedHandleEnumGuards::function_reads_a_non_tag_lane_observed(
                function, w.session, w.site,
            )? {
                w.admit(1, size_of::<Option<ObservedHandleEnumGuards<'_>>>())?;
                self.guards = Some(ObservedHandleEnumGuards::new_observed(
                    function, w.session, w.site,
                )?);
            }
            if ObservedSealedHandleSlots::function_allocates_a_handle_observed(
                function, nominal, w.session, w.site,
            )? {
                w.admit(1, size_of::<Option<ObservedSealedHandleSlots<'_>>>())?;
                self.slots = Some(ObservedSealedHandleSlots::new_observed(
                    layouts, function, nominal, w.session, w.site,
                )?);
            }
        }
        w.admit(1, size_of::<Option<ObservedIndirectCalls<'_, '_>>>())?;
        self.indirect = Some(ObservedIndirectCalls::new_observed(
            catalog,
            physical_function,
            w.session,
            w.site,
        )?);
        self.ready(w)?;
        self.pending = observed_effect_claims::validate_function_effect_claims_observed(
            function,
            Some(module),
            w.session,
            w.site,
        )?;
        self.merge(w)?;
        self.ready(w)?;
        self.pending = observed_enum_switch_coverage::validate_exhaustive_switch_cases_observed(
            layouts,
            function,
            self.values
                .as_ref()
                .ok_or(ObservedValueError::InvalidRange)?,
            w.session,
            w.site,
        )?;
        self.merge(w)?;
        self.ready(w)?;
        self.pending = observed_entry_params::validate_entry_params_observed(
            module, function, w.session, w.site,
        )?;
        self.merge(w)?;
        let mut b = 0;
        while let Some(block) = w.at(&function.blocks, b)? {
            let mut n = 0;
            while let Some(node) = w.at(&block.body, n)? {
                if let Some(nominal) = nominal {
                    self.ready(w)?;
                    self.pending =
                        observed_nominal_instructions::validate_nominal_instruction_types_observed(
                            module,
                            node,
                            self.values
                                .as_ref()
                                .ok_or(ObservedValueError::InvalidRange)?,
                            nominal,
                            block.id,
                            n,
                            self.guards.as_ref(),
                            self.slots.as_ref(),
                            &function.name,
                            w.session,
                            w.site,
                        )?;
                    self.merge(w)?;
                }
                self.node(
                    layouts,
                    catalog,
                    physical_function,
                    function,
                    b,
                    block.id,
                    n,
                    &node.inst,
                    node,
                    nominal,
                    schemas,
                    w,
                )?;
                w.next(&mut n)?;
            }
            w.next(&mut b)?;
        }
        Ok(())
    }
}
