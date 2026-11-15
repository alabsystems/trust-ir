// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'c, 'm> State<'c, 'm> {
    pub(super) fn node<O: ExecutionObserver>(
        &mut self,
        layouts: &trust_ir::LayoutTable<'m>,
        catalog: &'c ModuleFunctionCatalog<'m>,
        physical_function: usize,
        function: &'m Function,
        physical_block: usize,
        block: BlockId,
        index: usize,
        inst: &Inst,
        node: &trust_ir::InstrNode,
        nominal: Option<&ObservedNominalTypeReachability<'m>>,
        schemas: Option<&DialectSchemaRegistry>,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(w)?;
        let values = self
            .values
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?;
        let module = catalog.source_module();
        w.admit(
            67,
            2 * size_of::<&Inst>() + size_of::<Vec<ValidationError>>(),
        )?;
        self.pending = match inst {
            Inst::Drop { .. } | Inst::DropInvoke { .. } => {
                observed_drop_place::validate_drop_place_observed(
                    module, inst, values, block, w.session, w.site,
                )?
            }
            Inst::Return { .. } | Inst::CoroSuspend { .. } => match self.signature {
                Some(signature) => observed_returns::validate_return_instruction_observed(
                    inst, signature, values, block, w.session, w.site,
                )?,
                None => Vec::new(), // Only the already-recorded actual missing signature.
            },
            Inst::Call { .. } | Inst::CallCannotUnwind { .. } | Inst::Invoke { .. } => {
                observed_direct_calls::validate_direct_call_observed(
                    catalog, function, inst, values, nominal, block, w.session, w.site,
                )?
            }
            Inst::Assert { site: Some(_), .. } | Inst::AssertInvoke { .. } => {
                observed_panic_sites::validate_panic_site_at_observed(
                    catalog,
                    physical_function,
                    physical_block,
                    index,
                    values,
                    w.session,
                    w.site,
                )?
            }
            Inst::SeqMap { .. } => observed_seq_map::validate_seq_map_observed(
                catalog, inst, block, w.session, w.site,
            )?,
            Inst::CallIndirect { .. }
            | Inst::CallIndirectCannotUnwind { .. }
            | Inst::InvokeIndirect { .. } => self
                .indirect
                .as_mut()
                .ok_or(ObservedValueError::InvalidRange)?
                .validate_at_observed(physical_block, index, values, nominal, w.session, w.site)?,
            Inst::ExtractField { .. } | Inst::InsertField { .. } => {
                observed_field_access::validate_field_access_observed(
                    module, inst, values, block, w.session, w.site,
                )?
            }
            Inst::MakeAggregate { .. } => {
                observed_make_aggregate::validate_make_aggregate_observed(
                    layouts, inst, values, block, w.session, w.site,
                )?
            }
            Inst::ArraySplat { .. } => observed_array_splat::validate_array_splat_observed(
                module, inst, values, block, w.session, w.site,
            )?,
            Inst::DialectOp(_) => observed_dialect_ops::validate_dialect_node_observed(
                module, node, values, schemas, block, w.session, w.site,
            )?,
            _ => Vec::new(),
        };
        self.merge(w)
    }
}
