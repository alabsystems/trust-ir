// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        catalog: &ModuleFunctionCatalog<'_>,
        function: usize,
        block: usize,
        index: usize,
        values: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let module = catalog.source_module();
        let function = work
            .at(&module.functions, function)?
            .ok_or(ObservedValueError::InvalidRange)?;
        let block = work
            .at(&function.blocks, block)?
            .ok_or(ObservedValueError::InvalidRange)?;
        let node = work
            .at(&block.body, index)?
            .ok_or(ObservedValueError::InvalidRange)?;
        work.admit(16, size_of::<Request<'_>>())?;
        let (kind, panic) = match &node.inst {
            Inst::Assert {
                kind,
                site: Some(site),
                ..
            }
            | Inst::AssertInvoke { kind, site, .. } => (kind, site),
            _ => return Ok(()),
        };
        let request = Request {
            function,
            block: block.id,
            index: u32::try_from(index).unwrap_or(u32::MAX),
            panic,
        };
        self.location(module, request, work)?;
        let Some(entry) = catalog.unique_observed(panic.entry, work.session, work.site)? else {
            return self.scalar(
                ValidationError::CalleeNotFound {
                    block: block.id.index(),
                    callee_id: panic.entry.index(),
                },
                work,
            );
        };
        let signature = match function_signature_observed(module, entry, work.session, work.site)? {
            Ok(signature) => signature,
            Err(error) => {
                self.pending = Some(error);
                return self.transfer_pending(work);
            }
        };
        work.admit(16, 2 * size_of::<usize>() + size_of::<bool>())?;
        let operands = kind.operand_count();
        if !shape::valid(signature, operands, work)? {
            return self.signature(request, signature, operands, work);
        }
        if let PanicLocation::Value(value) = panic.location {
            let expected = work
                .at(&signature.params, operands)?
                .ok_or(ObservedValueError::InvalidRange)?;
            if let Some(actual) = values.get_observed(value, work.session, work.site)?
                && !actual.structural_eq_observed(expected, work.session, work.site)?
            {
                self.operand(request, expected, actual, work)?;
            }
        }
        Ok(())
    }
}
