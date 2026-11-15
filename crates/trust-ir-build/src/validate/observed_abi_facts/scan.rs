// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'m> State<'m> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        layouts: &LayoutTable<'m>,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let module = layouts.module();
        w.admit(1, size_of::<Option<ObservedAbiLanes<'_>>>())?;
        self.lanes = Some(ObservedAbiLanes::new_observed(layouts, w.session, w.site)?);
        let mut i = 0;
        while let Some(function) = w.at(&module.functions, i)? {
            self.slots(layouts, function, w)?;
            if let Some(signature) = w.at(&module.func_types, function.ty.as_usize())? {
                w.admit(
                    1,
                    size_of::<Option<&trust_ir::signature_abi::SignatureAbi>>(),
                )?;
                if let Some(abi) = &signature.abi {
                    self.abi_ready(w)?;
                    self.pending_abi =
                        Some(abi.reconcile_function_observed(function, w.session, w.site)?);
                    self.abi_commit(function.ty.index(), w)?;
                }
            }
            w.next(&mut i)?;
        }
        i = 0;
        while let Some(signature) = w.at(&module.func_types, i)? {
            w.admit(
                1,
                size_of::<Option<&trust_ir::signature_abi::SignatureAbi>>(),
            )?;
            if let Some(abi) = &signature.abi {
                self.abi_ready(w)?;
                self.pending_abi = Some(abi.validate_observed(signature, w.session, w.site)?);
                w.admit(1, size_of::<bool>())?;
                if matches!(&self.pending_abi, Some(Ok(()))) {
                    self.abi_commit(i as u32, w)?;
                    self.abi_ready(w)?;
                    self.pending_abi = Some(abi.validate_target_observed(
                        module.target_info.as_ref(),
                        w.session,
                        w.site,
                    )?);
                }
                self.abi_commit(i as u32, w)?;
            }
            w.next(&mut i)?;
        }
        Ok(())
    }
}
