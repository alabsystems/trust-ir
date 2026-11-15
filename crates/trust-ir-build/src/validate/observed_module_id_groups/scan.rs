// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn structs<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut i = 0;
        while let Some(row) = w.at(&module.structs, i)? {
            let mut j = 0;
            while j < i {
                w.admit(1, 0)?;
                let earlier = w
                    .at(&module.structs, j)?
                    .ok_or(ObservedValueError::InvalidRange)?;
                w.admit(1, size_of::<bool>())?;
                if earlier.id == row.id {
                    w.reserve(&mut self.errors)?;
                    w.admit(1, size_of::<ValidationError>())?;
                    self.errors
                        .push(ValidationError::DuplicateStructId(row.id.index()));
                    break;
                }
                w.next(&mut j)?;
            }
            w.next(&mut i)?;
        }
        Ok(())
    }
    pub(super) fn functions<O: ExecutionObserver>(
        &mut self,
        catalog: &ModuleFunctionCatalog<'_>,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1, size_of::<Vec<u32>>())?;
        if self.ids.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        self.ids = catalog.ambiguous_ids_observed(w.session, w.site)?;
        self.emit_functions(w)
    }
    pub(super) fn emit_functions<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        let mut i = 0;
        while let Some(id) = w.at(&self.ids, i)? {
            w.reserve(&mut self.errors)?;
            w.admit(1, size_of::<ValidationError>())?;
            self.errors.push(ValidationError::DuplicateFuncId(*id));
            w.next(&mut i)?;
        }
        Ok(())
    }
}
