// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn ffi<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Original BTreeMap::collect visits every row before any function.
        // Actual Copy rows replace only that discarded index; reverse lookup
        // preserves the last repr for every duplicated struct ID.
        let mut at = 0;
        while let Some(row) = work.at(&module.structs, at)? {
            work.reserve(&mut self.reprs)?;
            work.admit(2, size_of::<(u32, StructRepr)>())?;
            self.reprs.push((row.id.index(), row.repr));
            work.next(&mut at)?;
        }
        let mut at = 0;
        while let Some(function) = work.at(&module.functions, at)? {
            if foreign(function, work)? {
                work.admit(1, size_of::<usize>())?;
                if let Some(signature) = work.at(&module.func_types, function.ty.as_usize())? {
                    self.slots(&signature.params, function, "parameter", work)?;
                    self.slots(&signature.returns, function, "return", work)?;
                }
            }
            work.next(&mut at)?;
        }
        Ok(())
    }
    fn slots<O: ExecutionObserver>(
        &mut self,
        slots: &[Ty],
        function: &Function,
        position: &'static str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(ty) = work.at(slots, at)? {
            work.admit(1, 0)?;
            if let Ty::Struct(id) = ty {
                work.admit(1, size_of::<u32>())?;
                let id = id.index();
                if self.unpinned(id, work)? {
                    work.admit(1, 0)?;
                    if self.name.capacity() != 0 {
                        return Err(ObservedValueError::InvalidRange);
                    }
                    work.text(&function.name, &mut self.name)?;
                    work.reserve(&mut self.errors)?;
                    work.admit(1, size_of::<ValidationError>())?;
                    self.errors.push(ValidationError::FfiStructReprUnpinned {
                        func_name: take(&mut self.name),
                        struct_id: id,
                        position,
                    });
                }
            }
            work.next(&mut at)?;
        }
        Ok(())
    }
    fn unpinned<O: ExecutionObserver>(&self, id: u32, work: &mut Work<'_, '_, O>) -> R<bool> {
        work.admit(1, size_of::<usize>())?;
        let mut at = self.reprs.len();
        loop {
            work.admit(1, size_of::<usize>())?;
            let Some(previous) = at.checked_sub(1) else {
                return Ok(false);
            };
            at = previous;
            let row = work
                .at(&self.reprs, at)?
                .ok_or(ObservedValueError::InvalidRange)?;
            work.admit(1, size_of::<u32>())?;
            if row.0 == id {
                work.admit(1, size_of::<StructRepr>())?;
                return Ok(matches!(row.1, StructRepr::Rust));
            }
        }
    }
}
fn foreign<O: ExecutionObserver>(function: &Function, work: &mut Work<'_, '_, O>) -> R<bool> {
    work.admit(1, 0)?;
    if !function.blocks.is_empty() {
        return Ok(false);
    }
    work.admit(1, size_of::<Linkage>())?;
    if !matches!(function.linkage, Linkage::External | Linkage::ExternalWeak) {
        return Ok(false);
    }
    work.admit(1, size_of::<CallingConv>())?;
    Ok(!matches!(function.calling_conv, CallingConv::Rust))
}
