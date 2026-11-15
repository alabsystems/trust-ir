// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn function<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        entry: usize,
        glue: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Option<&FuncTy>>())?;
        match module.func_types.get(function.ty.as_usize()) {
            Some(signature) => {
                work.admit(4, 3 * size_of::<usize>() + size_of::<bool>())?;
                let shape = signature.params.len() == 1
                    && matches!(&signature.params[0], Ty::Ptr)
                    && signature.returns.is_empty()
                    && !signature.is_vararg;
                if !shape {
                    self.signature_reason(function, signature, work)?;
                    self.emit(entry, glue, work)?;
                }
            }
            None => {
                self.missing_signature_reason(function, work)?;
                self.emit(entry, glue, work)?;
            }
        }
        work.admit(2, size_of::<bool>())?;
        if function.blocks.is_empty() && matches!(function.linkage, trust_ir::Linkage::ExternalWeak)
        {
            work.text("the glue '", &mut self.reason)?;
            work.text(&function.name, &mut self.reason)?;
            work.text(
                "' is a weak declaration: its address may be null (F-058)",
                &mut self.reason,
            )?;
            self.emit(entry, glue, work)?;
        }
        if work.pinned(&function.name)? {
            work.text("the glue '", &mut self.reason)?;
            work.text(&function.name, &mut self.reason)?;
            work.text("' is a pinned runtime entry: a runtime entry takes a cell or a handle, while drop glue takes a place",&mut self.reason)?;
            self.emit(entry, glue, work)?;
        }
        Ok(())
    }
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn unique<'m>(&mut self, module: &'m Module, id: FuncId) -> R<Option<&'m Function>> {
        self.admit(1, size_of::<Option<&Function>>() + size_of::<usize>())?;
        let mut found = None;
        let mut index = 0usize;
        while let Some(function) = self.at(&module.functions, index)? {
            self.admit(2, 2 * size_of::<FuncId>() + size_of::<Option<&Function>>())?;
            if function.id == id {
                if found.is_some() {
                    return self.publish_value(None);
                }
                found = Some(function);
            }
            self.next(&mut index)?;
        }
        self.publish_value(found)
    }
    pub(super) fn pinned(&mut self, name: &str) -> R<bool> {
        let mut row = 0usize;
        while let Some(pin) = self.at(TRUSTED_RC_RUNTIMES, row)? {
            let mut index = 0usize;
            while let Some(entry) = self.at(pin.entry_points, index)? {
                if self.equal_text(name, entry.symbol)? {
                    return self.publish_value(true);
                }
                self.next(&mut index)?;
            }
            self.next(&mut row)?;
        }
        let mut row = 0usize;
        while let Some(pin) = self.at(TRUSTED_HANDLE_RUNTIMES, row)? {
            let mut index = 0usize;
            while let Some(entry) = self.at(pin.entry_points, index)? {
                if self.equal_text(name, entry.symbol)? {
                    return self.publish_value(true);
                }
                self.next(&mut index)?;
            }
            self.next(&mut row)?;
        }
        self.publish_value(false)
    }
    fn equal_text(&mut self, left: &str, right: &str) -> R<bool> {
        self.admit(2, 2 * size_of::<usize>())?;
        if left.len() != right.len() {
            return Ok(false);
        }
        let mut index = 0usize;
        loop {
            self.admit(1, 2 * size_of::<Option<&u8>>())?;
            match (left.as_bytes().get(index), right.as_bytes().get(index)) {
                (Some(a), Some(b)) => {
                    self.admit(1, 2)?;
                    if a != b {
                        return Ok(false);
                    }
                }
                (None, None) => return Ok(true),
                _ => return Err(ObservedValueError::InvalidRange),
            }
            self.next(&mut index)?;
        }
    }
}
