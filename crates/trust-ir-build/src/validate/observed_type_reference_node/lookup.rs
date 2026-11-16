// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Preserve Module's named-definition fast path and physical fallback order.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use trust_ir::value::{EnumId, RecordId, StructId};
impl<O: ExecutionObserver> Work<'_, '_, O> {
    // This public operation checks one original node. Scan every declaration
    // so a second matching ID can never authenticate the first row.
    pub(super) fn function_item_exists(&mut self, module: &Module, id: FuncId) -> R<bool> {
        let mut found = None;
        let mut at = 0;
        while let Some(row) = self.at(&module.functions, at)? {
            self.admit(1, size_of::<bool>())?;
            if row.id == id {
                if found.is_some() {
                    return Ok(false);
                }
                found = Some(row.ty);
            }
            self.next(&mut at)?;
        }
        match found {
            Some(signature) => Ok(self.at(&module.func_types, signature.as_usize())?.is_some()),
            None => Ok(false),
        }
    }
    pub(super) fn struct_exists(&mut self, module: &Module, id: StructId) -> R<bool> {
        self.admit(1, size_of::<usize>())?;
        if let Some(row) = self.at(&module.structs, id.as_usize())? {
            self.admit(1, 2 * size_of::<StructId>())?;
            if row.id == id {
                return Ok(true);
            }
        }
        let mut at = 0usize;
        while let Some(row) = self.at(&module.structs, at)? {
            self.admit(1, 2 * size_of::<StructId>())?;
            if row.id == id {
                return Ok(true);
            }
            self.next(&mut at)?;
        }
        Ok(false)
    }
    pub(super) fn enum_exists(&mut self, module: &Module, id: EnumId) -> R<bool> {
        self.admit(1, size_of::<usize>())?;
        if let Some(row) = self.at(&module.enums, id.as_usize())? {
            self.admit(1, 2 * size_of::<EnumId>())?;
            if row.id == id {
                return Ok(true);
            }
        }
        let mut at = 0usize;
        while let Some(row) = self.at(&module.enums, at)? {
            self.admit(1, 2 * size_of::<EnumId>())?;
            if row.id == id {
                return Ok(true);
            }
            self.next(&mut at)?;
        }
        Ok(false)
    }
    pub(super) fn record_exists(&mut self, module: &Module, id: RecordId) -> R<bool> {
        self.admit(1, size_of::<usize>())?;
        if let Some(row) = self.at(&module.records, id.as_usize())? {
            self.admit(1, 2 * size_of::<RecordId>())?;
            if row.id == id {
                return Ok(true);
            }
        }
        let mut at = 0usize;
        while let Some(row) = self.at(&module.records, at)? {
            self.admit(1, 2 * size_of::<RecordId>())?;
            if row.id == id {
                return Ok(true);
            }
            self.next(&mut at)?;
        }
        Ok(false)
    }
}
