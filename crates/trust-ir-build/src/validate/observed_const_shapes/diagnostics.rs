// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State<'_> {
    pub(super) fn global_location<O: ExecutionObserver>(
        &mut self,
        name: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text("global '", &mut self.location)?;
        work.text(name, &mut self.location)?;
        work.text("'", &mut self.location)
    }
    pub(super) fn block_location<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        block: BlockId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text("function '", &mut self.location)?;
        work.text(&function.name, &mut self.location)?;
        work.text("' bb", &mut self.location)?;
        work.unsigned(u128::from(block.index()), &mut self.location)
    }
    pub(super) fn global_nominal<O: ExecutionObserver>(
        &mut self,
        name: &str,
        handle: bool,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.global_location(name, work)?;
        work.text(if handle{"globals declare machine storage; an opaque runtime handle cannot be stored, initialized or addressed as data outside a sealed function-local slot (ratified: a top-level `Nat` constant is a function returning a fresh handle)"}else{"globals declare machine storage, not semantic constants; nominal dialect types require explicit legalization"},&mut self.detail)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
        self.errors.push(if handle {
            ValidationError::InvalidHandleUse {
                location: take(&mut self.location),
                detail: take(&mut self.detail),
            }
        } else {
            ValidationError::InvalidDialectType {
                location: take(&mut self.location),
                detail: take(&mut self.detail),
            }
        });
        Ok(())
    }
}
