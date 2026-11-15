// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn location<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        request: Request<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(8, size_of::<PanicLocation>())?;
        match request.panic.location {
            PanicLocation::Global(id) => {
                let Some(global) = work.at(&module.globals, id.as_usize())? else {
                    return self.scalar(
                        ValidationError::GlobalNotFound {
                            block: request.block.index(),
                            global_id: id.index(),
                        },
                        work,
                    );
                };
                work.admit(8, size_of::<Option<&str>>())?;
                let reason = if global.mutable {
                    Some("the global is mutable")
                } else if global.tls.is_some() {
                    Some("the global is thread-local")
                } else {
                    None
                };
                if let Some(reason) = reason {
                    self.name(request.function, work)?;
                    work.reserve(&mut self.errors)?;
                    work.admit(1, size_of::<ValidationError>())?;
                    self.errors
                        .push(ValidationError::PanicLocationGlobalInvalid {
                            function: take(&mut self.name),
                            block: request.block.index(),
                            inst_index: request.index,
                            global: id.index(),
                            reason,
                        });
                }
            }
            PanicLocation::Value(value) => {
                if origin::is_global(module, request.function, value, work)? {
                    self.name(request.function, work)?;
                    work.reserve(&mut self.errors)?;
                    work.admit(1, size_of::<ValidationError>())?;
                    self.errors
                        .push(ValidationError::NonCanonicalPanicLocation {
                            function: take(&mut self.name),
                            block: request.block.index(),
                            inst_index: request.index,
                        });
                }
            }
        }
        Ok(())
    }
}
