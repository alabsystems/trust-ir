// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual original one-node type-reference/nominal census rule.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod lookup;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    location: String,
    detail: String,
    name: String,
    runtime: String,
    errors: Vec<ValidationError>,
    census: NominalCensus,
}
#[derive(Clone, Copy)]
enum Refusal {
    Dialect(&'static str),
    Handle(&'static str),
    UntrustedHandle,
    Dangling(&'static str, u32),
    /// The tensor region: a non-integer element (`InvalidTensorType`).
    Tensor,
}
/// Exact original `check_node` rule at one actual visited Ty. This does NOT
/// recurse/follow table IDs or replace the mandatory complete source inventory.
/// Actual lexical checks, supplied registry's exact identity scan, diagnostic
/// copy/allocation and publication share this original session/site. A dialect
/// or handle is counted even when invalid, as in the original module census.
/// Named definitions preserve the original index/ID fast path and then scan
/// actual fallback rows under this session. No layouts are built.
///
/// Successful census/diagnostics convey no pinned-registry/type/module/source/
/// proof authority. No semantic check or accepting fallback is removed. Failed
/// partial/whole text and all errors are consumed under the same sticky owner.
/// Successful input/result disposal and physical std/Unicode/allocator/
/// deallocator/OOM/panic/unwind/RSS/hardtime remain OPEN.
pub(super) fn validate_type_reference_node_observed<O: ExecutionObserver>(
    module: &Module,
    registry: &HandleRegistry,
    ty: &Ty,
    location: &str,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<(Vec<ValidationError>, NominalCensus)> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.node(module, registry, ty, location, &mut work);
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok((take(&mut state.errors), state.census)),
        Err(error) => {
            let _ =
                retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
            Err(work.terminal(error))
        }
    }
}
impl State {
    fn node<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        registry: &HandleRegistry,
        ty: &Ty,
        location: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(48, 4 * size_of::<Refusal>() + size_of::<NominalCensus>())?;
        let error = match ty {
            Ty::Dialect(identity) => {
                self.census.dialect = true;
                match identity.validate_observed(work.session, work.site)? {
                    Ok(()) => None,
                    Err(error) => Some(Refusal::Dialect(error.message())),
                }
            }
            Ty::Handle(identity) => {
                self.census.handle = true;
                match identity.validate_observed(work.session, work.site)? {
                    Err(error) => Some(Refusal::Handle(error.message())),
                    Ok(()) => {
                        if work.pinned(registry, identity)? {
                            None
                        } else {
                            Some(Refusal::UntrustedHandle)
                        }
                    }
                }
            }
            Ty::Struct(id) if !work.struct_exists(module, *id)? => {
                Some(Refusal::Dangling("struct", id.index()))
            }
            Ty::Enum(id) if !work.enum_exists(module, *id)? => {
                Some(Refusal::Dangling("enum", id.index()))
            }
            Ty::Record(id) if !work.record_exists(module, *id)? => {
                Some(Refusal::Dangling("record", id.index()))
            }
            Ty::Closure(id) if module.closure_type(*id).is_none() => {
                Some(Refusal::Dangling("closure_type", id.index()))
            }
            Ty::Func(id) if module.func_type(*id).is_none() => {
                Some(Refusal::Dangling("func_type", id.index()))
            }
            Ty::FnItem(id) if !work.function_item_exists(module, *id)? => {
                Some(Refusal::Dangling("function_item", id.index()))
            }
            Ty::Array(id, _) | Ty::Set(id, _) | Ty::Sequence(id) if module.ty(*id).is_none() => {
                Some(Refusal::Dangling("ty", id.index()))
            }
            Ty::FatPtr(trust_ir::ty::FatPtrKind::Slice(id)) if module.ty(*id).is_none() => {
                Some(Refusal::Dangling("ty", id.index()))
            }
            Ty::Tensor(elem, _) if !elem.is_integer() => Some(Refusal::Tensor),
            // The original node rule ignores every other variant and inline
            // child; the separately mandatory inventory visits those children.
            _ => None,
        };
        if let Some(error) = error {
            self.error(error, ty, location, work)?;
        }
        Ok(())
    }
    fn error<O: ExecutionObserver>(
        &mut self,
        error: Refusal,
        ty: &Ty,
        location: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(location, &mut self.location)?;
        work.admit(4, size_of::<Refusal>())?;
        match error {
            Refusal::Dialect(detail) | Refusal::Handle(detail) => {
                work.text(detail, &mut self.detail)?
            }
            Refusal::UntrustedHandle => {
                work.admit(1, 2 * size_of::<&str>())?;
                let Ty::Handle(identity) = ty else {
                    return Err(ObservedValueError::InvalidRange);
                };
                work.text(&identity.name, &mut self.name)?;
                work.text(&identity.runtime, &mut self.runtime)?;
            }
            Refusal::Tensor => {
                let Ty::Tensor(elem, _) = ty else {
                    return Err(ObservedValueError::InvalidRange);
                };
                let element = elem.display_observed(work.session, work.site)?;
                let written = work
                    .text("tensor element type ", &mut self.detail)
                    .and_then(|()| work.text(&element, &mut self.detail))
                    .and_then(|()| {
                        work.text(
                            if elem.is_float() {
                                " is a float; float tensors wait on SemR's float model (PKG-U15)"
                            } else {
                                " is not an integer type"
                            },
                            &mut self.detail,
                        )
                    });
                work.flat(element);
                written?;
            }
            Refusal::Dangling(_, _) => {}
        }
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 4 * size_of::<String>())?;
        let location = take(&mut self.location);
        self.errors.push(match error {
            Refusal::Dialect(_) => ValidationError::InvalidDialectType {
                location,
                detail: take(&mut self.detail),
            },
            Refusal::Handle(_) => ValidationError::InvalidHandleType {
                location,
                detail: take(&mut self.detail),
            },
            Refusal::UntrustedHandle => ValidationError::UntrustedHandleRuntime {
                location,
                name: take(&mut self.name),
                runtime: take(&mut self.runtime),
            },
            Refusal::Dangling(kind, id) => {
                ValidationError::DanglingTypeReference { location, kind, id }
            }
            Refusal::Tensor => ValidationError::InvalidTensorType {
                location,
                detail: take(&mut self.detail),
            },
        });
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.location));
        work.flat(take(&mut self.detail));
        work.flat(take(&mut self.name));
        work.flat(take(&mut self.runtime));
    }
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    fn pinned(&mut self, registry: &HandleRegistry, identity: &HandleTy) -> R<bool> {
        self.admit(1, size_of::<&[HandleRuntimePin]>())?;
        let pins = registry.pins();
        let mut at = 0usize;
        while let Some(pin) = self.at(pins, at)? {
            if self.equal(pin.name, &identity.name)?
                && self.equal(pin.runtime, &identity.runtime)?
            {
                return Ok(true);
            }
            self.next(&mut at)?;
        }
        Ok(false)
    }
}
