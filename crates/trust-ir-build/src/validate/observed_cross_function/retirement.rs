// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State<'_, '_> {
    pub(super) fn ready<O: ExecutionObserver>(&self, w: &mut Work<'_, '_, O>) -> R {
        w.admit(1, size_of::<Vec<ValidationError>>())?;
        if self.pending.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    pub(super) fn retire_pending<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        retire_validation_errors_observed(take(&mut self.pending), w.session, w.site)
    }
    pub(super) fn retire_children<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        let mut failure = None;
        macro_rules! finish {
            ($call:expr) => {
                if let Err(error) = $call {
                    if failure.is_none() {
                        failure = Some(error);
                    }
                }
            };
        }
        w.step(size_of::<Option<Result<&FuncTy, ValidationError>>>().saturating_add(1));
        if let Some(Err(error)) = self.getter.take() {
            finish!(retire_validation_error_observed(error, w.session, w.site));
        }
        w.fixed(self.signature.take());
        finish!(self.retire_pending(w));
        w.step(size_of::<Option<ObservedIndirectCalls<'_, '_>>>().saturating_add(1));
        if let Some(indirect) = self.indirect.take() {
            finish!(indirect.retire_observed(w.session, w.site));
        }
        w.poll();
        w.step(size_of::<Option<ObservedSealedHandleSlots<'_>>>().saturating_add(1));
        if let Some(slots) = self.slots.take() {
            finish!(slots.retire_observed(w.session, w.site));
        }
        w.poll();
        w.step(size_of::<Option<ObservedHandleEnumGuards<'_>>>().saturating_add(1));
        if let Some(guards) = self.guards.take() {
            finish!(guards.retire_observed(w.session, w.site));
        }
        w.poll();
        w.step(size_of::<Option<ObservedValueTypes>>().saturating_add(1));
        if let Some(values) = self.values.take() {
            finish!(values.retire_observed(w.session, w.site));
        }
        w.poll();
        match failure {
            Some(error) => Err(w.terminal(error)),
            None => Ok(()),
        }
    }
}
