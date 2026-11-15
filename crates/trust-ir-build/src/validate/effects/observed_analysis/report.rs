// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::vec::IntoIter;
#[cfg(test)]
mod tests;
#[derive(Clone, Copy)]
enum Slot {
    Reason,
    Place,
}
#[derive(Default)]
struct Report {
    need: Option<ObservedNeed>,
    reason: Option<Reason>,
    place: Option<PlaceReason>,
    batch: Option<IntoIter<PlaceReason>>,
    name: String,
    errors: Vec<ValidationError>,
}
pub(super) fn run<O: ExecutionObserver>(
    need: ObservedNeed,
    function: &str,
    declared: &EffectSummary,
    work: &mut Work<'_, '_, O>,
) -> R<Vec<ValidationError>> {
    // Capture the complete returned Need before the first fallible callback.
    let mut state = Report {
        need: Some(need),
        ..Report::default()
    };
    let result = (|| -> R {
        work.admit(1, size_of::<Report>())?;
        state.side(Side::Read, "reads", &declared.reads, function, work)?;
        state.side(Side::Write, "writes", &declared.writes, function, work)?;
        work.admit(4, 4 * size_of::<(Flag, bool, &str)>())?;
        let flags = [
            (Flag::Allocates, declared.allocates, "allocates"),
            (Flag::Frees, declared.frees, "frees"),
            (Flag::MayUnwind, declared.may_unwind, "may_unwind"),
            (Flag::Io, declared.io, "io"),
        ];
        for (flag, allowed, effect) in flags {
            work.admit(2, size_of::<Option<Reason>>() + size_of::<bool>())?;
            if state.reason.is_some() {
                return Err(ObservedValueError::InvalidRange);
            }
            let n = state
                .need
                .as_mut()
                .ok_or(ObservedValueError::InvalidRange)?;
            state.reason = match flag {
                Flag::Allocates => n.allocates.take(),
                Flag::Frees => n.frees.take(),
                Flag::MayUnwind => n.may_unwind.take(),
                Flag::Io => n.io.take(),
            };
            work.admit(1, size_of::<bool>())?;
            if state.reason.is_some() && !allowed {
                state.emit(effect, Slot::Reason, function, work)?;
            }
            state.retire_reason(work);
            work.admit(1, 0)?;
        }
        Ok(())
    })();
    state.finish(result, work)
}
impl Report {
    fn side<O: ExecutionObserver>(
        &mut self,
        side: Side,
        effect: &'static str,
        declared: &EffectSet,
        function: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(
            2,
            size_of::<Option<Reason>>() + size_of::<Option<IntoIter<PlaceReason>>>(),
        )?;
        if self.reason.is_some() || self.place.is_some() || self.batch.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        let n = self.need.as_mut().ok_or(ObservedValueError::InvalidRange)?;
        self.reason = match side {
            Side::Read => n.reads.everything.take(),
            Side::Write => n.writes.everything.take(),
        };
        work.admit(3, size_of::<bool>())?;
        if self.reason.is_some() {
            if !matches!(declared, EffectSet::Everything) {
                let (_, why) = self
                    .reason
                    .as_mut()
                    .ok_or(ObservedValueError::InvalidRange)?;
                work.text(", which needs ", why)?;
                work.text(effect, why)?;
                work.text(": Everything", why)?;
                self.emit(effect, Slot::Reason, function, work)?;
            }
            self.retire_reason(work);
            return work.admit(1, 0);
        }
        work.admit(
            2,
            size_of::<IntoIter<PlaceReason>>() + size_of::<Vec<PlaceReason>>(),
        )?;
        let n = self.need.as_mut().ok_or(ObservedValueError::InvalidRange)?;
        self.batch = Some(
            match side {
                Side::Read => take(&mut n.reads.places),
                Side::Write => take(&mut n.writes.places),
            }
            .into_iter(),
        );
        loop {
            work.admit(1, size_of::<Option<PlaceReason>>())?;
            self.place = self
                .batch
                .as_mut()
                .ok_or(ObservedValueError::InvalidRange)?
                .next();
            let Some((place, _)) = self.place.as_ref() else {
                break;
            };
            if !covers_place(declared, *place, work)? {
                self.emit(effect, Slot::Place, function, work)?;
            }
            self.retire_place(work);
            work.admit(1, 0)?;
        }
        self.retire_batch(work);
        work.admit(1, 0)
    }
    fn emit<O: ExecutionObserver>(
        &mut self,
        effect: &'static str,
        slot: Slot,
        function: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<usize>())?;
        if self.name.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        work.text(function, &mut self.name)?;
        work.reserve(&mut self.errors)?;
        work.admit(
            3,
            size_of::<ValidationError>()
                + size_of::<Option<PlaceReason>>()
                + size_of::<Option<Reason>>()
                + size_of::<String>(),
        )?;
        let (block, inst) = match slot {
            Slot::Reason => self.reason.take().ok_or(ObservedValueError::InvalidRange)?,
            Slot::Place => self.place.take().ok_or(ObservedValueError::InvalidRange)?.1,
        };
        self.errors.push(ValidationError::EffectSummaryViolated {
            function: take(&mut self.name),
            effect,
            block,
            inst,
        });
        Ok(())
    }
    fn retire_reason<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<Reason>>().saturating_add(1));
        if let Some((_, why)) = self.reason.take() {
            work.step(size_of::<Reason>().saturating_add(1));
            work.retire_text(why);
        }
        work.poll();
    }
    fn retire_place<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<PlaceReason>>().saturating_add(1));
        if let Some((_, (_, why))) = self.place.take() {
            work.step(size_of::<PlaceReason>().saturating_add(1));
            work.retire_text(why);
        }
        work.poll();
    }
    fn retire_batch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        loop {
            work.step(size_of::<Option<PlaceReason>>().saturating_add(1));
            let Some((_, (_, why))) = self.batch.as_mut().and_then(Iterator::next) else {
                break;
            };
            work.step(size_of::<PlaceReason>().saturating_add(1));
            work.retire_text(why);
        }
        work.step(size_of::<Option<IntoIter<PlaceReason>>>().saturating_add(1));
        drop(self.batch.take());
        work.poll();
    }
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        work: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        self.retire_reason(work);
        self.retire_place(work);
        self.retire_batch(work);
        work.step(size_of::<Option<ObservedNeed>>().saturating_add(1));
        if let Some(need) = self.need.take() {
            let _ = need.retire_observed(work.session, work.site);
        }
        work.poll();
        work.retire_text(take(&mut self.name));
        match result.and_then(|()| work.publication(size_of::<Vec<ValidationError>>())) {
            Ok(()) => Ok(take(&mut self.errors)),
            Err(error) => {
                let _ = retire_validation_errors_observed(
                    take(&mut self.errors),
                    work.session,
                    work.site,
                );
                Err(work.terminal(error))
            }
        }
    }
}
// Exact specialization of covers(&Places(vec![place])). The discarded
// singleton allocation is not constructed, and no canonicality is assumed.
fn covers_place<O: ExecutionObserver>(
    declared: &EffectSet,
    place: EffectPlace,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(3, size_of::<bool>())?;
    match declared {
        EffectSet::Everything => Ok(true),
        EffectSet::Nothing => Ok(false),
        EffectSet::Places(rows) => {
            let mut at = 0usize;
            while let Some(candidate) = work.at(rows, at)? {
                work.admit(4, 2 * size_of::<EffectPlace>() + size_of::<bool>())?;
                let same = match (*candidate, place) {
                    (
                        EffectPlace::ParamPointee { index: a },
                        EffectPlace::ParamPointee { index: b },
                    ) => a == b,
                    (EffectPlace::Global(a), EffectPlace::Global(b)) => a.index() == b.index(),
                    (EffectPlace::ParamPointee { .. }, EffectPlace::Global(_))
                    | (EffectPlace::Global(_), EffectPlace::ParamPointee { .. }) => false,
                };
                if same {
                    return Ok(true);
                }
                work.next(&mut at)?;
            }
            Ok(false)
        }
    }
}
