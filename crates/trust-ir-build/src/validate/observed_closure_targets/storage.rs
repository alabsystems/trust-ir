// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(super) struct Work<'s, 'o, O: ExecutionObserver> {
    pub(super) session: &'s mut ObservedSession<'o, O>,
    pub(super) site: ExecutionSite,
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn admit(&mut self, work: usize, copy_bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Validation,
                site: self.site,
                work,
                copy_bytes,
            })
            .map_err(Into::into)
    }
    pub(super) fn at<'a, T>(&mut self, rows: &'a [T], at: usize) -> R<Option<&'a T>> {
        self.admit(1, size_of::<Option<&T>>())?;
        Ok(rows.get(at))
    }
    pub(super) fn next(&mut self, at: &mut usize) -> R {
        self.admit(1, size_of::<usize>())?;
        *at = at
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        Ok(())
    }
    pub(super) fn read(&mut self, map: &BTreeMap<u32, FuncId>, key: u32) -> R<Option<FuncId>> {
        self.admit(1, size_of::<usize>())?;
        self.admit(
            cost::population_work(map.len())?,
            size_of::<Option<FuncId>>(),
        )?;
        Ok(map.get(&key).copied())
    }
    pub(super) fn insert(&mut self, map: &mut BTreeMap<u32, FuncId>, key: u32, value: FuncId) -> R {
        self.admit(
            6 * 16,
            size_of::<[core::alloc::Layout; 6]>() + 4 * size_of::<usize>(),
        )?;
        let bound = cost::insertion_cost::<u32, FuncId>(map.len())?;
        self.admit(bound.work, bound.copy_bytes)?;
        self.admit(1, size_of::<Option<FuncId>>())?;
        let _ = map.insert(key, value);
        Ok(())
    }
    pub(super) fn publication(&mut self, copy_bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: usize::from(copy_bytes != 0),
                copy_bytes,
            })
            .map_err(Into::into)
    }
    pub(super) fn step(&mut self, work: usize) {
        self.session.retirement_step(self.site, work);
    }
    pub(super) fn poll(&mut self) {
        self.session.retirement_poll(self.site);
    }
    pub(super) fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        if self.session.first_refusal().is_some() {
            ObservedValueError::AdmissionRefused
        } else {
            error
        }
    }
}
