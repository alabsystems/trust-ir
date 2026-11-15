// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) struct Work<'s, 'o, O: ExecutionObserver> {
    pub(super) session: &'s mut ObservedSession<'o, O>,
    pub(super) site: ExecutionSite,
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    // Retirement admissions observe and charge actual cleanup even after the
    // original stop. Their refusals latch in that session and never interrupt
    // consumption of still-owned input. No fresh budget or deadline is made.
    pub(super) fn step(&mut self, work: usize) {
        self.session.retirement_step(self.site, work);
    }
    pub(super) fn poll(&mut self) {
        self.session.retirement_poll(self.site);
    }
    pub(super) fn fixed<T: Copy>(&mut self, value: T) {
        // The Copy bound forbids silently hiding a future owned payload in
        // fixed field cleanup. This is a constant field/header cost.
        self.step(size_of::<T>().saturating_add(1));
        let _ = value;
    }
    pub(super) fn string(&mut self, value: String) {
        self.step(size_of::<String>().saturating_add(1));
        drop(value);
        self.poll();
    }
    pub(super) fn optional_string(&mut self, value: Option<String>) {
        self.step(2);
        match value {
            Some(text) => self.string(text),
            None => self.fixed(()),
        }
    }
    pub(super) fn strings(&mut self, mut values: Vec<String>) {
        loop {
            self.step(1);
            let Some(text) = values.pop() else { break };
            self.string(text);
        }
        // Every String was separately consumed, including empty allocations.
        self.step(size_of::<Vec<String>>().saturating_add(1));
        drop(values);
        self.poll();
    }
    pub(super) fn numbers(&mut self, mut values: Vec<u32>) {
        loop {
            self.step(1);
            let Some(value) = values.pop() else { break };
            self.fixed(value);
        }
        self.step(size_of::<Vec<u32>>().saturating_add(1));
        drop(values);
        self.poll();
    }
    pub(super) fn finish(&mut self) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 0,
                copy_bytes: 0,
            })
            .map_err(Into::into)
    }
}
