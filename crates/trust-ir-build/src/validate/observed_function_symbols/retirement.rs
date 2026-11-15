// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn retire_pending<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_text(&mut self.name);
        work.retire_producer(self.first_producer.take());
        work.retire_producer(self.second_producer.take());
        work.retire_path(self.first_path.take());
        work.retire_path(self.second_path.take());
    }
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    fn fixed<T: Copy>(&mut self, value: T) {
        self.session
            .retirement_step(self.site, size_of::<T>().saturating_add(1));
        let _ = value;
    }
    pub(super) fn retire_path(&mut self, value: Option<String>) {
        self.session
            .retirement_step(self.site, size_of::<Option<String>>().saturating_add(1));
        match value {
            None => self.fixed(()),
            Some(mut text) => self.retire_text(&mut text),
        }
        self.session.retirement_poll(self.site);
    }
    pub(super) fn retire_producer(&mut self, value: Option<Producer>) {
        self.session
            .retirement_step(self.site, size_of::<Option<Producer>>().saturating_add(1));
        match value {
            None => self.fixed(()),
            Some(producer) => {
                self.session
                    .retirement_step(self.site, size_of::<Producer>().saturating_add(1));
                match producer {
                    Producer::TRust => self.fixed(()),
                    Producer::Clean => self.fixed(()),
                    Producer::TrustIr => self.fixed(()),
                    Producer::TSwift => self.fixed(()),
                    Producer::TC => self.fixed(()),
                    Producer::Other(mut text) => self.retire_text(&mut text),
                }
            }
        }
        self.session.retirement_poll(self.site);
    }
}
