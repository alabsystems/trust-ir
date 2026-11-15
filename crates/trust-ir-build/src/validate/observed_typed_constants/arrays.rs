// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn uniform_list<O: ExecutionObserver>(
        &mut self,
        constant: &Constant,
        values: &[Constant],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let table = self
            .uniform
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?;
        if !table.contains_observed(constant, work.session, work.site)? {
            return Ok(());
        }
        let first = work
            .at(values, 0)?
            .ok_or(ObservedValueError::InvalidRange)?;
        work.admit(1, size_of::<ConstantChildren<'_>>())?;
        self.render = if first.children().len() == 0 {
            first.display_observed(work.session, work.site)?
        } else {
            first.shape_label_observed(work.session, work.site)?
        };
        work.text("an array of ", &mut self.spelling)?;
        work.unsigned(values.len() as u128, &mut self.spelling)?;
        work.text(" equal elements is spelled `splat[ ", &mut self.spelling)?;
        work.text(&self.render, &mut self.spelling)?;
        work.text("; ", &mut self.spelling)?;
        work.unsigned(values.len() as u128, &mut self.spelling)?;
        work.text(" ]`", &mut self.spelling)?;
        work.flat(take(&mut self.render));
        work.admit(1, 0)?;
        self.uniform_error(work)
    }
}
