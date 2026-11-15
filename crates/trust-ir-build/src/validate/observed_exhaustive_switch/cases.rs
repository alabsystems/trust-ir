// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
fn bits<O: ExecutionObserver>(
    width: Option<u32>,
    constant: &Constant,
    work: &mut Work<'_, '_, O>,
) -> R<Option<u128>> {
    work.admit(4, size_of::<Option<u128>>())?;
    let Some(width) = width else {
        return Ok(None);
    };
    let raw = match constant {
        Constant::Int(value) => *value as u128,
        Constant::U128(value) => *value,
        _ => return Ok(None),
    };
    Ok(Some(if width >= 128 {
        raw
    } else {
        raw & ((1u128 << width) - 1)
    }))
}
impl<'f> State<'f> {
    pub(super) fn cases<O: ExecutionObserver>(
        &mut self,
        block: u32,
        selector: ValueId,
        cases: &'f [trust_ir::inst::SwitchCase],
        width: Option<u32>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if self.seen.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        let mut index = 0usize;
        loop {
            work.admit(1, size_of::<&trust_ir::inst::SwitchCase>())?;
            let Some(case) = cases.get(index) else {
                return Ok(());
            };
            if let Some(key) = bits(width, &case.value, work)? {
                let mut seen = 0usize;
                let mut first = None;
                loop {
                    work.admit(1, size_of::<(u128, &Constant)>())?;
                    let Some((candidate, constant)) = self.seen.get(seen).copied() else {
                        break;
                    };
                    if candidate == key {
                        first = Some(constant);
                        break;
                    }
                    seen = seen
                        .checked_add(1)
                        .ok_or(ObservedValueError::CapacityOverflow)?;
                }
                if let Some(first) = first {
                    self.alias(block, selector, first, &case.value, work)?;
                } else {
                    work.reserve(&mut self.seen)?;
                    work.admit(1, size_of::<(u128, &Constant)>())?;
                    self.seen.push((key, &case.value));
                }
            }
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
    fn alias<O: ExecutionObserver>(
        &mut self,
        block: u32,
        selector: ValueId,
        first: &Constant,
        second: &Constant,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.admit(1, 2 * size_of::<String>())?;
        // Masked keys only came from Int/U128, whose actual observed formatter
        // is complete. Never invoke an opaque float formatter or derived Eq.
        self.first = first.display_observed(work.session, work.site)?;
        self.second = second.display_observed(work.session, work.site)?;
        if !work.equal(&self.first, &self.second)? {
            work.text("case values ", &mut self.reason)?;
            work.text(&self.first, &mut self.reason)?;
            work.text(" and ", &mut self.reason)?;
            work.text(&self.second, &mut self.reason)?;
            work.text(" denote the same ", &mut self.reason)?;
            if let Some(ty) = self
                .values
                .as_ref()
                .ok_or(ObservedValueError::InvalidRange)?
                .get_observed(selector, work.session, work.site)?
            {
                self.ty = ty.display_observed(work.session, work.site)?;
                work.text(&self.ty, &mut self.reason)?;
            }
            work.text(" selector value", &mut self.reason)?;
            self.commit(block, work)?;
        }
        self.retire_text(work);
        work.admit(1, 0)
    }
}
