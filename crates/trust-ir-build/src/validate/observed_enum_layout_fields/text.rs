// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn begin<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(3, 0)?;
        if self.location.capacity() != 0
            || self.expected.capacity() != 0
            || self.actual.capacity() != 0
        {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    pub(super) fn field_prefix<O: ExecutionObserver>(
        &mut self,
        v: usize,
        f: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.begin(work)?;
        work.text("variant ", &mut self.expected)?;
        work.number(v as u128, &mut self.expected)?;
        work.text(" field ", &mut self.expected)?;
        work.number(f as u128, &mut self.expected)
    }
    pub(super) fn push<O: ExecutionObserver>(
        &mut self,
        enm: &EnumDef,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Original push closure constructs location after both argument texts.
        // All three pending owned Strings survive reserve/header refusals.
        work.admit(1, 0)?;
        if self.location.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        work.text("enum.", &mut self.location)?;
        work.admit(1, size_of::<u32>())?;
        work.number(u128::from(enm.id.index()), &mut self.location)?;
        work.text(" (", &mut self.location)?;
        work.text(&enm.name, &mut self.location)?;
        work.text(") layout", &mut self.location)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(ValidationError::ConstTypeMismatch {
            location: take(&mut self.location),
            expected: take(&mut self.expected),
            actual: take(&mut self.actual),
        });
        Ok(())
    }
}
