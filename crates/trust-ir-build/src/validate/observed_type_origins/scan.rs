// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'m> State<'m> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &'m Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0;
        loop {
            work.admit(1, size_of::<Option<&trust_ir::ty::StructDef>>())?;
            let Some(row) = module.structs.get(index) else {
                break;
            };
            work.admit(1, size_of::<Option<&TypeOrigin>>())?;
            if let Some(origin) = &row.origin {
                work.admit(1, size_of::<Key<'_>>())?;
                self.key(
                    Key {
                        origin,
                        table: "struct",
                        name: &row.name,
                    },
                    work,
                )?;
            }
            work.next(&mut index)?;
        }
        let mut index = 0;
        loop {
            work.admit(1, size_of::<Option<&trust_ir::ty::EnumDef>>())?;
            let Some(row) = module.enums.get(index) else {
                break;
            };
            work.admit(1, size_of::<Option<&TypeOrigin>>())?;
            if let Some(origin) = &row.origin {
                work.admit(1, size_of::<Key<'_>>())?;
                self.key(
                    Key {
                        origin,
                        table: "enum",
                        name: &row.name,
                    },
                    work,
                )?;
            }
            work.next(&mut index)?;
        }
        let mut index = 0;
        loop {
            work.admit(1, size_of::<Option<&Key<'_>>>())?;
            let Some(row) = self.keys.get(index) else {
                return Ok(());
            };
            work.admit(1, size_of::<Key<'_>>())?;
            let row = *row;
            let mut seen = 0;
            let mut first = None;
            loop {
                work.admit(1, size_of::<Option<&usize>>())?;
                let Some(&prior) = self.seen.get(seen) else {
                    break;
                };
                work.admit(1, size_of::<Key<'_>>())?;
                let prior = *self
                    .keys
                    .get(prior)
                    .ok_or(ObservedValueError::InvalidRange)?;
                if origin::equal(prior.origin, row.origin, work)? {
                    first = Some(prior);
                    break;
                }
                work.next(&mut seen)?;
            }
            if let Some(prior) = first {
                self.conflict(prior, row, work)?;
            } else {
                work.reserve(&mut self.seen)?;
                work.admit(1, size_of::<usize>())?;
                self.seen.push(index);
            }
            work.next(&mut index)?;
        }
    }
    fn key<O: ExecutionObserver>(&mut self, key: Key<'m>, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.keys)?;
        work.admit(1, size_of::<Key<'_>>())?;
        self.keys.push(key);
        Ok(())
    }
    fn conflict<O: ExecutionObserver>(
        &mut self,
        first: Key<'m>,
        second: Key<'m>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(3, 0)?;
        if self.origin.capacity() != 0 || self.first.capacity() != 0 || self.second.capacity() != 0
        {
            return Err(ObservedValueError::InvalidRange);
        }
        origin::write(first.origin, work, &mut self.origin)?;
        work.text(first.name, &mut self.first)?;
        work.text(second.name, &mut self.second)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(ValidationError::TypeOriginConflict {
            origin: take(&mut self.origin),
            first_module: None,
            first_table: first.table,
            first: take(&mut self.first),
            second_module: None,
            second_table: second.table,
            second: take(&mut self.second),
        });
        Ok(())
    }
}
