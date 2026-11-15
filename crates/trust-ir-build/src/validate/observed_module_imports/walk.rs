// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn interning<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0usize;
        loop {
            work.admit(1, size_of::<Option<&ModuleImport>>())?;
            let Some(import) = module.imports.get(index) else {
                return Ok(());
            };
            let id = work.id(index)?;
            let mut earlier = 0usize;
            loop {
                work.admit(2, size_of::<Option<&ModuleImport>>())?;
                if earlier == index {
                    break;
                }
                let first = module
                    .imports
                    .get(earlier)
                    .ok_or(ObservedValueError::InvalidRange)?;
                if work.import_equal(first, import)? {
                    let first = work.id(earlier)?;
                    self.ready(work)?;
                    work.text(&import.name, &mut self.first)?;
                    work.reserve(&mut self.errors)?;
                    work.admit(1, size_of::<ValidationError>())?;
                    self.errors.push(ValidationError::ImportTableNotInterned {
                        first,
                        duplicate: id,
                        name: take(&mut self.first),
                    });
                    break;
                }
                work.next(&mut earlier)?;
            }
            work.next(&mut index)?;
        }
    }
    pub(super) fn identity<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0usize;
        loop {
            work.admit(1, size_of::<Option<&ModuleImport>>())?;
            let Some(import) = module.imports.get(index) else {
                return Ok(());
            };
            let id = work.id(index)?;
            let mut earlier = 0usize;
            loop {
                work.admit(2, size_of::<Option<&ModuleImport>>())?;
                if earlier == index {
                    break;
                }
                let first = module
                    .imports
                    .get(earlier)
                    .ok_or(ObservedValueError::InvalidRange)?;
                if work.digest_equal(&first.digest, &import.digest)? {
                    let first = work.id(earlier)?;
                    // Preserve the original saturated-ID re-indexing too;
                    // no input row or identity byte is truncated/normalized.
                    work.admit(1, size_of::<&ModuleImport>())?;
                    let first_name = &module
                        .imports
                        .get(first as usize)
                        .ok_or(ObservedValueError::InvalidRange)?
                        .name;
                    if !work.equal(first_name, &import.name)? {
                        self.ready(work)?;
                        work.text(first_name, &mut self.first)?;
                        work.text(&import.name, &mut self.second)?;
                        work.reserve(&mut self.errors)?;
                        work.admit(1, size_of::<ValidationError>())?;
                        self.errors.push(ValidationError::ImportIdentityConflict {
                            first,
                            conflicting: id,
                            first_name: take(&mut self.first),
                            conflicting_name: take(&mut self.second),
                        });
                    }
                    break;
                }
                work.next(&mut earlier)?;
            }
            work.next(&mut index)?;
        }
    }
}
