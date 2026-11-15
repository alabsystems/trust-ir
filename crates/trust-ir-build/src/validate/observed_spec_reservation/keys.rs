// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn keys<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        spec: &SpecModule,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0;
        while let Some(row) = work.at(&spec.invariants, index)? {
            if work.prefix(&row.name, "fn:", Case::Exact)? {
                // All earlier names may be compared without a retained set:
                // equality to this fn: row itself proves that prior prefix.
                let mut duplicate = false;
                let mut prior = 0;
                while prior < index {
                    work.admit(1, 0)?;
                    let previous = work
                        .at(&spec.invariants, prior)?
                        .ok_or(ObservedValueError::InvalidRange)?;
                    if work.equal(&previous.name, &row.name)? {
                        duplicate = true;
                        break;
                    }
                    work.next(&mut prior)?;
                }
                if duplicate {
                    self.begin(spec, work)?;
                    work.text("disclosure row ", &mut self.detail)?;
                    work.text(&row.name, &mut self.detail)?;
                    work.text(" appears more than once", &mut self.detail)?;
                    self.push(work)?;
                } else {
                    work.admit(1, size_of::<&str>())?;
                    // Exact ASCII fn: prefix was established, hence byte3 is
                    // a UTF-8 boundary. No unchecked scalar/string indexing.
                    let digits = row.name.get(3..).ok_or(ObservedValueError::InvalidRange)?;
                    match work.decimal_index(digits)? {
                        None => {
                            self.begin(spec, work)?;
                            work.text("disclosure row ", &mut self.detail)?;
                            work.quoted(&row.name, &mut self.detail)?;
                            work.text(" does not parse: a `fn:` key is `fn:<FuncId index>` in canonical decimal",&mut self.detail)?;
                            self.push(work)?;
                        }
                        Some(id) => {
                            let (named, bodied) = functions(module, id, work)?;
                            if !bodied {
                                self.begin(spec, work)?;
                                work.text("disclosure row ", &mut self.detail)?;
                                work.text(&row.name, &mut self.detail)?;
                                work.text(" names no bodied function", &mut self.detail)?;
                                if named {
                                    work.text(" (function ", &mut self.detail)?;
                                    work.number(u128::from(id), &mut self.detail)?;
                                    work.text(" is a body-less declaration)", &mut self.detail)?;
                                }
                                self.push(work)?;
                            }
                        }
                    }
                }
            }
            work.next(&mut index)?;
        }
        Ok(())
    }
}
fn functions<O: ExecutionObserver>(
    module: &Module,
    id: u32,
    work: &mut Work<'_, '_, O>,
) -> R<(bool, bool)> {
    work.admit(2, 2 * size_of::<bool>())?;
    let mut named = false;
    let mut bodied = false;
    let mut index = 0;
    // Original filter/collect scans every function before deciding any-body.
    // The discarded reference vector is replaced by fixed flags, not a
    // first-ID lookup or a premature body shortcut.
    while let Some(function) = work.at(&module.functions, index)? {
        work.admit(1, size_of::<u32>())?;
        if function.id.index() == id {
            work.admit(2, 2 * size_of::<bool>())?;
            named = true;
            if !function.blocks.is_empty() {
                bodied = true;
            }
        }
        work.next(&mut index)?;
    }
    Ok((named, bodied))
}
