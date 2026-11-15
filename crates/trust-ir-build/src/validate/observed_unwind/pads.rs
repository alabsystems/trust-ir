// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl Checking<'_> {
    pub(super) fn pads<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for block in &function.blocks {
            work.admit(1, 0)?;
            let id = block.id.index();
            for (index, node) in block.body.iter().enumerate() {
                work.admit(1, 0)?;
                if !matches!(node.inst, Inst::LandingPad { .. }) {
                    continue;
                }
                self.has_pad = true;
                for (position, result) in node.results.iter().enumerate() {
                    work.admit(1, 0)?;
                    let mut replaced = false;
                    for (value, old) in &mut self.results {
                        work.admit(1, 0)?;
                        if value == result {
                            *old = position;
                            replaced = true;
                            break;
                        }
                    }
                    if !replaced {
                        work.push(&mut self.results, (*result, position))?;
                    }
                }
                let report = if index > 0 {
                    work.text(
                        "not the first instruction of its block (position ",
                        &mut self.text,
                    )?;
                    work.number(index, &mut self.text)?;
                    work.text(")", &mut self.text)?;
                    true
                } else if block.id == function.entry {
                    work.text(
                        "the function's entry block is entered by a call, never by the unwinder",
                        &mut self.text,
                    )?;
                    true
                } else if !work.contains(&self.unwind, &id)? {
                    work.text(
                        "no invoke names this block as its unwind_dest",
                        &mut self.text,
                    )?;
                    true
                } else {
                    self.normal_reason(id, work)?
                };
                if report {
                    self.reason(id, work)?;
                }
            }
        }
        Ok(())
    }
    fn normal_reason<O: ExecutionObserver>(
        &mut self,
        id: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut found = false;
        for (target, source) in &self.normal {
            work.admit(1, 0)?;
            if *target != id {
                continue;
            }
            if found {
                work.text(", ", &mut self.text)?;
            } else {
                work.text("also entered by a non-unwind edge from ", &mut self.text)?;
                found = true;
            }
            work.text("bb", &mut self.text)?;
            let source = usize::try_from(*source).map_err(|_| ObservedValueError::InvalidRange)?;
            work.number(source, &mut self.text)?;
        }
        Ok(found)
    }
    pub(super) fn resumes<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for block in &function.blocks {
            work.admit(1, 0)?;
            for node in &block.body {
                work.admit(1, 0)?;
                if matches!(
                    node.inst,
                    Inst::Const { .. }
                        | Inst::NullPtr
                        | Inst::Undef { .. }
                        | Inst::GlobalAddr { .. }
                ) {
                    for result in &node.results {
                        work.push(&mut self.literals, *result)?;
                    }
                }
            }
        }
        for block in &function.blocks {
            work.admit(1, 0)?;
            for node in &block.body {
                work.admit(1, 0)?;
                let Inst::Resume { exn } = &node.inst else {
                    continue;
                };
                let detail = if !self.has_pad {
                    Some("the function contains no landingpad")
                } else if self.selector(*exn, work)? {
                    Some("the operand is a landingpad's type selector, not its exception object")
                } else if work.contains(&self.literals, exn)? {
                    Some("the operand is a literal")
                } else {
                    None
                };
                if let Some(detail) = detail {
                    work.text(
                        "resume of a value no landing pad produced: ",
                        &mut self.text,
                    )?;
                    work.text(detail, &mut self.text)?;
                    self.reason(block.id.index(), work)?;
                }
            }
        }
        Ok(())
    }
    fn selector<O: ExecutionObserver>(&self, exn: ValueId, work: &mut Work<'_, '_, O>) -> R<bool> {
        for (value, position) in &self.results {
            work.admit(1, 0)?;
            if *value == exn {
                return Ok(*position != 0);
            }
        }
        Ok(false)
    }
}
