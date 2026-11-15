// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn flagged<O: ExecutionObserver>(f: &Function, w: &mut Work<'_, '_, O>) -> R<bool> {
    let mut b = 0;
    while let Some(block) = w.at(&f.blocks, b)? {
        w.admit(67, size_of::<Option<&trust_ir::InstrNode>>())?;
        if block.terminator().is_some_and(|n| {
            matches!(
                n.inst,
                Inst::Switch {
                    exhaustive_enum_unreachable: true,
                    ..
                }
            )
        }) {
            return Ok(true);
        }
        w.next(&mut b)?;
    }
    Ok(false)
}
impl<'f, 'm> State<'f, 'm> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        layouts: &trust_ir::LayoutTable<'m>,
        function: &'f Function,
        values: &ObservedValueTypes,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        if !flagged(function, w)? {
            return Ok(());
        }
        self.build_definitions(function, w)?;
        let mut b = 0;
        while let Some(block) = w.at(&function.blocks, b)? {
            w.admit(67, size_of::<Option<&trust_ir::InstrNode>>())?;
            if let Some(term) = block.terminator()
                && let Inst::Switch {
                    value,
                    cases,
                    exhaustive_enum_unreachable: true,
                    ..
                } = &term.inst
            {
                if self.selector(layouts.module(), values, *value, w)? {
                    self.cases(layouts, block.id.index(), cases, w)?;
                }
                self.retire_selection(w);
                w.admit(1, 0)?;
            }
            w.next(&mut b)?;
        }
        Ok(())
    }
}
