// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'a> State<'a> {
    pub(super) fn walk<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0usize;
        while let Some(global) = work.at(&module.globals, at)? {
            work.admit(1, size_of::<Option<&Constant>>())?;
            if let Some(value) = &global.initializer
                && self.mentions(value, work)?
            {
                work.text("global '", &mut self.location)?;
                work.text(&global.name, &mut self.location)?;
                work.text("'", &mut self.location)?;
                work.text(
                    "an unwritten lane (uninit) in a global initializer",
                    &mut self.actual,
                )?;
                self.emit(work)?;
            }
            work.next(&mut at)?;
        }
        let mut fi = 0usize;
        while let Some(function) = work.at(&module.functions, fi)? {
            let mut bi = 0usize;
            while let Some(block) = work.at(&function.blocks, bi)? {
                let mut ni = 0usize;
                while let Some(node) = work.at(&block.body, ni)? {
                    work.admit(3, 2 * size_of::<&Constant>())?;
                    match &node.inst {
                        Inst::Const { ty, value } => {
                            if !self.placed(ty, value, work)? {
                                self.function_location(function, block, work)?;
                                self.constant_detail(ty, value, work)?;
                                self.emit(work)?;
                            }
                        }
                        Inst::Switch { cases, .. } => {
                            let mut ci = 0usize;
                            while let Some(case) = work.at(cases, ci)? {
                                if self.mentions(&case.value, work)? {
                                    self.function_location(function, block, work)?;
                                    work.text(
                                        "an unwritten lane (uninit) as a switch case value",
                                        &mut self.actual,
                                    )?;
                                    self.emit(work)?;
                                    break;
                                }
                                work.next(&mut ci)?;
                            }
                        }
                        _ => {}
                    }
                    work.next(&mut ni)?;
                }
                work.next(&mut bi)?;
            }
            work.next(&mut fi)?;
        }
        Ok(())
    }
}
