// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl Trace {
    /// Every DefTable row, in its actual append order, including duplicate
    /// result IDs within a node. No last-write map or opaque Def callback.
    pub(super) fn definitions<O: ExecutionObserver>(
        &mut self,
        body: &ObservedBody<'_>,
        value: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<bool>())?;
        let mut found = false;
        let mut at = 0;
        while let Some(block) = work.at(&body.function.blocks, at)? {
            let mut index = 0;
            while let Some((candidate, _)) = work.at(&block.params, index)? {
                work.admit(4, 3 * size_of::<Root>())?;
                if *candidate == value {
                    found = true;
                    if block.id.index() == body.entry && body.entry_params_are_formals {
                        match u32::try_from(index) {
                            Ok(index) => {
                                self.root(Root::Place(EffectPlace::ParamPointee { index }), work)?
                            }
                            Err(_) => self.root(Root::Untraceable, work)?,
                        }
                    } else {
                        self.root(Root::Untraceable, work)?;
                    }
                }
                work.next(&mut index)?;
            }
            let mut index = 0;
            while let Some(node) = work.at(&block.body, index)? {
                let mut result = 0;
                while let Some(candidate) = work.at(&node.results, result)? {
                    work.admit(1, 2 * size_of::<ValueId>())?;
                    if *candidate == value {
                        found = true;
                        self.instruction(&node.inst, work)?;
                    }
                    work.next(&mut result)?;
                }
                work.next(&mut index)?;
            }
            work.next(&mut at)?;
        }
        work.admit(1, size_of::<Root>())?;
        if !found {
            self.root(Root::Untraceable, work)?;
        }
        Ok(())
    }
    fn instruction<O: ExecutionObserver>(
        &mut self,
        instruction: &Inst,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Bounded tag/scalar/borrowed-header dispatch before actual reads and
        // construction of up to two Enter headers or one scalar Root.
        work.admit(67, 3 * size_of::<Step>() + size_of::<Root>())?;
        match instruction {
            Inst::GEP { base, .. } => work.push(&mut self.stack, Step::Enter(*base)),
            Inst::PtrData { ptr, .. } | Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => {
                work.push(&mut self.stack, Step::Enter(*ptr))
            }
            Inst::Copy { operand, .. }
            | Inst::Cast {
                op: CastOp::PtrToPtr,
                operand,
                ..
            } => work.push(&mut self.stack, Step::Enter(*operand)),
            Inst::Select {
                then_val, else_val, ..
            } => {
                // Exact original pushes then first, so else executes first.
                work.push(&mut self.stack, Step::Enter(*then_val))?;
                work.push(&mut self.stack, Step::Enter(*else_val))
            }
            Inst::Alloca { .. } => self.root(Root::Local, work),
            Inst::GlobalAddr { global } => {
                self.root(Root::Place(EffectPlace::Global(*global)), work)
            }
            // The ordinary trace deliberately treats every other definition as
            // unknown, including malformed result IDs on non-result opcodes.
            _ => self.root(Root::Untraceable, work),
        }
    }
}
