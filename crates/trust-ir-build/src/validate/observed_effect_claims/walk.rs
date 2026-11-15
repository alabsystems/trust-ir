// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'f, 'm> State<'f, 'm> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        function: &'f Function,
        module: Option<&'m Module>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(3, size_of::<Option<Claim>>())?;
        let claim = if function.attrs.readnone {
            Claim::ReadNone
        } else if function.attrs.readonly {
            Claim::ReadOnly
        } else {
            return Ok(());
        };
        if function.blocks.is_empty() {
            return Ok(());
        }
        self.collect(function, work)?;
        if let Some(module) = module {
            work.admit(1, size_of::<Option<ObservedDropGlueIndex<'_>>>())?;
            self.drop_index = Some(module.drop_glue_index_observed(work.session, work.site)?);
        }
        self.scan(function, module, claim, work)
    }
    fn scan<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        module: Option<&Module>,
        claim: Claim,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut block_index = 0usize;
        loop {
            work.admit(1, size_of::<&trust_ir::Block>())?;
            let Some(block) = function.blocks.get(block_index) else {
                return Ok(());
            };
            let mut index = 0usize;
            loop {
                work.admit(1, size_of::<&trust_ir::InstrNode>())?;
                let Some(node) = block.body.get(index) else {
                    break;
                };
                work.admit(2, 0)?;
                if self.function_name.capacity() != 0 || self.inst_text.capacity() != 0 {
                    return Err(ObservedValueError::InvalidRange);
                }
                work.admit(67, size_of::<&str>())?;
                let mnemonic = names::mnemonic(&node.inst);
                if self.violation(&node.inst, mnemonic, module, claim, work)? {
                    self.commit(function, block.id.index(), claim, work)?;
                }
                work.next(&mut index)?;
            }
            work.next(&mut block_index)?;
        }
    }
    fn violation<O: ExecutionObserver>(
        &mut self,
        instruction: &Inst,
        mnemonic: &'static str,
        module: Option<&Module>,
        claim: Claim,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        match self.effect(instruction, work)? {
            Effect::None => Ok(false),
            Effect::Read { address } => {
                if claim == Claim::ReadOnly || self.roots_at_local_alloca(address, work)? {
                    Ok(false)
                } else {
                    self.reason(mnemonic, "reads memory not rooted at a local alloca", work)?;
                    Ok(true)
                }
            }
            Effect::Write { address } => {
                if self.roots_at_local_alloca(address, work)? {
                    Ok(false)
                } else {
                    self.reason(mnemonic, "writes memory not rooted at a local alloca", work)?;
                    Ok(true)
                }
            }
            Effect::Refused { reason } => {
                self.reason(mnemonic, reason, work)?;
                Ok(true)
            }
            Effect::CallEdge { callee } => self.call(mnemonic, callee, module, claim, work),
        }
    }
    fn reason<O: ExecutionObserver>(
        &mut self,
        mnemonic: &str,
        reason: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(mnemonic, &mut self.inst_text)?;
        work.text(" (", &mut self.inst_text)?;
        work.text(reason, &mut self.inst_text)?;
        work.text(")", &mut self.inst_text)
    }
    pub(super) fn call<O: ExecutionObserver>(
        &mut self,
        mnemonic: &str,
        callee: FuncId,
        module: Option<&Module>,
        claim: Claim,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let Some(module) = module else {
            self.unresolved_call(
                mnemonic,
                callee,
                "a callee's attributes cannot be resolved without module context",
                work,
            )?;
            return Ok(true);
        };
        let Some(target) = function_by_id(module, callee, work)? else {
            self.unresolved_call(mnemonic, callee, "the callee does not resolve", work)?;
            return Ok(true);
        };
        work.admit(2, 0)?;
        let admitted = match claim {
            Claim::ReadNone => target.attrs.readnone,
            Claim::ReadOnly => target.attrs.readonly || target.attrs.readnone,
        };
        if admitted {
            return Ok(false);
        }
        work.text(mnemonic, &mut self.inst_text)?;
        work.text(" @", &mut self.inst_text)?;
        work.text(&target.name, &mut self.inst_text)?;
        work.text(" (the callee does not carry ", &mut self.inst_text)?;
        work.text(claim.callee_requirement(), &mut self.inst_text)?;
        work.text(")", &mut self.inst_text)?;
        Ok(true)
    }
    fn unresolved_call<O: ExecutionObserver>(
        &mut self,
        mnemonic: &str,
        callee: FuncId,
        reason: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(mnemonic, &mut self.inst_text)?;
        work.text(" to function #", &mut self.inst_text)?;
        work.number(callee.index(), &mut self.inst_text)?;
        work.text(" (", &mut self.inst_text)?;
        work.text(reason, &mut self.inst_text)?;
        work.text(")", &mut self.inst_text)
    }
}

// Match Module::function_by_id, not the duplicate-aware catalog and not the
// last-definition value map: matching direct slot first, otherwise FIRST row.
pub(super) fn function_by_id<'m, O: ExecutionObserver>(
    module: &'m Module,
    id: FuncId,
    work: &mut Work<'_, '_, O>,
) -> R<Option<&'m Function>> {
    work.admit(2, size_of::<Option<&Function>>())?;
    if let Some(function) = module.functions.get(id.as_usize())
        && function.id == id
    {
        return Ok(Some(function));
    }
    let mut index = 0usize;
    loop {
        work.admit(2, size_of::<Option<&Function>>())?;
        let Some(function) = module.functions.get(index) else {
            return Ok(None);
        };
        if function.id == id {
            return Ok(Some(function));
        }
        work.next(&mut index)?;
    }
}
