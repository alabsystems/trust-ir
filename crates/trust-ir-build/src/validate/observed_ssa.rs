// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual definition, operand and dominance SSA validation.
use super::*;
use core::mem::{size_of, take};
use trust_ir::analysis::DominatorTree;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
struct Definition {
    value: u32,
    block: BlockId,
    instruction: Option<usize>,
}
#[derive(Default)]
struct Checking {
    errors: Vec<ValidationError>,
    definitions: Vec<Definition>,
    missing: Vec<(u32, u32)>,
    dominance: Vec<(u32, u32)>,
    operands: Vec<ValueId>,
    dominators: Option<DominatorTree>,
}
/// Exact ordinary SSA diagnostics: duplicate definitions, missing operands,
/// then ordering/dominance failures. The actual original-function dominator
/// analysis, complete operand walk, indexes, queries and retirement share this
/// caller session/site. Invoke/InvokeIndirect normal-edge arguments keep their
/// original distinct use coordinates. Invalid CFGs retain ordinary conservative
/// query behavior; this result never establishes complete function validity or
/// source/proof authority. Successful output/input disposal and physical
/// allocator/panic/time bounds remain caller responsibilities.
pub fn validate_function_ssa_observed<O: ExecutionObserver>(
    function: &Function,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<Checking>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = Checking::default();
    let mut work = Work { session, site };
    let result = state.collect(function, &mut work).and_then(|()| {
        state.dominators = Some(DominatorTree::new_observed(
            function,
            work.session,
            work.site,
        )?);
        state.uses(function, &mut work)?;
        state.merge(&mut work)
    });
    state.retire_scratch(&mut work);
    let result = result.and_then(|()| work.publication());
    match result {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            state.retire_errors(&mut work);
            Err(work.terminal(error))
        }
    }
}
impl Checking {
    fn error<O: ExecutionObserver>(
        &mut self,
        make: impl FnOnce() -> ValidationError,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Only fixed value/block IDs are captured by private callers. No owned
        // diagnostic exists before its complete reserve/construction admission.
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(make());
        Ok(())
    }
    fn define<O: ExecutionObserver>(
        &mut self,
        value: u32,
        block: BlockId,
        instruction: Option<usize>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut duplicate = false;
        for definition in &mut self.definitions {
            work.admit(1, 0)?;
            if definition.value == value {
                work.admit(1, size_of::<Definition>())?;
                *definition = Definition {
                    value,
                    block,
                    instruction,
                };
                duplicate = true;
                break;
            }
        }
        if duplicate {
            self.error(
                || ValidationError::DuplicateValueDef {
                    value,
                    block: block.index(),
                },
                work,
            )
        } else {
            work.reserve(&mut self.definitions)?;
            work.admit(1, size_of::<Definition>())?;
            self.definitions.push(Definition {
                value,
                block,
                instruction,
            });
            Ok(())
        }
    }
    fn check<O: ExecutionObserver>(
        &mut self,
        value: ValueId,
        use_site: SsaUseSite,
        reachable: bool,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        let mut found = None;
        for definition in &self.definitions {
            work.admit(1, size_of::<Definition>())?;
            if definition.value == value.index() {
                found = Some(*definition);
                break;
            }
        }
        let Some(definition) = found else {
            return work.push(&mut self.missing, (value.index(), use_site.block().index()));
        };
        if !reachable {
            return Ok(());
        }
        let tree = self
            .dominators
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?;
        let available = tree.definition_available_at_observed(
            SsaDefinitionSite {
                block: definition.block,
                instruction: definition.instruction,
            },
            use_site,
            work.session,
            work.site,
        )?;
        if !available {
            work.push(
                &mut self.dominance,
                (value.index(), use_site.block().index()),
            )?;
        }
        Ok(())
    }
    fn merge<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        for index in 0..self.missing.len() {
            work.admit(1, size_of::<(u32, u32)>())?;
            let (value, block) = self.missing[index];
            self.error(|| ValidationError::UseBeforeDef { value, block }, work)?;
        }
        for index in 0..self.dominance.len() {
            work.admit(1, size_of::<(u32, u32)>())?;
            let (value, block) = self.dominance[index];
            self.error(
                || ValidationError::UseBeforeDefInBlock { value, block },
                work,
            )?;
        }
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_vec(take(&mut self.definitions));
        work.retire_vec(take(&mut self.missing));
        work.retire_vec(take(&mut self.dominance));
        work.retire_vec(take(&mut self.operands));
        work.session.retirement_step(work.site, 1);
        if let Some(tree) = self.dominators.take() {
            // The consuming helper owns and drains every private tree map even
            // after refusal. Its Err cannot abandon any remaining state here.
            let _ = tree.retire_observed(work.session, work.site);
        }
        work.session.retirement_poll(work.site);
    }
    fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.errors.is_empty() {
            work.session.retirement_step(work.site, 1);
            // Only the three fixed value/block ID variants are constructed.
            if let Some(error) = self.errors.pop() {
                work.retire(error);
            }
        }
        work.retire(take(&mut self.errors));
    }
}
