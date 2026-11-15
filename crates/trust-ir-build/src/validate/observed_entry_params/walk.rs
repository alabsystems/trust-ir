// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    clippy::while_let_loop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[derive(Clone, Copy)]
enum Types<'a> {
    Signature(&'a [Ty]),
    Entry(&'a [(ValueId, Ty)]),
}
impl<'a> Types<'a> {
    fn at<O: ExecutionObserver>(
        self,
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<&'a Ty>> {
        match self {
            Self::Signature(types) => work.at(types, index),
            Self::Entry(params) => Ok(work.at(params, index)?.map(|(_, ty)| ty)),
        }
    }
}
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(signature) = work.at(&module.func_types, function.ty.as_usize())? else {
            return Ok(());
        };
        work.admit(1, size_of::<usize>())?;
        if function.blocks.is_empty() {
            return Ok(());
        }
        let mut at = 0;
        let entry = loop {
            let Some(block) = work.at(&function.blocks, at)? else {
                return Ok(());
            };
            work.admit(1, size_of::<bool>())?;
            if block.id == function.entry {
                break block;
            }
            work.next(&mut at)?;
        };
        work.admit(2, 2 * size_of::<usize>() + size_of::<bool>())?;
        let arity = entry.params.len() == signature.params.len();
        let mut at = 0;
        let mut compatible = true;
        loop {
            let Some((_, actual)) = work.at(&entry.params, at)? else {
                break;
            };
            let Some(expected) = work.at(&signature.params, at)? else {
                break;
            };
            if !actual.structural_eq_observed(expected, work.session, work.site)? {
                work.admit(2, 2 * size_of::<bool>())?;
                if !actual.is_refine() && !expected.is_refine() {
                    compatible = false;
                    break;
                }
            }
            work.next(&mut at)?;
        }
        work.admit(1, size_of::<bool>())?;
        if arity && compatible {
            return Ok(());
        }
        work.text(&function.name, &mut self.name)?;
        list(
            Types::Signature(&signature.params),
            &mut self.render,
            &mut self.expected,
            work,
        )?;
        list(
            Types::Entry(&entry.params),
            &mut self.render,
            &mut self.actual,
            work,
        )?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 3 * size_of::<String>())?;
        self.errors.push(ValidationError::EntryParamsMismatch {
            func_name: take(&mut self.name),
            expected: take(&mut self.expected),
            actual: take(&mut self.actual),
        });
        Ok(())
    }
}
fn list<O: ExecutionObserver>(
    types: Types<'_>,
    render: &mut String,
    out: &mut String,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.text("(", out)?;
    let mut at = 0;
    while let Some(ty) = types.at(at, work)? {
        work.admit(1, size_of::<bool>())?;
        if at != 0 {
            work.text(", ", out)?;
        }
        work.admit(1, size_of::<String>())?;
        if render.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        *render = ty.display_observed(work.session, work.site)?;
        work.text(render, out)?;
        work.flat(take(render));
        work.admit(1, 0)?;
        work.next(&mut at)?;
    }
    work.text(")", out)
}
