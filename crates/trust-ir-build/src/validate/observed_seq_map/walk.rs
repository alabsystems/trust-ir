// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        catalog: &ModuleFunctionCatalog<'_>,
        inst: &Inst,
        block: BlockId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<&Inst>())?;
        let Inst::SeqMap { ty, fwd, .. } = inst else {
            return Ok(());
        };
        let Some(function) = catalog.unique_observed(*fwd, work.session, work.site)? else {
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            self.errors.push(ValidationError::SeqMapFwdNotFound {
                block: block.index(),
                fwd_id: fwd.index(),
            });
            return Ok(());
        };
        let module = catalog.source_module();
        let signature =
            match function_signature_observed(module, function, work.session, work.site)? {
                Ok(signature) => signature,
                Err(error) => {
                    self.pending = Some(error);
                    return self.pending(work);
                }
            };
        work.admit(1, size_of::<Option<&Ty>>())?;
        let element = match ty {
            Ty::Sequence(id) => work.at(&module.types, id.as_usize())?,
            _ => None,
        };
        let Some(element) = element else {
            self.render = ty.display_observed(work.session, work.site)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            self.errors.push(ValidationError::SeqMapTypeNotSequence {
                block: block.index(),
                ty: take(&mut self.render),
            });
            return Ok(());
        };
        work.admit(4, 3 * size_of::<usize>() + size_of::<bool>())?;
        let mut yes =
            signature.returns.is_empty() && !signature.is_vararg && signature.params.len() == 1;
        if yes {
            work.admit(1, size_of::<bool>())?;
            yes = match work.at(&signature.params, 0)? {
                Some(Ty::RefMut(inner)) => {
                    inner.structural_eq_observed(element, work.session, work.site)?
                }
                _ => false,
            };
        }
        work.admit(1, size_of::<bool>())?;
        if yes {
            return Ok(());
        }
        // Lists borrow exact original rows, replacing only intermediate joins/clones.
        work.text("fn(", &mut self.actual)?;
        list(&signature.params, &mut self.render, &mut self.actual, work)?;
        work.text(") -> (", &mut self.actual)?;
        list(&signature.returns, &mut self.render, &mut self.actual, work)?;
        work.text(")", &mut self.actual)?;
        work.text(&function.name, &mut self.name)?;
        work.text("fn(&mut ", &mut self.expected)?;
        write_ty(element, &mut self.render, &mut self.expected, work)?;
        work.text(")", &mut self.expected)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 3 * size_of::<String>())?;
        self.errors
            .push(ValidationError::SeqMapFwdSignatureMismatch {
                block: block.index(),
                fwd: take(&mut self.name),
                expected: take(&mut self.expected),
                actual: take(&mut self.actual),
            });
        Ok(())
    }
}
fn write_ty<O: ExecutionObserver>(
    source: &Ty,
    render: &mut String,
    out: &mut String,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.admit(1, size_of::<String>())?;
    if render.capacity() != 0 {
        return Err(ObservedValueError::InvalidRange);
    }
    *render = source.display_observed(work.session, work.site)?;
    work.text(render, out)?;
    work.flat(take(render));
    work.admit(1, 0)
}
fn list<O: ExecutionObserver>(
    source: &[Ty],
    render: &mut String,
    out: &mut String,
    work: &mut Work<'_, '_, O>,
) -> R {
    let mut at = 0;
    while let Some(value) = work.at(source, at)? {
        work.admit(1, size_of::<bool>())?;
        if at != 0 {
            work.text(", ", out)?;
        }
        write_ty(value, render, out, work)?;
        work.next(&mut at)?;
    }
    Ok(())
}
