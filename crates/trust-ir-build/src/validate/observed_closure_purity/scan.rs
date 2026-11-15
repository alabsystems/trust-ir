// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn pure<O: ExecutionObserver>(proofs: &[ProofAnnotation], work: &mut Work<'_, '_, O>) -> R<bool> {
    let mut at = 0;
    while let Some(proof) = work.at(proofs, at)? {
        work.admit(1, size_of::<bool>())?;
        if matches!(proof, ProofAnnotation::Pure) {
            return Ok(true);
        }
        work.next(&mut at)?;
    }
    Ok(false)
}
fn stateful<'a, O: ExecutionObserver>(
    module: &'a Module,
    id: ClosureTyId,
    work: &mut Work<'_, '_, O>,
) -> R<Option<(usize, &'a Ty)>> {
    let Some(closure) = work.at(&module.closure_types, id.as_usize())? else {
        return Ok(None);
    };
    let mut at = 0;
    while let Some(capture) = work.at(&closure.captures, at)? {
        work.admit(3, size_of::<bool>())?;
        if matches!(capture, Ty::RefMut(_) | Ty::PtrMut(_) | Ty::Rc(_)) {
            return Ok(Some((at, capture)));
        }
        work.next(&mut at)?;
    }
    Ok(None)
}
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut f = 0;
        while let Some(function) = work.at(&module.functions, f)? {
            if pure(&function.proofs, work)?
                && let Some(signature) = work.at(&module.func_types, function.ty.as_usize())?
            {
                self.signature(module, function, signature, work)?;
            }
            let mut b = 0;
            while let Some(block) = work.at(&function.blocks, b)? {
                let mut n = 0;
                while let Some(node) = work.at(&block.body, n)? {
                    if pure(&node.proofs, work)? {
                        work.admit(1, size_of::<Vec<(usize, ClosureTyId)>>())?;
                        if self.results.capacity() != 0 {
                            return Err(ObservedValueError::InvalidRange);
                        }
                        self.results =
                            module_closure_results_observed(module, node, work.session, work.site)?;
                        let mut r = 0;
                        while let Some((ordinal, id)) = work.at(&self.results, r)? {
                            if let Some((capture_index, capture)) = stateful(module, *id, work)? {
                                self.capture = capture.display_observed(work.session, work.site)?;
                                let value = work.at(&node.results, *ordinal)?.map(|v| v.index());
                                work.reserve(&mut self.errors)?;
                                work.admit(2, size_of::<ValidationError>() + size_of::<String>())?;
                                self.errors
                                    .push(ValidationError::ClosurePureWithStatefulCapture {
                                        block: block.id.index(),
                                        value,
                                        closure_ty_id: id.index(),
                                        capture_index: capture_index as u32,
                                        capture_ty: take(&mut self.capture),
                                    });
                            }
                            work.next(&mut r)?;
                        }
                        work.rows(take(&mut self.results));
                        work.admit(1, 0)?;
                    }
                    work.next(&mut n)?;
                }
                work.next(&mut b)?;
            }
            work.next(&mut f)?;
        }
        Ok(())
    }
    fn signature<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        signature: &FuncTy,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // These two borrowed slices preserve params-before-returns with one
        // break across the concatenation: at most one finding per function.
        work.admit(1, size_of::<[&[Ty]; 2]>())?;
        for types in [&signature.params[..], &signature.returns[..]] {
            let mut at = 0;
            while let Some(ty) = work.at(types, at)? {
                work.admit(1, size_of::<bool>())?;
                if let Ty::Closure(id) = ty
                    && let Some((capture_index, capture)) = stateful(module, *id, work)?
                {
                    work.text(&function.name, &mut self.name)?;
                    self.capture = capture.display_observed(work.session, work.site)?;
                    work.reserve(&mut self.errors)?;
                    work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
                    self.errors
                        .push(ValidationError::FunctionPureWithStatefulClosureSignature {
                            func_name: take(&mut self.name),
                            closure_ty_id: id.index(),
                            capture_index: capture_index as u32,
                            capture_ty: take(&mut self.capture),
                        });
                    return Ok(());
                }
                work.next(&mut at)?;
            }
        }
        Ok(())
    }
}
