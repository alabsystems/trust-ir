// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'a> State<'a> {
    fn defect<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        base: &Ty,
        pred: &'a Pred,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.push(&mut self.pred_stack, PredFrame::Visit(pred))?;
        while let Some(frame) = self.pred_stack.last().copied() {
            work.admit(1, size_of::<PredFrame<'_>>())?;
            self.pred_stack.pop();
            let p = match frame {
                PredFrame::Exit(p) => {
                    let Some(last) = self.pred_path.pop() else {
                        return Err(ObservedValueError::InvalidRange);
                    };
                    if !core::ptr::eq(last, p) {
                        return Err(ObservedValueError::InvalidRange);
                    }
                    continue;
                }
                PredFrame::Visit(p) => p,
            };
            for previous in &self.pred_path {
                work.admit(1, 0)?;
                if core::ptr::eq(*previous, p) {
                    // Ordinary malformed recursion has no finite diagnostic
                    // return. Refuse operationally; never publish a smaller
                    // result or reinterpret a cycle as an accepting leaf.
                    return Err(ObservedValueError::UnsupportedValue);
                }
            }
            match p {
                Pred::Interval { .. }
                | Pred::FiniteSet(_)
                | Pred::InUniverse(..)
                | Pred::NonZero => {
                    if !base.is_integer() && !matches!(base, Ty::Bool | Ty::Char) {
                        work.text("predicate ", &mut self.detail)?;
                        work.pred_view(lattice::View::node(p), &mut self.detail)?;
                        work.text(
                            " constrains an integer carrier but the base representation is ",
                            &mut self.detail,
                        )?;
                        work.ty(base, &mut self.detail)?;
                        work.retire_vec(&mut self.pred_stack);
                        work.retire_vec(&mut self.pred_path);
                        return Ok(true);
                    }
                }
                Pred::NonNull => {
                    if !base.is_reference() && !matches!(base, Ty::Ptr) {
                        work.text(
                            "predicate `nonnull` requires a pointer-like base, got ",
                            &mut self.detail,
                        )?;
                        work.ty(base, &mut self.detail)?;
                        work.retire_vec(&mut self.pred_stack);
                        work.retire_vec(&mut self.pred_path);
                        return Ok(true);
                    }
                }
                Pred::Conj(children) | Pred::Disj(children) => {
                    work.push(&mut self.pred_path, p)?;
                    work.push(&mut self.pred_stack, PredFrame::Exit(p))?;
                    for id in children.iter().rev() {
                        work.admit(1, 0)?;
                        if let Some(child) = work.at(&module.predicates, id.as_usize())? {
                            work.push(&mut self.pred_stack, PredFrame::Visit(child))?;
                        }
                    }
                }
                Pred::Top | Pred::Bottom => {}
            }
        }
        work.retire_vec(&mut self.pred_stack);
        work.retire_vec(&mut self.pred_path);
        Ok(false)
    }
    pub(super) fn check_type<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        root: &'a Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.push(&mut self.type_stack, root)?;
        while let Some(ty) = self.type_stack.last().copied() {
            work.admit(1, size_of::<&Ty>())?;
            self.type_stack.pop();
            match ty {
                Ty::Vector(t, _)
                | Ty::Tensor(t, _)
                | Ty::Ref(t)
                | Ty::RefMut(t)
                | Ty::PtrConst(t)
                | Ty::PtrMut(t)
                | Ty::Rc(t) => work.push(&mut self.type_stack, t.as_ref())?,
                Ty::Tuple(types) => {
                    for ty in types.iter().rev() {
                        work.admit(1, 0)?;
                        work.push(&mut self.type_stack, ty)?;
                    }
                }
                _ => {}
            }
            let Ty::Refine(base_id, pred_id) = ty else {
                continue;
            };
            let Some(base) = work.at(&module.types, base_id.as_usize())? else {
                self.error_location(work)?;
                work.text("base ty.", &mut self.detail)?;
                work.number(base_id.index() as u128, &mut self.detail)?;
                work.text(" is out of range", &mut self.detail)?;
                self.commit(ErrorKind::Invalid, Sink::Main, work)?;
                continue;
            };
            if base.is_refine() {
                self.error_location(work)?;
                work.text("base ty.", &mut self.detail)?;
                work.number(base_id.index() as u128, &mut self.detail)?;
                work.text(" is itself a refinement; refinements do not nest — conjoin the predicates instead, so there is exactly one spelling per fact and interning stays an identity",&mut self.detail)?;
                self.commit(ErrorKind::Invalid, Sink::Main, work)?;
                continue;
            }
            let Some(pred) = work.at(&module.predicates, pred_id.as_usize())? else {
                self.error_location(work)?;
                self.commit(
                    ErrorKind::Dangling("pred", pred_id.index()),
                    Sink::Main,
                    work,
                )?;
                continue;
            };
            if self.defect(module, base, pred, work)? {
                self.error_location(work)?;
                self.commit(ErrorKind::Invalid, Sink::Main, work)?;
            }
        }
        work.retire_vec(&mut self.type_stack);
        Ok(())
    }
    fn begin_type<O: ExecutionObserver>(
        &mut self,
        prefix: &str,
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.flat(take(&mut self.base_location));
        work.text(prefix, &mut self.base_location)?;
        work.number(index as u128, &mut self.base_location)
    }
    pub(super) fn occurrences<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for (i, ty) in module.types.iter().enumerate() {
            work.admit(1, 0)?;
            self.begin_type("type ty.", i, work)?;
            self.check_type(module, ty, work)?;
        }
        for (i, sig) in module.func_types.iter().enumerate() {
            work.admit(1, 0)?;
            for (what, types) in [
                (" param ", sig.params.as_slice()),
                (" return ", sig.returns.as_slice()),
            ] {
                work.admit(1, 0)?;
                for (j, ty) in types.iter().enumerate() {
                    work.admit(1, 0)?;
                    self.begin_type("functy.", i, work)?;
                    work.text(what, &mut self.base_location)?;
                    work.number(j as u128, &mut self.base_location)?;
                    self.check_type(module, ty, work)?;
                }
            }
        }
        for global in &module.globals {
            work.admit(1, 0)?;
            work.flat(take(&mut self.base_location));
            work.text("global '", &mut self.base_location)?;
            work.text(&global.name, &mut self.base_location)?;
            work.text("'", &mut self.base_location)?;
            self.check_type(module, &global.ty, work)?;
        }
        for (i, row) in module.drop_glue.iter().enumerate() {
            work.admit(1, 0)?;
            self.begin_type("drop_glue row ", i, work)?;
            self.check_type(module, &row.ty, work)?;
        }
        for def in &module.structs {
            work.admit(1, 0)?;
            for field in &def.fields {
                work.admit(1, 0)?;
                self.named_field("struct", &def.name, &field.name, work)?;
                self.check_type(module, &field.ty, work)?;
            }
        }
        for def in &module.records {
            work.admit(1, 0)?;
            for field in &def.fields {
                work.admit(1, 0)?;
                self.named_field("record", &def.name, &field.name, work)?;
                self.check_type(module, &field.ty, work)?;
            }
        }
        for def in &module.enums {
            work.admit(1, 0)?;
            for variant in &def.variants {
                work.admit(1, 0)?;
                for (i, ty) in variant.fields.iter().enumerate() {
                    work.admit(1, 0)?;
                    work.flat(take(&mut self.base_location));
                    work.text("enum @", &mut self.base_location)?;
                    work.text(&def.name, &mut self.base_location)?;
                    work.text(" variant '", &mut self.base_location)?;
                    work.text(&variant.name, &mut self.base_location)?;
                    work.text("' field ", &mut self.base_location)?;
                    work.number(i as u128, &mut self.base_location)?;
                    self.check_type(module, ty, work)?;
                }
            }
        }
        for (i, closure) in module.closure_types.iter().enumerate() {
            work.admit(1, 0)?;
            for (j, ty) in closure.captures.iter().enumerate() {
                work.admit(1, 0)?;
                self.begin_type("closurety.", i, work)?;
                work.text(" capture ", &mut self.base_location)?;
                work.number(j as u128, &mut self.base_location)?;
                self.check_type(module, ty, work)?;
            }
        }
        for func in &module.functions {
            work.admit(1, 0)?;
            for block in &func.blocks {
                work.admit(1, 0)?;
                for (param, ty) in &block.params {
                    work.admit(1, 0)?;
                    self.base(&func.name, Some(block.id.index()), work)?;
                    work.text(" param %", &mut self.base_location)?;
                    work.number(param.index() as u128, &mut self.base_location)?;
                    self.check_type(module, ty, work)?;
                }
                for (i, node) in block.body.iter().enumerate() {
                    work.admit(1, size_of::<Vec<&Ty>>())?;
                    self.inline_types = node.inst.inline_types_observed(work.session, work.site)?;
                    let mut j = 0;
                    while j < self.inline_types.len() {
                        work.admit(1, size_of::<&Ty>())?;
                        let ty = self.inline_types[j];
                        self.base(&func.name, Some(block.id.index()), work)?;
                        work.text(" instruction ", &mut self.base_location)?;
                        work.number(i as u128, &mut self.base_location)?;
                        self.check_type(module, ty, work)?;
                        j += 1;
                    }
                    work.retire_vec(&mut self.inline_types);
                }
            }
        }
        Ok(())
    }
    fn named_field<O: ExecutionObserver>(
        &mut self,
        kind: &str,
        name: &str,
        field: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.flat(take(&mut self.base_location));
        work.text(kind, &mut self.base_location)?;
        work.text(" @", &mut self.base_location)?;
        work.text(name, &mut self.base_location)?;
        work.text(" field '", &mut self.base_location)?;
        work.text(field, &mut self.base_location)?;
        work.text("'", &mut self.base_location)
    }
}
