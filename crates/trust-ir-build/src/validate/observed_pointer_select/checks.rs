// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn check<O: ExecutionObserver>(
        &mut self,
        block: u32,
        instruction: &Inst,
        values: &ObservedValueTypes,
        pointer_bits: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(4, 0)?;
        match instruction {
            Inst::PtrData { ptr_ty, ptr } => {
                self.operand(block, "ptr_data", "ptr", *ptr, ptr_ty, values, work)?;
                // Fixed top-level eight-variant discriminant predicate only.
                work.admit(8, 0)?;
                if !ptr_ty.is_pointer_like() {
                    self.invalid(block, "ptr_data", ptr_ty, "type is not pointer-like", work)?;
                }
            }
            Inst::PtrMetadata {
                ptr_ty,
                metadata_ty,
                ptr,
            } => {
                self.operand(block, "ptr_metadata", "ptr", *ptr, ptr_ty, values, work)?;
                self.metadata(
                    block,
                    "ptr_metadata",
                    ptr_ty,
                    metadata_ty,
                    pointer_bits,
                    work,
                )?;
            }
            Inst::PtrFromParts {
                ptr_ty,
                metadata_ty,
                data,
                metadata,
            } => {
                self.operand(
                    block,
                    "ptr_from_parts",
                    "data",
                    *data,
                    &Ty::Ptr,
                    values,
                    work,
                )?;
                self.operand(
                    block,
                    "ptr_from_parts",
                    "metadata",
                    *metadata,
                    metadata_ty,
                    values,
                    work,
                )?;
                self.metadata(
                    block,
                    "ptr_from_parts",
                    ptr_ty,
                    metadata_ty,
                    pointer_bits,
                    work,
                )?;
            }
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                self.operand(block, "select", "then", *then_val, ty, values, work)?;
                self.operand(block, "select", "else", *else_val, ty, values, work)?;
                self.condition(block, ty, *cond, values, work)?;
            }
            _ => return Err(ObservedValueError::InvalidRange),
        }
        Ok(())
    }
    fn operand<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: &'static str,
        role: &'static str,
        value: ValueId,
        expected: &Ty,
        values: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(actual) = values.get_observed(value, work.session, work.site)? else {
            return Ok(());
        };
        if !actual.structural_eq_observed(expected, work.session, work.site)? {
            self.ready(work)?;
            work.text(op, &mut self.op)?;
            work.text(role, &mut self.role)?;
            work.spelling(expected, &mut self.expected)?;
            work.spelling(actual, &mut self.actual)?;
            self.commit(Diagnostic::Operand(block), work)?;
        }
        Ok(())
    }
    pub(super) fn invalid<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: &'static str,
        ptr_ty: &Ty,
        reason: &'static str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text(op, &mut self.op)?;
        work.spelling(ptr_ty, &mut self.pointer)?;
        work.text(reason, &mut self.reason)?;
        self.commit(Diagnostic::Pointer(block), work)
    }
    fn metadata<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: &'static str,
        ptr_ty: &Ty,
        metadata_ty: &Ty,
        pointer_bits: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(32, size_of::<Option<Ty>>())?;
        if self.pending_ty.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        // Exact pointer_metadata_ty is a bounded shape classifier that returns
        // only Unit/unsigned scalar/Ptr; it does not traverse or allocate.
        self.pending_ty = ptr_ty.pointer_metadata_ty(pointer_bits);
        let Some(expected) = self.pending_ty.as_ref() else {
            return self.invalid(block, op, ptr_ty, "type has no pointer metadata", work);
        };
        if !expected.structural_eq_observed(metadata_ty, work.session, work.site)? {
            self.ready(work)?;
            work.text(op, &mut self.op)?;
            work.spelling(ptr_ty, &mut self.pointer)?;
            work.spelling(expected, &mut self.expected)?;
            work.spelling(metadata_ty, &mut self.actual)?;
            self.commit(Diagnostic::Metadata(block), work)?;
        }
        Ok(())
    }
    fn condition<O: ExecutionObserver>(
        &mut self,
        block: u32,
        selected: &Ty,
        cond: ValueId,
        values: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(actual) = values.get_observed(cond, work.session, work.site)? else {
            return Ok(());
        };
        work.admit(1, size_of::<Option<Ty>>())?;
        if self.pending_ty.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        if let Ty::Vector(_, lanes) = selected {
            work.admit(1, size_of::<Ty>())?;
            self.pending_ty = Some(Ty::Vector(Box::new(Ty::Bool), *lanes));
        } else {
            self.pending_ty = Some(Ty::Bool);
        }
        let expected = self
            .pending_ty
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?;
        // Original validate_select_condition_ty classifies a mismatch as either
        // a physical integer mask or another mismatch. The original caller
        // collapses both to the SAME expected/actual pair; discarded selected-
        // type clones and that classification cannot change its diagnostics.
        if !actual.structural_eq_observed(expected, work.session, work.site)? {
            self.ready(work)?;
            work.spelling(expected, &mut self.expected)?;
            work.spelling(actual, &mut self.actual)?;
            self.commit(Diagnostic::Select(block), work)?;
        }
        Ok(())
    }
}
