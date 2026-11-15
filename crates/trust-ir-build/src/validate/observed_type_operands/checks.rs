// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn pointer<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: &'static str,
        value: ValueId,
        values: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(ty) = values.get_observed(value, work.session, work.site)? else {
            return Ok(());
        };
        // The original predicate is a fixed eight-variant discriminant test.
        work.admit(8, 0)?;
        if !ty.is_pointer_like() {
            self.ready(work)?;
            work.text(op, &mut self.op)?;
            work.spelling(ty, &mut self.actual)?;
            self.commit(Diagnostic::Pointer(block), work)?;
        }
        Ok(())
    }
    pub(super) fn operand<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: &'static str,
        role: &'static str,
        value: ValueId,
        expected: &Ty,
        refinement: Refinement,
        values: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(actual) = values.get_observed(value, work.session, work.site)? else {
            return Ok(());
        };
        work.admit(2, 0)?;
        if matches!(refinement, Refinement::Consumption)
            && (matches!(actual, Ty::Refine(..)) || matches!(expected, Ty::Refine(..)))
        {
            return Ok(());
        }
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
    pub(super) fn boolean<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: Option<&'static str>,
        value: ValueId,
        values: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(actual) = values.get_observed(value, work.session, work.site)? else {
            return Ok(());
        };
        if !actual.structural_eq_observed(&Ty::Bool, work.session, work.site)? {
            self.ready(work)?;
            let kind = if let Some(op) = op {
                work.text(op, &mut self.op)?;
                Diagnostic::Predicate(block)
            } else {
                Diagnostic::Condition(block)
            };
            work.spelling(actual, &mut self.actual)?;
            self.commit(kind, work)?;
        }
        Ok(())
    }
    pub(super) fn byte_count<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: &'static str,
        value: ValueId,
        values: &ObservedValueTypes,
        module: Option<&Module>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(actual) = values.get_observed(value, work.session, work.site)? else {
            return Ok(());
        };
        work.admit(2, size_of::<Option<Ty>>())?;
        // Only the two fixed scalar variants are materialized here; the
        // ordinary eagerly formatted expected string is otherwise discarded.
        let expected = module.map(|module| {
            if module.target_info.is_some() {
                Ty::Usize
            } else {
                Ty::U64
            }
        });
        let ok = match &expected {
            Some(expected) => actual.structural_eq_observed(expected, work.session, work.site)?,
            None => matches!(actual, Ty::Usize | Ty::U64),
        };
        if !ok {
            self.ready(work)?;
            work.text(op, &mut self.op)?;
            work.text("bytes", &mut self.role)?;
            match &expected {
                Some(expected) => work.spelling(expected, &mut self.expected)?,
                None => work.text("usize or u64 (no module context)", &mut self.expected)?,
            }
            work.spelling(actual, &mut self.actual)?;
            self.commit(Diagnostic::Operand(block), work)?;
        }
        Ok(())
    }
    pub(super) fn indices<O: ExecutionObserver>(
        &mut self,
        block: u32,
        indices: &[ValueId],
        values: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0usize;
        loop {
            work.admit(1, size_of::<ValueId>())?;
            let Some(value) = indices.get(index) else {
                return Ok(());
            };
            if let Some(ty) = values.get_observed(*value, work.session, work.site)? {
                work.admit(12, 0)?;
                if !ty.is_integer() {
                    self.ready(work)?;
                    work.spelling(ty, &mut self.actual)?;
                    self.commit(Diagnostic::Index(block), work)?;
                }
            }
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
    pub(super) fn ordering<O: ExecutionObserver>(
        &mut self,
        block: u32,
        op: &'static str,
        role: &'static str,
        ordering: Ordering,
        atomic: AtomicRole,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(5, 0)?;
        let legal = match atomic {
            AtomicRole::Load => ordering.is_legal_for_load(),
            AtomicRole::Store => ordering.is_legal_for_store(),
        };
        if !legal {
            self.ready(work)?;
            // Original Ordering::Display is exactly this closed five-token table.
            work.admit(5, size_of::<&str>())?;
            let token = match ordering {
                Ordering::Relaxed => "relaxed",
                Ordering::Acquire => "acquire",
                Ordering::Release => "release",
                Ordering::AcqRel => "acq_rel",
                Ordering::SeqCst => "seq_cst",
            };
            work.text(token, &mut self.actual)?;
            let legal = match atomic {
                AtomicRole::Load => LEGAL_LOAD_ORDERINGS,
                AtomicRole::Store => LEGAL_STORE_ORDERINGS,
            };
            self.commit(
                Diagnostic::Atomic {
                    block,
                    op,
                    role,
                    legal,
                },
                work,
            )?;
        }
        Ok(())
    }
}
