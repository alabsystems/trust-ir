// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'m> State<'m> {
    pub(super) fn canonical<O: ExecutionObserver>(
        &mut self,
        root: &'m Constant,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(1, size_of::<Option<&Constant>>())?;
        self.canonical_current = Some(root);
        loop {
            work.admit(
                8,
                size_of::<ConstantChildren<'m>>() + size_of::<Option<&Constant>>(),
            )?;
            let constant = self
                .canonical_current
                .ok_or(ObservedValueError::InvalidRange)?;
            if matches!(constant,Constant::U128(n)if *n<=i128::MAX as u128) {
                return Ok(false);
            }
            let mut children = constant.children();
            if let Some(first) = children.next() {
                if children.len() != 0 {
                    work.reserve(&mut self.canonical_pending)?;
                    work.admit(1, size_of::<ConstantChildren<'m>>())?;
                    self.canonical_pending.push(children);
                }
                self.canonical_current = Some(first);
                continue;
            }
            loop {
                work.admit(1, size_of::<Option<&mut ConstantChildren<'m>>>())?;
                let Some(frame) = self.canonical_pending.last_mut() else {
                    return Ok(true);
                };
                work.admit(
                    1,
                    size_of::<ConstantChildren<'m>>() + size_of::<Option<&Constant>>(),
                )?;
                if let Some(next) = frame.next() {
                    self.canonical_current = Some(next);
                    break;
                }
                work.admit(1, size_of::<Option<ConstantChildren<'m>>>())?;
                work.fixed(self.canonical_pending.pop());
            }
        }
    }
    pub(super) fn one<O: ExecutionObserver>(
        &mut self,
        symbols: &ObservedConstantSymbols<'_, 'm>,
        constant: &'m Constant,
        ty: &Ty,
        case: Option<usize>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(&self.location, &mut self.here)?;
        if let Some(index) = case {
            work.text(" switch case ", &mut self.here)?;
            work.unsigned(index as u128, &mut self.here)?;
        }
        let result = self.canonical(constant, work);
        self.retire_canonical(work);
        let canonical = result?;
        work.admit(1, size_of::<bool>())?;
        if !canonical {
            work.text("canonical integer spelling (values <= i128::MAX are Constant::Int;                        Constant::U128 only above)",&mut self.expected)?;
            self.actual = constant.shape_label_observed(work.session, work.site)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>() + 3 * size_of::<String>())?;
            work.text(&self.here, &mut self.detail)?;
            self.errors.push(ValidationError::ConstTypeMismatch {
                location: take(&mut self.detail),
                expected: take(&mut self.expected),
                actual: take(&mut self.actual),
            });
        }
        // Whole child-owned output is retained before the first merge fee.
        self.pending = validate_constant_against_ty_observed(
            symbols,
            constant,
            ty,
            &self.here,
            work.session,
            work.site,
        )?;
        self.merge(work)?;
        work.flat(take(&mut self.here));
        work.admit(1, 0)
    }
}
