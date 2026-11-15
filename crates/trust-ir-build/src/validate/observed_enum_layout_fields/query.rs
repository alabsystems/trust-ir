// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn query<O: ExecutionObserver>(
        &mut self,
        ty: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R<Summary> {
        work.admit(4, 0)?;
        if self.shape.is_some()
            || self.error.is_some()
            || self.reason.is_some()
            || self.tytext.is_some()
        {
            return Err(ObservedValueError::InvalidRange);
        }
        let table = self
            .table
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?;
        // No fallible operation intervenes between the actual helper return
        // and retention of its complete owning result in State.
        match table.ty_layout_observed(ty, work.session, work.site)? {
            Ok(shape) => self.shape = Some(shape),
            Err(error) => self.error = Some(error),
        }
        work.admit(6, size_of::<Summary>())?;
        Ok(match &self.shape {
            Some(shape) => Summary {
                known: true,
                size: if shape.size_bits.is_multiple_of(8) {
                    Some(shape.size_bits / 8)
                } else {
                    None
                },
                align: shape.align_bits,
            },
            None => Summary {
                known: false,
                size: None,
                align: None,
            },
        })
    }
    pub(super) fn error_reason<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, size_of::<Option<String>>())?;
        if self.reason.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        if let Some(error) = &self.error {
            self.reason = Some(error.display_observed(work.session, work.site)?);
        }
        Ok(())
    }
    pub(super) fn type_text<O: ExecutionObserver>(
        &mut self,
        ty: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Option<String>>())?;
        if self.tytext.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        self.tytext = Some(ty.display_observed(work.session, work.site)?);
        Ok(())
    }
}
pub(super) fn spelling_zero<O: ExecutionObserver>(ty: &Ty, work: &mut Work<'_, '_, O>) -> R<bool> {
    work.admit(1, 0)?;
    Ok(match ty {
        Ty::Unit => true,
        Ty::Tuple(elems) => elems.is_empty(),
        Ty::Array(_, 0) => true,
        _ => false,
    })
}
