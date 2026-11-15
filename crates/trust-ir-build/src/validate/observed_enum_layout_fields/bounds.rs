// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn bounds<O: ExecutionObserver>(
        &mut self,
        enm: &EnumDef,
        layout: &EnumLayoutDescriptor,
        v: usize,
        f: usize,
        ty: &Ty,
        offset: u64,
        size: Option<u64>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(3, size_of::<Option<u64>>())?;
        let outside = match size {
            Some(size) => offset.checked_add(size).is_none_or(|end| end > layout.size),
            None => !query::spelling_zero(ty, work)? || offset > layout.size,
        };
        if outside {
            self.field_prefix(v, f, work)?;
            match size {
                Some(size) => {
                    work.text(" entirely within size ", &mut self.expected)?;
                    work.number(u128::from(layout.size), &mut self.expected)?;
                    work.text("offset ", &mut self.actual)?;
                    work.number(u128::from(offset), &mut self.actual)?;
                    work.text(", field size ", &mut self.actual)?;
                    work.number(u128::from(size), &mut self.actual)?;
                }
                None => {
                    work.text(
                        " to have a resolvable layout (needed to bound it within size ",
                        &mut self.expected,
                    )?;
                    work.number(u128::from(layout.size), &mut self.expected)?;
                    work.text(")", &mut self.expected)?;
                    self.type_text(ty, work)?;
                    work.text("offset ", &mut self.actual)?;
                    work.number(u128::from(offset), &mut self.actual)?;
                    work.admit(1, 0)?;
                    work.text(
                        if self.reason.is_some() {
                            ", layout UNRESOLVABLE for type "
                        } else {
                            ", no size for type "
                        },
                        &mut self.actual,
                    )?;
                    work.text(
                        self.tytext
                            .as_deref()
                            .ok_or(ObservedValueError::InvalidRange)?,
                        &mut self.actual,
                    )?;
                    if let Some(reason) = &self.reason {
                        work.text(": ", &mut self.actual)?;
                        work.text(reason, &mut self.actual)?;
                    }
                }
            }
            self.push(enm, work)?;
            retire_text_slot(&mut self.tytext, work);
            work.admit(1, 0)?;
        }
        Ok(())
    }
}
