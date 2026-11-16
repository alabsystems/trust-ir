// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'m> State<'m> {
    pub(super) fn prelude<O: ExecutionObserver>(
        &mut self,
        module: &'m Module,
        enm: &EnumDef,
        layout: &EnumLayoutDescriptor,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<u64>> {
        work.admit(1, 0)?;
        if matches!(
            &layout.encoding,
            EnumTagEncoding::DirectWithUninhabited { .. }
        ) {
            // Its complete checked layout is owned by the field stage.
            return Ok(None);
        }
        self.table = Some(LayoutTable::new_observed(module, work.session, work.site)?);
        work.admit(1, size_of::<Option<EnumTagRepr>>())?;
        let repr = match &layout.encoding {
            EnumTagEncoding::Direct { .. } | EnumTagEncoding::DirectWithUninhabited { .. } => {
                enm.canonical_tag_repr_observed(work.session, work.site)?
            }
            EnumTagEncoding::Niche { niche_ty, .. } => Some(*niche_ty),
            EnumTagEncoding::Untagged | EnumTagEncoding::SingleInhabited { .. } => None,
        };
        let align = match repr {
            Some(repr) => self.alignment(enm, repr, work)?,
            None => None,
        };
        work.admit(4, 2 * size_of::<u64>())?;
        if layout.align == 0 || !layout.align.is_power_of_two() {
            work.admit(1, size_of::<[Part<'_>; 3]>())?;
            self.message(
                enm,
                &[Part::Text("a non-zero power-of-two alignment")],
                &[Part::Text("align "), Part::Number(u128::from(layout.align))],
                work,
            )?;
        } else if !layout.size.is_multiple_of(layout.align) {
            work.admit(1, size_of::<[Part<'_>; 4]>())?;
            self.message(
                enm,
                &[
                    Part::Text("size a multiple of align "),
                    Part::Number(u128::from(layout.align)),
                ],
                &[Part::Text("size "), Part::Number(u128::from(layout.size))],
                work,
            )?;
        }
        Ok(align)
    }
    fn alignment<O: ExecutionObserver>(
        &mut self,
        enm: &EnumDef,
        repr: EnumTagRepr,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<u64>> {
        // repr.ty is an exhaustive ten-scalar, nonallocating match, not a
        // recursively owned type construction or arbitrary formatter.
        work.admit(10, size_of::<Ty>())?;
        let ty = repr.ty();
        if let Some(summary) = self.query(&ty, work)? {
            work.admit(4, size_of::<Option<u64>>())?;
            if let Some(bits) = summary
                .align
                .filter(|bits| *bits != 0 && bits.is_multiple_of(8))
            {
                return Ok(Some(bits / 8));
            }
            work.admit(2, size_of::<LayoutError>())?;
            self.error = Some(LayoutError::UnsupportedTyShape(ty.shape()));
        }
        work.admit(1, 0)?;
        if self.triple.capacity() != 0 || self.why.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        match self.error.take() {
            Some(LayoutError::TargetScalarLayoutUnavailable { triple }) => {
                self.triple = triple;
                work.reserve(&mut self.errors)?;
                work.admit(1, size_of::<ValidationError>() + size_of::<u32>())?;
                self.errors
                    .push(ValidationError::EnumTagTargetScalarLayoutUnavailable {
                        enum_id: enm.id.index(),
                        triple: take(&mut self.triple),
                    });
            }
            Some(error) => {
                self.error = Some(error);
                self.why = self
                    .error
                    .as_ref()
                    .ok_or(ObservedValueError::InvalidRange)?
                    .display_observed(work.session, work.site)?;
                self.retire_error(work);
                work.admit(1, 0)?;
                work.admit(1, size_of::<[Part<'_>; 2]>())?;
                // The returned why remains in State while location/expected
                // allocate; moving it into actual is infallible afterwards.
                work.text("enum.", &mut self.location)?;
                work.number(u128::from(enm.id.index()), &mut self.location)?;
                work.text(" (", &mut self.location)?;
                work.text(&enm.name, &mut self.location)?;
                work.text(") layout", &mut self.location)?;
                work.text(
                    "a resolvable alignment for the tag lane's integer type",
                    &mut self.expected,
                )?;
                work.admit(1, size_of::<String>())?;
                self.actual = take(&mut self.why);
                self.push(work)?;
            }
            None => return Err(ObservedValueError::InvalidRange),
        }
        Ok(None)
    }
}
