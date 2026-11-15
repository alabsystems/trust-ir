// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn here<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.text(self.base, &mut self.location)?;
        let mut at = 0;
        while let Some(part) = work.at(&self.path, at)? {
            match part {
                PathElement::Index(n) => {
                    work.text("[", &mut self.location)?;
                    work.unsigned(*n as u128, &mut self.location)?;
                    work.text("]", &mut self.location)?;
                }
                PathElement::Field(s) => {
                    work.text(".", &mut self.location)?;
                    work.text(s, &mut self.location)?;
                }
            }
            work.next(&mut at)?;
        }
        Ok(())
    }
    pub(super) fn mismatch<O: ExecutionObserver>(
        &mut self,
        item: Item<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.expected = item.ty.display_observed(work.session, work.site)?;
        self.actual = item
            .constant
            .shape_label_observed(work.session, work.site)?;
        self.mismatch_ready(work)
    }
    pub(super) fn mismatch_ready<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        self.here(work)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 3 * size_of::<String>())?;
        self.errors.push(ValidationError::ConstTypeMismatch {
            location: take(&mut self.location),
            expected: take(&mut self.expected),
            actual: take(&mut self.actual),
        });
        Ok(())
    }
    pub(super) fn missing<O: ExecutionObserver>(
        &mut self,
        kind: &str,
        id: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.here(work)?;
        work.text(kind, &mut self.expected)?;
        work.unsigned(u128::from(id), &mut self.expected)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
        self.errors
            .push(ValidationError::ConstTypeReferenceNotFound {
                location: take(&mut self.location),
                type_ref: take(&mut self.expected),
            });
        Ok(())
    }
    pub(super) fn uniform_error<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        self.here(work)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
        self.errors.push(ValidationError::NonCanonicalUniformArray {
            location: take(&mut self.location),
            spelling: take(&mut self.spelling),
        });
        Ok(())
    }
    #[allow(clippy::too_many_arguments)] // The node's own fields, spelled out.
    pub(super) fn tensor_blob<O: ExecutionObserver>(
        &mut self,
        symbols: &ObservedConstantSymbols<'_, '_>,
        constant: &Constant,
        digest: &trust_ir::blob::BlobDigest,
        dims: &[u64],
        elem: &Ty,
        rank: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // The rules read each extent once and scan the table for the row; a
        // refusal's text is bounded by its extents' spelling.
        work.admit(
            dims.len()
                .saturating_add(symbols.module().blobs.len())
                .saturating_add(64),
            dims.len().saturating_mul(48).saturating_add(512),
        )?;
        let root = core::ptr::eq(constant, self.root);
        let Some(refusal) = super::super::constant_values::tensor_blob_refusal(
            symbols.module(),
            root,
            digest,
            dims,
            elem,
            rank,
        ) else {
            return Ok(());
        };
        self.here(work)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
        self.errors
            .push(refusal.into_error(take(&mut self.location), digest));
        Ok(())
    }
    pub(super) fn render_actual_ty<O: ExecutionObserver>(
        &mut self,
        ty: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.render = ty.display_observed(work.session, work.site)?;
        work.text(&self.render, &mut self.actual)?;
        work.flat(take(&mut self.render));
        work.admit(1, 0)
    }
    pub(super) fn pointer_error<O: ExecutionObserver>(
        &mut self,
        symbol: &str,
        ty: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.here(work)?;
        work.text(symbol, &mut self.symbol)?;
        self.tytext = ty.display_observed(work.session, work.site)?;
        work.reserve(&mut self.errors)?;
        work.admit(
            1,
            size_of::<ValidationError>()
                + 3 * size_of::<String>()
                + size_of::<PointerConstantRefusal>(),
        )?;
        self.errors.push(ValidationError::PointerConstantRefused {
            location: take(&mut self.location),
            symbol: take(&mut self.symbol),
            ty: take(&mut self.tytext),
            reason: self.reason.take().ok_or(ObservedValueError::InvalidRange)?,
        });
        Ok(())
    }
}
