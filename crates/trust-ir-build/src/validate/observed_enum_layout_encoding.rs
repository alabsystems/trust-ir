// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original enum descriptor prelude and encoding, at their original stages.
use super::*;
use core::mem::{size_of, take};
use std::sync::Arc;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::shape::TyLayoutShape;
use trust_ir::ty::{EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr};
use trust_ir::{LayoutError, LayoutTable};
mod direct;
mod niche;
mod niche_fields;
mod prelude;
mod query;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
enum Part<'a> {
    Text(&'a str),
    Number(u128),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Summary {
    size: Option<u64>,
    align: Option<u64>,
}
#[derive(Default)]
struct State<'m> {
    table: Option<LayoutTable<'m>>,
    shape: Option<Arc<TyLayoutShape>>,
    error: Option<LayoutError>,
    location: String,
    expected: String,
    actual: String,
    triple: String,
    why: String,
    errors: Vec<ValidationError>,
}
/// Private enclosing-pass context: its returned alignment must be supplied
/// unchanged to `validate_enum_layout_encoding_observed` after field checks.
/// Neither diagnostic list nor scalar is a layout/producer authority.
pub(super) fn validate_enum_layout_prelude_observed<O: ExecutionObserver>(
    module: &Module,
    enm: &EnumDef,
    layout: &EnumLayoutDescriptor,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<(Vec<ValidationError>, Option<u64>)> {
    header(session, site)?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.prelude(module, enm, layout, &mut work);
    match result {
        Ok(align) => state
            .finish(Ok(()), &mut work)
            .map(|errors| (errors, align)),
        Err(error) => state
            .finish(Err(error), &mut work)
            .map(|errors| (errors, None)),
    }
}
/// Exact original Direct/Niche/Untagged clauses. The private alignment comes
/// only from the preceding original prelude, never caller-selected evidence.
pub(super) fn validate_enum_layout_encoding_observed<O: ExecutionObserver>(
    module: &Module,
    enm: &EnumDef,
    layout: &EnumLayoutDescriptor,
    lane_align: Option<u64>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    header(session, site)?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = (|| {
        work.admit(1, size_of::<Option<u64>>())?;
        if lane_align == Some(0) {
            return Err(ObservedValueError::InvalidRange);
        }
        state.table = Some(LayoutTable::new_observed(module, work.session, work.site)?);
        match &layout.encoding {
            EnumTagEncoding::DirectWithUninhabited { .. } => Ok(()),
            EnumTagEncoding::Untagged => {
                work.admit(1, size_of::<usize>())?;
                if enm.variants.len() != 1 {
                    work.admit(1, size_of::<[Part<'_>; 3]>())?;
                    state.message(
                        enm,
                        &[Part::Text(
                            "exactly one variant under the untagged encoding",
                        )],
                        &[
                            Part::Number(enm.variants.len() as u128),
                            Part::Text(" variants"),
                        ],
                        &mut work,
                    )?;
                }
                Ok(())
            }
            EnumTagEncoding::SingleInhabited { variant } => {
                state.single_inhabited(enm, variant, &mut work)
            }
            EnumTagEncoding::Direct { tag_offset } => {
                state.direct(enm, layout, *tag_offset, lane_align, &mut work)
            }
            EnumTagEncoding::Niche {
                untagged_variant,
                niche_variants_start,
                niche_variants_end,
                niche_start,
                niche_offset,
                niche_ty,
            } => {
                work.admit(6, size_of::<Niche>())?;
                state.niche(
                    enm,
                    layout,
                    Niche {
                        untagged: *untagged_variant,
                        start: *niche_variants_start,
                        end: *niche_variants_end,
                        value: *niche_start,
                        offset: *niche_offset,
                        repr: *niche_ty,
                    },
                    lane_align,
                    &mut work,
                )
            }
        }
    })();
    state.finish(result, &mut work)
}
fn header<O: ExecutionObserver>(session: &mut ObservedSession<'_, O>, site: ExecutionSite) -> R {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 1,
            copy_bytes: size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>(),
        })
        .map_err(Into::into)
}
#[derive(Clone, Copy)]
struct Niche {
    untagged: u32,
    start: u32,
    end: u32,
    value: u128,
    offset: u64,
    repr: EnumTagRepr,
}
impl State<'_> {
    fn single_inhabited<O: ExecutionObserver>(
        &mut self,
        enm: &EnumDef,
        variant: &u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Option<usize>>())?;
        let active = usize::try_from(*variant).ok();
        let mut valid = active.is_some_and(|index| index < enm.variants.len());
        for (index, item) in enm.variants.iter().enumerate() {
            work.admit(1, size_of::<bool>())?;
            let uninhabited = self
                .table
                .as_ref()
                .ok_or(ObservedValueError::InvalidRange)?
                .variant_is_uninhabited_observed(item, work.session, work.site)?;
            if uninhabited == (Some(index) == active) {
                valid = false;
            }
        }
        if !valid {
            self.message(enm,
                &[Part::Text("one selected inhabited variant and only structurally uninhabited inactive variants")],
                &[Part::Text("single-inhabited selector "), Part::Number(u128::from(*variant))],
                work)?;
        }
        Ok(())
    }
    fn message<O: ExecutionObserver>(
        &mut self,
        enm: &EnumDef,
        expected: &[Part<'_>],
        actual: &[Part<'_>],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if self.location.capacity() != 0
            || self.expected.capacity() != 0
            || self.actual.capacity() != 0
        {
            return Err(ObservedValueError::InvalidRange);
        }
        work.text("enum.", &mut self.location)?;
        work.number(u128::from(enm.id.index()), &mut self.location)?;
        work.text(" (", &mut self.location)?;
        work.text(&enm.name, &mut self.location)?;
        work.text(") layout", &mut self.location)?;
        work.parts(expected, &mut self.expected)?;
        work.parts(actual, &mut self.actual)?;
        self.push(work)
    }
    fn push<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(ValidationError::ConstTypeMismatch {
            location: take(&mut self.location),
            expected: take(&mut self.expected),
            actual: take(&mut self.actual),
        });
        Ok(())
    }
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        work: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        self.retire_scratch(work);
        match result.and_then(|()| work.publication()) {
            Ok(()) => Ok(take(&mut self.errors)),
            Err(error) => {
                let _ = retire_validation_errors_observed(
                    take(&mut self.errors),
                    work.session,
                    work.site,
                );
                Err(work.terminal(error))
            }
        }
    }
    fn retire_shape<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<Arc<TyLayoutShape>>>().saturating_add(1));
        if let Some(shape) = self.shape.take() {
            let _ = shape.retire_arc_observed(work.session, work.site);
        }
        work.poll();
    }
    fn retire_error<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<LayoutError>>().saturating_add(1));
        if let Some(error) = self.error.take() {
            let _ = error.retire_observed(work.session, work.site);
        }
        work.poll();
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_shape(work);
        self.retire_error(work);
        work.retire_text(&mut self.location);
        work.retire_text(&mut self.expected);
        work.retire_text(&mut self.actual);
        work.retire_text(&mut self.triple);
        work.retire_text(&mut self.why);
        // Fresh private table, observed calls only: ordinary memo is empty.
        // This fixed empty release is not general populated-table retirement.
        work.step(size_of::<Option<LayoutTable<'_>>>().saturating_add(1));
        drop(self.table.take());
        work.poll();
    }
}
fn lane_size<O: ExecutionObserver>(repr: EnumTagRepr, work: &mut Work<'_, '_, O>) -> R<u64> {
    work.admit(1, size_of::<u64>())?;
    Ok(match repr {
        EnumTagRepr::U8 | EnumTagRepr::I8 => 1,
        EnumTagRepr::U16 | EnumTagRepr::I16 => 2,
        EnumTagRepr::U32 | EnumTagRepr::I32 => 4,
        EnumTagRepr::U64 | EnumTagRepr::I64 => 8,
        EnumTagRepr::U128 | EnumTagRepr::I128 => 16,
    })
}
// Original supplied owner/site, no new clock/grant/TLS/fuel/flag/fallback.
// Private alignment is not authority. Successful output/input disposal, full
// module/proof/native orchestration and physical std/allocator/deallocator/
// OOM/panic/unwind/RSS/hard100ms remain OPEN, including old layout Work internals.
