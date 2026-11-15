// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Full ordinary module refinement tables, propagation and consumption order.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{replace, size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::value::{PredId, UnivId};
use trust_ir::{Pred, Space, Universe};
mod consumption;
mod facts;
mod graph;
mod lattice;
mod sites;
mod storage;
mod tables;
#[cfg(test)]
mod tests;
mod text;
mod types;
use facts::{Fact, Facts};
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

#[derive(Default)]
struct State<'a> {
    errors: Vec<ValidationError>,
    scratch: Vec<ValidationError>,
    refusals: Vec<ValidationError>,
    location: String,
    base_location: String,
    detail: String,
    actual: String,
    required: String,
    key: String,
    seen_universes: Vec<(String, u32)>,
    seen_preds: Vec<(String, u32)>,
    type_stack: Vec<&'a Ty>,
    pred_stack: Vec<PredFrame<'a>>,
    pred_path: Vec<&'a Pred>,
    inline_types: Vec<&'a Ty>,
}

/// Preserve the complete original validate_refinements order and every error
/// field under this existing session/site. All actual table, inline surface,
/// propagation, CFG/frame closure and typed consumption work is observed.
/// Borrowed rows substitute for dead ordinary clones; no input is mutated.
/// A direct callee is selected by a paid full unique-ID scan, equivalent to
/// the original catalog constructed from this same module, including duplicates.
/// This returns diagnostics only, never module/proof/source authority.
/// Successful diagnostics remain caller-owned. On refusal, no partial output
/// escapes; every complete child, partial string, replaced record and owned
/// local buffer is consumed by the original session's retirement path.
/// Physical allocator/compiler/stack/time and input disposal remain external.
/// No grant, deadline, observer, epoch or fuel is created or renewed.
pub(crate) fn validate_module_refinements_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, &mut work);
    state.retire(&mut work);
    match result.and_then(|()| work.publication(size_of::<Vec<ValidationError>>())) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            let _ =
                retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
            Err(work.terminal(error))
        }
    }
}

impl State<'_> {
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.errors(&mut self.scratch);
        work.errors(&mut self.refusals);
        for text in [
            &mut self.base_location,
            &mut self.location,
            &mut self.detail,
            &mut self.actual,
            &mut self.required,
            &mut self.key,
        ] {
            work.flat(take(text));
        }
        for rows in [&mut self.seen_universes, &mut self.seen_preds] {
            while !rows.is_empty() {
                work.step(1);
                if let Some((text, _)) = rows.pop() {
                    work.flat(text);
                }
            }
            work.retire_vec(rows);
        }
        work.retire_vec(&mut self.type_stack);
        work.retire_vec(&mut self.pred_stack);
        work.retire_vec(&mut self.pred_path);
        work.retire_vec(&mut self.inline_types);
    }
    fn commit<O: ExecutionObserver>(
        &mut self,
        kind: ErrorKind,
        sink: Sink,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let rows = match sink {
            Sink::Main => &mut self.errors,
            Sink::Scratch => &mut self.scratch,
        };
        work.reserve(rows)?;
        work.admit(1, size_of::<ValidationError>())?;
        rows.push(match kind {
            ErrorKind::Malformed => ValidationError::PredicateTableMalformed {
                location: take(&mut self.location),
                detail: take(&mut self.detail),
            },
            ErrorKind::Invalid => ValidationError::RefinementTypeInvalid {
                location: take(&mut self.location),
                detail: take(&mut self.detail),
            },
            ErrorKind::Dangling(kind, id) => ValidationError::DanglingPredicateRef {
                location: take(&mut self.location),
                kind,
                id,
            },
            ErrorKind::Duplicate(kind, first, duplicate) => {
                ValidationError::PredicateTableNotInterned {
                    kind,
                    first,
                    duplicate,
                    content: take(&mut self.key),
                }
            }
            ErrorKind::NotImplied => ValidationError::RefinementNotImplied {
                location: take(&mut self.location),
                actual: take(&mut self.actual),
                required: take(&mut self.required),
            },
            ErrorKind::Contradicted => ValidationError::RefinementContradicted {
                location: take(&mut self.location),
                declared: take(&mut self.actual),
                derived: take(&mut self.required),
            },
        });
        // A dangling diagnostic need not consume a previously formed detail.
        work.flat(take(&mut self.detail));
        Ok(())
    }
    fn clear_location<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.location));
    }
}
#[derive(Clone, Copy)]
enum Sink {
    Main,
    Scratch,
}
enum ErrorKind {
    Malformed,
    Invalid,
    Dangling(&'static str, u32),
    Duplicate(&'static str, u32, u32),
    NotImplied,
    Contradicted,
}

#[derive(Clone, Copy)]
enum PredFrame<'a> {
    Visit(&'a Pred),
    Exit(&'a Pred),
}
