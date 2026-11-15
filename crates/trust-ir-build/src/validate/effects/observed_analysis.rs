// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original conservative body effects; carried claims never mint authority.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::observed_effect_admission::{
    admissible_effects_observed, function_by_id_observed,
};
use super::super::{
    ImportPolicy, ValidationError, instruction_kind, retire_validation_errors_observed,
};
use super::observed_context::{Arguments, Call, CallKind, What, root_label_observed};
use super::observed_need::{Flag, ObservedNeed, Piece, PlaceReason, Reason, Side};
use super::observed_roots::{ObservedBody, ObservedRoots};
use super::{
    Arg, AssertKind, EffectPlace, EffectSet, EffectSummary, Function, Inst, Module, PanicSite,
    Root, ValueId,
};
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::value::FuncId;
mod access;
mod calls;
mod instructions;
mod report;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
struct Analysis<'m, 'f> {
    module: &'m Module,
    policy: ImportPolicy<'m>,
    body: Option<ObservedBody<'f>>,
    need: Option<ObservedNeed>,
    roots: Option<ObservedRoots>,
}
/// Exact structural effect-summary body pass under the existing import policy.
/// Definitions may rely on each other's carried summaries only under the same
/// original enclosing whole-module body validation premise as the ordinary
/// pass. This function authenticates no import, body, proof or source itself.
pub(crate) fn validate_effect_summary_observed<O: ExecutionObserver>(
    module: &Module,
    function: &Function,
    policy: ImportPolicy<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(
        2,
        size_of::<Analysis<'_, '_>>()
            + size_of::<Work<'_, '_, O>>()
            + size_of::<Option<&EffectSummary>>(),
    )?;
    let Some(declared) = function.summary.as_ref().and_then(|s| s.effects.as_ref()) else {
        work.publication(size_of::<Vec<ValidationError>>())?;
        return Ok(Vec::new());
    };
    work.admit(1, size_of::<usize>() + size_of::<bool>())?;
    if function.blocks.is_empty() {
        work.publication(size_of::<Vec<ValidationError>>())?;
        return Ok(Vec::new());
    }
    let mut analysis = Analysis {
        module,
        policy,
        body: None,
        need: None,
        roots: None,
    };
    let result = (|| -> R {
        work.admit(
            2,
            size_of::<ObservedBody<'_>>() + size_of::<Option<ObservedBody<'_>>>(),
        )?;
        analysis.body = Some(ObservedBody::new_observed(
            function,
            work.session,
            work.site,
        )?);
        work.admit(
            2,
            size_of::<ObservedNeed>() + size_of::<Option<ObservedNeed>>(),
        )?;
        analysis.need = Some(ObservedNeed::new_observed(work.session, work.site)?);
        analysis.walk(function, &mut work)
    })();
    analysis.retire_roots(&mut work);
    analysis.retire_body(&mut work);
    match result.and_then(|()| {
        work.admit(
            2,
            size_of::<ObservedNeed>()
                + size_of::<Option<ObservedNeed>>()
                + size_of::<&str>()
                + size_of::<&EffectSummary>(),
        )
    }) {
        Ok(()) => {
            let need = analysis
                .need
                .take()
                .ok_or(ObservedValueError::InvalidRange)?;
            // Complete owned Need moves directly into Report before its first
            // callback. Its own return/transport storage was admitted above.
            report::run(need, &function.name, declared, &mut work)
        }
        Err(error) => {
            analysis.retire_need(&mut work);
            Err(work.terminal(error))
        }
    }
}
impl Analysis<'_, '_> {
    fn walk<O: ExecutionObserver>(&mut self, function: &Function, work: &mut Work<'_, '_, O>) -> R {
        let mut at = 0usize;
        while let Some(block) = work.at(&function.blocks, at)? {
            let mut index = 0usize;
            while let Some(node) = work.at(&block.body, index)? {
                work.admit(1, size_of::<u32>() + size_of::<&Inst>())?;
                self.instruction(&node.inst, block.id.index(), work)?;
                work.next(&mut index)?;
            }
            work.next(&mut at)?;
        }
        work.admit(1, 0)
    }
    fn retire_roots<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<ObservedRoots>>().saturating_add(1));
        if let Some(roots) = self.roots.take() {
            let _ = roots.retire_observed(work.session, work.site);
        }
        work.poll();
    }
    fn retire_body<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<ObservedBody<'_>>>().saturating_add(1));
        if let Some(body) = self.body.take() {
            let _ = body.retire_observed(work.session, work.site);
        }
        work.poll();
    }
    fn retire_need<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<ObservedNeed>>().saturating_add(1));
        if let Some(need) = self.need.take() {
            let _ = need.retire_observed(work.session, work.site);
        }
        work.poll();
    }
    fn need_mut(&mut self) -> R<&mut ObservedNeed> {
        self.need.as_mut().ok_or(ObservedValueError::InvalidRange)
    }
    fn side<O: ExecutionObserver>(
        &mut self,
        side: Side,
        place: Option<EffectPlace>,
        block: u32,
        pieces: &[Piece<'_>],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.need_mut()?
            .add_side_observed(side, place, block, pieces, work.session, work.site)
    }
    fn flag<O: ExecutionObserver>(
        &mut self,
        flag: Flag,
        block: u32,
        pieces: &[Piece<'_>],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.need_mut()?
            .add_flag_observed(flag, block, pieces, work.session, work.site)
    }
    fn top<O: ExecutionObserver>(
        &mut self,
        block: u32,
        pieces: &[Piece<'_>],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.side(Side::Read, None, block, pieces, work)?;
        self.side(Side::Write, None, block, pieces, work)?;
        for flag in [Flag::Allocates, Flag::Frees, Flag::MayUnwind, Flag::Io] {
            work.admit(1, size_of::<Flag>())?;
            self.flag(flag, block, pieces, work)?;
        }
        Ok(())
    }
}
