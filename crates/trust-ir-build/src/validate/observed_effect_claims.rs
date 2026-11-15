// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original readnone/readonly body diagnostics under one supplied observer.
use super::{Function, Inst, Module, ValidationError, ValueId};
use core::mem::{size_of, take};
use trust_ir::inst::{CastOp, Ordering};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::value::FuncId;
use trust_ir::{DropResolution, ObservedDropGlueIndex};
mod collect;
mod effect;
mod names;
mod roots;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Claim {
    ReadNone,
    ReadOnly,
}
impl Claim {
    fn attr(self) -> &'static str {
        match self {
            Self::ReadNone => "readnone",
            Self::ReadOnly => "readonly",
        }
    }
    fn callee_requirement(self) -> &'static str {
        match self {
            Self::ReadNone => "readnone",
            Self::ReadOnly => "readonly or readnone",
        }
    }
}
#[derive(Clone, Copy)]
enum Definition<'f> {
    Parameter { block: u32, index: usize },
    Node(&'f Inst),
}
type DefRow<'f> = (ValueId, Definition<'f>);
#[derive(Clone, Copy)]
enum Effect {
    None,
    Read { address: ValueId },
    Write { address: ValueId },
    Refused { reason: &'static str },
    CallEdge { callee: FuncId },
}
#[derive(Default)]
struct State<'f, 'm> {
    definitions: Vec<DefRow<'f>>,
    stack: Vec<ValueId>,
    seen: Vec<ValueId>,
    roots: Vec<Option<Definition<'f>>>,
    drop_index: Option<ObservedDropGlueIndex<'m>>,
    function_name: String,
    inst_text: String,
    errors: Vec<ValidationError>,
}

/// Exact original effect-claim diagnostics, including malformed duplicate and
/// cyclic definitions. Only GEP, Copy and PtrToPtr are transparent to the
/// ALL-local-Alloca root question. Module direct calls use the original
/// direct-slot/first-fallback lookup; drops use that exact module's observed
/// unique/ambiguous drop lookup. No partial diagnostics escape a resource stop.
///
/// All actual traversal, text, storage, nested type comparisons and cleanup use
/// this original session/site. Bodyless/no-claim functions keep their original
/// empty diagnostic result; this is neither a full validator nor effect/source
/// authority. Successful input/output disposal remains caller-owned. Logical
/// cleanup establishes no physical allocator/deallocator or hard-time bound.
pub(super) fn validate_function_effect_claims_observed<O: ExecutionObserver>(
    function: &Function,
    module: Option<&Module>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<State<'_, '_>>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.run(function, module, &mut work);
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            state.retire_errors(&mut work);
            Err(work.terminal(error))
        }
    }
}
impl State<'_, '_> {
    fn retire_trace<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_rows(&mut self.stack);
        work.retire_rows(&mut self.seen);
        work.retire_rows(&mut self.roots);
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_trace(work);
        work.retire_rows(&mut self.definitions);
        // The index contains only one borrowed module reference, not owned Ty
        // keys. Explicitly retire its header; never consume the caller module.
        work.session.retirement_step(
            work.site,
            size_of::<Option<ObservedDropGlueIndex<'_>>>().saturating_add(1),
        );
        work.retire_flat(self.drop_index.take());
        work.session
            .retirement_step(work.site, size_of::<String>().saturating_add(1));
        work.retire_text(take(&mut self.function_name));
        work.session
            .retirement_step(work.site, size_of::<String>().saturating_add(1));
        work.retire_text(take(&mut self.inst_text));
    }
    fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.session.retirement_step(
            work.site,
            size_of::<Vec<ValidationError>>().saturating_add(1),
        );
        let _ = super::retire_validation_errors_observed(
            take(&mut self.errors),
            work.session,
            work.site,
        );
    }
    fn commit<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        block: u32,
        claim: Claim,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(&function.name, &mut self.function_name)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(ValidationError::FuncAttrClaimViolated {
            function: take(&mut self.function_name),
            attr: claim.attr(),
            block,
            inst: take(&mut self.inst_text),
        });
        Ok(())
    }
}
