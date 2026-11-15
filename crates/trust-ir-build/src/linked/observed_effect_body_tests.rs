// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; private stored labels do not authenticate any input.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::validate::{
    ImportPolicy, ValidationError, retire_validation_errors_observed,
    validate_effect_summary_observed,
};
use std::{cell::Cell, rc::Rc};
use trust_ir::inst::Inst;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, InterpretOptions,
    ObservedSession, ObservedValueError,
};
use trust_ir::value::{BlockId, FuncTyId, GlobalId, ValueId};
use trust_ir::{
    Block, EffectPlace, EffectSet, EffectSummary, Function, FunctionSummary, InstrNode, Ty,
};

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    calls: Rc<Cell<usize>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original recorded-policy stop");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(313))
}
fn fixture(global: bool, declaration: bool) -> (Module, Function) {
    let mut caller = Function::new(
        FuncId::new(0),
        "callerλ\0",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(ValueId::new(1), Ty::Ptr)];
    block.body.push(InstrNode::new(Inst::Call {
        callee: FuncId::new(7),
        args: vec![ValueId::new(1)],
    }));
    caller.blocks.push(block);
    let mut summary = FunctionSummary::new();
    summary.effects = Some(EffectSummary::pure());
    caller.summary = Some(summary);
    let mut callee = Function::new(
        FuncId::new(7),
        "calleeλ\0",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    if !declaration {
        callee.blocks.push(Block::new(BlockId::new(0)));
    }
    let mut summary = FunctionSummary::new();
    let mut effects = EffectSummary::pure();
    effects.reads = EffectSet::Places(vec![if global {
        EffectPlace::Global(GlobalId::new(9))
    } else {
        EffectPlace::ParamPointee { index: 0 }
    }]);
    summary.effects = Some(effects);
    callee.summary = Some(summary);
    let mut module = Module::new("recorded body effects");
    module.functions = vec![caller.clone(), callee];
    (module, caller)
}
fn run(
    module: &Module,
    caller: &Function,
    auth: &AuthenticatedImports,
) -> (Vec<ValidationError>, Observer, usize) {
    let mut observer = Observer::default();
    let calls = observer.calls.clone();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let errors = validate_effect_summary_observed(
        module,
        caller,
        ImportPolicy::Authenticated(auth),
        &mut session,
        site(),
    )
    .unwrap();
    let copy = errors.clone();
    let bound = calls.get(); // Actual outer return, before caller disposal.
    retire_validation_errors_observed(errors, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    drop(session);
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert!(auth.digests().is_empty() && auth.authenticated_inheritances().is_empty());
    (copy, observer, bound)
}
#[test]
fn complete_body_uses_only_the_exact_recorded_authenticated_declaration_outcome() {
    let (module, caller) = fixture(false, true);
    for outcome in [
        None,
        Some(SiteOutcome::Authenticated),
        Some(SiteOutcome::Reported),
        Some(SiteOutcome::Refused("full λ\0".repeat(3000))),
    ] {
        let admitted = matches!(outcome.as_ref(), Some(SiteOutcome::Authenticated));
        let mut auth = AuthenticatedImports::default();
        auth.record_backed_by(FuncId::new(6), SiteOutcome::Authenticated);
        if let Some(outcome) = outcome {
            auth.record_backed_by(FuncId::new(7), outcome);
        }
        let before = auth.backed_by.clone();
        let (errors, _, _) = run(&module, &caller, &auth);
        assert_eq!(errors.len(), if admitted { 1 } else { 6 });
        if admitted {
            assert!(
                matches!(&errors[0], ValidationError::EffectSummaryViolated {function,effect:"reads",block:0,inst} if function=="callerλ\0" && inst=="call (callee reads *param0) through *param0")
            );
        } else {
            assert!(
                matches!(&errors[0], ValidationError::EffectSummaryViolated {effect:"reads",inst,..} if inst=="call to @calleeλ\0, which has no admissible effect summary (havoc), which needs reads: Everything")
            );
        }
        assert_eq!(auth.backed_by, before);
    }
}
#[test]
fn imported_global_claim_never_becomes_a_local_global_effect() {
    let (module, caller) = fixture(true, true);
    let mut auth = AuthenticatedImports::default();
    auth.record_backed_by(FuncId::new(7), SiteOutcome::Authenticated);
    let (errors, _, _) = run(&module, &caller, &auth);
    assert_eq!(errors.len(), 1);
    assert!(
        matches!(&errors[0],ValidationError::EffectSummaryViolated {effect:"reads",inst,..} if inst=="call, whose declaration's summary names a global of another module, which needs reads: Everything")
    );
}
#[test]
fn stored_outcomes_do_not_override_interposition_or_the_original_definition_premise() {
    for declaration in [false, true] {
        for linkage in [
            trust_ir::Linkage::Weak,
            trust_ir::Linkage::LinkOnce,
            trust_ir::Linkage::ExternalWeak,
        ] {
            let (mut module, caller) = fixture(false, declaration);
            module.functions[1].linkage = linkage;
            let mut auth = AuthenticatedImports::default();
            auth.record_backed_by(FuncId::new(7), SiteOutcome::Authenticated);
            assert_eq!(run(&module, &caller, &auth).0.len(), 6);
        }
    }
    let (module, caller) = fixture(false, false);
    let mut auth = AuthenticatedImports::default();
    auth.record_backed_by(
        FuncId::new(7),
        SiteOutcome::Refused("not the definition premise".into()),
    );
    let (errors, _, _) = run(&module, &caller, &auth);
    assert_eq!(errors.len(), 1);
    assert!(
        matches!(&errors[0],ValidationError::EffectSummaryViolated {effect:"reads",inst,..} if inst=="call (callee reads *param0) through *param0")
    );
}
#[test]
fn actual_interior_recorded_map_stop_refuses_the_whole_body_without_havoc_fallback() {
    let (module, caller) = fixture(false, true);
    let mut auth = AuthenticatedImports::default();
    for id in 0..7 {
        auth.record_backed_by(FuncId::new(id), SiteOutcome::Reported);
    }
    auth.record_backed_by(FuncId::new(7), SiteOutcome::Authenticated);
    let before = auth.backed_by.clone();
    let (_, base, end) = run(&module, &caller, &auth);
    // Select every original body callback: this includes the actual stored
    // lookup interior and outer publication, without a same-size ordinal guess.
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    for stop in 1..=end {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_effect_summary_observed(
                &module,
                &caller,
                ImportPolicy::Authenticated(&auth),
                &mut session,
                site()
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original recorded-policy stop"
        );
        drop(session);
        assert_eq!(&observer.events[..stop], &base.events[..stop]);
        assert!(
            observer.events[stop..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
        assert_eq!(auth.backed_by, before);
    }
    assert!(auth.digests().is_empty() && auth.authenticated_inheritances().is_empty());
}
