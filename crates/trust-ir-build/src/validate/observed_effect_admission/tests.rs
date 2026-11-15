// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; borrowed effect pointers are never authentication receipts.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use trust_ir::interpret::{InstructionSite, InterpretOptions};
use trust_ir::value::{BlockId, FuncTyId, GlobalId};
use trust_ir::{Block, EffectPlace, EffectSet, FunctionSummary};
mod parity;
mod stops;
#[derive(Default)]
pub(crate) struct Observer {
    pub(crate) events: Vec<ExecutionProgress>,
    pub(crate) stop: Option<usize>,
    work: usize,
    bytes: usize,
    cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl Observer {
    pub(crate) fn stopping(stop: usize) -> Self {
        Self {
            stop: Some(stop),
            ..Self::default()
        }
    }
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("original effect admission");
        }
        self.work = self.work.checked_add(event.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(event.copy_bytes)
            .ok_or("copy overflow")?;
        if self.cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        }
        Ok(())
    }
}
pub(crate) fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(221))
}
pub(crate) fn fixture(declaration: bool) -> Module {
    let mut m = Module::new("borrowed admission");
    let mut f = Function::new(
        FuncId::new(221),
        "calleeλ",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    if !declaration {
        f.blocks.push(Block::new(BlockId::new(0)));
    }
    let mut summary = FunctionSummary::new();
    summary.effects = Some(EffectSummary::pure());
    f.summary = Some(summary);
    m.functions.push(f);
    m
}
fn interposable_oracle(linkage: Linkage) -> bool {
    match linkage {
        Linkage::Weak | Linkage::LinkOnce | Linkage::ExternalWeak => true,
        Linkage::External
        | Linkage::Internal
        | Linkage::Private
        | Linkage::AvailableExternally
        | Linkage::WeakOdr
        | Linkage::LinkOnceOdr => false,
    }
}
// Complete ordinary admissible_effects policy, with the original lookup and
// private recorded-outcome read, copied only as a test oracle.
fn ordinary<'m>(
    module: &'m Module,
    callee: FuncId,
    policy: ImportPolicy<'_>,
) -> Option<&'m EffectSummary> {
    let target = module.function_by_id(callee)?;
    let effects = target.summary.as_ref()?.effects.as_ref()?;
    if interposable_oracle(target.linkage) {
        return None;
    }
    if !target.is_declaration() {
        return Some(effects);
    }
    match policy {
        ImportPolicy::Authenticated(authenticated) => matches!(
            authenticated.backed_by_outcome(callee),
            Some(crate::linked::SiteOutcome::Authenticated)
        )
        .then_some(effects),
        ImportPolicy::Structural | ImportPolicy::Refuse => None,
    }
}
pub(crate) fn assert_ordinary(m: &Module, callee: FuncId, policy: ImportPolicy<'_>) -> Observer {
    let expected = ordinary(m, callee, policy);
    let mut o = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut o);
    let actual = admissible_effects_observed(m, callee, policy, &mut session, site()).unwrap();
    match (actual, expected) {
        (Some(a), Some(b)) => assert!(core::ptr::eq(a, b)),
        (None, None) => {}
        _ => panic!("effect admission changed"),
    }
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    drop(session);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    o
}
fn linkages() -> [Linkage; 9] {
    [
        Linkage::External,
        Linkage::Internal,
        Linkage::Private,
        Linkage::AvailableExternally,
        Linkage::WeakOdr,
        Linkage::LinkOnceOdr,
        Linkage::Weak,
        Linkage::LinkOnce,
        Linkage::ExternalWeak,
    ]
}
