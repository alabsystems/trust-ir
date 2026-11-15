// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: actual original registry lookup/signature data and custody.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
mod lookup;
mod signature;
#[derive(Default)]
pub(super) struct Observer {
    pub(super) events: Vec<ExecutionProgress>,
    pub(super) calls: Rc<Cell<usize>>,
    pub(super) stop: Option<usize>,
    pub(super) cleanup_after: Option<usize>,
    pub(super) work: usize,
    pub(super) bytes: usize,
    pub(super) work_cap: Option<usize>,
    pub(super) byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original registry-inner stop");
        }
        if e.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_after.is_some_and(|n| self.events.len() > n)
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        }
        Ok(())
    }
}
pub(super) fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(1009))
}
pub(super) fn entry(
    symbol: &'static str,
    params: Vec<PinnedTy>,
    returns: Vec<PinnedTy>,
) -> HandleEntryPoint {
    HandleEntryPoint {
        role: "role",
        symbol,
        def_path: "opaque::path",
        params: Box::leak(params.into_boxed_slice()),
        returns: Box::leak(returns.into_boxed_slice()),
    }
}
pub(super) fn pin(entries: Vec<HandleEntryPoint>) -> HandleRuntimePin {
    HandleRuntimePin {
        name: "RawName",
        runtime: "raw::Runtime",
        calling_conv: trust_ir::CallingConv::C,
        entry_points: Box::leak(entries.into_boxed_slice()),
    }
}
pub(super) fn fixture() -> HandleRegistry {
    HandleRegistry {
        pins: vec![
            pin(vec![]),
            pin(vec![
                entry("early", vec![], vec![]),
                entry("same", vec![], vec![]),
                entry("same", vec![PinnedTy::Handle], vec![]),
            ]),
            pin(vec![
                entry("same", vec![], vec![PinnedTy::Handle]),
                entry("late", vec![], vec![]),
            ]),
        ],
    }
}
pub(super) fn lookup_events(r: &HandleRegistry, symbol: &str) -> Observer {
    let old = r.entry_for_symbol(symbol);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = r.entry_for_symbol_observed(symbol, &mut s, site()).unwrap();
    match (old, out) {
        (None, None) => {}
        (Some((a, b)), Some((c, d))) => {
            assert!(core::ptr::eq(a, c));
            assert!(core::ptr::eq(b, d));
        }
        _ => panic!("lookup mismatch"),
    }
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    o
}
pub(super) fn signature_events(
    pin: &HandleRuntimePin,
    entry: &HandleEntryPoint,
) -> (Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = pin.func_ty_observed(entry, &mut s, site()).unwrap();
    let bound = calls.get();
    assert_eq!(out.signature(), &pin.func_ty(entry));
    assert!(out.signature().abi.is_none());
    assert!(!out.signature().is_vararg);
    out.retire_observed(&mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(
        o.events[bound - 1].copy_bytes,
        size_of::<ObservedPinnedFuncTy>()
    );
    (o, bound)
}
