// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; exact contiguous ordinary block is retained as oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, GlobalId};
use trust_ir::{EffectSummary, Global, Visibility};
mod oracle;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    at: Option<usize>,
    work: usize,
    bytes: usize,
    cap: Option<usize>,
    byte_cap: Option<usize>,
    next: Option<Rc<Cell<bool>>>,
    cleanup: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.at == Some(self.events.len())
            || self.next.as_ref().is_some_and(|v| v.replace(false))
        {
            return Err("original interior");
        }
        if self.cleanup && e.phase == ExecutionPhase::ScratchRetirement {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(155))
}
fn fixture() -> (Module, Function, FunctionSummary) {
    let mut m = Module::new("summary shape");
    m.func_types
        .push(FuncTy::unrecorded(vec![Ty::Ptr, Ty::U8], Vec::new(), false));
    m.globals.push(Global {
        name: "g".into(),
        ty: Ty::U8,
        mutable: false,
        initializer: None,
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    let f = Function::new(
        FuncId::new(23),
        "full summary λ",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    (m, f, FunctionSummary::new())
}
fn execute(
    m: &Module,
    f: &Function,
    summary: &FunctionSummary,
) -> (Vec<ValidationError>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out =
        validate_function_summary_signature_effect_shape_observed(m, f, summary, &mut s, site())
            .unwrap();
    assert_eq!(out, oracle::ordinary(m, f, summary));
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    (out, o)
}
fn mixed() -> (Module, Function, FunctionSummary) {
    let (m, f, mut summary) = fixture();
    summary.params = vec!["x".into()];
    summary.effects = Some(
        EffectSummary::pure()
            .reading(EffectSet::Places(vec![
                EffectPlace::ParamPointee { index: 9 },
                EffectPlace::ParamPointee { index: 9 },
            ]))
            .writing(EffectSet::Places(vec![
                EffectPlace::Global(GlobalId::new(5)),
                EffectPlace::Global(GlobalId::new(1)),
            ])),
    );
    (m, f, summary)
}
