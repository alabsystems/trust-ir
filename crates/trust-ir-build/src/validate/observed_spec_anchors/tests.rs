// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; complete ordinary anchor mapping is the exact oracle.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::{InstructionSite, InterpretOptions};
use trust_ir::value::FuncTyId;
use trust_ir::{Block, FuncTy, SpecAnchor, SpecEnforcementMode, SpecModule, SpecProjectionTarget};
mod custody;
mod parity;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    cleanup: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) {
            return Err("original anchor stop");
        }
        if self.cleanup.as_ref().is_some_and(|arm| arm.get())
            && e.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(e.copy_bytes)
            .ok_or("copy overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(210))
}
fn fixture() -> Module {
    let mut m = Module::new("moduleλ");
    m.func_types.push(FuncTy::unrecorded(
        vec![Ty::Ref(Box::new(Ty::U8))],
        vec![Ty::U8],
        false,
    ));
    for (id, name) in [(7, "action"), (12, "project")] {
        let mut f = Function::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0));
        f.blocks.push(Block::new(BlockId::new(0)));
        m.functions.push(f);
    }
    let mut spec = SpecModule::new("M");
    spec.actions.push("a".into());
    spec.anchors.push(SpecAnchor {
        machine: "M".into(),
        action: "a".into(),
        rust_symbol: "action".into(),
        span: "opaque".into(),
        project: Some("project".into()),
        function: Some(FuncId::new(7)),
        projection_target: Some(SpecProjectionTarget::Function(FuncId::new(12))),
    });
    m.spec_modules.push(spec);
    m
}
fn bad() -> Module {
    let mut m = fixture();
    m.spec_modules[0].anchors[0].function = Some(FuncId::new(u32::MAX));
    m.spec_modules[0].anchors[0].projection_target =
        Some(SpecProjectionTarget::Function(FuncId::new(u32::MAX)));
    m
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer) {
    let mut o = Observer::default();
    let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
    let actual = validate_spec_anchor_functions_observed(m, &mut owner, site()).unwrap();
    assert_eq!(actual, super::super::validate_spec_anchor_functions(m));
    assert!(owner.first_refusal().is_none());
    assert_eq!(owner.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    (actual, o)
}
fn row(target: &'static str, label: &str) -> SpecLinkViolation {
    SpecLinkViolation::ExecutableTargetInvalid {
        machine: format!("M{label}"),
        action: format!("a{label}"),
        target,
        function: u32::MAX,
        detail: format!("detail{label}"),
    }
}
fn empty(state: &State) -> bool {
    state.batch.is_none() && state.pending.is_none() && state.errors.capacity() == 0
}
