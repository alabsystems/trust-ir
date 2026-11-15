// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored Rust controls, all UNRUN.
use super::*;
use trust_ir::inst::{BindingFrameDef, BindingSlot, CastOp};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::{
    ClosureTy, EnumDef, EnumVariant, FieldDef, RecordDef, SetRepr, StructDef, StructRepr,
};
use trust_ir::value::{
    BindingFrameId, ClosureTyId, EnumId, FuncTyId, PredId, RecordId, StructId, TyId,
};
use trust_ir::{Block, DropGlueEntry, Global, InstrNode};
mod fixtures;
mod parity;
mod stops;
use fixtures::*;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("original poison stop");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(119))
}
fn observed(module: &Module) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let actual = validate_module_error_types_observed(module, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (actual, observer)
}
fn parity(module: &Module) -> Vec<ValidationError> {
    let (actual, observer) = observed(module);
    assert_eq!(actual, validate_module_error_types(module));
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
fn poison(location: &str) -> ValidationError {
    ValidationError::ConstTypeMismatch {
        location: location.into(),
        expected: EXPECTED.into(),
        actual: "error".into(),
    }
}
