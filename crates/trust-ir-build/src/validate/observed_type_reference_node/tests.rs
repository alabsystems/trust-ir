// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: original one-node rule, configured registry and ownership.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::{ClosureTy, DialectTy, EnumDef, RecordDef, SetRepr, StructDef, StructRepr};
use trust_ir::value::{ClosureTyId, EnumId, FuncTyId, PredId, RecordId, StructId, TyId};
mod custody;
mod lookup;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    cleanup_after: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original type-reference stop");
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
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(509))
}
fn registry() -> HandleRegistry {
    HandleRegistry {
        pins: TRUSTED_HANDLE_RUNTIMES.to_vec(),
    }
}
fn run(
    m: &Module,
    r: &HandleRegistry,
    ty: &Ty,
    loc: &str,
) -> ((Vec<ValidationError>, NominalCensus), Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_type_reference_node_observed(m, r, ty, loc, &mut s, site()).unwrap();
    let mut expected = vec![];
    super::super::check_ty_reference_node(
        m,
        &ModuleFunctionCatalog::new(m),
        r,
        ty,
        loc,
        &mut expected,
    );
    let census = NominalCensus {
        dialect: matches!(ty, Ty::Dialect(_)),
        handle: matches!(ty, Ty::Handle(_)),
    };
    assert_eq!(out, (expected, census));
    let saved = out.clone();
    let bound = calls.get();
    retire_validation_errors_observed(out.0, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events[bound - 1].phase, ExecutionPhase::Publication);
    (saved, o, bound)
}
fn targets() -> Module {
    let mut m = Module::new("");
    m.types.push(Ty::Bool);
    m.func_types.push(FuncTy::unrecorded(vec![], vec![], false));
    m.closure_types.push(ClosureTy::bare(FuncTyId::new(0)));
    m.structs.push(StructDef {
        id: StructId::new(0),
        name: "S".into(),
        fields: vec![],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    });
    m.enums.push(EnumDef::new(EnumId::new(0), "E", vec![]));
    m.records.push(RecordDef {
        id: RecordId::new(0),
        name: "R".into(),
        fields: vec![],
    });
    m
}
fn references(id: u32) -> Vec<Ty> {
    vec![
        Ty::Struct(StructId::new(id)),
        Ty::Enum(EnumId::new(id)),
        Ty::Record(RecordId::new(id)),
        Ty::Closure(ClosureTyId::new(id)),
        Ty::Func(FuncTyId::new(id)),
        Ty::Array(TyId::new(id), 0),
        Ty::Set(TyId::new(id), SetRepr::Bitset),
        Ty::Sequence(TyId::new(id)),
        Ty::FatPtr(trust_ir::ty::FatPtrKind::Slice(TyId::new(id))),
    ]
}
fn invalid() -> Ty {
    Ty::Dialect(Box::new(DialectTy::new("bad namespace", "name", 1)))
}
fn untrusted() -> Ty {
    Ty::handle("RawName_9", "untrusted::runtime::RawName_9")
}
fn prior() -> ValidationError {
    ValidationError::InvalidDialectType {
        location: "prior λ\0FULL".into(),
        detail: "prior 尾\0FULL".into(),
    }
}
fn drain<O: ExecutionObserver>(s: &mut State, w: &mut Work<'_, '_, O>) {
    s.retire_scratch(w);
    let _ = retire_validation_errors_observed(take(&mut s.errors), w.session, w.site);
}
fn empty(s: &State) -> bool {
    s.location.capacity() == 0
        && s.detail.capacity() == 0
        && s.name.capacity() == 0
        && s.runtime.capacity() == 0
        && s.errors.capacity() == 0
}
