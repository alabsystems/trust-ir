// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN against the complete actual ordinary collector/formatter.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{ClosureTyId, EnumId, FuncTyId, PredId, RecordId, StructId, TyId};
use trust_ir::{ClosureTy, EnumDef, EnumVariant, FieldDef, RecordDef, StructDef, StructRepr};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    work: usize,
    bytes: usize,
    stop: Option<usize>,
    cleanup_after: Option<usize>,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original handle-name stop");
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
    ExecutionSite::Entry(FuncId::new(823))
}
fn array(id: u32) -> Ty {
    Ty::Array(TyId::new(id), 0)
}
fn handle(name: &str) -> Ty {
    Ty::handle(name, format!("rt::{name}"))
}
fn field(ty: Ty) -> FieldDef {
    FieldDef {
        name: "opaque".into(),
        ty,
        offset: None,
    }
}
fn structure(id: u32, ty: Ty) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: "S".into(),
        fields: vec![field(ty)],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    }
}
fn enumeration(id: u32, ty: Ty) -> EnumDef {
    EnumDef::new(
        EnumId::new(id),
        "E",
        vec![EnumVariant {
            name: "V".into(),
            fields: vec![ty],
            field_names: vec![],
        }],
    )
}
fn record(id: u32, ty: Ty) -> RecordDef {
    RecordDef {
        id: RecordId::new(id),
        name: "R".into(),
        fields: vec![field(ty)],
    }
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.types = vec![
        handle("Z"),
        array(0),
        Ty::Tuple(vec![array(1), handle("A")]),
    ];
    m.func_types = vec![FuncTy::unrecorded(vec![handle("M")], vec![array(2)], false)];
    m.structs = vec![structure(70, array(2)), structure(70, handle("B"))];
    m.enums = vec![enumeration(90, Ty::Struct(StructId::new(70)))];
    m.records = vec![record(100, Ty::Enum(EnumId::new(90)))];
    m.closure_types = vec![ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![Ty::Record(RecordId::new(100))],
    }];
    m
}
fn expected(m: &Module, params: &[Ty], returns: &[Ty]) -> String {
    super::super::reachable_handles(m, params.iter().chain(returns))
        .into_iter()
        .map(|h| Ty::Handle(Box::new(h)).to_string())
        .collect::<Vec<_>>()
        .join(", ")
}
fn run(m: &Module, params: &[Ty], returns: &[Ty]) -> (String, Observer, usize) {
    let expected = expected(m, params, returns);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let output = reachable_handles_text_observed(m, params, returns, &mut s, site()).unwrap();
    let bound = calls.get();
    assert_eq!(output, expected);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    work.flat(output);
    drop(work);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events[bound - 1].phase, ExecutionPhase::Publication);
    (expected, o, bound)
}
fn drain<O: ExecutionObserver>(state: &mut State<'_>, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    work.flat(take(&mut state.output));
}
fn empty(state: &State<'_>) -> bool {
    state.stack.capacity() == 0
        && state.frames.capacity() == 0
        && state.seen.capacity() == 0
        && state.handles.capacity() == 0
        && state.pending.capacity() == 0
        && state.output.capacity() == 0
}
