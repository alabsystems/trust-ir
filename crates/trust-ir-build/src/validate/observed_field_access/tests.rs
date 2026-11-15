// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; actual original validate_field_access oracle, not validity.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::{ClosureTy, EnumTagRepr, EnumVariant};
use trust_ir::value::{ClosureTyId, FuncTyId, PredId, TyId};
use trust_ir::{Block, InstrNode, StructRepr};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    work: Rc<Cell<usize>>,
    bytes: Rc<Cell<usize>>,
    stop: Option<usize>,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original field-access stop");
        }
        self.work
            .set(self.work.get().checked_add(e.work).ok_or("overflow")?);
        self.bytes.set(
            self.bytes
                .get()
                .checked_add(e.copy_bytes)
                .ok_or("overflow")?,
        );
        if self.work_cap.is_some_and(|n| self.work.get() > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes.get() > n) {
            return Err("copy");
        }
        Ok(())
    }
}

fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(1321))
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn field(ty: Ty) -> FieldDef {
    FieldDef {
        name: "F".into(),
        ty,
        offset: None,
    }
}
fn structure(id: u32, types: Vec<Ty>) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: "S".into(),
        fields: types.into_iter().map(field).collect(),
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    }
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.types = vec![Ty::Bool, Ty::U64];
    m.structs = vec![structure(0, vec![Ty::Bool, Ty::U64])];
    m.records = vec![RecordDef {
        id: RecordId::new(0),
        name: "R".into(),
        fields: vec![field(Ty::Bool), field(Ty::U64)],
    }];
    m.closure_types = vec![ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![Ty::Bool, Ty::U64],
    }];
    m.enums = vec![EnumDef::new(
        EnumId::new(0),
        "E",
        vec![
            EnumVariant {
                name: "A".into(),
                fields: vec![Ty::Bool],
                field_names: vec![],
            },
            EnumVariant {
                name: "B".into(),
                fields: vec![Ty::U64],
                field_names: vec![],
            },
            EnumVariant {
                name: "Empty".into(),
                fields: vec![],
                field_names: vec![],
            },
        ],
    )];
    let types = vec![
        Ty::Struct(StructId::new(0)),
        Ty::Record(RecordId::new(0)),
        Ty::Tuple(vec![Ty::Bool, Ty::U64]),
        Ty::Closure(ClosureTyId::new(0)),
        Ty::Enum(EnumId::new(0)),
        Ty::Bool,
        Ty::U64,
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::Ptr,
    ];
    m.func_types = vec![FuncTy::unrecorded(types.clone(), vec![], false)];
    let mut f = Function::new(
        FuncId::new(1321),
        "fields",
        FuncTyId::new(0),
        BlockId::new(1),
    );
    let mut b = Block::new(f.entry);
    b.params = types
        .into_iter()
        .enumerate()
        .map(|(i, t)| (v(i as u32), t))
        .collect();
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    m.functions.push(f);
    m
}
fn extract(aggregate: u32, field: u32, ty: Ty) -> Inst {
    Inst::ExtractField {
        ty,
        aggregate: v(aggregate),
        field,
    }
}
fn insert(aggregate: u32, field: u32, ty: Ty, value: u32) -> Inst {
    Inst::InsertField {
        ty,
        aggregate: v(aggregate),
        field,
        value: v(value),
    }
}
fn original(m: &Module, inst: &Inst) -> Vec<ValidationError> {
    let mut out = Vec::new();
    let map = build_module_value_types(&m.functions[0], m);
    match inst {
        Inst::ExtractField {
            ty,
            aggregate,
            field,
        } => validate_field_access(
            &mut out,
            m,
            1,
            "extract_field",
            *aggregate,
            *field,
            ty,
            None,
            &map,
        ),
        Inst::InsertField {
            ty,
            aggregate,
            field,
            value,
        } => validate_field_access(
            &mut out,
            m,
            1,
            "insert_field",
            *aggregate,
            *field,
            ty,
            Some(*value),
            &map,
        ),
        _ => {}
    }
    out
}
fn setup<O: ExecutionObserver>(m: &Module, s: &mut ObservedSession<'_, O>) -> ObservedValueTypes {
    build_module_value_types_observed(&m.functions[0], m, s, site()).unwrap()
}
fn run(m: &Module, inst: &Inst) -> (Vec<ValidationError>, Observer, usize, usize) {
    let expected = original(m, inst);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let values = setup(m, &mut s);
    let begin = calls.get();
    let out =
        validate_field_access_observed(m, inst, &values, BlockId::new(1), &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    values.retire_observed(&mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (expected, o, begin, end)
}
fn empty(s: &State<'_>) {
    assert_eq!(
        s.op.capacity()
            + s.role.capacity()
            + s.reason.capacity()
            + s.expected.capacity()
            + s.actual.capacity()
            + s.render.capacity()
            + s.lanes.capacity()
            + s.errors.capacity(),
        0
    );
    assert!(s.tag.is_none())
}
fn drain<O: ExecutionObserver>(s: &mut State<'_>, work: &mut Work<'_, '_, O>) {
    s.retire(work);
    let _ = retire_validation_errors_observed(take(&mut s.errors), work.session, work.site);
}
fn long_enum() -> Module {
    let mut m = fixture();
    for i in 0..8 {
        m.enums[0].variants.push(EnumVariant {
            name: ("é🦀variant".repeat(200) + &i.to_string()),
            fields: vec![Ty::handle("中", "rt::long")],
            field_names: vec![],
        });
    }
    m
}
