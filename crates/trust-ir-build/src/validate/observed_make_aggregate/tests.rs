// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; actual original rule is the parity oracle, never validity.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::observed_value_types::build_module_value_types_observed;
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::{EnumTagRepr, EnumVariant};
use trust_ir::value::{FuncTyId, PredId, TyId};
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
            return Err("original make-aggregate stop");
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
    ExecutionSite::Entry(FuncId::new(1401))
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
    m.types = vec![Ty::Bool, Ty::U64, Ty::Never];
    m.structs = vec![structure(0, vec![Ty::Bool, Ty::U64])];
    m.records = vec![RecordDef {
        id: RecordId::new(0),
        name: "R".into(),
        fields: vec![field(Ty::Bool), field(Ty::U64)],
    }];
    m.enums = vec![EnumDef::new(
        EnumId::new(0),
        "E",
        vec![
            EnumVariant {
                name: "A".into(),
                fields: vec![Ty::Bool, Ty::U64],
                field_names: vec![],
            },
            EnumVariant {
                name: "Empty".into(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "Void".into(),
                fields: vec![Ty::Never],
                field_names: vec![],
            },
        ],
    )];
    let types = vec![
        Ty::Bool,
        Ty::U64,
        Ty::U8,
        Ty::Ptr,
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::handle("H", "rt::H"),
        Ty::Rc(Box::new(Ty::Bool)),
        Ty::Ref(Box::new(Ty::Bool)),
    ];
    m.func_types = vec![FuncTy::unrecorded(types.clone(), vec![], false)];
    let mut f = Function::new(
        FuncId::new(1401),
        "aggregate",
        FuncTyId::new(0),
        BlockId::new(1),
    );
    let mut block = Block::new(f.entry);
    block.params = types
        .into_iter()
        .enumerate()
        .map(|(i, t)| (v(i as u32), t))
        .collect();
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(block);
    m.functions.push(f);
    m
}
fn make(ty: Ty, variant: Option<u32>, fields: &[u32]) -> Inst {
    Inst::MakeAggregate {
        ty,
        variant,
        fields: fields.iter().copied().map(v).collect(),
    }
}
fn original(m: &Module, inst: &Inst) -> Vec<ValidationError> {
    let mut errors = Vec::new();
    let values = build_module_value_types(&m.functions[0], m);
    if let Inst::MakeAggregate {
        ty,
        variant,
        fields,
    } = inst
    {
        validate_make_aggregate(
            &mut errors,
            &trust_ir::LayoutTable::new(m),
            1,
            ty,
            *variant,
            fields,
            &values,
        );
    }
    errors
}
fn setup<'m, O: ExecutionObserver>(
    m: &'m Module,
    s: &mut ObservedSession<'_, O>,
) -> (trust_ir::LayoutTable<'m>, ObservedValueTypes) {
    (
        trust_ir::LayoutTable::new_observed(m, s, site()).unwrap(),
        build_module_value_types_observed(&m.functions[0], m, s, site()).unwrap(),
    )
}
fn run(m: &Module, inst: &Inst) -> (Vec<ValidationError>, Observer, usize, usize) {
    let expected = original(m, inst);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (layouts, values) = setup(m, &mut s);
    let begin = calls.get();
    let out =
        validate_make_aggregate_observed(&layouts, inst, &values, BlockId::new(1), &mut s, site())
            .unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    values.retire_observed(&mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    drop(layouts); // Borrowed original table/module disposal is a separate caller duty.
    assert!(o.events.iter().all(|e| e.site == site()));
    (expected, o, begin, end)
}
fn empty(s: &State) {
    assert_eq!(
        s.ty.capacity()
            + s.reason.capacity()
            + s.op.capacity()
            + s.role.capacity()
            + s.expected.capacity()
            + s.actual.capacity()
            + s.render.capacity()
            + s.location.capacity()
            + s.enum_name.capacity()
            + s.variant_name.capacity()
            + s.spelling.capacity()
            + s.discriminants.capacity()
            + s.errors.capacity(),
        0
    );
}
fn drain<O: ExecutionObserver>(s: &mut State, w: &mut Work<'_, '_, O>) {
    s.retire(w);
    let _ = retire_validation_errors_observed(take(&mut s.errors), w.session, w.site);
}
fn long_void() -> Module {
    let mut m = fixture();
    m.enums[0].name = "é🦀Enum".repeat(300);
    m.enums[0].variants[2].name = "中Void".repeat(300);
    m
}
