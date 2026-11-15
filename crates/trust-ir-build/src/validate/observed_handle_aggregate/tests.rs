// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: original full lane rule and actual observed children.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::observed_value_types::build_module_value_types_observed;
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::inst::SwitchCase;
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::{EnumVariant, StructRepr};
use trust_ir::value::FuncTyId;
use trust_ir::{Block, InstrNode};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
pub(super) struct Observer {
    pub(super) events: Vec<ExecutionProgress>,
    pub(super) calls: Rc<Cell<usize>>,
    pub(super) work: Rc<Cell<usize>>,
    pub(super) bytes: Rc<Cell<usize>>,
    pub(super) stop: Option<usize>,
    pub(super) cleanup_after: Option<usize>,
    pub(super) work_cap: Option<usize>,
    pub(super) byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original aggregate stop");
        }
        if e.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_after.is_some_and(|n| self.events.len() > n)
        {
            return Err("cleanup");
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

pub(super) fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(1093))
}
fn v(i: u32) -> ValueId {
    ValueId::new(i)
}
fn handle() -> Ty {
    Ty::handle("Name", "rt::Name")
}
fn tuple() -> Ty {
    Ty::Tuple(vec![handle(), Ty::Bool])
}
fn fixture() -> (Module, Function) {
    let mut m = Module::new("");
    m.structs = vec![StructDef {
        id: StructId::new(0),
        name: "S".into(),
        fields: vec![
            FieldDef {
                name: "H".into(),
                ty: handle(),
                offset: None,
            },
            FieldDef {
                name: "B".into(),
                ty: Ty::Bool,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    }];
    m.enums = vec![EnumDef::new(
        EnumId::new(0),
        "E",
        vec![
            EnumVariant {
                name: "A".into(),
                fields: vec![handle()],
                field_names: vec![],
            },
            EnumVariant {
                name: "B".into(),
                fields: vec![Ty::U64],
                field_names: vec![],
            },
        ],
    )];
    let params = vec![
        (v(0), handle()),
        (v(1), Ty::Bool),
        (v(2), tuple()),
        (v(3), Ty::Struct(StructId::new(0))),
        (v(4), Ty::Enum(EnumId::new(0))),
        (v(5), Ty::U64),
    ];
    m.func_types = vec![FuncTy::unrecorded(
        params.iter().map(|(_, t)| t.clone()).collect(),
        vec![],
        false,
    )];
    let mut f = Function::new(FuncId::new(1093), "F", FuncTyId::new(0), BlockId::new(1));
    let mut entry = Block::new(f.entry);
    entry.params = params;
    entry.body.push(
        InstrNode::new(Inst::ExtractField {
            ty: Ty::U8,
            aggregate: v(4),
            field: 0,
        })
        .with_result(v(10)),
    );
    entry.body.push(InstrNode::new(Inst::Switch {
        value: v(10),
        cases: vec![
            SwitchCase {
                value: Constant::Int(0),
                target: BlockId::new(17),
                args: vec![],
            },
            SwitchCase {
                value: Constant::Int(1),
                target: BlockId::new(18),
                args: vec![],
            },
        ],
        default: BlockId::new(33),
        default_args: vec![],
        exhaustive_enum_unreachable: false,
    }));
    f.blocks.push(entry);
    for id in [17, 18, 33] {
        let mut b = Block::new(BlockId::new(id));
        b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(b);
    }
    (m, f)
}
fn make(ty: Ty, variant: Option<u32>, fields: &[u32]) -> Inst {
    Inst::MakeAggregate {
        ty,
        variant,
        fields: fields.iter().copied().map(v).collect(),
    }
}
fn extract(ty: Ty, aggregate: u32, field: u32) -> Inst {
    Inst::ExtractField {
        ty,
        aggregate: v(aggregate),
        field,
    }
}
fn insert(ty: Ty, aggregate: u32, field: u32, value: u32) -> Inst {
    Inst::InsertField {
        ty,
        aggregate: v(aggregate),
        field,
        value: v(value),
    }
}
fn setup<'m, 'f, O: ExecutionObserver>(
    m: &'m Module,
    f: &'f Function,
    guard: bool,
    s: &mut ObservedSession<'_, O>,
) -> (
    ObservedValueTypes,
    trust_ir::ObservedNominalTypeReachability<'m>,
    Option<ObservedHandleEnumGuards<'f>>,
) {
    let values = build_module_value_types_observed(f, m, s, site()).unwrap();
    let nominal = m.nominal_type_reachability_observed(s, site()).unwrap();
    let guards = if guard {
        Some(ObservedHandleEnumGuards::new_observed(f, s, site()).unwrap())
    } else {
        None
    };
    (values, nominal, guards)
}
fn dispose<O: ExecutionObserver>(
    values: ObservedValueTypes,
    nominal: trust_ir::ObservedNominalTypeReachability<'_>,
    guards: Option<ObservedHandleEnumGuards<'_>>,
    s: &mut ObservedSession<'_, O>,
) {
    if let Some(guards) = guards {
        let _ = guards.retire_observed(s, site());
    }
    let _ = values.retire_observed(s, site());
    let _ = nominal.retire_observed(s, site());
}
fn dispose_reason<O: ExecutionObserver>(
    answer: Result<(), String>,
    s: &mut ObservedSession<'_, O>,
) {
    if let Err(reason) = answer {
        Work {
            session: s,
            site: site(),
        }
        .flat(reason);
    }
}
fn run(
    m: &Module,
    f: &Function,
    inst: &Inst,
    block: BlockId,
    guard: bool,
) -> (Result<(), String>, Observer, usize, usize) {
    let old_values = super::super::build_module_value_types(f, m);
    let old_nominal = m.nominal_type_reachability();
    let old_guard = if guard {
        Some(super::super::HandleEnumGuards::new(f))
    } else {
        None
    };
    let expected = super::super::handle_aggregate_lane_rule(
        m,
        inst,
        &old_values,
        &old_nominal,
        block,
        old_guard.as_ref(),
    );
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (values, nominal, guards) = setup(m, f, guard, &mut s);
    let begin = calls.get();
    let out = handle_aggregate_lane_rule_observed(
        m,
        inst,
        &values,
        &nominal,
        block,
        guards.as_ref(),
        &mut s,
        site(),
    )
    .unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    dispose_reason(out, &mut s);
    dispose(values, nominal, guards, &mut s);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(
        o.events[end - 1],
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 1,
            copy_bytes: size_of::<Result<(), String>>()
        }
    );
    (expected, o, begin, end)
}
fn empty(s: &State) -> bool {
    s.reason.capacity() == 0
        && s.render.capacity() == 0
        && s.discriminants.capacity() == 0
        && s.selected.capacity() == 0
        && s.tag_ty.is_none()
}
fn drain<O: ExecutionObserver>(s: &mut State, work: &mut Work<'_, '_, O>) {
    s.retire_scratch(work);
    work.flat(take(&mut s.reason));
}
