// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN. Complete actual original module Rule2 is the oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{
    cell::{Cell, RefCell},
    rc::Rc,
};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::{EnumTagRepr, EnumVariant};
use trust_ir::value::FuncTyId;
use trust_ir::{Block, InstrNode};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    trace: Rc<RefCell<Vec<ExecutionProgress>>>,
    interrupt: Option<Rc<Cell<bool>>>,
    calls: Rc<Cell<usize>>,
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
        self.trace.borrow_mut().push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original enum-coverage stop");
        }
        if self.interrupt.as_ref().is_some_and(|a| a.get()) {
            return Err("interrupt");
        }
        if self.cleanup.as_ref().is_some_and(|a| a.get())
            && e.phase == ExecutionPhase::ScratchRetirement
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
    ExecutionSite::Entry(FuncId::new(6101))
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn variant(name: &str, fields: Vec<Ty>) -> EnumVariant {
    EnumVariant {
        name: name.into(),
        fields,
        field_names: vec![],
    }
}
fn switch(value: u32, values: Vec<Constant>) -> InstrNode {
    InstrNode::new(Inst::Switch {
        value: v(value),
        default: BlockId::new(9),
        default_args: vec![],
        cases: values
            .into_iter()
            .map(|value| trust_ir::inst::SwitchCase {
                value,
                target: BlockId::new(9),
                args: vec![],
            })
            .collect(),
        exhaustive_enum_unreachable: true,
    })
}
fn cast(op: CastOp, src: Ty, dst: Ty, operand: u32, result: u32) -> InstrNode {
    InstrNode::new(Inst::Cast {
        op,
        src_ty: src,
        dst_ty: dst,
        operand: v(operand),
    })
    .with_result(v(result))
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.enums.push(EnumDef::new(
        EnumId::new(7),
        "E",
        vec![variant("Zero", vec![]), variant("One", vec![])],
    ));
    m.func_types.push(FuncTy::unrecorded(
        vec![Ty::Enum(EnumId::new(7))],
        vec![],
        false,
    ));
    let mut f = Function::new(
        FuncId::new(6101),
        "caller",
        FuncTyId::new(0),
        BlockId::new(1),
    );
    let mut b = Block::new(f.entry);
    b.params = vec![(v(0), Ty::Enum(EnumId::new(7)))];
    b.body = vec![
        InstrNode::new(Inst::ExtractField {
            ty: Ty::U8,
            aggregate: v(0),
            field: 0,
        })
        .with_result(v(1)),
        switch(1, vec![Constant::Int(0)]),
    ];
    f.blocks.push(b);
    let mut end = Block::new(BlockId::new(9));
    end.body.push(InstrNode::new(Inst::Unreachable));
    f.blocks.push(end);
    m.functions.push(f);
    m
}
fn signed() -> Module {
    let mut m = fixture();
    m.enums[0].discriminants = vec![Some(-1), Some(0)];
    m.enums[0].repr = Some(EnumTagRepr::I8);
    m.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::ExtractField {
            ty: Ty::I8,
            aggregate: v(0),
            field: 0,
        })
        .with_result(v(1)),
        cast(CastOp::SExt, Ty::I8, Ty::I16, 1, 2),
        cast(CastOp::SExt, Ty::I16, Ty::I32, 2, 3),
        switch(3, vec![Constant::Int(-1), Constant::Int(0)]),
    ];
    m
}
fn original(m: &Module) -> Vec<ValidationError> {
    let f = &m.functions[0];
    let values = super::super::build_module_value_types(f, m);
    super::super::exhaustive_switch::validate_exhaustive_switch_cases(&m.layout_table(), f, &values)
}
fn setup<O: ExecutionObserver>(m: &Module, s: &mut ObservedSession<'_, O>) -> ObservedValueTypes {
    build_module_value_types_observed(&m.functions[0], m, s, site()).unwrap()
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize, usize) {
    let expected = original(m);
    let layouts = m.layout_table();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let values = setup(m, &mut s);
    let begin = calls.get();
    let out = validate_exhaustive_switch_cases_observed(
        &layouts,
        &m.functions[0],
        &values,
        &mut s,
        site(),
    )
    .unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    values.retire_observed(&mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (expected, o, begin, end)
}
fn empty(s: &State<'_, '_>) {
    assert!(s.selection.is_none());
    assert_eq!(
        s.definitions.capacity()
            + s.widen.capacity()
            + s.discriminants.capacity()
            + s.disc_bits.capacity()
            + s.covered.capacity()
            + s.enum_ty.capacity()
            + s.literal.capacity()
            + s.reason.capacity()
            + s.here.capacity()
            + s.errors.capacity(),
        0
    );
}
fn drain<O: ExecutionObserver>(s: &mut State<'_, '_>, w: &mut Work<'_, '_, O>) {
    s.retire_scratch(w);
    let _ = retire_validation_errors_observed(take(&mut s.errors), w.session, w.site);
}
