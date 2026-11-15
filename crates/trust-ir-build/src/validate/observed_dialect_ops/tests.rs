// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN. Entire actual ordinary builtin+schema route is the oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::observed_value_types::build_module_value_types_observed;
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::dialect::schema::{
    AttributeKind, AttributeSchema, DialectSchema, OperandType, OperationSchema,
};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::FuncTyId;
use trust_ir::{Block, InstrNode};
mod abi_fixture;
mod builtin_parity;
mod custody;
mod parity;
mod schemas;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    work: usize,
    bytes: usize,
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
            return Err("original dialect stop");
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
    ExecutionSite::Entry(FuncId::new(1501))
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn vec_ty(t: Ty, n: u32) -> Ty {
    Ty::Vector(Box::new(t), n)
}
fn fixture() -> Module {
    let mut m = Module::new("");
    let types = vec![
        Ty::I32,
        Ty::I64,
        Ty::F32,
        Ty::F64,
        vec_ty(Ty::I32, 4),
        vec_ty(Ty::I16, 8),
        vec_ty(Ty::I64, 2),
        vec_ty(Ty::I8, 16),
        vec_ty(Ty::I8, 8),
        vec_ty(Ty::F32, 4),
        vec_ty(Ty::F64, 2),
        vec_ty(Ty::Bool, 4),
        Ty::Ptr,
        Ty::handle("H", "rt::H"),
        Ty::Func(FuncTyId::new(1)),
        Ty::Tuple(vec![Ty::Bool]),
        Ty::Bool,
        Ty::Func(FuncTyId::new(999)),
        Ty::Ref(Box::new(Ty::Bool)),
    ];
    m.func_types = vec![
        FuncTy::unrecorded(types.clone(), vec![], false),
        FuncTy::unrecorded(vec![Ty::I32], vec![Ty::Bool], false),
    ];
    let mut f = Function::new(
        FuncId::new(1501),
        "dialects",
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
fn node(op: DialectInst, count: usize) -> InstrNode {
    let mut n = InstrNode::new(Inst::DialectOp(Box::new(op)));
    n.results = (0..count).map(|i| v(100 + i as u32)).collect();
    n
}
fn schema() -> DialectSchemaRegistry {
    DialectSchemaRegistry::new([DialectSchema {
        namespace: "example".into(),
        version: 1,
        operations: vec![OperationSchema {
            name: "read".into(),
            operands: vec![Ty::I32.into()],
            results: vec![Ty::Bool],
            attributes: vec![AttributeSchema {
                name: "slot".into(),
                kind: AttributeKind::U64,
            }],
        }],
    }])
    .unwrap()
}
fn operation() -> DialectInst {
    DialectInst::new("example", "read")
        .with_operand(v(0))
        .with_result_ty(Ty::Bool)
        .with_attr("slot", AttrValue::U64(7))
}
fn callback_schema() -> DialectSchemaRegistry {
    DialectSchemaRegistry::new([DialectSchema {
        namespace: "example".into(),
        version: 1,
        operations: vec![OperationSchema {
            name: "call".into(),
            operands: vec![OperandType::Function {
                params: vec![Ty::I32],
                returns: vec![Ty::Bool],
            }],
            results: vec![Ty::Bool],
            attributes: vec![],
        }],
    }])
    .unwrap()
}
fn call(id: u32) -> DialectInst {
    DialectInst::new("example", "call")
        .with_operand(v(id))
        .with_result_ty(Ty::Bool)
}
fn setup<O: ExecutionObserver>(m: &Module, s: &mut ObservedSession<'_, O>) -> ObservedValueTypes {
    build_module_value_types_observed(&m.functions[0], m, s, site()).unwrap()
}
fn original(m: &Module, n: &InstrNode, r: Option<&DialectSchemaRegistry>) -> Vec<ValidationError> {
    let mut out = Vec::new();
    let values = build_module_value_types(&m.functions[0], m);
    if let Inst::DialectOp(op) = &n.inst {
        validate_dialect_op(&mut out, 1, op, &values);
        if let Some(r) = r
            && let Err(e) = r.validate_op_with_func_types(
                op,
                n.results.len(),
                |id| values.get(&id.index()),
                |id| m.func_type(id),
            )
        {
            out.push(ValidationError::InvalidDialectSchema {
                block: 1,
                op: op.qualified_name(),
                reason: e.to_string(),
            });
        }
    }
    out
}
fn run(
    m: &Module,
    n: &InstrNode,
    r: Option<&DialectSchemaRegistry>,
) -> (Vec<ValidationError>, Observer, usize, usize) {
    let expected = original(m, n, r);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let values = setup(m, &mut s);
    let begin = calls.get();
    let out =
        validate_dialect_node_observed(m, n, &values, r, BlockId::new(1), &mut s, site()).unwrap();
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
fn empty(state: &State<'_>) {
    assert_eq!(
        state.qualified.capacity()
            + state.reason.capacity()
            + state.temporary.capacity()
            + state.operand_tys.capacity()
            + state.seen.capacity()
            + state.errors.capacity(),
        0
    )
}
fn drain<O: ExecutionObserver>(state: &mut State<'_>, w: &mut Work<'_, '_, O>) {
    state.retire(w);
    let _ = retire_validation_errors_observed(take(&mut state.errors), w.session, w.site);
}
fn bounds(m: &Module, n: &InstrNode, r: Option<&DialectSchemaRegistry>) -> (usize, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let values = setup(m, &mut s);
    let begin = calls.get();
    let mut state = State::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state
        .run(m, n, &values, r, BlockId::new(1), &mut w)
        .unwrap();
    let end = calls.get();
    drain(&mut state, &mut w);
    empty(&state);
    values.retire_observed(w.session, w.site).unwrap();
    (begin, end)
}
