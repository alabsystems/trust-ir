// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN. Complete actual ordinary indirect arm, not filtered whole-module success.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::observed_value_types::build_module_value_types_observed;
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{ClosureTyId, FuncTyId, PredId, TyId};
use trust_ir::{Block, InstrNode};
mod custody;
mod diagnostic_lists;
mod original;
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
            return Err("original indirect stop");
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
    ExecutionSite::Entry(FuncId::new(1201))
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn h() -> Ty {
    Ty::handle("Handle", "rt::Handle")
}
fn d() -> Ty {
    Ty::Dialect(Box::new(trust_ir::DialectTy::new("ns", "D", 1)))
}
fn call(callee: u32, sig: u32, args: &[u32]) -> Inst {
    Inst::CallIndirect {
        callee: v(callee),
        sig: FuncTyId::new(sig),
        args: args.iter().copied().map(v).collect(),
        calling_conv: CallingConv::C,
    }
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.types = vec![Ty::Bool];
    m.func_types = vec![
        FuncTy::unrecorded(
            vec![Ty::Bool, Ty::U64, h(), d(), Ty::Func(FuncTyId::new(1))],
            vec![],
            false,
        ),
        FuncTy::unrecorded(vec![Ty::Bool, Ty::U64], vec![], false),
        FuncTy::unrecorded(vec![Ty::U64], vec![Ty::Bool], false),
    ];
    let mut f = Function::new(
        FuncId::new(1201),
        "caller",
        FuncTyId::new(0),
        BlockId::new(1),
    );
    let mut b = Block::new(f.entry);
    b.params = vec![
        (v(0), Ty::Bool),
        (v(1), Ty::U64),
        (v(2), h()),
        (v(3), d()),
        (v(4), Ty::Func(FuncTyId::new(1))),
    ];
    b.body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::Func(FuncTyId::new(1)),
            value: Constant::FnDef(FuncId::new(9)),
        })
        .with_result(v(10)),
        InstrNode::new(call(10, 1, &[0, 1])),
        InstrNode::new(Inst::Return { values: vec![] }),
    ];
    f.blocks.push(b);
    let target = Function::new(FuncId::new(9), "target", FuncTyId::new(1), BlockId::new(0));
    m.functions = vec![f, target];
    m
}
fn closure() -> Module {
    let mut m = fixture();
    m.closure_types = vec![trust_ir::ty::ClosureTy {
        func: FuncTyId::new(1),
        captures: vec![Ty::Bool],
    }];
    m.func_types.push(FuncTy::unrecorded(
        vec![Ty::Bool, Ty::Bool, Ty::U64],
        vec![],
        false,
    ));
    m.functions[1].ty = FuncTyId::new(3);
    m.functions[0].blocks[0].body[0] = InstrNode::new(Inst::Const {
        ty: Ty::Closure(ClosureTyId::new(0)),
        value: Constant::Closure {
            func: FuncId::new(9),
            captures: vec![Constant::Bool(true)],
        },
    })
    .with_result(v(10));
    m
}
fn abi() -> trust_ir::signature_abi::SignatureAbi {
    use trust_ir::signature_abi::*;
    let argument = AbiArgument {
        size: 0,
        align: 0,
        mode: AbiPassMode::Ignore,
        bindings: vec![],
    };
    SignatureAbi {
        target: AbiTarget {
            triple: "raw".into(),
            data_layout: "".into(),
            abi: "".into(),
            cpu: "".into(),
            features: vec!["z".into(), "a".into(), "a".into()],
            target_spec: "".into(),
            pointer_bytes: 0,
            little_endian: true,
        },
        frontend: AbiFrontend {
            name: "".into(),
            revision: "".into(),
        },
        convention: "contradictory".into(),
        lowered_convention: CallingConv::C,
        source_abi: "raw".into(),
        can_unwind: false,
        variadic: true,
        fixed_count: u32::MAX,
        arguments: vec![],
        result: argument,
    }
}
fn setup<'m, O: ExecutionObserver>(
    m: &'m Module,
    s: &mut ObservedSession<'_, O>,
) -> (
    ModuleFunctionCatalog<'m>,
    ObservedValueTypes,
    ObservedNominalTypeReachability<'m>,
) {
    (
        ModuleFunctionCatalog::new_observed(m, s, site()).unwrap(),
        build_module_value_types_observed(&m.functions[0], m, s, site()).unwrap(),
        m.nominal_type_reachability_observed(s, site()).unwrap(),
    )
}
fn dispose<O: ExecutionObserver>(
    catalog: ModuleFunctionCatalog<'_>,
    values: ObservedValueTypes,
    nominal: ObservedNominalTypeReachability<'_>,
    s: &mut ObservedSession<'_, O>,
) {
    let _ = values.retire_observed(s, site());
    let _ = nominal.retire_observed(s, site());
    let _ = catalog.retire_observed(s, site());
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize, usize) {
    run_at(m, 0, 1)
}
fn run_at(
    m: &Module,
    block: usize,
    index: usize,
) -> (Vec<ValidationError>, Observer, usize, usize) {
    let expected = original::original(m, block, index);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values, nominal) = setup(m, &mut s);
    let begin = calls.get();
    let mut context = ObservedIndirectCalls::new_observed(&catalog, 0, &mut s, site()).unwrap();
    let out = context
        .validate_at_observed(block, index, &values, Some(&nominal), &mut s, site())
        .unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    context.retire_observed(&mut s, site()).unwrap();
    dispose(catalog, values, nominal, &mut s);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events[begin..].iter().all(|e| e.site == site()));
    (expected, o, begin, end)
}
fn empty(state: &State) {
    assert_eq!(
        state.name.capacity()
            + state.detail.capacity()
            + state.expected.capacity()
            + state.actual.capacity()
            + state.render.capacity()
            + state.pending.capacity()
            + state.errors.capacity(),
        0
    );
}
