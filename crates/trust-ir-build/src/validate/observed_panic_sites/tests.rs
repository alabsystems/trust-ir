// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; direct actual original validator, never full validity.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, GlobalId, PredId, TyId};
use trust_ir::{AssertKind, Block, Global, InstrNode, TlsModel};
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
            return Err("original panic-site stop");
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
    ExecutionSite::Entry(FuncId::new(1251))
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn global(name: &str) -> Global {
    Global {
        name: name.into(),
        ty: Ty::U8,
        mutable: false,
        initializer: None,
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    }
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.types = vec![Ty::Ptr];
    m.func_types = vec![
        FuncTy::unrecorded(vec![Ty::Bool, Ty::Usize, Ty::Usize, Ty::Ptr], vec![], false),
        FuncTy::unrecorded(vec![Ty::Usize, Ty::Usize, Ty::Ptr], vec![], false),
    ];
    let mut f = Function::new(
        FuncId::new(1251),
        "caller",
        FuncTyId::new(0),
        BlockId::new(1),
    );
    let mut b = Block::new(f.entry);
    b.params = vec![
        (v(0), Ty::Bool),
        (v(1), Ty::Usize),
        (v(2), Ty::Usize),
        (v(3), Ty::Ptr),
    ];
    b.body = vec![
        InstrNode::new(Inst::NullPtr).with_result(v(20)),
        InstrNode::new(Inst::Assert {
            cond: v(0),
            kind: AssertKind::BoundsCheck {
                index: v(1),
                len: v(2),
            },
            site: Some(PanicSite {
                entry: FuncId::new(9),
                location: PanicLocation::Value(v(3)),
            }),
        }),
        InstrNode::new(Inst::Return { values: vec![] }),
    ];
    f.blocks.push(b);
    m.functions.push(f);
    m.functions.push(Function::new(
        FuncId::new(9),
        "panic_entry",
        FuncTyId::new(1),
        BlockId::new(0),
    ));
    m.globals.push(global("panic-location"));
    m
}
fn change_site(m: &mut Module, location: PanicLocation) {
    match &mut m.functions[0].blocks[0].body[1].inst {
        Inst::Assert {
            site: Some(site), ..
        }
        | Inst::AssertInvoke { site, .. } => site.location = location,
        _ => panic!(),
    }
}
fn original(m: &Module, block: usize, index: usize) -> Vec<ValidationError> {
    let f = &m.functions[0];
    let b = &f.blocks[block];
    let node = &b.body[index];
    let mut errors = Vec::new();
    let (kind, panic) = match &node.inst {
        Inst::Assert {
            kind,
            site: Some(site),
            ..
        }
        | Inst::AssertInvoke { kind, site, .. } => (kind, site),
        _ => return errors,
    };
    validate_panic_site(
        m,
        &ModuleFunctionCatalog::new(m),
        f,
        b.id.index(),
        index,
        kind,
        panic,
        &build_module_value_types(f, m),
        &mut errors,
    );
    errors
}
fn setup<'m, O: ExecutionObserver>(
    m: &'m Module,
    s: &mut ObservedSession<'_, O>,
) -> (ModuleFunctionCatalog<'m>, ObservedValueTypes) {
    (
        ModuleFunctionCatalog::new_observed(m, s, site()).unwrap(),
        build_module_value_types_observed(&m.functions[0], m, s, site()).unwrap(),
    )
}
fn dispose<O: ExecutionObserver>(
    catalog: ModuleFunctionCatalog<'_>,
    values: ObservedValueTypes,
    s: &mut ObservedSession<'_, O>,
) {
    let _ = values.retire_observed(s, site());
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
    let expected = original(m, block, index);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values) = setup(m, &mut s);
    let begin = calls.get();
    let out = validate_panic_site_at_observed(&catalog, 0, block, index, &values, &mut s, site())
        .unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    dispose(catalog, values, &mut s);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events[begin..].iter().all(|e| e.site == site()));
    (expected, o, begin, end)
}
fn empty(s: &State) {
    assert_eq!(
        s.name.capacity()
            + s.op.capacity()
            + s.role.capacity()
            + s.expected.capacity()
            + s.actual.capacity()
            + s.render.capacity()
            + s.errors.capacity(),
        0
    );
    assert!(s.pending.is_none())
}
fn drain<O: ExecutionObserver>(s: &mut State, work: &mut Work<'_, '_, O>) {
    s.retire(work);
    let _ = retire_validation_errors_observed(take(&mut s.errors), work.session, work.site);
}
fn long_symbol() -> Module {
    let mut m = fixture();
    m.functions[0].name = "é🦀caller".repeat(300);
    let name = "中name".repeat(500);
    m.globals = (0..5)
        .map(|i| global(&(name.clone() + &i.to_string())))
        .collect();
    m.globals.push(global(&name));
    m.functions[0].blocks[0].body[0] = InstrNode::new(Inst::Const {
        ty: Ty::Ptr,
        value: Constant::SymbolAddr {
            symbol: name,
            addend: 0,
        },
    })
    .with_result(v(3));
    m
}
