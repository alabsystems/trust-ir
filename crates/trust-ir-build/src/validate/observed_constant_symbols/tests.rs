// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; complete actual ordinary target_global and weak predicates.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::{FuncTyId, Global, Linkage, TlsModel, Visibility};
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
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original symbol stop");
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
    ExecutionSite::Entry(FuncId::new(3711))
}
fn global(name: &str) -> Global {
    Global {
        name: name.into(),
        ty: Ty::Bool,
        mutable: false,
        initializer: Some(Constant::Bool(false)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}
fn function(id: u32, name: &str) -> Function {
    Function::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0))
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.globals = vec![global("other"), global("target")];
    m.functions = vec![function(9, "unrelated"), function(2, "weak")];
    m.functions[1].linkage = Linkage::ExternalWeak;
    m
}
type Answer = (bool, Result<usize, PointerConstantRefusal>);
fn index(m: &Module, g: &Global) -> usize {
    m.globals
        .iter()
        .position(|row| core::ptr::eq(row, g))
        .unwrap()
}
fn expected(m: &Module, layouts: &trust_ir::LayoutTable<'_>, name: &str) -> Answer {
    (
        m.functions
            .iter()
            .any(|f| f.is_weak_declaration() && f.name == name),
        super::super::constant_values::target_global_test_oracle(layouts, name)
            .map(|g| index(m, g)),
    )
}
fn exercise<O: ExecutionObserver>(
    m: &Module,
    layouts: &trust_ir::LayoutTable<'_>,
    functions: &ModuleFunctionCatalog<'_>,
    name: &str,
    s: &mut ObservedSession<'_, O>,
) -> R<Answer> {
    let ctx = ObservedConstantSymbols::new_observed(layouts, functions, s, site())?;
    let weak = ctx.weak_symbol_observed(name, s, site())?;
    let target = ctx
        .target_global_observed(name, s, site())?
        .map(|g| index(m, g));
    ctx.retire_observed(s, site())?;
    Ok((weak, target))
}
fn run(m: &Module, name: &str) -> (Answer, Observer) {
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(m);
    let answer = expected(m, &layouts, name);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = exercise(m, &layouts, &functions, name, &mut s).unwrap();
    assert_eq!(out, answer);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (out, o)
}
