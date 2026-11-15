// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Twenty-four authored UNRUN controls; ordinary T1–T7 is the exact oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::{InstructionSite, InterpretOptions};
use trust_ir::value::{BlockId, FuncId, FuncTyId, PredId, StructId, TyId};
use trust_ir::{Block, CallingConv, DropGlueEntry, Linkage};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    cleanup_after: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original glue-table stop");
        }
        if self.cleanup_after.is_some_and(|at| self.events.len() > at)
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
    ExecutionSite::Entry(FuncId::new(401))
}
fn function(id: u32, name: &str, body: bool) -> Function {
    let mut f = Function::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0));
    if body {
        f.blocks.push(Block::new(BlockId::new(0)));
    }
    f
}
fn module() -> Module {
    let mut m = Module::new("T1-T7");
    m.func_types
        .push(FuncTy::unrecorded(vec![Ty::Ptr], vec![], false));
    m
}
fn add(m: &mut Module, id: u32, ty: Ty) {
    m.drop_glue.push(DropGlueEntry {
        glue: FuncId::new(id),
        ty,
    });
}
fn valid() -> Module {
    let mut m = module();
    m.functions.push(function(7, "glueλ\0", true));
    add(&mut m, 7, Ty::Struct(StructId::new(3)));
    m
}
fn multi() -> Module {
    let mut m = module();
    m.func_types
        .push(FuncTy::unrecorded(vec![], vec![Ty::Unit], true));
    m.functions.push(function(9, "first", true));
    let mut f = function(7, TRUSTED_RC_RUNTIMES[0].entry_points[0].symbol, false);
    f.ty = FuncTyId::new(1);
    f.linkage = Linkage::ExternalWeak;
    m.functions.push(f);
    add(&mut m, 9, Ty::Unit);
    add(&mut m, 7, Ty::Unit);
    m
}
fn error(entry: usize, glue: u32, reason: &str) -> ValidationError {
    ValidationError::InvalidDropGlue {
        entry,
        glue,
        reason: reason.into(),
    }
}
fn prior() -> ValidationError {
    error(12, 13, "already owned reason λ\0FULLTAIL")
}
fn seeded() -> State {
    State {
        errors: vec![prior()],
        ..State::default()
    }
}
fn key_text(ty: &Ty, refined: bool) -> String {
    if refined {
        format!(
            "the key {ty} is a refinement: a refinement has its base's representation, so its drop is spelled at the base"
        )
    } else {
        format!(
            "the key {ty} is trivially droppable: a drop that does nothing is spelled by absence, so it has no glue"
        )
    }
}
fn duplicate_text(ty: &Ty) -> String {
    format!("a second row for type {ty}: one row per type")
}
fn order_text(glue: u32, previous: u32) -> String {
    format!(
        "rows are strictly ascending by glue, and @func.{glue} does not follow @func.{previous} (one glue would destroy two types)"
    )
}
fn signature_text(f: &Function, s: &FuncTy) -> String {
    format!(
        "the glue '{}' has signature {}; drop glue is exactly (ptr) -> () and not variadic",
        f.name,
        super::super::format_func_ty(s)
    )
}
fn weak_text(name: &str) -> String {
    format!("the glue '{name}' is a weak declaration: its address may be null (F-058)")
}
fn pinned_text(name: &str) -> String {
    format!(
        "the glue '{name}' is a pinned runtime entry: a runtime entry takes a cell or a handle, while drop glue takes a place"
    )
}
fn oracle(m: &Module) -> Vec<ValidationError> {
    let catalog = ModuleFunctionCatalog::new(m);
    super::super::validate_drop_glue_table(m, &catalog)
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize) {
    let expected = oracle(m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_drop_glue_table_observed(m, &mut s, site()).unwrap();
    assert_eq!(out, expected);
    let copy = out.clone();
    let bound = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events[bound - 1].phase, ExecutionPhase::Publication);
    (copy, o, bound)
}
fn empty(state: &State) -> bool {
    state.ty.capacity() == 0 && state.reason.capacity() == 0 && state.errors.capacity() == 0
}
