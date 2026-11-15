// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual module-aware typedconstant walk under one original emission owner.
use super::observed_constant_symbols::ObservedConstantSymbols;
use super::*;
use core::mem::{size_of, take};
use std::sync::Arc;
use trust_ir::constant::{ConstantChildren, ObservedUniformElementLists, utf8_is_valid_observed};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::ty::{EnumDef, FieldDef, RecordDef, StructDef};
use trust_ir::value::{EnumId, FuncTyId, RecordId, StructId, TyId};
use trust_ir::{FatPtrKind, LayoutError, TyLayoutShape};
mod arrays;
mod bytes;
mod diagnostics;
mod enums;
mod lookup;
mod node;
mod nominals;
mod pointers;
mod storage;
#[cfg(test)]
mod tests;
mod tree;
mod weak;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
enum PathElement<'a> {
    Index(usize),
    Field(&'a str),
}
#[derive(Clone, Copy)]
enum ChildTypes<'a> {
    Repeated(&'a Ty),
    Positional(&'a [Ty]),
    Fields(&'a [FieldDef]),
}
struct Children<'a> {
    constants: ConstantChildren<'a>,
    types: ChildTypes<'a>,
    names: Option<&'a [(String, Constant)]>,
    index: usize,
    indexed: bool,
}
#[derive(Clone, Copy)]
struct Item<'a> {
    constant: &'a Constant,
    ty: &'a Ty,
    path: Option<PathElement<'a>>,
    wrong_name: Option<(&'a str, &'a str, usize)>,
}
struct State<'a> {
    base: &'a str,
    root: &'a Constant,
    current: Option<Item<'a>>,
    children: Option<Children<'a>>,
    pending: Vec<(Children<'a>, usize)>,
    path: Vec<PathElement<'a>>,
    uniform: Option<ObservedUniformElementLists<'a>>,
    discriminants: Option<Vec<i128>>,
    layout: Option<Arc<TyLayoutShape>>,
    layout_error: Option<LayoutError>,
    reason: Option<PointerConstantRefusal>,
    location: String,
    expected: String,
    actual: String,
    render: String,
    spelling: String,
    symbol: String,
    tytext: String,
    enum_name: String,
    variant_name: String,
    errors: Vec<ValidationError>,
}
impl<'a> State<'a> {
    fn new(root: &'a Constant, ty: &'a Ty, base: &'a str) -> Self {
        Self {
            base,
            root,
            current: Some(Item {
                constant: root,
                ty,
                path: None,
                wrong_name: None,
            }),
            children: None,
            pending: Vec::new(),
            path: Vec::new(),
            uniform: None,
            discriminants: None,
            layout: None,
            layout_error: None,
            reason: None,
            location: String::new(),
            expected: String::new(),
            actual: String::new(),
            render: String::new(),
            spelling: String::new(),
            symbol: String::new(),
            tytext: String::new(),
            enum_name: String::new(),
            variant_name: String::new(),
            errors: Vec::new(),
        }
    }
}
/// Exact original per-constant diagnostic order and one actual source-bound
/// symbol/layout/catalog context. Input/source/type/initializer/proof authority
/// is not established here; all other original module rules remain mandatory.
/// Same original session/site/fuel, no new owner/grant/deadline/accepting skip.
/// Complete child inventories, diagnostic paths, uniform classes, payloads and
/// pending child results remain owned until transfer or full observed cleanup.
/// Exact module-aware structural equality is an authored source dependency,
/// not raw type-ID equality or a candidate callback. Full independent/compiler/
/// native qualification and physical runtime/allocator/hard-time/caller disposal
/// remain OPEN.
pub(super) fn validate_constant_against_ty_observed<'a, 'm: 'a, O: ExecutionObserver>(
    symbols: &ObservedConstantSymbols<'_, 'm>,
    constant: &'a Constant,
    ty: &'a Ty,
    base: &'a str,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State<'a>>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::new(constant, ty, base);
    let result = state.run(symbols, &mut work);
    state.retire(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(e) => {
            let _ =
                retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
            Err(work.terminal(e))
        }
    }
}
impl State<'_> {
    fn retire_discriminants<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<Vec<i128>>>().saturating_add(1));
        if let Some(rows) = self.discriminants.take() {
            work.rows(rows)
        }
        work.poll();
    }
    fn retire_layout<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<Arc<TyLayoutShape>>>().saturating_add(1));
        if let Some(row) = self.layout.take() {
            let _ = row.retire_arc_observed(work.session, work.site);
        }
        work.poll();
        work.step(size_of::<Option<LayoutError>>().saturating_add(1));
        if let Some(e) = self.layout_error.take() {
            let _ = e.retire_observed(work.session, work.site);
        }
        work.poll();
    }
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.fixed(self.current.take());
        work.fixed(self.children.take());
        loop {
            work.step(size_of::<Option<(Children<'_>, usize)>>().saturating_add(1));
            let Some(row) = self.pending.pop() else { break };
            work.fixed(row)
        }
        work.fixed(take(&mut self.pending));
        work.rows(take(&mut self.path));
        self.retire_discriminants(work);
        self.retire_layout(work);
        work.step(
            size_of::<Option<PointerConstantRefusal>>()
                .saturating_add(size_of::<ValidationError>())
                .saturating_add(1),
        );
        if let Some(reason) = self.reason.take() {
            let _ = retire_validation_error_observed(
                ValidationError::PointerConstantRefused {
                    location: String::new(),
                    symbol: String::new(),
                    ty: String::new(),
                    reason,
                },
                work.session,
                work.site,
            );
        }
        work.step(size_of::<Option<ObservedUniformElementLists<'_>>>().saturating_add(1));
        if let Some(uniform) = self.uniform.take() {
            let _ = uniform.retire_observed(work.session, work.site);
        }
        work.flat(take(&mut self.location));
        work.flat(take(&mut self.expected));
        work.flat(take(&mut self.actual));
        work.flat(take(&mut self.render));
        work.flat(take(&mut self.spelling));
        work.flat(take(&mut self.symbol));
        work.flat(take(&mut self.tytext));
        work.flat(take(&mut self.enum_name));
        work.flat(take(&mut self.variant_name));
    }
}
