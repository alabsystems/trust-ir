// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use lattice::View;
use trust_ir::ty::{EnumDef, EnumVariant, FieldDef, RecordDef, StructDef};
macro_rules! definition {
    ($name:ident,$table:ident,$id:ty,$output:ty) => {
        pub(super) fn $name<'a, O: ExecutionObserver>(
            module: &'a Module,
            id: $id,
            work: &mut Work<'_, '_, O>,
        ) -> R<Option<&'a $output>> {
            if let Some(def) = work.at(&module.$table, id.as_usize())? {
                if def.id == id {
                    return Ok(Some(def));
                }
            }
            for def in &module.$table {
                work.admit(1, 0)?;
                if def.id == id {
                    return Ok(Some(def));
                }
            }
            Ok(None)
        }
    };
}
definition!(strukt, structs, trust_ir::value::StructId, StructDef);
definition!(record, records, trust_ir::value::RecordId, RecordDef);
definition!(enumeration, enums, trust_ir::value::EnumId, EnumDef);
pub(super) fn callee<'a, O: ExecutionObserver>(
    module: &'a Module,
    id: FuncId,
    work: &mut Work<'_, '_, O>,
) -> R<Option<&'a Function>> {
    let mut first = None;
    for function in &module.functions {
        work.admit(1, 0)?;
        if function.id == id {
            if first.is_some() {
                return Ok(None);
            }
            first = Some(function)
        }
    }
    Ok(first)
}
#[derive(Clone, Copy)]
pub(super) enum Fields<'a> {
    Named(&'a [FieldDef]),
    Plain(&'a [Ty]),
    Repeated(&'a Ty, usize),
}
impl<'a> Fields<'a> {
    pub(super) fn len(self) -> usize {
        match self {
            Self::Named(v) => v.len(),
            Self::Plain(v) => v.len(),
            Self::Repeated(_, n) => n,
        }
    }
    pub(super) fn get<O: ExecutionObserver>(
        self,
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<&'a Ty>> {
        match self {
            Self::Named(v) => Ok(work.at(v, index)?.map(|f| &f.ty)),
            Self::Plain(v) => work.at(v, index),
            Self::Repeated(t, n) => {
                work.admit(1, 0)?;
                Ok((index < n).then_some(t))
            }
        }
    }
}
pub(super) fn fields<'a, O: ExecutionObserver>(
    module: &'a Module,
    ty: &'a Ty,
    work: &mut Work<'_, '_, O>,
) -> R<Option<Fields<'a>>> {
    work.admit(1, size_of::<Option<Fields<'a>>>())?;
    match ty {
        Ty::Struct(id) => Ok(strukt(module, *id, work)?.map(|d| Fields::Named(&d.fields))),
        Ty::Record(id) => Ok(record(module, *id, work)?.map(|d| Fields::Named(&d.fields))),
        Ty::Tuple(v) => Ok(Some(Fields::Plain(v))),
        _ => Ok(None),
    }
}
pub(super) fn element<'a, O: ExecutionObserver>(
    module: &'a Module,
    ty: &'a Ty,
    work: &mut Work<'_, '_, O>,
) -> R<Option<&'a Ty>> {
    work.admit(1, size_of::<Option<&Ty>>())?;
    match ty {
        Ty::Array(id, _) | Ty::Sequence(id) => work.at(&module.types, id.as_usize()),
        Ty::Vector(t, _) => Ok(Some(t.as_ref())),
        _ => Ok(None),
    }
}
fn representation<'a, O: ExecutionObserver>(
    module: &'a Module,
    ty: &'a Ty,
    work: &mut Work<'_, '_, O>,
) -> R<Option<&'a Ty>> {
    work.admit(1, 0)?;
    match ty {
        Ty::Refine(base, _) => work.at(&module.types, base.as_usize()),
        other => Ok(Some(other)),
    }
}
impl State<'_> {
    pub(super) fn consumption<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        actual: &Ty,
        required: &Ty,
        derived: Option<Fact>,
        facts: &Facts,
        sink: Sink,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(
            1,
            size_of::<(Option<PredId>, Option<PredId>, Option<Fact>)>(),
        )?;
        if !actual.is_refine() && !required.is_refine() {
            return Ok(());
        }
        let (Some(ar), Some(rr)) = (
            representation(module, actual, work)?,
            representation(module, required, work)?,
        ) else {
            self.error_location(work)?;
            work.text(
                "refinement base type reference is out of range",
                &mut self.detail,
            )?;
            return self.commit(ErrorKind::Invalid, sink, work);
        };
        if !ar.structural_eq_observed(rr, work.session, work.site)? {
            self.error_location(work)?;
            work.text("representation ", &mut self.detail)?;
            work.ty(ar, &mut self.detail)?;
            work.text(
                " does not match the required representation ",
                &mut self.detail,
            )?;
            work.ty(rr, &mut self.detail)?;
            return self.commit(ErrorKind::Invalid, sink, work);
        }
        let ap = actual.predicate();
        let rp = required.predicate();
        let declared_implies = match (ap, rp) {
            (_, None) => true,
            (None, Some(r)) => matches!(lattice::pred(module, r, work)?, Some(View::Top)),
            (Some(a), Some(b)) => {
                if a == b {
                    lattice::pred(module, a, work)?.is_some()
                } else {
                    match (
                        lattice::pred(module, a, work)?,
                        lattice::pred(module, b, work)?,
                    ) {
                        (Some(a), Some(b)) => lattice::implies(module, a, b, 0, work)?,
                        _ => false,
                    }
                }
            }
        };
        if declared_implies {
            return Ok(());
        }
        let Some(required_pred) = rp else {
            return Ok(());
        };
        let derived = match derived {
            Some(d) => {
                if facts.view(module, d, work)?.top() {
                    None
                } else {
                    Some(d)
                }
            }
            None => None,
        };
        if let Some(d) = derived
            && let Some(required) = lattice::pred(module, required_pred, work)?
            && lattice::implies(module, facts.view(module, d, work)?, required, 0, work)?
        {
            return Ok(());
        }
        self.error_location(work)?;
        match ap {
            Some(p) => work.describe_id(module, p, &mut self.actual)?,
            None => work.text(
                "top (no refinement carried — the fact was dropped)",
                &mut self.actual,
            )?,
        }
        if let Some(d) = derived {
            work.text(", and propagation derives only ", &mut self.actual)?;
            let view = facts.view(module, d, work)?;
            work.describe_view(module, view, &mut self.actual)?;
        }
        work.describe_id(module, required_pred, &mut self.required)?;
        self.commit(ErrorKind::NotImplied, sink, work)
    }
}
#[derive(Clone, Copy)]
pub(super) enum Direction {
    Read,
    Write,
}
#[derive(Clone, Copy)]
enum Lanes<'a> {
    Tag(&'a Ty),
    Variants(&'a [EnumVariant], usize),
}
impl<'a> Lanes<'a> {
    fn len(self) -> usize {
        match self {
            Self::Tag(_) => 1,
            Self::Variants(v, _) => v.len(),
        }
    }
    fn get<O: ExecutionObserver>(
        self,
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<(&'a str, &'a Ty)>> {
        match self {
            Self::Tag(t) => {
                work.admit(1, 0)?;
                Ok((index == 0).then_some(("tag", t)))
            }
            Self::Variants(v, field) => {
                let Some(v) = work.at(v, index)? else {
                    return Ok(None);
                };
                Ok(work.at(&v.fields, field)?.map(|ty| (v.name.as_str(), ty)))
            }
        }
    }
}
impl State<'_> {
    pub(super) fn enum_consumption<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        ty: &Ty,
        field: u32,
        incoming: &Ty,
        derived: Option<Fact>,
        facts: &Facts,
        direction: Direction,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Ty::Enum(id) = ty else { return Ok(()) };
        let Some(def) = enumeration(module, *id, work)? else {
            return Ok(());
        };
        work.admit(
            1,
            size_of::<Option<trust_ir::ty::EnumTagRepr>>() + size_of::<Option<Ty>>(),
        )?;
        let Some(repr) = def.canonical_tag_repr_observed(work.session, work.site)? else {
            return Ok(());
        };
        let tag = if field == 0 { Some(repr.ty()) } else { None };
        let result = (|| {
            let lanes = match &tag {
                Some(tag) => Lanes::Tag(tag),
                None => Lanes::Variants(&def.variants, (field - 1) as usize),
            };
            let mut candidates = 0usize;
            for i in 0..lanes.len() {
                work.admit(1, 0)?;
                if let Some((_, lane)) = lanes.get(i, work)? {
                    if lane.structural_eq_observed(incoming, work.session, work.site)? {
                        return Ok(());
                    }
                    if lane.is_refine() || incoming.is_refine() {
                        candidates = candidates
                            .checked_add(1)
                            .ok_or(ObservedValueError::CapacityOverflow)?;
                    }
                }
            }
            work.admit(1, size_of::<String>())?;
            let mut base = String::new();
            let result = work.text(&self.base_location, &mut base).and_then(|()| {
                for i in 0..lanes.len() {
                    work.admit(1, 0)?;
                    let Some((variant, lane)) = lanes.get(i, work)? else {
                        continue;
                    };
                    if !lane.is_refine() && !incoming.is_refine() {
                        continue;
                    }
                    work.flat(take(&mut self.base_location));
                    work.text(&base, &mut self.base_location)?;
                    if candidates != 1 {
                        work.text(" (as variant '", &mut self.base_location)?;
                        work.text(variant, &mut self.base_location)?;
                        work.text("')", &mut self.base_location)?;
                    }
                    match direction {
                        Direction::Read => self.consumption(
                            module,
                            lane,
                            incoming,
                            None,
                            facts,
                            Sink::Scratch,
                            work,
                        )?,
                        Direction::Write => self.consumption(
                            module,
                            incoming,
                            lane,
                            derived,
                            facts,
                            Sink::Scratch,
                            work,
                        )?,
                    }
                    if self.scratch.is_empty() {
                        work.errors(&mut self.refusals);
                        return Ok(());
                    }
                    work.transfer(&mut self.scratch, &mut self.refusals)?;
                }
                work.transfer(&mut self.refusals, &mut self.errors)
            });
            work.flat(base);
            result
        })();
        work.step(1);
        if let Some(tag) = tag {
            let _ = tag.retire_observed(work.session, work.site);
        }
        work.session.retirement_poll(work.site);
        result
    }
}
