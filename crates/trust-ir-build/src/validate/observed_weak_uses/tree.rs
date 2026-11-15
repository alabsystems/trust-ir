// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'m> Frame<'m> {
    fn new<O: ExecutionObserver>(constant: &'m Constant, work: &mut Work<'_, '_, O>) -> R<Self> {
        work.admit(64, size_of::<Self>())?;
        let children = match constant {
            Constant::Aggregate(v)
            | Constant::Array(v)
            | Constant::Vector(v)
            | Constant::Sequence(v)
            | Constant::Set(v) => Children::Values(v),
            Constant::Record(v) => Children::Fields(v),
            Constant::Closure { captures, .. } => Children::Values(captures),
            Constant::Splat { elem, .. } => Children::One(Some(elem)),
            Constant::Int(_)
            | Constant::U128(_)
            | Constant::Bytes { .. }
            | Constant::Float(_)
            | Constant::Bool(_)
            | Constant::FnDef(_)
            | Constant::SymbolAddr { .. }
            | Constant::PhantomData
            | Constant::Uninit
            | Constant::TensorBlob { .. } => Children::None,
            Constant::Ext(e) => e.unreachable(),
        };
        let remaining = match children {
            Children::Values(v) => v.len(),
            Children::Fields(v) => v.len(),
            Children::One(v) => usize::from(v.is_some()),
            Children::None => 0,
        };
        Ok(Self {
            children,
            remaining,
        })
    }
    fn next<O: ExecutionObserver>(
        &mut self,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<&'m Constant>> {
        work.admit(8, size_of::<Option<&Constant>>() + size_of::<usize>())?;
        if self.remaining == 0 {
            return Ok(None);
        }
        self.remaining = self
            .remaining
            .checked_sub(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        Ok(Some(match self.children {
            Children::Values(v) => work
                .at(v, self.remaining)?
                .ok_or(ObservedValueError::InvalidRange)?,
            Children::Fields(v) => {
                &work
                    .at(v, self.remaining)?
                    .ok_or(ObservedValueError::InvalidRange)?
                    .1
            }
            Children::One(v) => v.ok_or(ObservedValueError::InvalidRange)?,
            Children::None => return Err(ObservedValueError::InvalidRange),
        }))
    }
}
impl<'m> State<'m> {
    pub(super) fn switch_tree<O: ExecutionObserver>(
        &mut self,
        catalog: &ModuleFunctionCatalog<'m>,
        root: &'m Constant,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Option<&Constant>>())?;
        self.current = Some(root);
        loop {
            work.admit(1, size_of::<Option<&Constant>>())?;
            let constant = self.current.ok_or(ObservedValueError::InvalidRange)?;
            self.switch_row(catalog, constant, work)?;
            let frame = Frame::new(constant, work)?;
            if frame.remaining != 0 {
                work.reserve(&mut self.frames)?;
                work.admit(1, size_of::<Frame<'m>>())?;
                self.frames.push(frame);
            }
            loop {
                work.admit(1, size_of::<Option<&mut Frame<'m>>>())?;
                let Some(frame) = self.frames.last_mut() else {
                    return Ok(());
                };
                if let Some(next) = frame.next(work)? {
                    self.current = Some(next);
                    break;
                }
                work.admit(1, size_of::<Option<Frame<'m>>>())?;
                work.fixed(self.frames.pop());
            }
        }
    }
    fn switch_row<O: ExecutionObserver>(
        &mut self,
        catalog: &ModuleFunctionCatalog<'m>,
        constant: &Constant,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(64, size_of::<Option<&Function>>())?;
        match constant {
            Constant::FnDef(id) | Constant::Closure { func: id, .. } => {
                if let Some(f) = catalog.unique_observed(*id, work.session, work.site)? {
                    work.admit(8, size_of::<bool>())?;
                    if f.is_weak_declaration() {
                        work.text(&self.location, &mut self.here)?;
                        work.text(&f.name, &mut self.name)?;
                        work.reserve(&mut self.errors)?;
                        work.admit(1, size_of::<ValidationError>() + 2 * size_of::<String>())?;
                        self.errors.push(ValidationError::WeakDeclarationAsFnDef {
                            location: take(&mut self.here),
                            function: id.index(),
                            name: take(&mut self.name),
                        });
                    }
                }
            }
            Constant::SymbolAddr { symbol, .. }
                if queries::last(catalog.source_module(), symbol, work)?.is_some() =>
            {
                work.text(&self.location, &mut self.here)?;
                work.text(symbol, &mut self.symbol)?;
                work.text(
                    "a switch case value (compare it with `icmp` against a ptr instead)",
                    &mut self.detail,
                )?;
                work.reserve(&mut self.errors)?;
                work.admit(1, size_of::<ValidationError>() + 3 * size_of::<String>())?;
                self.errors
                    .push(ValidationError::WeakDeclarationAddressNotNullable {
                        location: take(&mut self.here),
                        symbol: take(&mut self.symbol),
                        detail: take(&mut self.detail),
                    });
            }
            _ => {}
        }
        Ok(())
    }
}
