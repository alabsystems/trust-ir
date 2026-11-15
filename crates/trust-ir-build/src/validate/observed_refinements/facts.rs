// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use lattice::{Members, Scalar, View};
mod derive;
mod propagate;
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Fact {
    Top,
    Table(PredId),
    Interval(i128, i128),
    Set(usize),
}
#[derive(Default)]
pub(super) struct Facts {
    pub(super) sets: Vec<Vec<Scalar>>,
    pub(super) pending: Vec<Scalar>,
}
impl Facts {
    pub(super) fn view<'a, O: ExecutionObserver>(
        &'a self,
        module: &'a Module,
        fact: Fact,
        work: &mut Work<'_, '_, O>,
    ) -> R<View<'a>> {
        work.admit(1, size_of::<View<'_>>())?;
        Ok(match fact {
            Fact::Top => View::Top,
            Fact::Interval(a, b) => View::Interval(a, b),
            Fact::Table(id) => {
                lattice::pred(module, id, work)?.ok_or(ObservedValueError::InvalidRange)?
            }
            Fact::Set(i) => View::Set(Members::Keys(
                work.at(&self.sets, i)?
                    .ok_or(ObservedValueError::InvalidRange)?,
            )),
        })
    }
    pub(super) fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_vec(&mut self.pending);
        while !self.sets.is_empty() {
            work.step(1);
            if let Some(mut keys) = self.sets.pop() {
                work.retire_vec(&mut keys)
            }
        }
        work.retire_vec(&mut self.sets);
    }
    pub(super) fn assumed<O: ExecutionObserver>(
        &self,
        module: &Module,
        declared: Fact,
        derived: Fact,
        work: &mut Work<'_, '_, O>,
    ) -> R<Fact> {
        let a = self.view(module, declared, work)?;
        let b = self.view(module, derived, work)?;
        if b.top() {
            return Ok(declared);
        }
        if a.top() {
            return Ok(derived);
        }
        if lattice::implies(module, b, a, 0, work)? {
            Ok(derived)
        } else {
            Ok(declared)
        }
    }
    pub(super) fn join<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        a: Fact,
        b: Fact,
        work: &mut Work<'_, '_, O>,
    ) -> R<Fact> {
        work.admit(1, size_of::<(Fact, Fact, Option<Fact>, usize)>())?;
        let pa = self.view(module, a, work)?;
        let pb = self.view(module, b, work)?;
        if lattice::equal(pa, pb, work)? {
            return Ok(a);
        }
        if lattice::implies(module, pa, pb, 0, work)? {
            return Ok(b);
        }
        if lattice::implies(module, pb, pa, 0, work)? {
            return Ok(a);
        }
        match (pa, pb) {
            (View::Interval(al, ah), View::Interval(bl, bh)) => {
                Ok(Fact::Interval(al.min(bl), ah.max(bh)))
            }
            (View::Set(_), View::Set(_)) => {
                // No table vectors are cloned. The only new payload is a canonical
                // scalar union retained in pending before each next paid move.
                if !self.pending.is_empty() {
                    return Err(ObservedValueError::InvalidRange);
                }
                for fact in [a, b] {
                    let len = match self.view(module, fact, work)? {
                        View::Set(v) => v.len(),
                        _ => return Err(ObservedValueError::InvalidRange),
                    };
                    for i in 0..len {
                        work.admit(1, 0)?;
                        let key = match self.view(module, fact, work)? {
                            View::Set(v) => v.key(i, work)?,
                            _ => None,
                        };
                        let Some(key) = key else {
                            work.retire_vec(&mut self.pending);
                            return Ok(Fact::Top);
                        };
                        let mut at = 0;
                        while at < self.pending.len() {
                            work.admit(1, 0)?;
                            if self.pending[at] >= key {
                                break;
                            }
                            at += 1;
                        }
                        if self.pending.get(at).is_some_and(|k| *k == key) {
                            continue;
                        }
                        work.reserve(&mut self.pending)?;
                        let shifted = self.pending.len() - at + 1;
                        work.admit(
                            shifted,
                            shifted
                                .checked_mul(size_of::<Scalar>())
                                .ok_or(ObservedValueError::CapacityOverflow)?,
                        )?;
                        self.pending.insert(at, key);
                        if self.pending.len() > trust_ir::pred::MAX_ENUMERATED_MEMBERS {
                            work.retire_vec(&mut self.pending);
                            return Ok(Fact::Top);
                        }
                    }
                }
                if self.pending.is_empty() {
                    return Ok(Fact::Top);
                }
                work.reserve(&mut self.sets)?;
                work.admit(1, size_of::<Vec<Scalar>>())?;
                let index = self.sets.len();
                self.sets.push(take(&mut self.pending));
                Ok(Fact::Set(index))
            }
            _ => Ok(Fact::Top),
        }
    }
}
pub(super) fn declared<O: ExecutionObserver>(
    module: &Module,
    ty: Option<&Ty>,
    work: &mut Work<'_, '_, O>,
) -> R<Fact> {
    work.admit(1, size_of::<Fact>())?;
    if let Some(id) = ty.and_then(Ty::predicate)
        && work.at(&module.predicates, id.as_usize())?.is_some()
    {
        return Ok(Fact::Table(id));
    }
    Ok(Fact::Top)
}
