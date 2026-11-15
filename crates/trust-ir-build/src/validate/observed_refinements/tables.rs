// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[derive(Clone, Copy)]
enum Interned {
    Universe,
    Predicate,
}
impl State<'_> {
    fn table_location<O: ExecutionObserver>(
        &mut self,
        kind: &str,
        id: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.clear_location(work);
        work.text(kind, &mut self.location)?;
        work.text(".", &mut self.location)?;
        work.number(id as u128, &mut self.location)
    }
    fn members_defect<O: ExecutionObserver>(
        &mut self,
        items: &[Constant],
        what: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.flat(take(&mut self.detail));
        work.admit(1, size_of::<Option<lattice::Scalar>>())?;
        if items.is_empty() {
            work.text(what, &mut self.detail)?;
            work.text(" extension is empty; an empty extension is `bottom`, which must be spelled explicitly rather than implied",&mut self.detail)?;
            return Ok(true);
        }
        if items.len() > trust_ir::pred::MAX_ENUMERATED_MEMBERS {
            work.text(what, &mut self.detail)?;
            work.text(" extension has ", &mut self.detail)?;
            work.number(items.len() as u128, &mut self.detail)?;
            work.text(" members, over the ", &mut self.detail)?;
            work.number(
                trust_ir::pred::MAX_ENUMERATED_MEMBERS as u128,
                &mut self.detail,
            )?;
            work.text(" cap — a decidable lattice must stay decidable in microseconds; spell a contiguous range as an interval instead",&mut self.detail)?;
            return Ok(true);
        }
        let mut previous = None;
        for (i, c) in items.iter().enumerate() {
            work.admit(1, 0)?;
            let key = trust_ir::pred::constant_key(c);
            if key.is_none() || previous.is_some_and(|p| key.is_some_and(|k| k <= p)) {
                work.text(what, &mut self.detail)?;
                work.text(
                    if key.is_none() {
                        " extension element "
                    } else {
                        " extension is not in canonical order at element "
                    },
                    &mut self.detail,
                )?;
                work.number(i as u128, &mut self.detail)?;
                work.text(" (", &mut self.detail)?;
                work.constant(c, &mut self.detail)?;
                work.text(if key.is_none(){") is not a scalar with a total order; only integer and bool constants may appear (floats have no total order at NaN)"}else{"): entries must be strictly ascending and duplicate-free, or two equal extensions would intern to two different ids"},&mut self.detail)?;
                return Ok(true);
            }
            previous = key;
        }
        Ok(false)
    }
    fn intern<O: ExecutionObserver>(
        &mut self,
        kind: Interned,
        id: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let rows = if matches!(kind, Interned::Universe) {
            &mut self.seen_universes
        } else {
            &mut self.seen_preds
        };
        let mut first = None;
        for (text, old) in rows.iter() {
            work.admit(1, 0)?;
            if work.eq_bytes(text.as_bytes(), self.key.as_bytes())? {
                first = Some(*old);
                break;
            }
        }
        if let Some(first) = first {
            self.commit(
                ErrorKind::Duplicate(
                    match kind {
                        Interned::Universe => "universe",
                        Interned::Predicate => "predicate",
                    },
                    first,
                    id,
                ),
                Sink::Main,
                work,
            )
        } else {
            work.reserve(rows)?;
            work.admit(1, size_of::<(String, u32)>())?;
            rows.push((take(&mut self.key), id));
            Ok(())
        }
    }
    pub(super) fn tables<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for (i, u) in module.universes.iter().enumerate() {
            work.admit(1, 0)?;
            let id = work.index(i)?;
            let malformed = match u {
                Universe::IntRange { lo, hi } => {
                    if lo > hi {
                        work.text("inverted integer range: lo ", &mut self.detail)?;
                        work.signed(*lo, &mut self.detail)?;
                        work.text(" > hi ", &mut self.detail)?;
                        work.signed(*hi, &mut self.detail)?;
                        true
                    } else {
                        false
                    }
                }
                Universe::Members(v) => self.members_defect(v, "universe", work)?,
            };
            if malformed {
                self.table_location("univ", id, work)?;
                self.commit(ErrorKind::Malformed, Sink::Main, work)?;
                continue;
            }
            work.universe(u, &mut self.key)?;
            self.intern(Interned::Universe, id, work)?;
        }
        for (i, p) in module.predicates.iter().enumerate() {
            work.admit(1, 0)?;
            let id = work.index(i)?;
            self.table_location("pred", id, work)?;
            let mut malformed = false;
            match p {
                Pred::Interval { lo, hi } => {
                    if lo > hi {
                        work.text("inverted interval: lo ", &mut self.detail)?;
                        work.signed(*lo, &mut self.detail)?;
                        work.text(" > hi ", &mut self.detail)?;
                        work.signed(*hi, &mut self.detail)?;
                    }
                }
                Pred::FiniteSet(v) => {
                    self.members_defect(v, "finite-set", work)?;
                }
                Pred::InUniverse(u, _) => {
                    if u.as_usize() >= module.universes.len() {
                        self.commit(ErrorKind::Dangling("univ", u.index()), Sink::Main, work)?;
                        malformed = true;
                    }
                }
                Pred::Conj(children) | Pred::Disj(children) => {
                    if children.len() < 2 {
                        work.text("connective has ", &mut self.detail)?;
                        work.number(children.len() as u128, &mut self.detail)?;
                        work.text(" operand(s); a 0- or 1-operand connective has a shorter canonical spelling (`top` / the operand itself) and would break interning",&mut self.detail)?;
                    } else if children.len() > trust_ir::pred::MAX_CONNECTIVE_ARITY {
                        work.text("connective has ", &mut self.detail)?;
                        work.number(children.len() as u128, &mut self.detail)?;
                        work.text(" operands, over the ", &mut self.detail)?;
                        work.number(
                            trust_ir::pred::MAX_CONNECTIVE_ARITY as u128,
                            &mut self.detail,
                        )?;
                        work.text(" cap", &mut self.detail)?;
                    } else {
                        for pair in children.windows(2) {
                            work.admit(1, 0)?;
                            if pair[0] >= pair[1] {
                                work.text("connective operands are not strictly ascending; unsorted or duplicated operands would let two equal predicates intern to two different ids",&mut self.detail)?;
                                break;
                            }
                        }
                    }
                    // The original defect remains pending through all child errors.
                    work.admit(1, size_of::<String>())?;
                    let mut defect = take(&mut self.detail);
                    let result: R = (|| {
                        for child in children {
                            work.admit(1, 0)?;
                            if child.as_usize() >= module.predicates.len() {
                                self.table_location("pred", id, work)?;
                                self.commit(
                                    ErrorKind::Dangling("pred", child.index()),
                                    Sink::Main,
                                    work,
                                )?;
                                malformed = true;
                            } else if child.index() >= id {
                                self.table_location("pred", id, work)?;
                                work.text("operand pred.", &mut self.detail)?;
                                work.number(child.index() as u128, &mut self.detail)?;
                                work.text(" is not strictly older than pred.", &mut self.detail)?;
                                work.number(id as u128, &mut self.detail)?;
                                work.text(
                                    "; the predicate graph must be acyclic by construction",
                                    &mut self.detail,
                                )?;
                                self.commit(ErrorKind::Malformed, Sink::Main, work)?;
                                malformed = true;
                            }
                        }
                        Ok(())
                    })();
                    work.flat(take(&mut self.detail));
                    self.detail = take(&mut defect);
                    work.flat(defect);
                    result?;
                }
                _ => {}
            }
            if !self.detail.is_empty() {
                self.table_location("pred", id, work)?;
                self.commit(ErrorKind::Malformed, Sink::Main, work)?;
                malformed = true;
            }
            if malformed {
                continue;
            }
            work.pred_view(lattice::View::node(p), &mut self.key)?;
            self.intern(Interned::Predicate, id, work)?;
        }
        Ok(())
    }
}
