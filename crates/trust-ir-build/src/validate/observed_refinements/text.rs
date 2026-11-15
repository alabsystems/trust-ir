// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use lattice::{Members, View};
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn universe(&mut self, u: &Universe, out: &mut String) -> R {
        self.admit(1, 0)?;
        match u {
            Universe::IntRange { lo, hi } => {
                self.signed(*lo, out)?;
                self.text("..=", out)?;
                self.signed(*hi, out)
            }
            Universe::Members(items) => {
                self.text("{", out)?;
                for (i, c) in items.iter().enumerate() {
                    self.admit(1, 0)?;
                    if i > 0 {
                        self.text(", ", out)?
                    }
                    self.constant(c, out)?;
                }
                self.text("}", out)
            }
        }
    }
    pub(super) fn pred_view(&mut self, p: View<'_>, out: &mut String) -> R {
        self.admit(1, size_of::<View<'_>>())?;
        match p {
            View::Interval(lo, hi) => {
                self.text("in[", out)?;
                self.signed(lo, out)?;
                self.text(", ", out)?;
                self.signed(hi, out)?;
                self.text("]", out)
            }
            View::Set(v) => {
                self.text("in{", out)?;
                for i in 0..v.len() {
                    self.admit(1, 0)?;
                    if i > 0 {
                        self.text(", ", out)?
                    }
                    match v {
                        Members::Constants(v) => self.constant(&v[i], out)?,
                        Members::Keys(v) => match v[i] {
                            (0, n) => self.signed(n, out)?,
                            (1, 0) => self.text("false", out)?,
                            (1, 1) => self.text("true", out)?,
                            _ => return Err(ObservedValueError::InvalidRange),
                        },
                    }
                }
                self.text("}", out)
            }
            View::Universe(u, s) => {
                self.text("in_universe(univ.", out)?;
                self.number(u.index() as u128, out)?;
                self.text(", ", out)?;
                self.text(
                    match s {
                        Space::Index => "index",
                        Space::Member => "member",
                    },
                    out,
                )?;
                self.text(")", out)
            }
            View::Conj(v) | View::Disj(v) => {
                self.text(
                    if matches!(p, View::Conj(_)) {
                        "and("
                    } else {
                        "or("
                    },
                    out,
                )?;
                for (i, c) in v.iter().enumerate() {
                    self.admit(1, 0)?;
                    if i > 0 {
                        self.text(", ", out)?
                    }
                    self.text("pred.", out)?;
                    self.number(c.index() as u128, out)?;
                }
                self.text(")", out)
            }
            View::NonZero => self.text("nonzero", out),
            View::NonNull => self.text("nonnull", out),
            View::Top => self.text("top", out),
            View::Bottom => self.text("bottom", out),
        }
    }
    fn universe_detail(&mut self, module: &Module, p: View<'_>, out: &mut String) -> R {
        if let View::Universe(u, s) = p {
            match lattice::universe(module, u, self)? {
                Some(univ) => match s {
                    Space::Index => {
                        self.text(" = 0-based index into ", out)?;
                        self.universe(univ, out)?;
                        self.text(" (|U| = ", out)?;
                        match lattice::cardinality(univ, self)? {
                            Some(n) => self.number(n, out)?,
                            None => self.text("?", out)?,
                        }
                        self.text(")", out)?;
                    }
                    Space::Member => {
                        self.text(" = member of ", out)?;
                        self.universe(univ, out)?;
                    }
                },
                None => self.text(" = OVER A DANGLING UNIVERSE", out)?,
            }
        }
        Ok(())
    }
    pub(super) fn describe_view(&mut self, module: &Module, p: View<'_>, out: &mut String) -> R {
        self.pred_view(p, out)?;
        self.universe_detail(module, p, out)
    }
    pub(super) fn describe_id(&mut self, module: &Module, id: PredId, out: &mut String) -> R {
        self.text("pred.", out)?;
        self.number(id.index() as u128, out)?;
        let Some(p) = lattice::pred(module, id, self)? else {
            return self.text(" (DANGLING)", out);
        };
        self.text(" (", out)?;
        self.pred_view(p, out)?;
        self.universe_detail(module, p, out)?;
        if let View::Conj(children) | View::Disj(children) = p {
            self.text(" = [", out)?;
            for (i, c) in children.iter().enumerate() {
                self.admit(1, 0)?;
                if i > 0 {
                    self.text(", ", out)?
                }
                match lattice::pred(module, *c, self)? {
                    Some(child) => self.pred_view(child, out)?,
                    None => {
                        self.text("pred.", out)?;
                        self.number(c.index() as u128, out)?;
                        self.text(" DANGLING", out)?
                    }
                }
            }
            self.text("]", out)?;
        }
        self.text(")", out)
    }
}
impl State<'_> {
    pub(super) fn base<O: ExecutionObserver>(
        &mut self,
        function: &str,
        block: Option<u32>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.flat(take(&mut self.base_location));
        work.text("function '", &mut self.base_location)?;
        work.text(function, &mut self.base_location)?;
        work.text("'", &mut self.base_location)?;
        if let Some(block) = block {
            work.text(" bb", &mut self.base_location)?;
            work.number(block as u128, &mut self.base_location)?;
        }
        Ok(())
    }
    pub(super) fn error_location<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        self.clear_location(work);
        work.text(&self.base_location, &mut self.location)
    }
}
