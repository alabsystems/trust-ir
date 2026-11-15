// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Private top-level equation roots inside one actual external inventory.
//! A first successful canonical close is followed by a paid complete census;
//! no caller-supplied closed-term or reference certificate enters this cache.
use super::*;
use clean_kernel::{ExprKind, expr::ExprFolderOpt};
use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
    sync::Arc,
};

#[derive(Clone)]
struct Graph(Expr);
impl PartialEq for Graph {
    fn eq(&self, other: &Self) -> bool {
        crate::proof_assembly::normalize::same_graph(&self.0, &other.0)
    }
}
impl Eq for Graph {}
impl Hash for Graph {
    fn hash<H: Hasher>(&self, hash: &mut H) {
        crate::proof_assembly::normalize::hash_graph(&self.0, hash);
    }
}
struct Entry {
    closed: Expr,
    names: Arc<HashSet<FVarId>>,
    height: u32,
    prefix: usize,
    generation: u64,
}
pub(super) struct Census {
    names: HashSet<FVarId>,
    fvars: HashSet<FVarId>,
    height: u32,
}
pub(super) struct Memo {
    entries: HashMap<Graph, Entry>,
    retained_names: usize,
    bound: usize,
    failed: bool,
}
fn charge(work: &mut usize, limit: usize, amount: usize) -> Result<(), TermScopeError> {
    *work = work
        .checked_add(amount)
        .filter(|next| *next <= limit)
        .ok_or(TermScopeError::VisitLimit)?;
    Ok(())
}
pub(super) fn eligible(root: &Expr) -> bool {
    !root.has_loose_bvars() && matches!(root.kind(), ExprKind::Pi(..) | ExprKind::App(..))
}
impl Memo {
    pub(super) fn new(bound: usize) -> Self {
        Self {
            entries: HashMap::new(),
            retained_names: 0,
            bound,
            failed: false,
        }
    }
    pub(super) fn poison(&mut self) {
        self.failed = true;
    }
    #[cfg(test)]
    pub(super) fn len(&self) -> usize {
        self.entries.len()
    }
    pub(super) fn lookup(
        &self,
        root: &Expr,
        external: &HashSet<FVarId>,
        generations: &[u64],
        limits: TermScopeLimits,
    ) -> (Result<Option<Expr>, TermScopeError>, usize) {
        let mut work = 0;
        let result = (|| {
            if self.failed {
                return Err(TermScopeError::VisitLimit);
            }
            // Root graph pin/probe, prefix fact and complete-height check.
            charge(&mut work, limits.max_visits, 4)?;
            let Some(entry) = self.entries.get(&Graph(root.clone())) else {
                return Ok(None);
            };
            if generations.get(entry.prefix) != Some(&entry.generation) {
                return Ok(None);
            }
            // Check every retained name, including unused declarations. Do
            // not let HashSet iteration choose the failed payment prefix.
            let mut shadow = false;
            for name in entry.names.iter() {
                charge(&mut work, limits.max_visits, 1)?;
                shadow |= external.contains(name);
            }
            if shadow {
                // Canonical closing determines the actual first refusal,
                // before the following argument roots are processed.
                return Ok(None);
            }
            if entry.height > limits.max_depth {
                return Err(TermScopeError::DepthLimit);
            }
            charge(&mut work, limits.max_visits, 1)?; // returned output pin
            Ok(Some(entry.closed.clone()))
        })();
        (result, work)
    }
    pub(super) fn publish(
        &mut self,
        root: &Expr,
        closed: &Expr,
        census: Census,
        external_positions: &HashMap<FVarId, usize>,
        initial_len: usize,
        generations: &[u64],
        limit: usize,
    ) -> (Result<(), TermScopeError>, usize) {
        let mut work = 0;
        let result = (|| {
            if self.failed {
                return Err(TermScopeError::VisitLimit);
            }
            charge(&mut work, limit, 1)?;
            if census.height < 8
                || closed.has_loose_bvars()
                || self.entries.len() >= self.bound
                || census.names.len() > self.bound.saturating_sub(self.retained_names)
            {
                return Ok(());
            }
            // The successful canonical close and COMPLETE original FVar set
            // establish which inventory facts were actually read. Keep every
            // syntactic FVar, including named formals; never subtract binders.
            // All named declarations retain their independent hit-time guard.
            let mut prefix = 0;
            for id in &census.fvars {
                charge(&mut work, limit, 1)?;
                // Canonical closing has ALREADY succeeded. Missing IDs here
                // are an intersection skip (for example internal formals),
                // never a new scope-admission decision.
                if let Some(&position) = external_positions.get(id) {
                    if position >= initial_len {
                        prefix = prefix.max(position - initial_len + 1);
                    }
                }
            }
            let generation = generations
                .get(prefix)
                .copied()
                .ok_or(TermScopeError::VisitLimit)?;
            // Original/output graph pins, name-set header and map publication.
            // Census already paid each retained name's allocation/insertion.
            charge(&mut work, limit, 4)?;
            self.retained_names += census.names.len();
            self.entries.insert(
                Graph(root.clone()),
                Entry {
                    closed: closed.clone(),
                    names: Arc::new(census.names),
                    height: census.height,
                    prefix,
                    generation,
                },
            );
            Ok(())
        })();
        (result, work)
    }
}

struct Scan<'a> {
    scope: &'a TermScope,
    seen: HashMap<usize, u32>,
    names: HashSet<FVarId>,
    fvars: HashSet<FVarId>,
    work: usize,
    limits: TermScopeLimits,
    depth: u32,
    height: u32,
    error: Option<TermScopeError>,
}
pub(super) fn census(
    scope: &TermScope,
    root: &Expr,
    limits: TermScopeLimits,
) -> (Result<Census, TermScopeError>, usize) {
    let mut scan = Scan {
        scope,
        seen: HashMap::new(),
        names: HashSet::new(),
        fvars: HashSet::new(),
        work: 0,
        limits,
        depth: 0,
        height: 0,
        error: None,
    };
    scan.fold_expr_opt(root);
    let result = match scan.error {
        Some(error) => Err(error),
        None => Ok(Census {
            names: scan.names,
            fvars: scan.fvars,
            height: scan.height,
        }),
    };
    (result, scan.work)
}
impl Scan<'_> {
    fn charge(&mut self, amount: usize) -> bool {
        match charge(&mut self.work, self.limits.max_visits, amount) {
            Ok(()) => true,
            Err(error) => {
                self.error = Some(error);
                false
            }
        }
    }
}
struct Stack<'a, 'b>(&'a mut Scan<'b>);
impl ExprFolderOpt for Stack<'_, '_> {
    fn fold_expr_opt_inner(&mut self, expression: &Expr) -> Option<Expr> {
        self.0.fold_expr_opt_inner(expression)
    }
}
impl ExprFolderOpt for Scan<'_> {
    fn fold_expr_opt(&mut self, expression: &Expr) -> Option<Expr> {
        if self.error.is_some() || !self.charge(1) {
            return None;
        }
        if self.depth >= self.limits.max_depth {
            self.error = Some(TermScopeError::DepthLimit);
            return None;
        }
        match expression.kind() {
            ExprKind::FVar(id) => {
                if !self.charge(1) {
                    return None;
                }
                if !self.fvars.contains(id) {
                    if !self.charge(2) {
                        return None;
                    }
                    self.fvars.insert(*id);
                }
                self.height = self.height.max(1);
                return None;
            }
            ExprKind::BVar(_)
            | ExprKind::Sort(_)
            | ExprKind::Const(..)
            | ExprKind::Lit(_)
            | ExprKind::SProp
            | ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1 => {
                self.height = self.height.max(1);
                return None;
            }
            _ => {}
        }
        // The original immutable root pins these exact input addresses for
        // this fresh census. No address survives into another census.
        let address = expression as *const Expr as usize;
        if let Some(height) = self.seen.get(&address).copied() {
            if self
                .depth
                .checked_add(height)
                .is_none_or(|depth| depth > self.limits.max_depth)
            {
                self.error = Some(TermScopeError::DepthLimit);
            } else {
                self.height = self.height.max(height);
            }
            return None;
        }
        if let Some(name) = self.scope.component_binder_id(expression) {
            if !self.charge(1) {
                return None;
            }
            if !self.names.contains(&name) {
                if !self.charge(2) {
                    return None;
                }
                self.names.insert(name);
            }
        }
        let parent = std::mem::take(&mut self.height);
        self.depth += 1;
        Stack(self).fold_expr_opt(expression);
        self.depth -= 1;
        let Some(height) = self.height.checked_add(1) else {
            self.error = Some(TermScopeError::DepthLimit);
            return None;
        };
        self.height = parent.max(height);
        if self.error.is_none() && self.charge(1) {
            self.seen.insert(address, height);
        }
        None
    }
}
