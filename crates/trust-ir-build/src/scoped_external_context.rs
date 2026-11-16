// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Owned inventory with opt-in unchanged ordinary-graph materialization reuse.
use super::*;
use std::collections::{HashMap, HashSet};

#[path = "scoped_equation_roots.rs"]
mod equation_roots;

pub(crate) struct OwnedExternalContext {
    owner: LocalScopeOwner,
    ids: Vec<FVarId>,
    set: HashSet<FVarId>,
    initial_len: usize,
    reuse: Option<Box<ExternalReuse>>,
}
struct ExternalReuse {
    generations: Vec<u64>,
    next: u64,
    positions: HashMap<FVarId, usize>,
    cache: RefCell<crate::term_scope::FullScopeCache>,
    equations: RefCell<equation_roots::Memo>,
}
pub(crate) struct PreparedOrdinaryView<'a> {
    cache: std::cell::Ref<'a, crate::term_scope::FullScopeCache>,
    generations: &'a [u64],
}
impl PreparedOrdinaryView<'_> {
    pub(crate) fn envelope(
        &self,
        expression: &Expr,
    ) -> Option<crate::term_scope::CompleteFVarEnvelope> {
        self.cache.envelope(expression, self.generations)
    }
}

impl OwnedExternalContext {
    #[cfg(test)]
    pub(crate) fn equation_root_count(&self) -> usize {
        self.reuse
            .as_ref()
            .map_or(0, |reuse| reuse.equations.borrow().len())
    }
    pub(crate) fn ordinary_view_for(
        &self,
        scope: &LocalScope,
    ) -> Result<Option<PreparedOrdinaryView<'_>>, String> {
        self.ids_for(scope)?;
        Ok(self.reuse.as_ref().map(|reuse| PreparedOrdinaryView {
            cache: reuse.cache.borrow(),
            generations: &reuse.generations,
        }))
    }
    pub(crate) fn ids_for(&self, scope: &LocalScope) -> Result<&HashSet<FVarId>, String> {
        if !self.owner.matches(&scope.memo_owner()) {
            return Err("prepared external context has another scope owner".into());
        }
        Ok(&self.set)
    }
    pub(crate) fn len(&self) -> usize {
        self.ids.len()
    }
    pub(crate) fn checkpoint(&self) -> usize {
        self.ids.len()
    }
    pub(crate) fn dynamic_len(&self) -> usize {
        self.ids.len() - self.initial_len
    }
    pub(crate) fn reuses_materialization(&self) -> bool {
        self.reuse.is_some()
    }
    pub(crate) fn poison_materialization(&self) {
        if let Some(reuse) = &self.reuse {
            reuse.cache.borrow_mut().poison();
            reuse.equations.borrow_mut().poison();
        }
    }
    pub(crate) fn restore(&mut self, checkpoint: usize) -> Result<(), String> {
        if checkpoint < self.initial_len || checkpoint > self.ids.len() {
            return Err("external context restoration is not a dynamic prefix".into());
        }
        for id in self.ids.drain(checkpoint..) {
            self.set.remove(&id);
            if let Some(reuse) = &mut self.reuse {
                reuse.positions.remove(&id);
            }
        }
        if let Some(reuse) = &mut self.reuse {
            reuse
                .generations
                .truncate(checkpoint - self.initial_len + 1);
        }
        Ok(())
    }
}

impl LocalScope {
    pub(crate) fn prepare_external_context(
        &self,
        locals: &[ScopedLocal],
    ) -> Result<OwnedExternalContext, String> {
        let mut ids = Vec::with_capacity(locals.len());
        let mut set = HashSet::with_capacity(locals.len());
        for local in locals {
            if !self.owns(local) || !set.insert(local.id()) {
                return Err("foreign or duplicate prepared external handle".into());
            }
            ids.push(local.id());
        }
        Ok(OwnedExternalContext {
            owner: self.memo_owner(),
            initial_len: ids.len(),
            ids,
            set,
            reuse: None,
        })
    }

    pub(crate) fn enable_prepared_materialization_reuse(
        &self,
        context: &mut OwnedExternalContext,
    ) -> Result<(), String> {
        if !context.owner.matches(&self.memo_owner()) {
            return Err("prepared materialization reuse has another scope owner".into());
        }
        if let Some(reuse) = &context.reuse {
            return if reuse.cache.borrow().has_failed() {
                Err("prepared materialization retains a failed attempt".into())
            } else {
                Ok(())
            };
        }
        let next = u64::try_from(context.dynamic_len())
            .map_err(|_| "prepared prefix generation overflow")?;
        context.reuse = Some(Box::new(ExternalReuse {
            generations: (0..=next).collect(),
            next,
            positions: context
                .ids
                .iter()
                .copied()
                .enumerate()
                .map(|(position, id)| (id, position))
                .collect(),
            cache: RefCell::new(crate::term_scope::FullScopeCache::new(
                self.limits.closing.max_visits,
            )),
            equations: RefCell::new(equation_roots::Memo::new(self.limits.closing.max_visits)),
        }));
        Ok(())
    }

    pub(crate) fn extend_external_context(
        &self,
        context: &mut OwnedExternalContext,
        locals: &[ScopedLocal],
    ) -> Result<(), String> {
        if !context.owner.matches(&self.memo_owner()) {
            return Err("prepared external context has another scope owner".into());
        }
        let mut incoming = HashSet::with_capacity(locals.len());
        if let Some(reuse) = &context.reuse {
            reuse
                .next
                .checked_add(
                    u64::try_from(locals.len())
                        .map_err(|_| "prepared prefix generation overflow")?,
                )
                .ok_or("prepared prefix generation overflow")?;
            if reuse.cache.borrow().has_failed() {
                return Err("prepared materialization retains a failed attempt".into());
            }
        }
        for local in locals {
            if !self.owns(local)
                || context.set.contains(&local.id())
                || !incoming.insert(local.id())
            {
                return Err("foreign or duplicate external context extension".into());
            }
        }
        // Commit only after the complete extension is checked.
        let first = context.ids.len();
        context.ids.extend(locals.iter().map(ScopedLocal::id));
        context.set.extend(incoming);
        if let Some(reuse) = &mut context.reuse {
            for (offset, local) in locals.iter().enumerate() {
                reuse.next += 1;
                reuse.generations.push(reuse.next);
                reuse.positions.insert(local.id(), first + offset);
            }
        }
        Ok(())
    }

    pub(crate) fn close_prepared_external_forest_fully_with_limits(
        &self,
        expressions: &[Expr],
        context: &OwnedExternalContext,
        limits: TermScopeLimits,
    ) -> (Result<Vec<Expr>, LocalScopeError>, TermScopeStats) {
        if !context.owner.matches(&self.memo_owner()) {
            return (
                Err(LocalScopeError::UnboundFreeVariable),
                TermScopeStats::default(),
            );
        }
        let limits = TermScopeLimits {
            max_visits: limits.max_visits.min(self.limits.closing.max_visits),
            max_depth: limits.max_depth.min(self.limits.closing.max_depth),
        };
        let mut saved = context.reuse.as_ref().map(|reuse| reuse.cache.borrow_mut());
        if saved.as_ref().is_some_and(|cache| cache.has_failed()) {
            return (
                Err(LocalScopeError::Closure(
                    crate::term_scope::TermScopeError::VisitLimit,
                )),
                TermScopeStats::default(),
            );
        }
        let reuse = saved
            .as_mut()
            .map(|cache| crate::term_scope::FullScopeReuse {
                cache,
                generations: &context.reuse.as_ref().unwrap().generations,
                positions: &context.reuse.as_ref().unwrap().positions,
                initial_len: context.initial_len,
            });
        let (result, stats) = self.terms.borrow().close_prepared_external_forest_fully(
            expressions,
            &context.set,
            limits,
            reuse,
        );
        if result.is_err() {
            if let Some(cache) = saved.as_mut() {
                cache.poison();
            }
            if let Some(reuse) = &context.reuse {
                reuse.equations.borrow_mut().poison();
            }
        }
        (result.map_err(LocalScopeError::Closure), stats)
    }

    /// Only the first actual equation-statement root may reuse its successful
    /// top-level materialization. Arguments still receive fresh full closure.
    /// The canonical first close, complete name/height census and publication
    /// happen here; no caller-asserted materialization result is accepted.
    pub(crate) fn close_prepared_equation_forest_fully_with_limits(
        &self,
        expressions: &[Expr],
        context: &OwnedExternalContext,
        limits: TermScopeLimits,
    ) -> (Result<Vec<Expr>, LocalScopeError>, TermScopeStats) {
        if !context.owner.matches(&self.memo_owner()) {
            return (
                Err(LocalScopeError::UnboundFreeVariable),
                TermScopeStats::default(),
            );
        }
        let Some(root) = expressions.first() else {
            return self.close_prepared_external_forest_fully_with_limits(
                expressions,
                context,
                limits,
            );
        };
        let Some(reuse) = context
            .reuse
            .as_ref()
            .filter(|_| equation_roots::eligible(root))
        else {
            return self.close_prepared_external_forest_fully_with_limits(
                expressions,
                context,
                limits,
            );
        };
        let limits = TermScopeLimits {
            max_visits: limits.max_visits.min(self.limits.closing.max_visits),
            max_depth: limits.max_depth.min(self.limits.closing.max_depth),
        };
        let remaining = |spent: usize| TermScopeLimits {
            max_visits: limits.max_visits.saturating_sub(spent),
            max_depth: limits.max_depth,
        };
        let mut stats = TermScopeStats::default();
        let result = (|| {
            if limits.max_depth >= (1 << 31) || reuse.cache.borrow().has_failed() {
                return Err(LocalScopeError::Closure(if limits.max_depth >= (1 << 31) {
                    TermScopeError::DepthLimit
                } else {
                    TermScopeError::VisitLimit
                }));
            }
            let (hit, lookup_work) =
                reuse
                    .equations
                    .borrow()
                    .lookup(root, &context.set, &reuse.generations, limits);
            stats.visits = lookup_work;
            let hit = hit.map_err(LocalScopeError::Closure)?;
            let roots = if hit.is_some() {
                &expressions[1..]
            } else {
                expressions
            };
            let (closed, child_stats) = self.close_prepared_external_forest_fully_with_limits(
                roots,
                context,
                remaining(lookup_work),
            );
            stats = child_stats;
            stats.visits += lookup_work;
            if hit.is_some() {
                stats.memo_hits += 1;
                stats.completed_roots += 1;
            }
            let closed = closed?;
            if let Some(hit) = hit {
                // Request exactly n+1 slots, instead of relying on insert's
                // geometric growth. Prepay every slot and move plus its header
                // before allocation or publication of the assembled forest.
                let capacity = closed
                    .len()
                    .checked_add(1)
                    .ok_or(LocalScopeError::Closure(TermScopeError::VisitLimit))?;
                let rebuild = capacity
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(1))
                    .ok_or(LocalScopeError::Closure(TermScopeError::VisitLimit))?;
                if rebuild > remaining(stats.visits).max_visits {
                    return Err(LocalScopeError::Closure(TermScopeError::VisitLimit));
                }
                stats.visits += rebuild;
                let mut assembled = Vec::with_capacity(capacity);
                assembled.push(hit);
                assembled.extend(closed);
                return Ok(assembled);
            }
            // This fresh census never skips FVar-free inputs, unused names,
            // binder types or let values. Its pointers live for this root only.
            let (census, work) =
                equation_roots::census(&self.terms.borrow(), root, remaining(stats.visits));
            stats.visits += work;
            let census = census.map_err(LocalScopeError::Closure)?;
            let (published, work) = reuse.equations.borrow_mut().publish(
                root,
                &closed[0],
                census,
                &reuse.positions,
                context.initial_len,
                &reuse.generations,
                remaining(stats.visits).max_visits,
            );
            stats.visits += work;
            published.map_err(LocalScopeError::Closure)?;
            Ok(closed)
        })();
        if result.is_err() {
            context.poison_materialization();
        }
        (result, stats)
    }
}

#[cfg(test)]
mod position_tests {
    use super::*;
    fn equivalent(context: &OwnedExternalContext) {
        let reuse = context.reuse.as_ref().unwrap();
        assert_eq!(context.ids.len(), context.set.len());
        assert_eq!(context.ids.len(), reuse.positions.len());
        for (position, id) in context.ids.iter().enumerate() {
            assert!(context.set.contains(id));
            assert_eq!(reuse.positions.get(id), Some(&position));
        }
        assert_eq!(reuse.generations.len(), context.dynamic_len() + 1);
    }
    #[test]
    fn prepared_position_index_is_opt_in_atomic_and_tracks_restored_generations() {
        let mut scope = LocalScope::new();
        let a = scope.try_local(Expr::const_str("Nat")).unwrap();
        let b = scope.try_local(Expr::const_str("Nat")).unwrap();
        let c = scope.try_local(Expr::const_str("Nat")).unwrap();
        let d = scope.try_local(Expr::const_str("Nat")).unwrap();
        let mut foreign = LocalScope::new();
        let outsider = foreign.try_local(Expr::const_str("Nat")).unwrap();
        let mut context = scope
            .prepare_external_context(std::slice::from_ref(&a))
            .unwrap();
        assert!(
            context.reuse.is_none(),
            "ordinary inventories allocate no index"
        );
        scope
            .enable_prepared_materialization_reuse(&mut context)
            .unwrap();
        equivalent(&context);
        let before = context.ids.clone();
        let before_generations = context.reuse.as_ref().unwrap().generations.clone();
        let before_next = context.reuse.as_ref().unwrap().next;
        assert!(
            scope
                .extend_external_context(&mut context, &[c.clone(), outsider])
                .is_err()
        );
        assert_eq!(context.ids, before);
        assert_eq!(
            context.reuse.as_ref().unwrap().generations,
            before_generations
        );
        assert_eq!(context.reuse.as_ref().unwrap().next, before_next);
        equivalent(&context);
        assert!(scope.extend_external_context(&mut context, &[a]).is_err());
        assert_eq!(context.ids, before);
        assert_eq!(
            context.reuse.as_ref().unwrap().generations,
            before_generations
        );
        assert_eq!(context.reuse.as_ref().unwrap().next, before_next);
        equivalent(&context);
        scope
            .extend_external_context(&mut context, &[b, c])
            .unwrap();
        equivalent(&context);
        let old_generation = context.reuse.as_ref().unwrap().generations[2];
        context.restore(2).unwrap();
        equivalent(&context);
        scope.extend_external_context(&mut context, &[d]).unwrap();
        equivalent(&context);
        assert_ne!(
            context.reuse.as_ref().unwrap().generations[2],
            old_generation
        );
        let before = context.ids.clone();
        assert!(
            context.restore(0).is_err(),
            "initial facts cannot be removed"
        );
        assert_eq!(context.ids, before);
        equivalent(&context);
        assert!(
            foreign
                .enable_prepared_materialization_reuse(&mut context)
                .is_err()
        );
        equivalent(&context);
    }
}
