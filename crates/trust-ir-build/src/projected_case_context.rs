// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Checked case-context candidates preserve shared state/outcome correlations.
//! No branch equation, invariant, provider fidelity or converse is assumed.
use super::*;
use clean_kernel::expr::ExprFolderOpt;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    hash::{Hash, Hasher},
};

#[derive(Clone)]
struct Key(Expr);
#[path = "projected_case_support.rs"]
mod support;
pub(super) use support::CaseSupportCache;
impl PartialEq for Key {
    fn eq(&self, other: &Self) -> bool {
        crate::proof_assembly::normalize::same_graph(&self.0, &other.0)
    }
}
impl Eq for Key {}
impl Hash for Key {
    fn hash<H: Hasher>(&self, state: &mut H) {
        crate::proof_assembly::normalize::hash_graph(&self.0, state);
    }
}
struct Case {
    term: Expr,
    name: String,
    levels: Vec<Level>,
    args: Vec<Expr>,
    params: usize,
    fields: Vec<Vec<Expr>>,
    theorem: &'static str,
    result: Expr,
}
fn case(term: &Expr, checker: &TypeChecker<'_>) -> Option<Case> {
    let ExprKind::Const(name, levels) = term.get_app_fn().kind() else {
        return None;
    };
    let args = term
        .get_app_args()
        .iter()
        .map(|e| (*e).clone())
        .collect::<Vec<_>>();
    let name = name.to_string();
    let (params, fields, theorem) = match name.as_str() {
        "Prod.rec" if args.len() == 5 && levels.len() == 3 => (
            2,
            vec![vec![args[0].clone(), args[1].clone()]],
            CASE_MAP_PROD,
        ),
        "Except.rec" if args.len() == 6 && levels.len() == 3 => (
            2,
            vec![vec![args[0].clone()], vec![args[1].clone()]],
            CASE_MAP_EXCEPT,
        ),
        "Option.rec" if args.len() == 5 && levels.len() == 2 => {
            (1, vec![vec![], vec![args[0].clone()]], CASE_MAP_OPTION)
        }
        "Bool.rec" if args.len() == 4 && levels.len() == 1 => {
            (0, vec![vec![], vec![]], CASE_MAP_BOOL)
        }
        _ => return None,
    };
    let motive = checker.whnf(&args[params]);
    let ExprKind::Lam(_, _, body) = motive.kind() else {
        return None;
    };
    // Existing case-map contracts are nondependent. A loose motive variable
    // would require a different checked contract, not an erased dependency.
    if body.has_loose_bvars() || term.has_loose_bvars() {
        return None;
    }
    Some(Case {
        term: term.clone(),
        name,
        levels: levels.to_vec(),
        args,
        params,
        fields,
        theorem,
        result: body.as_ref().clone(),
    })
}
struct Search<'a, 'e> {
    checker: &'a TypeChecker<'e>,
    work: &'a mut usize,
    limit: usize,
    depth: usize,
    max_depth: usize,
    first: bool,
    seen: HashSet<Key>,
    found: Option<Case>,
    error: Option<&'static str>,
    scope: &'a crate::scoped_local::LocalScope,
    support: &'a mut CaseSupportCache,
    support_limit: usize,
    support_visits: &'a mut usize,
    support_hits: &'a mut usize,
    visits: usize,
}
struct SearchStack<'a, 'b, 'e>(&'a mut Search<'b, 'e>);
impl ExprFolderOpt for SearchStack<'_, '_, '_> {
    fn fold_expr_opt_inner(&mut self, e: &Expr) -> Option<Expr> {
        self.0.fold_expr_opt_inner(e)
    }
}
impl ExprFolderOpt for Search<'_, '_> {
    fn fold_expr_opt(&mut self, e: &Expr) -> Option<Expr> {
        if self.found.is_some() || self.error.is_some() {
            return None;
        }
        if *self.work >= self.limit {
            self.error = Some("projected case-context search work limit");
            return None;
        }
        if self.depth > self.max_depth {
            self.error = Some("projected case-context search depth limit");
            return None;
        }
        *self.work += 1;
        self.visits += 1;
        if !self.seen.insert(Key(e.clone())) {
            return None;
        }
        let root = std::mem::replace(&mut self.first, false);
        // Prefer the computed observation below its field projections. Picking
        // only a projected outcome would discard its correlation with state.
        if matches!(e.kind(), ExprKind::Lam(..) | ExprKind::Pi(..)) {
            return None;
        }
        match self.support.summary(
            self.checker,
            self.scope,
            e,
            self.work,
            self.limit,
            self.max_depth.saturating_sub(self.depth),
            self.support_limit,
            self.support_visits,
        ) {
            Ok(Some(summary))
                if summary.cases == 0
                    && self
                        .depth
                        .checked_add(summary.search_height)
                        .is_some_and(|end| end <= self.max_depth) =>
            {
                *self.support_hits += 1;
                return None;
            }
            Err(error) => {
                self.error = Some(error);
                return None;
            }
            _ => {}
        }
        // A demanded node's exposed case precedes its cold raw arguments.
        // Descending first can select an unrelated case inside the complete
        // State which the surrounding projection will discard after this one.
        if !root && !e.has_loose_bvars() {
            let normalized = self.checker.whnf(e);
            if let Some(found) = case(&normalized, self.checker) {
                self.found = Some(found);
                return None;
            }
        }
        self.depth += 1;
        let _unchanged = SearchStack(self).fold_expr_opt(e);
        self.depth -= 1;
        None
    }
    fn fold_binder_body_opt(&mut self, _e: &Expr) -> Option<Expr> {
        None
    }
}
struct Replace<'a, 'e> {
    checker: &'a TypeChecker<'e>,
    target: &'a Expr,
    proper: &'a HashSet<Key>,
    hole: &'a Expr,
    work: &'a mut usize,
    limit: usize,
    depth: usize,
    max_depth: usize,
    memo: HashMap<Key, Option<Expr>>,
    changed: bool,
    error: Option<&'static str>,
    scope: &'a crate::scoped_local::LocalScope,
    support: &'a mut CaseSupportCache,
    support_limit: usize,
    support_visits: &'a mut usize,
    support_hits: &'a mut usize,
    visits: usize,
    allowed: &'a [ScopedLocal],
    materialized_cache: &'a mut crate::scoped_local::materialized::MaterializedCache,
    validation_context:
        Option<crate::scoped_local::materialized::MaterializedValidationContext<'a>>,
    validation_mode: MaterializedValidationMode,
    comparison_visits: &'a mut usize,
    comparisons: &'a mut usize,
    comparison_matches: &'a mut usize,
    reduction_visits: &'a mut usize,
    reductions: &'a mut usize,
}
// Administrative beta/let/projection reductions can expose the demanded case
// without walking their discarded data. Numeric computation is not a search
// shortcut: ordinary cold data keeps the existing raw depth boundary.
fn administrative_redex(e: &Expr) -> bool {
    match e.kind() {
        ExprKind::Let(..) | ExprKind::Proj(..) => true,
        ExprKind::App(..) => match e.get_app_fn().kind() {
            ExprKind::Lam(..) => true,
            ExprKind::Const(name, _) => {
                matches!(name.to_string().as_str(), "Prod.fst" | "Prod.snd")
            }
            _ => false,
        },
        _ => false,
    }
}
struct ReplaceStack<'a, 'b, 'e>(&'a mut Replace<'b, 'e>);
impl ExprFolderOpt for ReplaceStack<'_, '_, '_> {
    fn fold_expr_opt_inner(&mut self, e: &Expr) -> Option<Expr> {
        self.0.fold_expr_opt_inner(e)
    }
}
impl Replace<'_, '_> {
    fn validate_materialized(&mut self, root: &Expr) -> Result<(), String> {
        match self.validation_mode {
            #[cfg(test)]
            MaterializedValidationMode::FreshInventory => {
                return crate::scoped_local::materialized::validate_materialized_cached(
                    self.scope,
                    self.allowed,
                    root,
                    self.work,
                    self.limit,
                    self.materialized_cache,
                );
            }
            MaterializedValidationMode::PerReplace => {}
        }
        if self.validation_context.is_none() {
            // Called within the existing before/after comparison/reduction
            // ledger span. Preparation is lazy and spends that same budget.
            self.validation_context = Some(
                crate::scoped_local::materialized::MaterializedValidationContext::new(
                    self.scope,
                    self.allowed,
                    self.work,
                    self.limit,
                    self.materialized_cache,
                )?,
            );
        }
        crate::scoped_local::materialized::validate_materialized_in_context_cached(
            self.validation_context
                .as_mut()
                .ok_or("missing materialized validation context")?,
            root,
            self.work,
            self.limit,
            self.materialized_cache,
        )
    }
}
impl ExprFolderOpt for Replace<'_, '_> {
    fn fold_expr_opt(&mut self, e: &Expr) -> Option<Expr> {
        if self.error.is_some() {
            return None;
        }
        if *self.work >= self.limit {
            self.error = Some("projected case-context replacement work limit");
            return None;
        }
        if self.depth > self.max_depth {
            self.error = Some("projected case-context replacement depth limit");
            return None;
        }
        *self.work += 1;
        self.visits += 1;
        let key = Key(e.clone());
        if let Some(known) = self.memo.get(&key) {
            return known.clone();
        }
        // This is only a rewrite-search hint, never an absence/truth premise.
        // A proper expression from the selected finite graph stays unchanged;
        // any missed normalized occurrence still has to pass the original-
        // endpoint equality and property in complete kernel replay.
        if self.proper.contains(&key) {
            self.memo.insert(key, None);
            return None;
        }
        match self.support.summary(
            self.checker,
            self.scope,
            e,
            self.work,
            self.limit,
            self.max_depth.saturating_sub(self.depth),
            self.support_limit,
            self.support_visits,
        ) {
            Ok(Some(summary))
                if summary.cases & CaseSupportCache::bits(self.target)
                    != CaseSupportCache::bits(self.target)
                    && self
                        .depth
                        .checked_add(summary.replacement_height)
                        .is_some_and(|end| end <= self.max_depth) =>
            {
                *self.support_hits += 1;
                self.memo.insert(key, None);
                return None;
            }
            Err(error) => {
                self.error = Some(error);
                return None;
            }
            _ => {}
        }
        // A conservative full height that does not fit is not a new refusal.
        // The original walk can cut a deeper raw tree at its proper/memo
        // frontier. Fall back to that same depth-checked walk in that case.
        // The selected case and the fresh hole are closed with respect to
        // de Bruijn binders. Replacement under a binder cannot capture them.
        let mut reduced = None;
        if !e.has_loose_bvars() {
            let normalized = self.checker.whnf(e);
            let mut matches =
                crate::proof_assembly::normalize::same_graph(&normalized, self.target);
            if !matches
                && normalized.hash_cached() == self.target.hash_cached()
                && case(&normalized, self.checker).is_some()
            {
                // Expr equality can conflate named and ordinary binders. Only
                // compare after authenticating ordinary materialized terms in
                // this exact owner's current allowed context. The structural
                // hash is a search hint; the shared checker decides equality.
                *self.comparisons += 1;
                let before = *self.work;
                let left = self.validate_materialized(&normalized);
                let right = if left.is_ok() {
                    self.validate_materialized(self.target)
                } else {
                    left.clone()
                };
                *self.comparison_visits += (*self.work).saturating_sub(before);
                if left.is_ok() && right.is_ok() {
                    matches = self.checker.is_def_eq(&normalized, self.target);
                    if matches {
                        *self.comparison_matches += 1;
                    }
                } else if *self.work >= self.limit {
                    self.error = Some("projected materialized case comparison work limit");
                    return None;
                }
                if self.checker.heartbeat_spent() {
                    self.error = Some("projected materialized case comparison kernel budget");
                    return None;
                }
            }
            if matches {
                self.changed = true;
                let replacement = Some(self.hole.clone());
                self.memo.insert(key, replacement.clone());
                return replacement;
            }
            if !crate::proof_assembly::normalize::same_graph(e, &normalized)
                && (case(&normalized, self.checker).is_some() || administrative_redex(e))
            {
                // Follow the existing checker's ordinary WHNF rather than a
                // cold beta/let spine. This is candidate construction only;
                // the original endpoint remains in the strict external claim.
                let before = *self.work;
                let ordinary = self.validate_materialized(&normalized);
                *self.reduction_visits += (*self.work).saturating_sub(before);
                if ordinary.is_ok() {
                    *self.reductions += 1;
                    reduced = Some(normalized);
                } else if *self.work >= self.limit {
                    self.error = Some("projected replacement reduction work limit");
                    return None;
                }
            }
        }
        if self.checker.heartbeat_spent() {
            self.error = Some("projected replacement reduction kernel budget");
            return None;
        }
        self.depth += 1;
        let result = if let Some(normalized) = reduced {
            Some(
                ReplaceStack(self)
                    .fold_expr_opt(&normalized)
                    .unwrap_or(normalized),
            )
        } else {
            ReplaceStack(self).fold_expr_opt(e)
        };
        self.depth -= 1;
        if self.error.is_none() {
            self.memo.insert(key, result.clone());
        }
        result
    }
}
impl<L: ScopedLocalAllocator> Replay<'_, '_, L> {
    fn materialized_case_locals(
        &self,
        extra: &[ScopedLocal],
        binder: Option<&ScopedLocal>,
    ) -> Result<Vec<ScopedLocal>, String> {
        // globals already authenticates the initial retained-data context used
        // by this Replay's immutable checker. Later emitted proof components
        // are not new computation inputs or implicit abstraction permissions.
        let mut allowed = Vec::new();
        let mut ids = HashSet::new();
        for local in self
            .globals
            .iter()
            .cloned()
            .chain(self.captures.iter().map(|c| c.local().clone()))
            .chain(extra.iter().cloned())
        {
            if !self.allocator.local_scope().owns(&local) {
                return Err("foreign materialized case local".into());
            }
            if binder.is_some_and(|binder| binder.id() == local.id()) {
                continue;
            }
            if ids.insert(local.id()) {
                allowed.push(local);
            }
        }
        Ok(allowed)
    }
    fn abstract_case_local(
        &mut self,
        binder: &ScopedLocal,
        body: &Expr,
        extra: &[ScopedLocal],
        limit: usize,
    ) -> Result<Expr, String> {
        let allowed = self.materialized_case_locals(extra, Some(binder))?;
        let before = self.context_work;
        let result = crate::scoped_local::materialized::abstract_materialized_cached(
            self.allocator.local_scope(),
            &allowed,
            binder,
            body,
            &mut self.context_work,
            limit,
            &mut self.materialized_cache,
        );
        self.work.abstraction_visits += self.context_work.saturating_sub(before);
        result
    }
    pub(super) fn materialize_case_computation(
        &mut self,
        term: Expr,
        limit: usize,
    ) -> Result<Expr, String> {
        // globals already authenticates the initial retained-data context used
        // by this Replay's immutable checker. Later emitted proof components
        // are not new computation inputs or implicit abstraction permissions.
        let mut allowed = self.globals.clone();
        let mut ids = allowed
            .iter()
            .map(|local| local.id())
            .collect::<HashSet<_>>();
        for local in self.captures.iter().map(|capture| capture.local().clone()) {
            if !self.allocator.local_scope().owns(&local) {
                return Err("foreign case-computation capture".into());
            }
            if ids.insert(local.id()) {
                allowed.push(local);
            }
        }
        let (closed, stats) =
            self.allocator
                .local_scope()
                .close_external_forest(&[term], &allowed, &[allowed.len()]);
        self.context_work = self
            .context_work
            .checked_add(stats.visits)
            .ok_or("case-computation closure work overflow")?;
        self.work.computation_materialization_visits += stats.visits;
        if self.context_work > limit {
            return Err("projected case-context aggregate closure limit".into());
        }
        let mut closed = closed.map_err(|error| error.to_string())?;
        closed
            .pop()
            .ok_or_else(|| "case-computation closure lost its root".into())
    }

    /// Follow only demanded primitive projection receivers. Their WHNF can
    /// expose a nonrecursive case even when no Const recursor heads the full
    /// observation. Unread constructor fields are not searched here.
    fn projection_receiver_case(
        &mut self,
        source: &Expr,
        limit: usize,
    ) -> Result<Option<Case>, String> {
        let before = self.context_work;
        let result = self.projection_receiver_case_inner(source, limit);
        self.work.receiver_visits += self.context_work.saturating_sub(before);
        result
    }
    fn projection_receiver_case_inner(
        &mut self,
        source: &Expr,
        limit: usize,
    ) -> Result<Option<Case>, String> {
        let mut current = source.clone();
        for _ in 0..=self.limits.max_depth {
            let ExprKind::Proj(_, _, receiver) = current.kind() else {
                return Ok(None);
            };
            self.context_work = self
                .context_work
                .checked_add(1)
                .ok_or("projected receiver work overflow")?;
            if self.context_work > limit {
                return Err("projected receiver aggregate work limit".into());
            }
            current = self.checker.whnf(receiver);
            if let Some(selected) = case(&current, &self.checker) {
                return Ok(Some(selected));
            }
        }
        Err("projected receiver depth limit".into())
    }

    pub(super) fn commute_nested_case(
        &mut self,
        source: &Expr,
    ) -> Result<Option<(Expr, Expr)>, String> {
        if self.limits.max_cases == 0 {
            return Ok(None);
        }
        let limit = self
            .limits
            .max_cases
            .checked_mul(self.limits.max_app_args.max(1))
            .ok_or("projected case-context work overflow")?
            .min(1_000_000);
        let selected = if matches!(source.kind(), ExprKind::Proj(..)) {
            self.projection_receiver_case(source, limit)?
        } else {
            // Only the active discriminator is demanded. Searching unrelated
            // state/payload fields would force cold data and duplicate work.
            let major = if let Some(outer) = case(source, &self.checker) {
                outer
                    .args
                    .last()
                    .cloned()
                    .ok_or("case-context missing outer major")?
            } else {
                // A demanded list fold can hide a computed receiver below its
                // major's projections. Commute only an existing nonrecursive
                // case in that major, using its checked CaseMap contract. The
                // fold itself is not a Case and gains no recursive theorem.
                let ExprKind::Const(name, levels) = source.get_app_fn().kind() else {
                    return Ok(None);
                };
                let args = source.get_app_args();
                if name.to_string() != "List.rec" || args.len() != 5 || levels.len() != 2 {
                    return Ok(None);
                }
                let motive = self.checker.whnf(args[1]);
                let ExprKind::Lam(_, _, body) = motive.kind() else {
                    return Ok(None);
                };
                if body.has_loose_bvars() || source.has_loose_bvars() {
                    return Ok(None);
                }
                args[4].clone()
            };
            let before = self.context_work;
            self.work.search_calls += 1;
            if self.work.first_search_entry_work.is_none() {
                self.work.first_search_entry_work = Some(before);
            }
            let mut search = Search {
                checker: &self.checker,
                work: &mut self.context_work,
                limit,
                depth: 0,
                max_depth: self.limits.max_depth,
                first: false,
                seen: HashSet::new(),
                found: None,
                error: None,
                scope: self.allocator.local_scope(),
                support: &mut self.case_support,
                support_limit: self.limits.max_cache_entries,
                support_visits: &mut self.work.case_support_visits,
                support_hits: &mut self.work.search_case_support_hits,
                visits: 0,
            };
            let _unchanged = search.fold_expr_opt(&major);
            let visits = search.visits;
            self.work.search_visits += visits;
            self.work.search_unique_visits += search.seen.len();
            self.work.search_duplicate_visits += visits.saturating_sub(search.seen.len());
            if let Some(error) = search.error {
                return Err(format!(
                    "{error}; visits={}/{}; depth={}/{}",
                    *search.work, search.limit, search.depth, search.max_depth
                ));
            }
            search.found
        };
        let Some(case) = selected else {
            return Ok(None);
        };
        // Index a bounded frontier of the selected graph. Large past-state
        // arguments are retained whole, so rewriting another occurrence need
        // not descend into those same irrelevant arguments again. Missing
        // index entries affect producer completeness only; no proof rule uses
        // the index as evidence. All existing scan/depth limits stay fixed.
        let mut proper = HashSet::new();
        let mut frontier = VecDeque::from(case.args.clone());
        for _ in 0..self.limits.max_app_args {
            let Some(expression) = frontier.pop_front() else {
                break;
            };
            self.context_work = self
                .context_work
                .checked_add(1)
                .ok_or("case-context index work overflow")?;
            self.work.index_visits += 1;
            if self.context_work > limit {
                return Err("projected case-context index work limit".into());
            }
            if crate::proof_assembly::normalize::same_graph(&expression, &case.term)
                || !proper.insert(Key(expression.clone()))
            {
                continue;
            }
            match expression.kind() {
                ExprKind::App(_, _) => {
                    frontier.push_back(expression.get_app_fn().clone());
                    frontier.extend(
                        expression
                            .get_app_args()
                            .iter()
                            .take(self.limits.max_app_args)
                            .map(|e| (*e).clone()),
                    );
                }
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    frontier.push_back(ty.as_ref().clone());
                    frontier.push_back(body.as_ref().clone());
                }
                ExprKind::Let(_, ty, value, body, _) => {
                    frontier.push_back(ty.as_ref().clone());
                    frontier.push_back(value.as_ref().clone());
                    frontier.push_back(body.as_ref().clone());
                }
                ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
                    frontier.push_back(inner.as_ref().clone())
                }
                _ => {} // Optional index only; the full folder/replay is unchanged.
            }
        }
        let hole = self.allocator.allocate_local(case.result.clone())?;
        let comparison_allowed = self.materialized_case_locals(&[], None)?;
        let mut replace = Replace {
            checker: &self.checker,
            target: &case.term,
            proper: &proper,
            hole: hole.term(),
            work: &mut self.context_work,
            limit,
            depth: 0,
            max_depth: self.limits.max_depth,
            memo: HashMap::new(),
            changed: false,
            error: None,
            scope: self.allocator.local_scope(),
            support: &mut self.case_support,
            support_limit: self.limits.max_cache_entries,
            support_visits: &mut self.work.case_support_visits,
            support_hits: &mut self.work.replacement_case_support_hits,
            visits: 0,
            allowed: &comparison_allowed,
            materialized_cache: &mut self.materialized_cache,
            validation_context: None,
            validation_mode: self.validation_mode,
            comparison_visits: &mut self.work.comparison_materialization_visits,
            comparisons: &mut self.work.materialized_case_comparisons,
            comparison_matches: &mut self.work.materialized_case_matches,
            reduction_visits: &mut self.work.replacement_reduction_visits,
            reductions: &mut self.work.replacement_reductions,
        };
        let template = replace
            .fold_expr_opt(source)
            .unwrap_or_else(|| source.clone());
        self.work.replacement_visits += replace.visits;
        if let Some(error) = replace.error {
            return Err(format!(
                "{error}; visits={}/{}; depth={}/{}",
                *replace.work, replace.limit, replace.depth, replace.max_depth
            ));
        }
        if !replace.changed {
            return Err("selected projected case lost its owned context".into());
        }
        if self.checker.heartbeat_spent() {
            return Err("projected case-context kernel budget".into());
        }
        // ScopedLocal binders are deliberately deferred. Materialize through
        // the owning scope before asking the kernel normalizer to beta-reduce;
        // otherwise its hole/branch locals would be interpreted as free data.
        let context = self.abstract_case_local(&hole, &template, &[], limit)?;
        self.cases = self
            .cases
            .checked_add(1)
            .ok_or("projected case-context count overflow")?;
        if self.cases > self.limits.max_cases {
            return Err("projected equality case limit".into());
        }
        let mut mapped = Vec::new();
        let mut identities = Vec::new();
        for (index, fields) in case.fields.iter().enumerate() {
            let locals = fields
                .iter()
                .cloned()
                .map(|t| self.allocator.allocate_local(t))
                .collect::<Result<Vec<_>, _>>()?;
            let original = Expr::apps(
                case.args[case.params + 1 + index].clone(),
                locals.iter().map(|l| l.term().clone()),
            );
            let value = Expr::app(context.clone(), original);
            let mut mapped_branch = value.clone();
            let mut identity = refl(&self.u, self.observed.clone(), value);
            for local in locals.iter().rev() {
                mapped_branch = self.abstract_case_local(local, &mapped_branch, &locals, limit)?;
                identity = self.abstract_case_local(local, &identity, &locals, limit)?;
            }
            mapped.push(mapped_branch);
            identities.push(identity);
        }
        let major = case
            .args
            .last()
            .ok_or("case-context missing major")?
            .clone();
        let major_type = match case.name.as_str() {
            "Prod.rec" => at(
                "Prod",
                case.levels[1..].to_vec(),
                case.args[..case.params].to_vec(),
            ),
            "Except.rec" => at(
                "Except",
                case.levels[1..].to_vec(),
                case.args[..case.params].to_vec(),
            ),
            "Option.rec" => at("Option", case.levels[1..].to_vec(), [case.args[0].clone()]),
            _ => Expr::const_str("Bool"),
        };
        let motive = self.allocator.allocate_local(major_type)?;
        let mut normalized_args = case.args[..case.params].to_vec();
        normalized_args.push(self.abstract_case_local(
            &motive,
            &self.observed.clone(),
            &[],
            limit,
        )?);
        normalized_args.extend(mapped.iter().cloned());
        normalized_args.push(major.clone());
        let mut levels = case.levels.clone();
        levels[0] = Level::succ(self.u.clone());
        let normalized = at(&case.name, levels, normalized_args);
        let allowed = self.materialized_case_locals(&[], None)?;
        let before = self.context_work;
        let valid = crate::scoped_local::materialized::validate_materialized_cached(
            self.allocator.local_scope(),
            &allowed,
            &normalized,
            &mut self.context_work,
            limit,
            &mut self.materialized_cache,
        );
        self.work.validation_visits += self.context_work.saturating_sub(before);
        valid?;
        let mut natural = case.args[..case.params].to_vec();
        natural.extend([case.result, self.observed.clone(), context]);
        natural.extend(mapped);
        natural.extend(
            case.args[case.params + 1..case.args.len() - 1]
                .iter()
                .cloned(),
        );
        natural.extend(identities);
        natural.push(major);
        let equality = at(
            "Eq.symm",
            vec![Level::succ(self.u.clone())],
            [
                self.observed.clone(),
                normalized.clone(),
                source.clone(),
                at(case.theorem, vec![self.u.clone()], natural),
            ],
        );
        Ok(Some((normalized, equality)))
    }
}

#[cfg(test)]
#[path = "projected_case_context_depth_tests.rs"]
mod depth_tests;
