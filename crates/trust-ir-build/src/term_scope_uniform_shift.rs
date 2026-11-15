// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! A checked index translation of a completed, declaration-free named output.
//! No source meaning, new scope, candidate slot or independent budget is added.

use super::observations::{DependencyRejection, OutputProjectionObservation};
use super::*;

/// Exact coordinates for a completed ordinary output translation.
pub(super) type OutputShiftKey = (usize, i64, u32);
type OutputCoordinate = (usize, u32);
type Renaming = HashMap<u32, u32>;

#[path = "term_scope_named_footprint.rs"]
mod named_footprint;
use named_footprint::NamedFootprint;

#[derive(Clone)]
struct OutputMemo {
    output: Option<Arc<Expr>>,
    guard_extent: u32,
    footprint: NamedFootprint,
}

/// A completed output and its exact input owner. This carries no dependency
/// or declaration proof and is consulted only after the normal scope probe.
#[derive(Clone)]
pub(super) struct CompletedNamedOutput {
    input: Arc<Expr>,
    renaming: Arc<Renaming>,
    memo: OutputMemo,
}

impl CompletedNamedOutput {
    fn matches(&self, expression: &Expr, renaming: &Renaming, closer: &mut Closer<'_>) -> bool {
        if !std::ptr::eq(Arc::as_ptr(&self.input), expression)
            || !self
                .memo
                .footprint
                .fits(closer.walk_depth, closer.limits.max_depth)
            || (self.memo.guard_extent != 0
                && closer
                    .binder_depth
                    .checked_add(self.memo.guard_extent - 1)
                    .is_none_or(|depth| depth > Expr::MAX_BVAR_INDEX))
        {
            return false;
        }
        self.memo
            .footprint
            .matches(&self.renaming, renaming, closer)
    }
}

/// Retained owners prevent address reuse for the exact-coordinate cache.
pub(super) struct CompletedOutputShift {
    input: Arc<Expr>,
    output: Arc<Expr>,
    guard_extent: u32,
}

/// One completed uniform translation, never a scope/dependency certificate.
/// Lookup is one hop: witnesses may share outputs, so no acyclicity is assumed.
pub(super) struct OutputShiftOrigin {
    input: Arc<Expr>,
    output: Arc<Expr>,
    delta: i64,
    guard_extent: u32,
}

impl Closer<'_> {
    #[cfg(test)]
    pub(super) fn uniform_named_output(
        &mut self,
        cached: &ContextEntry,
        input: &Expr,
    ) -> Option<MemoEntry> {
        self.project_named_output(cached, input, false, false)
            .map(|(entry, _)| entry)
    }

    #[cfg(test)]
    fn mapped_named_output(&mut self, cached: &ContextEntry, input: &Expr) -> Option<MemoEntry> {
        self.project_named_output(cached, input, true, true)
            .map(|(entry, _)| entry)
    }

    /// Validate the SAME selected candidate once. A mixed live delta switches
    /// this ongoing proof to an exact map; no paid prefix is discarded/repeated.
    pub(super) fn named_output_projection(
        &mut self,
        cached: &ContextEntry,
        input: &Expr,
    ) -> Option<(MemoEntry, bool)> {
        self.project_named_output(cached, input, true, false)
    }

    fn observe_projection(&mut self, mapped: bool, event: OutputProjectionObservation) {
        if mapped {
            self.observe_named_projection(event);
        } else {
            self.observe_uniform_shift(event);
        }
    }

    fn project_named_output(
        &mut self,
        cached: &ContextEntry,
        input: &Expr,
        allow_mapping: bool,
        mut mapped: bool,
    ) -> Option<(MemoEntry, bool)> {
        if self.error.is_some()
            || input.has_loose_bvars_quick()
            || cached.entry.declarations().is_some()
        {
            return None;
        }
        self.observe_projection(mapped, OutputProjectionObservation::Attempt);
        self.observe_phase(TermScopeStopPhase::RelativeDependency);
        let before = self.stats.context_check_visits;
        let nodes = self.dependencies.len();
        let result = self.project_named_output_inner(cached, input, allow_mapping, &mut mapped);
        if result.is_none() {
            self.observe_projection(mapped, OutputProjectionObservation::Refusal);
            if self.error == Some(TermScopeError::VisitLimit) {
                self.observe_dependency_rejection(DependencyRejection::Budget);
            }
        }
        self.observe_probe_result(
            true,
            result.is_some(),
            self.stats.context_check_visits - before,
            self.dependencies.len() - nodes,
        );
        result.map(|entry| (entry, mapped))
    }

    fn project_named_output_inner(
        &mut self,
        cached: &ContextEntry,
        input: &Expr,
        allow_mapping: bool,
        mapped: &mut bool,
    ) -> Option<MemoEntry> {
        let root = cached.entry.dependencies()?;
        let mut delta = None;
        // Only primitive indices, each inserted on its already charged leaf.
        // No structural equality search or second dependency walk is needed.
        let mut renaming = allow_mapping.then(HashMap::new);
        let dependencies = if !*mapped && self.known_named_prefix(root, cached.binder_depth) {
            if !self.visit() {
                return None;
            }
            self.stats.context_check_visits += 1;
            self.observe_projection(false, OutputProjectionObservation::DependencyVisit);
            self.observe_named_prefix_proof();
            // Every dependency is Named, external, and still at its old depth.
            // The original absolute footprint is already the new footprint.
            delta = Some(i64::from(self.binder_depth) - i64::from(cached.binder_depth));
            Some(root)
        } else if !matches!(self.dependencies[root].dependency, Dependency::Join(_, _)) {
            if !self.visit() {
                return None;
            }
            self.stats.context_check_visits += 1;
            self.observe_projection(*mapped, OutputProjectionObservation::DependencyVisit);
            if self.dependencies[root].min_depth >= cached.binder_depth {
                return None;
            }
            Some(self.project_external_leaf(
                root,
                cached.binder_depth,
                &mut delta,
                &mut renaming,
                mapped,
            )?)
        } else {
            let mut rebased: HashMap<usize, Option<usize>> = HashMap::new();
            let mut stack = vec![(root, false)];
            while let Some((index, finish)) = stack.pop() {
                if finish {
                    let Dependency::Join(left, right) = self.dependencies[index].dependency else {
                        unreachable!("only a dependency Join has a finish request")
                    };
                    let output = match (rebased[&left], rebased[&right]) {
                        (Some(left), Some(right)) if left != right => {
                            Some(self.union_dependencies(left, right))
                        }
                        (left, right) => left.or(right),
                    };
                    rebased.insert(index, output);
                    continue;
                }
                // Repeated DAG edges and internal cutoff requests pay before
                // screens/memoization, under the one original closing budget.
                if !self.visit() {
                    return None;
                }
                self.stats.context_check_visits += 1;
                self.observe_projection(*mapped, OutputProjectionObservation::DependencyVisit);
                if rebased.contains_key(&index) {
                    continue;
                }
                if self.dependencies[index].min_depth >= cached.binder_depth {
                    rebased.insert(index, None);
                    continue;
                }
                let output = match self.dependencies[index].dependency {
                    Dependency::Join(left, right) => {
                        stack.push((index, true));
                        stack.push((right, false));
                        stack.push((left, false));
                        continue;
                    }
                    _ => Some(self.project_external_leaf(
                        index,
                        cached.binder_depth,
                        &mut delta,
                        &mut renaming,
                        mapped,
                    )?),
                };
                rebased.insert(index, output);
            }
            rebased[&root]
        };
        let delta = delta?;
        let mut entry = cached.entry.clone();
        if *mapped || delta != 0 {
            if *mapped && let (Some(output), Some(map)) = (&entry.replacement, &renaming) {
                self.observe_named_projection_root(output, map);
            }
            let mut shift = OutputShift {
                closer: self,
                delta,
                renaming: if *mapped {
                    renaming.map(Arc::new)
                } else {
                    None
                },
                refused: false,
                cutoff: 0,
                guard_extent: 0,
                named: NamedFootprint::default(),
                memo: HashMap::new(),
            };
            let changed = match &entry.replacement {
                Some(output) => shift.shared_arc(output),
                None => shift.shared(input),
            };
            if shift.refused || shift.closer.error.is_some() {
                return None;
            }
            if changed.is_some() {
                entry.replacement = changed;
            }
        }
        entry.dependencies = MemoEntry::compact(dependencies);
        Some(entry)
    }

    /// Exact live endpoints for one already charged external leaf.
    fn project_external_leaf(
        &mut self,
        index: usize,
        cached_depth: u32,
        delta: &mut Option<i64>,
        renaming: &mut Option<HashMap<u32, u32>>,
        mapped: &mut bool,
    ) -> Option<usize> {
        match self.dependencies[index].dependency {
            Dependency::Ordinary(_, _) => {
                self.observe_dependency_rejection(DependencyRejection::UnexpectedOrdinary);
                None
            }
            Dependency::Named(id, old_depth) => {
                let Some(new_depth) = self.active.get(&id).copied() else {
                    self.observe_dependency_rejection(DependencyRejection::NamedMissing);
                    return None;
                };
                let old_index = cached_depth.checked_sub(old_depth.checked_add(1)?)?;
                let new_index = self.binder_depth.checked_sub(new_depth.checked_add(1)?)?;
                if old_index > Expr::MAX_BVAR_INDEX || new_index > Expr::MAX_BVAR_INDEX {
                    return None;
                }
                if let Some(renaming) = renaming
                    && renaming
                        .insert(old_index, new_index)
                        .is_some_and(|old| old != new_index)
                {
                    return None;
                }
                let current = i64::from(new_index) - i64::from(old_index);
                if !*mapped && delta.is_some_and(|previous| previous != current) {
                    self.observe_dependency_rejection(DependencyRejection::NamedMoved);
                    if renaming.is_none() {
                        return None;
                    }
                    self.observe_uniform_shift(OutputProjectionObservation::Refusal);
                    self.observe_named_projection(OutputProjectionObservation::Attempt);
                    *mapped = true;
                }
                *delta = Some(current);
                Some(self.named_read_dependency(id, new_depth))
            }
            Dependency::Join(_, _) => unreachable!("external leaf helper received a Join"),
        }
    }
}

/// Shift ordinary OUTPUT, never revisit the input's deferred binder registry.
/// A fixed delta or exact map and (live output address, internal cutoff)
/// determine a result for one attempt.
/// The output graph stays borrowed for the whole attempt, so keys cannot recycle.
struct OutputShift<'a, 'scope> {
    closer: &'a mut Closer<'scope>,
    delta: i64,
    renaming: Option<Arc<Renaming>>,
    refused: bool,
    cutoff: u32,
    guard_extent: u32,
    named: NamedFootprint,
    memo: HashMap<OutputCoordinate, OutputMemo>,
}

struct ShiftBoundary<'a, 'b, 'scope>(&'a mut OutputShift<'b, 'scope>);

impl ExprFolderOpt for ShiftBoundary<'_, '_, '_> {
    fn fold_expr_opt_inner(&mut self, expression: &Expr) -> Option<Expr> {
        self.0.fold_expr_opt_inner(expression)
    }
}

impl OutputShift<'_, '_> {
    fn observe_output(&mut self, event: OutputProjectionObservation) {
        if self.renaming.is_some() {
            self.closer.observe_named_projection(event);
        } else {
            self.closer.observe_uniform_shift(event);
        }
    }

    fn shared(&mut self, expression: &Expr) -> Option<Arc<Expr>> {
        self.shared_inner(expression, None)
    }

    fn shared_arc(&mut self, expression: &Arc<Expr>) -> Option<Arc<Expr>> {
        self.shared_inner(expression, Some(expression))
    }

    fn shared_inner(&mut self, expression: &Expr, owner: Option<&Arc<Expr>>) -> Option<Arc<Expr>> {
        if self.refused || self.closer.error.is_some() {
            return None;
        }
        self.closer.observe_phase(if self.renaming.is_some() {
            TermScopeStopPhase::NamedIndexProjectionOutput
        } else {
            TermScopeStopPhase::UniformIndexShiftOutput
        });
        if !self.closer.visit() {
            return None;
        }
        self.observe_output(OutputProjectionObservation::OutputVisit);
        if self.closer.walk_depth >= self.closer.limits.max_depth {
            self.closer.fail(TermScopeError::DepthLimit);
            return None;
        }
        if expression.loose_bvar_range() <= self.cutoff {
            if self.renaming.is_some() {
                self.named.walk_extent = self.named.walk_extent.max(1);
            }
            return None;
        }
        let address = expression as *const Expr as usize;
        let key = (address, self.cutoff);
        if let Some(memo) = self.memo.get(&key).cloned()
            && (self.renaming.is_none()
                || memo
                    .footprint
                    .fits(self.closer.walk_depth, self.closer.limits.max_depth))
        {
            return self.use_memo(memo);
        }
        if let Some(renaming) = &self.renaming
            && let Some(completed) = self.closer.named_outputs.get(&key).cloned()
            && completed.matches(expression, renaming, self.closer)
        {
            let memo = completed.memo.clone();
            self.memo.insert(key, memo.clone());
            return self.use_memo(memo);
        }
        if self.closer.error.is_some() {
            return None;
        }
        // A successful first translation preserves which indices are below
        // this cutoff. Therefore S(b, c, S(a, c, x)) = S(a+b, c, x), subject
        // to the SAME checked final indices. Different cutoffs never compose.
        let origin = self
            .renaming
            .is_none()
            .then(|| {
                self.closer
                    .shift_origins
                    .get(&(address, self.cutoff))
                    .and_then(|origin| {
                        (std::ptr::eq(Arc::as_ptr(&origin.output), expression))
                            .then(|| self.delta.checked_add(origin.delta))
                            .flatten()
                            .map(|delta| (origin.input.clone(), delta, origin.guard_extent))
                    })
            })
            .flatten();
        let input_owner = origin
            .as_ref()
            .map(|(input, _, _)| input.clone())
            .or_else(|| owner.cloned());
        let input = origin
            .as_ref()
            .map_or(expression, |(input, _, _)| input.as_ref());
        let delta = origin.as_ref().map_or(self.delta, |(_, delta, _)| *delta);
        // The original immutable Expr already has valid BVar indices (the same
        // constructor/metadata invariant used by loose-range pruning). Undoing
        // an exact completed shift restores those indices, but still inherits
        // every binder guard of its actual visitor. This is a memo hit, not a
        // new traversal: the charged request-depth check above still applies.
        if let Some((input, 0, guard_extent)) = &origin
            && (*guard_extent == 0
                || self
                    .closer
                    .binder_depth
                    .checked_add(*guard_extent - 1)
                    .is_some_and(|depth| depth <= Expr::MAX_BVAR_INDEX))
        {
            let memo = OutputMemo {
                output: Some(input.clone()),
                guard_extent: *guard_extent,
                footprint: NamedFootprint::default(),
            };
            self.memo.insert(key, memo.clone());
            self.closer.observe_composed_shift(true);
            return self.use_memo(memo);
        }
        let output_key = (input as *const Expr as usize, delta, self.cutoff);
        // The result depends on indices, not parent depth. Reuse only when
        // every binder addition observed during its construction remains safe.
        // Even a zero net delta needs this bound or its original traversal.
        if self.renaming.is_none()
            && let Some(completed) = self.closer.shifted_outputs.get(&output_key)
            && std::ptr::eq(Arc::as_ptr(&completed.input), input)
            && (completed.guard_extent == 0
                || self
                    .closer
                    .binder_depth
                    .checked_add(completed.guard_extent - 1)
                    .is_some_and(|depth| depth <= Expr::MAX_BVAR_INDEX))
        {
            let result = Some(completed.output.clone());
            let guard_extent = completed.guard_extent;
            self.guard_extent = self.guard_extent.max(guard_extent);
            if origin.is_some() {
                self.closer.observe_composed_shift(true);
            }
            self.observe_output(OutputProjectionObservation::OutputMemoHit);
            self.memo.insert(
                key,
                OutputMemo {
                    output: result.clone(),
                    guard_extent,
                    footprint: NamedFootprint::default(),
                },
            );
            return result;
        }
        if origin.is_some() {
            self.closer.observe_composed_shift(false);
        }
        let parent_extent = self.guard_extent;
        self.guard_extent = 0;
        let parent_named = std::mem::take(&mut self.named);
        self.closer.walk_depth += 1;
        // Composition normalizes the cache coordinate, not the miss traversal.
        // Keep the original input DAG, delta, exhaustive binder hooks and
        // stack-safe visitor. An older origin may have less structural sharing.
        let result = ShiftBoundary(self).fold_expr_opt(expression).map(Arc::new);
        self.closer.walk_depth -= 1;
        let guard_extent = self.guard_extent;
        self.guard_extent = parent_extent.max(guard_extent);
        let footprint = std::mem::replace(&mut self.named, parent_named);
        self.include_named(footprint.clone().under_parent());
        if self.refused || self.closer.error.is_some() {
            return None;
        }
        let result = result.map(|node| self.closer.intern_output_node(node));
        if let Some(output) = &result {
            self.observe_output(OutputProjectionObservation::OutputNodeChanged);
            if self.renaming.is_none()
                && let Some(input) = input_owner
            {
                // No transitive walk through witnesses: a single immutable
                // equality is sufficient even when other origins form cycles.
                if !Arc::ptr_eq(&input, output) {
                    self.closer
                        .shift_origins
                        .entry((Arc::as_ptr(output) as usize, self.cutoff))
                        .or_insert_with(|| OutputShiftOrigin {
                            input: input.clone(),
                            output: output.clone(),
                            delta,
                            guard_extent,
                        });
                }
                self.closer.shifted_outputs.insert(
                    output_key,
                    CompletedOutputShift {
                        input,
                        output: output.clone(),
                        guard_extent,
                    },
                );
            }
        }
        let memo = OutputMemo {
            output: result.clone(),
            guard_extent,
            footprint: footprint.clone(),
        };
        if let Some(renaming) = &self.renaming
            && let Some(input) = owner
            && footprint.is_known()
            && footprint.walk_extent >= 2
        {
            self.closer.named_outputs.insert(
                key,
                CompletedNamedOutput {
                    input: input.clone(),
                    renaming: renaming.clone(),
                    memo: memo.clone(),
                },
            );
        }
        self.memo.insert(key, memo);
        result
    }

    fn include_named(&mut self, footprint: NamedFootprint) {
        if self.renaming.is_some() {
            self.named.include(&footprint, self.closer);
            self.named.walk_extent = self.named.walk_extent.max(footprint.walk_extent);
        }
    }

    fn use_memo(&mut self, memo: OutputMemo) -> Option<Arc<Expr>> {
        self.guard_extent = self.guard_extent.max(memo.guard_extent);
        self.include_named(memo.footprint.under_parent());
        if self.closer.error.is_some() {
            return None;
        }
        self.observe_output(OutputProjectionObservation::OutputMemoHit);
        memo.output
    }

    fn under_output(&mut self, expression: &Expr, owner: Option<&Arc<Expr>>) -> Option<Arc<Expr>> {
        let depth = self.closer.binder_depth.checked_add(self.cutoff);
        if depth.is_none_or(|depth| depth > Expr::MAX_BVAR_INDEX) {
            self.closer.fail(TermScopeError::IndexOverflow);
            return None;
        }
        let saved = self.cutoff;
        let Some(next) = saved.checked_add(1) else {
            self.closer.fail(TermScopeError::IndexOverflow);
            return None;
        };
        self.guard_extent = self.guard_extent.max(next);
        self.cutoff = next;
        let result = self.shared_inner(expression, owner);
        self.cutoff = saved;
        result
    }
}

#[cfg(test)]
#[path = "term_scope_uniform_shift_tests.rs"]
mod tests;

impl ExprFolderOpt for OutputShift<'_, '_> {
    fn fold_expr_opt(&mut self, expression: &Expr) -> Option<Expr> {
        self.shared(expression)
            .map(|output| output.as_ref().clone())
    }

    fn fold_expr_arc_opt(&mut self, expression: &Arc<Expr>) -> Option<Arc<Expr>> {
        self.shared_arc(expression)
    }

    fn fold_binder_body_opt(&mut self, expression: &Expr) -> Option<Expr> {
        self.under_output(expression, None)
            .map(|output| output.as_ref().clone())
    }

    fn fold_binder_body_arc_opt(&mut self, expression: &Arc<Expr>) -> Option<Arc<Expr>> {
        self.under_output(expression, Some(expression))
    }

    fn fold_bvar_opt(&mut self, index: u32) -> Option<Expr> {
        if index < self.cutoff {
            return None;
        }
        if let Some(renaming) = &self.renaming {
            let external = index - self.cutoff;
            let Some(mapped) = renaming.get(&external).copied() else {
                // An incomplete footprint cannot authorize a partial output.
                // Refuse this attempt privately; the caller may fold source.
                self.refused = true;
                return None;
            };
            self.named.include_index(external, self.closer);
            if self.closer.error.is_some() {
                return None;
            }
            let shifted = mapped
                .checked_add(self.cutoff)
                .filter(|i| *i <= Expr::MAX_BVAR_INDEX);
            if shifted == Some(index) {
                return None;
            }
            return self.closer.index(shifted);
        }
        let shifted = i64::from(index)
            .checked_add(self.delta)
            .and_then(|index| u32::try_from(index).ok())
            .filter(|index| *index >= self.cutoff && *index <= Expr::MAX_BVAR_INDEX);
        self.closer.index(shifted)
    }
}

#[cfg(test)]
#[path = "term_scope_named_projection_tests.rs"]
mod named_projection_tests;
