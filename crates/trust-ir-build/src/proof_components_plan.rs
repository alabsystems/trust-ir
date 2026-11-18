// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::dependencies::{
    CaptureDependencies, DependencyEntry, DependencyKey, NormalizationReferences,
};
use super::{ScopedBuildWork, ScopedProofComponentBundle, ScopedProofDeclaration};
use crate::proof_assembly::{ProofLimits, normalize::same_graph};
use crate::scoped_local::{LocalScope, LocalScopeOwner, ScopedLocal, ScopedLocalAllocator};
use clean_kernel::{Expr, Name, expr::FVarId};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

type NormalizationEntries = Vec<(ScopedLocal, Option<Expr>)>;

#[derive(Clone)]
pub enum OwnedProofCapture {
    Parameter(ScopedLocal),
    Definition {
        local: ScopedLocal,
        value: Arc<Expr>,
    },
}

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct NormalizationContextWork {
    pub dependency_visits: usize,
    pub materialization_visits: usize,
    /// Prepaid declaration-inventory work units, not observed CPU visits.
    /// Dynamic inventories debit these units before construction, including
    /// constructions that later refuse. Successful reports count each once.
    pub inventory_visits: usize,
    pub cached_definition_visits: usize,
}

impl NormalizationContextWork {
    pub(crate) fn total(self) -> Result<usize, String> {
        self.dependency_visits
            .checked_add(self.materialization_visits)
            .and_then(|work| work.checked_add(self.inventory_visits))
            .and_then(|work| work.checked_add(self.cached_definition_visits))
            .ok_or_else(|| "opaque normalization work overflow".into())
    }
}
impl OwnedProofCapture {
    pub fn local(&self) -> &ScopedLocal {
        match self {
            Self::Parameter(local) | Self::Definition { local, .. } => local,
        }
    }
}

pub struct ProofComponents {
    namespace: String,
    limits: ProofLimits,
    owner: Option<LocalScopeOwner>,
    base: Vec<OwnedProofCapture>,
    base_ids: HashSet<FVarId>,
    bindings: Vec<(ScopedLocal, Expr)>,
    references: HashMap<FVarId, Arc<Expr>>,
    captures: usize,
    analysis_visits: usize,
    analysis_words: usize,
    retained_words: usize,
    retained_sets: HashSet<usize>,
    dependencies: HashMap<DependencyKey, DependencyEntry>,
    // Sealing has an empty ambient set. Never reuse the ordinary capture cache,
    // whose entries may omit ambient globals and their transitive types.
    sealing_dependencies: HashMap<DependencyKey, DependencyEntry>,
    // Only this component's explicitly materialized declarations enter here.
    // Original definitions stay in `bindings` and in complete scoped replay.
    materialized_definitions: HashMap<FVarId, materialized_definition::MaterializedDefinition>,
    // Complete syntactic references only; no visibility or capture filtering.
    normalization_references: Option<Box<complete_references::Cache>>,
    external_context_owner: Option<Arc<()>>,
    materialized_capture_roots: usize,
    materialized_capture_failed: bool,
}

impl ProofComponents {
    pub fn new(namespace: impl Into<String>, limits: ProofLimits) -> Self {
        Self {
            namespace: namespace.into(),
            limits,
            owner: None,
            base: Vec::new(),
            base_ids: HashSet::new(),
            bindings: Vec::new(),
            references: HashMap::new(),
            captures: 0,
            analysis_visits: 0,
            analysis_words: 0,
            retained_words: 0,
            retained_sets: HashSet::new(),
            dependencies: HashMap::new(),
            sealing_dependencies: HashMap::new(),
            materialized_definitions: HashMap::new(),
            normalization_references: None,
            external_context_owner: None,
            materialized_capture_roots: 0,
            materialized_capture_failed: false,
        }
    }
    pub fn set_base(
        &mut self,
        scope: &LocalScope,
        captures: Vec<OwnedProofCapture>,
    ) -> Result<(), String> {
        if self.owner.is_some() || !self.bindings.is_empty() {
            return Err("component base already set".into());
        }
        if captures.len() > self.limits.captures {
            return Err("component base capture limit".into());
        }
        let mut ids = HashSet::new();
        for capture in &captures {
            if !scope.owns(capture.local()) || !ids.insert(capture.local().id()) {
                return Err("foreign or duplicate component base capture".into());
            }
        }
        self.owner = Some(scope.memo_owner());
        self.base_ids = ids;
        self.captures = captures.len();
        self.base = captures;
        Ok(())
    }
    /// Request reusable COMPLETE syntactic references for this actual owner.
    /// Ordinary callers retain their original fresh reference walk. This only
    /// chooses producer data reuse: cold construction and every hit spend the
    /// component ledger, and profiled callers also retain their existing work
    /// report/ledger. Complete replay remains required. Only retained original
    /// types/values publish keys; temporary input graphs are never retained.
    /// No body, footprint, replacement scope or resource budget is accepted.
    /// Repeating this request never clears entries, failure or charged work.
    pub fn enable_normalization_reference_reuse(
        &mut self,
        scope: &LocalScope,
    ) -> Result<(), String> {
        self.spend_context_work(1)?;
        if !self
            .owner
            .as_ref()
            .is_some_and(|owner| owner.matches(&scope.memo_owner()))
        {
            return Err("normalization reference reuse has another component owner".into());
        }
        if let Some(cache) = &self.normalization_references {
            return if cache.has_failed() {
                Err("normalization dependency cache retains a failed scan".into())
            } else {
                Ok(())
            };
        }
        let inventory = self
            .base
            .len()
            .checked_add(self.bindings.len())
            .and_then(|count| count.checked_mul(4))
            .ok_or("normalization reference reuse inventory overflow")?;
        self.spend_context_work(inventory)?;
        let _original_entries = self.normalization_entries(scope)?;
        self.normalization_references = Some(Box::new(complete_references::Cache::new(
            self.limits.operations,
        )));
        Ok(())
    }

    pub fn extend_base_definition(&mut self, capture: OwnedProofCapture) -> Result<(), String> {
        if !matches!(capture, OwnedProofCapture::Definition { .. }) {
            return Err("component definition extension requires a defining value".into());
        }
        self.extend_base(capture)
    }
    pub fn extend_base(&mut self, capture: OwnedProofCapture) -> Result<(), String> {
        if !self
            .owner
            .as_ref()
            .is_some_and(|owner| owner.owns(capture.local()))
            || self.captures >= self.limits.captures
            || !self.base_ids.insert(capture.local().id())
        {
            return Err("invalid component base extension".into());
        }
        self.captures += 1;
        // New base captures precede every retained declaration. Never carry a
        // materialized prefix result across that change of external scope.
        self.materialized_definitions.clear();
        if let Some(cache) = &mut self.normalization_references {
            cache.clear_entries();
        }
        self.base.push(capture);
        Ok(())
    }
    pub fn counts(&self) -> (usize, usize, usize, usize) {
        (
            self.bindings.len(),
            self.base.len(),
            self.captures,
            self.analysis_visits + self.analysis_words,
        )
    }
    fn normalization_entries(&self, scope: &LocalScope) -> Result<NormalizationEntries, String> {
        if !self
            .owner
            .as_ref()
            .is_some_and(|owner| owner.matches(&scope.memo_owner()))
        {
            return Err("normalization context has no matching component owner".into());
        }
        let mut ids = HashSet::new();
        let mut entries = Vec::new();
        for capture in &self.base {
            let local = capture.local();
            if !scope.owns(local) || !ids.insert(local.id()) {
                return Err("foreign or duplicate normalization base".into());
            }
            let value = match capture {
                OwnedProofCapture::Parameter(_) => None,
                OwnedProofCapture::Definition { value, .. } => Some(value.as_ref().clone()),
            };
            entries.push((local.clone(), value));
        }
        for (local, value) in &self.bindings {
            if !scope.owns(local) || !ids.insert(local.id()) {
                return Err("foreign or duplicate normalization component".into());
            }
            entries.push((local.clone(), Some(value.clone())));
        }
        Ok(entries)
    }
    pub(crate) fn retained_normalization_locals(
        &self,
        scope: &LocalScope,
    ) -> Result<Vec<ScopedLocal>, String> {
        Ok(self
            .normalization_entries(scope)?
            .into_iter()
            .map(|(local, _)| local)
            .collect())
    }
    fn normalization_entries_with_dynamic(
        &mut self,
        scope: &LocalScope,
        dynamic: &[OwnedProofCapture],
    ) -> Result<(NormalizationEntries, usize), String> {
        if dynamic.is_empty() {
            return Ok((self.normalization_entries(scope)?, 0));
        }
        if !self
            .owner
            .as_ref()
            .is_some_and(|owner| owner.matches(&scope.memo_owner()))
        {
            return Err("normalization context has no matching component owner".into());
        }
        let retained = self
            .base
            .len()
            .checked_add(self.bindings.len())
            .ok_or("dynamic normalization declaration count overflow")?;
        let work = dynamic
            .len()
            .checked_mul(5)
            .and_then(|n| n.checked_add(retained))
            .filter(|n| *n <= self.limits.operations)
            .ok_or("dynamic normalization inventory work limit")?;
        if dynamic.len() > self.limits.captures
            || retained.saturating_add(dynamic.len())
                > self.limits.contexts.saturating_add(self.limits.captures)
        {
            return Err("dynamic normalization capture inventory limit".into());
        }
        if work > self.context_work_remaining()? {
            return Err("dynamic normalization inventory admission limit".into());
        }
        // Prepay the unchanged inventory fee before cloning retained entries,
        // allocating lookup maps or inspecting capture handles/values. This
        // admission remains spent on every later error; the returned count is
        // only for reporting and must never be debited by the caller again.
        self.spend_context_work(work)?;
        let mut entries = self.normalization_entries(scope)?;
        let mut positions = entries
            .iter()
            .enumerate()
            .map(|(index, (local, _))| (local.id(), index))
            .collect::<HashMap<_, _>>();
        let mut seen = HashSet::new();
        for capture in dynamic {
            let local = capture.local();
            if !scope.owns(local) || !seen.insert(local.id()) {
                return Err("foreign or duplicate dynamic normalization capture".into());
            }
            let value = match capture {
                OwnedProofCapture::Parameter(_) => None,
                OwnedProofCapture::Definition { value, .. } => Some(value.as_ref().clone()),
            };
            if let Some(&index) = positions.get(&local.id()) {
                let (original, original_value) = &entries[index];
                let same_value = match (&value, original_value) {
                    (None, None) => true,
                    (Some(value), Some(original)) => same_graph(value, original),
                    _ => false,
                };
                if !same_graph(local.ty(), original.ty()) || !same_value {
                    return Err(
                        "dynamic capture changes a retained declaration kind or value".into(),
                    );
                }
            } else {
                positions.insert(local.id(), entries.len());
                entries.push((local.clone(), value));
            }
        }
        Ok((entries, work))
    }
    /// Authenticate exact dynamic declarations without changing the retained
    /// component inventory. Dynamic inventory work is prepaid before any
    /// construction. The returned count reports that debit, not another fee.
    pub(crate) fn normalization_locals_with_dynamic(
        &mut self,
        scope: &LocalScope,
        dynamic: &[OwnedProofCapture],
    ) -> Result<(Vec<ScopedLocal>, usize), String> {
        let (entries, work) = self.normalization_entries_with_dynamic(scope, dynamic)?;
        Ok((entries.into_iter().map(|(local, _)| local).collect(), work))
    }
    /// Producer-only normalization data, never evidence of well-typedness.
    /// Deferred binders are materialized with their actual preceding captures;
    /// all original defining values remain in mandatory complete scoped replay.
    #[cfg(test)]
    pub(crate) fn untrusted_normalization_context(
        &mut self,
        scope: &LocalScope,
        inputs: &[Expr],
    ) -> Result<(clean_kernel::LocalContext, Vec<ScopedLocal>, usize), String> {
        self.untrusted_normalization_context_with_opaque(scope, inputs, &[])
    }
    pub(crate) fn untrusted_normalization_context_profiled(
        &mut self,
        scope: &LocalScope,
        inputs: &[Expr],
    ) -> Result<
        (
            clean_kernel::LocalContext,
            Vec<ScopedLocal>,
            NormalizationContextWork,
        ),
        String,
    > {
        self.normalization_context_profiled(scope, inputs, &[], &[])
    }
    /// Include an already authenticated call-local capture telescope in the
    /// producer view. These untrusted declarations never extend the retained
    /// base, publish persistent dependency keys, or supply replay premises.
    pub(crate) fn untrusted_normalization_context_with_captures_profiled(
        &mut self,
        scope: &LocalScope,
        inputs: &[Expr],
        dynamic: &[OwnedProofCapture],
    ) -> Result<
        (
            clean_kernel::LocalContext,
            Vec<ScopedLocal>,
            NormalizationContextWork,
        ),
        String,
    > {
        if dynamic.is_empty() {
            self.untrusted_normalization_context_profiled(scope, inputs)
        } else {
            self.normalization_context_profiled(scope, inputs, &[], dynamic)
        }
    }
    /// Leave exact owned operation definitions opaque to a PRODUCER only.
    /// The complete carrier is unchanged and still checks every original
    /// defining value. Opacity supplies no image, invariant or proof premise.
    #[cfg(test)]
    pub(crate) fn untrusted_normalization_context_with_opaque(
        &mut self,
        scope: &LocalScope,
        inputs: &[Expr],
        opaque: &[ScopedLocal],
    ) -> Result<(clean_kernel::LocalContext, Vec<ScopedLocal>, usize), String> {
        let (context, locals, work) =
            self.normalization_context_profiled(scope, inputs, opaque, &[])?;
        Ok((context, locals, work.total()?))
    }
    fn normalization_context_profiled(
        &mut self,
        scope: &LocalScope,
        inputs: &[Expr],
        opaque: &[ScopedLocal],
        dynamic: &[OwnedProofCapture],
    ) -> Result<
        (
            clean_kernel::LocalContext,
            Vec<ScopedLocal>,
            NormalizationContextWork,
        ),
        String,
    > {
        let retained_len = self.base.len() + self.bindings.len();
        let (mut entries, mut inventory_work) =
            self.normalization_entries_with_dynamic(scope, dynamic)?;
        if !opaque.is_empty() {
            // Charge inventory setup and every requested probe before any
            // opacity can be published. No cache or unknown-footprint reuse.
            let probes = opaque
                .len()
                .checked_mul(4)
                .ok_or("opaque normalization inventory work overflow")?;
            inventory_work = entries
                .len()
                .checked_add(probes)
                .and_then(|n| n.checked_add(inventory_work))
                .filter(|work| *work <= self.limits.operations)
                .ok_or("opaque normalization inventory operation limit")?;
            let indices = entries
                .iter()
                .enumerate()
                .map(|(index, (local, _))| (local.id(), index))
                .collect::<HashMap<_, _>>();
            let mut seen = HashSet::new();
            for local in opaque {
                if !scope.owns(local) || !seen.insert(local.id()) {
                    return Err("foreign or duplicate opaque normalization owner".into());
                }
                let index = *indices
                    .get(&local.id())
                    .ok_or("opaque normalization local is not retained")?;
                if entries[index].1.is_none() {
                    return Err("opaque normalization requires an original defining value".into());
                }
                entries[index].1 = None;
            }
        }
        let locals = entries
            .iter()
            .map(|(local, _)| local.clone())
            .collect::<Vec<_>>();
        // Only normalization needs this dependency slice. Complete scoped replay
        // still retains and checks every original declaration, including unused
        // defining values. Named-binder formal references are conservatively
        // retained too; no binder-dependent subtraction can omit a dependency.
        let reusable = self.normalization_references.is_some();
        let charged = reusable || !dynamic.is_empty();
        let walk_limit = if charged {
            self.context_work_remaining()?
        } else {
            self.limits.operations
        };
        // Only immutable retained declarations may publish persistent summary
        // keys. A dynamic telescope lives for this call, so use the original
        // fresh bounded walk, without clearing or reviving an existing cache.
        if !dynamic.is_empty()
            && self
                .normalization_references
                .as_ref()
                .is_some_and(|cache| cache.has_failed())
        {
            return Err("normalization dependency cache retains a failed scan".into());
        }
        let cache = if dynamic.is_empty() {
            self.normalization_references.as_deref_mut()
        } else {
            None
        };
        let mut walker = complete_references::References::new(cache, walk_limit)?;
        let mut needed = Vec::new();
        // Definitions are ordered by actual preceding scope, so reverse
        // traversal computes the transitive closure without guessing handles.
        let scanned = (|| -> Result<(), String> {
            for input in inputs {
                walker.scan_input(input)?;
            }
            needed = vec![false; entries.len()];
            for (index, (local, value)) in entries.iter().enumerate().rev() {
                if walker.contains(local.id())? {
                    needed[index] = true;
                    if index < retained_len {
                        walker.scan_retained(local.ty())?;
                        if let Some(value) = value {
                            walker.scan_retained(value)?;
                        }
                    } else {
                        // Temporary dynamic values are not retained component
                        // data and must not publish persistent reference keys.
                        walker.scan_input(local.ty())?;
                        if let Some(value) = value {
                            walker.scan_input(value)?;
                        }
                    }
                }
            }
            Ok(())
        })();
        let work = walker.work();
        drop(walker);
        if !dynamic.is_empty()
            && scanned.is_err()
            && let Some(cache) = &mut self.normalization_references
        {
            // A fresh scan may not publish temporary keys, but it must retain
            // the same monotonic owner failure as the reused input walker.
            cache.poison();
        }
        if charged {
            // Persistent summaries and temporary dynamic scans are paid by
            // this original owner even when a later materialization or replay
            // attempt refuses.
            // The projected caller still receives/spends its full work report.
            self.spend_context_work(work)?;
        }
        scanned?;
        let mut forest = Vec::new();
        let mut visible = Vec::new();
        let use_cache = !self.materialized_definitions.is_empty();
        let mut cached = if use_cache {
            vec![None; entries.len()]
        } else {
            Vec::new()
        };
        let mut cached_definition_visits = 0usize;
        for (index, (local, value)) in entries.iter().enumerate() {
            if !needed[index] {
                continue;
            }
            if use_cache
                && index >= self.base.len()
                && index < retained_len
                && let Some(value) = value
            {
                let before = cached_definition_visits;
                // Bound the lookup itself before it inspects the retained prefix.
                // Completed probes remain charged even when a later probe refuses.
                let lookup_limit = if dynamic.is_empty() {
                    self.limits.operations
                } else {
                    before
                        .checked_add(self.context_work_remaining()?)
                        .ok_or("dynamic cached definition lookup work overflow")?
                };
                let result = self.cached_materialized_definition(
                    scope,
                    index - self.base.len(),
                    local,
                    value,
                    &mut cached_definition_visits,
                    lookup_limit,
                );
                if !dynamic.is_empty() {
                    self.spend_context_work(cached_definition_visits - before)?;
                }
                cached[index] = result?;
                if cached[index].is_some() {
                    continue;
                }
            }
            forest.push(local.ty().clone());
            visible.push(index);
            if let Some(value) = value {
                forest.push(value.clone());
                visible.push(index);
            }
        }
        let (materialized, stats) = if dynamic.is_empty() {
            scope.close_external_forest(&forest, &locals, &visible)
        } else {
            scope.close_external_forest_with_limits(
                &forest,
                &locals,
                &visible,
                crate::term_scope::TermScopeLimits {
                    max_visits: self.context_work_remaining()?,
                    max_depth: 16_384,
                },
            )
        };
        if !dynamic.is_empty() {
            self.spend_context_work(stats.visits)?;
        }
        let mut materialized = materialized.map_err(|error| error.to_string())?.into_iter();
        let mut context = clean_kernel::LocalContext::new();
        for (index, (local, value)) in entries.into_iter().enumerate() {
            if !needed[index] {
                continue;
            }
            let saved = if use_cache {
                cached[index].take()
            } else {
                None
            };
            let (ty, saved_value) = if let Some((ty, value)) = saved {
                (ty, Some(value))
            } else {
                (
                    materialized
                        .next()
                        .ok_or("normalization closure lost declaration type")?,
                    None,
                )
            };
            if value.is_some() {
                let value = match saved_value {
                    Some(value) => value,
                    None => materialized
                        .next()
                        .ok_or("normalization closure lost defining value")?,
                };
                context.push_let_with_id(
                    local.id(),
                    Name::from_string("component.definition"),
                    ty,
                    value,
                );
            } else {
                context.push_with_id(
                    local.id(),
                    Name::from_string("component.parameter"),
                    ty,
                    clean_kernel::BinderInfo::Default,
                );
            }
        }
        if materialized.next().is_some() {
            return Err("normalization closure has extra roots".into());
        }
        let work = NormalizationContextWork {
            dependency_visits: work,
            materialization_visits: stats.visits,
            inventory_visits: inventory_work,
            cached_definition_visits,
        };
        let total = work.total()?;
        if (!opaque.is_empty() || !dynamic.is_empty()) && total > self.limits.operations {
            return Err("normalization aggregate operation limit".into());
        }
        Ok((context, locals, work))
    }
    pub fn bind_scoped<A: ScopedLocalAllocator>(
        &mut self,
        allocator: &mut A,
        captures: &[OwnedProofCapture],
        type_: Expr,
        value: Expr,
    ) -> Result<Expr, String> {
        let result = self.bind_scoped_impl(allocator, captures, type_, value);
        if result.is_err()
            && self
                .owner
                .as_ref()
                .is_some_and(|owner| owner.matches(&allocator.local_scope().memo_owner()))
        {
            self.materialized_capture_failed = true;
        }
        result
    }
    fn bind_scoped_impl<A: ScopedLocalAllocator>(
        &mut self,
        allocator: &mut A,
        captures: &[OwnedProofCapture],
        type_: Expr,
        value: Expr,
    ) -> Result<Expr, String> {
        if !self
            .owner
            .as_ref()
            .is_some_and(|owner| owner.matches(&allocator.local_scope().memo_owner()))
        {
            return Err("proof components have no matching root scope".into());
        }
        if self.bindings.len() >= self.limits.contexts
            || self.bindings.len() >= self.limits.operations
        {
            return Err("proof component declaration limit".into());
        }
        let mut ids = HashSet::new();
        let mut dynamic = Vec::new();
        for capture in captures {
            if !allocator.local_scope().owns(capture.local()) || !ids.insert(capture.local().id()) {
                return Err("foreign or duplicate dynamic component capture".into());
            }
        }
        let mut walker = CaptureDependencies {
            scope: allocator.local_scope(),
            ambient: &self.base_ids,
            work: &mut self.analysis_visits,
            word_work: &mut self.analysis_words,
            cache: &mut self.dependencies,
            retained_words: &mut self.retained_words,
            retained_sets: &mut self.retained_sets,
            limit: self.limits.operations,
            needed: Arc::new(Vec::new()),
            empty: Arc::new(Vec::new()),
            error: None,
            depth: 0,
            max_depth: 16_384,
            materialized_reuse: self.materialized_capture_roots != 0
                && !self.materialized_capture_failed,
            bound: HashSet::new(),
            pruned: false,
        };
        let scanned = (|| -> Result<(), String> {
            walker.scan(&type_)?;
            walker.scan(&value)?;
            for capture in captures.iter().rev() {
                if !self.base_ids.contains(&capture.local().id())
                    && walker.contains(capture.local().id())
                {
                    walker.scan(capture.local().ty())?;
                    if let OwnedProofCapture::Definition { value, .. } = capture {
                        walker.scan(value)?;
                    }
                    dynamic.push(capture);
                }
            }
            Ok(())
        })();
        drop(walker);
        if let Err(error) = scanned {
            self.materialized_capture_failed = true;
            return Err(error);
        }
        dynamic.reverse();
        if dynamic.len() > self.limits.captures.saturating_sub(self.captures) {
            return Err("component capture limit".into());
        }
        let mut arguments = Vec::new();
        for capture in &dynamic {
            if let OwnedProofCapture::Parameter(local) = capture {
                arguments.push(local.term().clone());
            }
        }
        let mut type_ = type_;
        let mut value = value;
        for capture in dynamic.iter().rev() {
            match capture {
                OwnedProofCapture::Parameter(local) => {
                    type_ = local.pi(type_);
                    value = local.lam(value);
                }
                OwnedProofCapture::Definition {
                    local,
                    value: definition,
                } => {
                    type_ = local.let_(definition.as_ref().clone(), type_);
                    value = local.let_(definition.as_ref().clone(), value);
                }
            }
        }
        let local = allocator.allocate_local(type_)?;
        let reference = Expr::apps(local.term().clone(), arguments);
        self.base_ids.insert(local.id());
        self.bindings.push((local, value));
        self.captures += dynamic.len();
        Ok(reference)
    }
    pub fn retain_definition<A: ScopedLocalAllocator>(
        &mut self,
        allocator: &mut A,
        captures: &[OwnedProofCapture],
        local: &ScopedLocal,
        value: Expr,
    ) -> Result<Arc<Expr>, String> {
        if !allocator.local_scope().owns(local) {
            return Err("foreign retained definition".into());
        }
        if let Some(reference) = self.references.get(&local.id())
            && same_graph(reference, &value)
        {
            return Ok(reference.clone());
        }
        let reference =
            Arc::new(self.bind_scoped(allocator, captures, local.ty().clone(), value)?);
        self.references.insert(local.id(), reference.clone());
        Ok(reference)
    }
    /// Preserve the complete original telescope and all defining values while
    /// closing only internal binders. One interning pass and one aggregate
    /// closure cover every declaration, component, root body and open goal.
    pub fn close_scoped(
        self,
        scope: &LocalScope,
        root: Expr,
        goal: Expr,
        limits: crate::term_scope::TermScopeLimits,
    ) -> Result<ScopedProofComponentBundle, String> {
        self.close_scoped_impl(scope, root, goal, limits, false)
    }

    /// Close a scoped proof with detailed traversal diagnostics on failure.
    pub fn close_scoped_with_diagnostics(
        self,
        scope: &LocalScope,
        root: Expr,
        goal: Expr,
        limits: crate::term_scope::TermScopeLimits,
    ) -> Result<ScopedProofComponentBundle, String> {
        self.close_scoped_impl(scope, root, goal, limits, true)
    }

    fn close_scoped_impl(
        self,
        scope: &LocalScope,
        root: Expr,
        goal: Expr,
        limits: crate::term_scope::TermScopeLimits,
        observe: bool,
    ) -> Result<ScopedProofComponentBundle, String> {
        if !self
            .owner
            .as_ref()
            .is_some_and(|owner| owner.matches(&scope.memo_owner()))
        {
            return Err("scoped proof has another owner".into());
        }
        self.context_work_remaining()?;
        let mut body = root;
        let mut declarations = Vec::new();
        let mut external = Vec::new();
        for capture in &self.base {
            let next = scope
                .component_prefix_body(
                    capture.local(),
                    matches!(capture, OwnedProofCapture::Definition { .. }),
                    &body,
                )
                .ok_or("scoped root prefix mismatch")?;
            let (name, binder, non_dep, type_, value) = match body.kind() {
                clean_kernel::ExprKind::Lam(data, ty, _) => {
                    (Name::anon(), *data, false, ty.as_ref().clone(), None)
                }
                clean_kernel::ExprKind::Let(name, ty, value, _, non_dep) => (
                    name.clone(),
                    clean_kernel::expr::BinderInfo::Default.into(),
                    *non_dep,
                    ty.as_ref().clone(),
                    Some(value.as_ref().clone()),
                ),
                _ => return Err("scoped root prefix kind mismatch".into()),
            };
            declarations.push(ScopedProofDeclaration {
                id: capture.local().id(),
                name,
                binder,
                non_dep,
                type_,
                value,
            });
            external.push(capture.local().clone());
            body = next;
        }
        let outer_count = declarations.len();
        for (local, value) in &self.bindings {
            declarations.push(ScopedProofDeclaration {
                id: local.id(),
                name: Name::from_string(&self.namespace),
                binder: clean_kernel::expr::BinderInfo::Default.into(),
                non_dep: false,
                type_: local.ty().clone(),
                value: Some(value.clone()),
            });
            external.push(local.clone());
        }
        let mut roots = Vec::new();
        let mut root_labels = Vec::new();
        let mut visible = Vec::new();
        for (index, declaration) in declarations.iter().enumerate() {
            roots.push(declaration.type_.clone());
            visible.push(index);
            root_labels.push(format!("declaration {index} {:?} type", declaration.id));
            if let Some(value) = &declaration.value {
                roots.push(value.clone());
                visible.push(index);
                root_labels.push(format!("declaration {index} {:?} value", declaration.id));
            }
        }
        roots.extend([body, goal]);
        visible.extend([declarations.len(), declarations.len()]);
        root_labels.extend(["complete root body".into(), "complete open goal".into()]);
        let prepared = if observe {
            scope
                .intern_external_forest_with_diagnostics(&roots, limits)
                .map_err(|failure| {
                    format!(
                        "scoped part {:?}; preparation diagnostics {failure:?}: {}",
                        root_labels.get(failure.completed_roots),
                        failure.error
                    )
                })?
        } else {
            scope
                .intern_external_forest(&roots, limits)
                .map_err(|error| error.to_string())?
        };
        let (closed, closing, diagnostics) =
            scope.close_external_forest_observed(&prepared.terms, &external, &visible, observe);
        let closed = closed.map_err(|error| {
            let mut message = format!(
                "scoped part {:?}; preparation {:?}; aggregate closure {closing:?}: {error}",
                root_labels.get(closing.completed_roots),
                prepared.stats
            );
            if let Some(diagnostics) = diagnostics {
                message.push_str(&format!("; closure diagnostics {diagnostics:?}"));
            }
            message
        })?;
        let mut terms = closed.into_iter();
        for declaration in &mut declarations {
            declaration.type_ = terms.next().ok_or("missing scoped declaration type")?;
            if declaration.value.is_some() {
                declaration.value = Some(terms.next().ok_or("missing scoped definition value")?);
            }
        }
        let root = terms.next().ok_or("missing complete scoped root")?;
        let goal = terms.next().ok_or("missing complete scoped goal")?;
        if terms.next().is_some() {
            return Err("extra scoped root terms".into());
        }
        Ok(ScopedProofComponentBundle {
            declarations,
            outer_count,
            root,
            goal,
            work: Some(ScopedBuildWork {
                preparation: prepared.stats,
                closing,
            }),
        })
    }
}

#[path = "proof_components_seal.rs"]
mod sealing;
pub use sealing::SealedScopedDefinition;

#[path = "proof_components_instantiate.rs"]
mod instantiation;
pub use instantiation::InstantiatedScopedCandidate;

#[path = "proof_components_materialize.rs"]
mod materialization;

#[path = "proof_components_materialized_definition.rs"]
mod materialized_definition;

#[path = "proof_components_reference_memo.rs"]
mod reference_memo;

#[path = "proof_components_complete_references.rs"]
mod complete_references;

#[cfg(test)]
#[path = "proof_components_combined_budget_tests.rs"]
mod combined_budget_tests;
#[path = "proof_components_generated_references.rs"]
mod generated_references;
#[path = "proof_components_observation_references.rs"]
mod observation_references;
pub(crate) use observation_references::{ConstructedObservation, ObservationReferences};

#[path = "proof_components_substitute.rs"]
mod substitute;

#[path = "proof_components_aliases.rs"]
mod aliases;
pub use aliases::OwnedDefinitionAlias;

#[path = "proof_components_owned_bind.rs"]
mod owned_bind;
pub use owned_bind::OwnedScopedDefinition;

#[path = "proof_components_charged_context.rs"]
mod charged_context;

#[path = "proof_components_bounded_instantiate.rs"]
mod bounded_instantiate;

#[path = "proof_components_external_context.rs"]
mod external_context;
pub(crate) use external_context::ExternalContext;
pub use external_context::ScopedMaterializationContext;

#[cfg(test)]
#[path = "proof_components_complete_references_tests.rs"]
mod complete_reference_tests;

#[cfg(test)]
#[path = "proof_components_materialized_capture_tests.rs"]
mod materialized_capture_tests;

#[cfg(test)]
#[path = "proof_components_inventory_admission_tests.rs"]
mod inventory_admission_tests;
