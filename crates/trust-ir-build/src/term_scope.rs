// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deferred, sharing-preserving closure of named locals in Clean terms.
//!
//! Repeatedly calling `abstract_fvar` while wrapping a growing term visits the
//! accumulated suffix once per binder. [`TermScope`] instead builds ordinary
//! expressions without abstraction, then closes all its binders in one walk.
//! A binder is identified by its fresh, privately retained body `Arc`, not by a
//! serializable name, annotation, or certificate assertion. Clone expressions
//! freely, but do not serialize or otherwise rebuild these open binders before
//! closing them. The result is an ordinary expression with no scope metadata.
//!
//! This is a term-construction utility, **not** proof authority. Consumers must
//! still check the resulting term and its claimed type in the kernel.
//!
//! [`TermScopeLimits`] bounds traversal visits and depth, and consequently the
//! number of memo/context entries. It does not bound aggregate builder storage,
//! arbitrary expression payload bytes (such as universe-level lists), output
//! encoding size, or subsequent kernel normalization. Each distinct input
//! node/binder-context pair is transformed at most once. Shared nodes under
//! different contexts may require different results; no unconditional linear
//! bound in the context-insensitive DAG size is claimed. Unchanged child Arcs
//! are retained; each changed input/context result retains one Arc, reused
//! directly at child edges instead of allocating a shallow root copy per hit.
//! Successfully traversed subgraphs whose OUTPUT is closed are reused across
//! binder contexts. Deferred named binders retain a shared declaration footprint:
//! reuse checks that no declaration would shadow a currently active local.
//! These checks also consume the visit budget; a partial check never admits reuse.
//! Conservative ID envelopes can discharge disjoint declaration subgraphs in
//! constant time after charging their probe. Overlapping envelopes still use
//! the exact declaration traversal; no membership is inferred from overlap.
//! Open results may also be reused at the same binder depth and ordinary-binder
//! count when every external local/index dependency resolves identically. The
//! dependency footprint is a shared DAG, not a copied free-variable set; probes
//! consume the same visit budget and never replace declaration-shadow checks.
//! Candidate retention is bounded to two projections per live input address;
//! a second slot is allocated only when a different projection displaces one.
//! A validated open result may also move outward through ordinary binders when
//! every external read retains its exact output index. Dependency footprints
//! are rebased by a charged DAG walk; named declarations remain scope guards.
//! After the original projection selection misses, declaration-free inputs with
//! no original loose BVars may use one named-only relative probe. Existing
//! outward candidates keep priority; an inward candidate must validate that
//! every external named binding moves by exactly the added parent depth.
//! Internal reads are pruned at cached depth, never at the deeper new parent.
//! Its work is fully charged: additional probes can change a finite-budget refusal prefix,
//! and neither failed work nor previously charged visits are refunded.
//! If that same selected named-only candidate refuses its unchanged-index
//! check, an additional charged proof may establish one common index delta for
//! every external named read. Only original no-loose-BVar, declaration-free
//! inputs qualify. A cutoff-aware exhaustive walk translates completed ordinary
//! output, retaining sharing; no partial proof/output is published or refunded.

use clean_kernel::expr::{BinderData, ExprFolderOpt, ExprKind, FVarId};
use clean_kernel::{Expr, Name};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::num::NonZeroUsize;
use std::sync::Arc;

#[path = "term_scope_census.rs"]
mod census;
pub use census::TermScopeInputKindCounts;

#[path = "term_scope_intern.rs"]
mod intern;
pub use intern::{
    InternedForest, InternedTerm, TermScopeInternFailure, TermScopeInternPhase,
    TermScopeInternStats,
};

#[path = "term_scope_binding_reads.rs"]
mod binding_reads;

#[path = "term_scope_dependency_nodes.rs"]
mod dependency_nodes;
#[path = "term_scope_named_prefix.rs"]
mod named_prefix;
use binding_reads::NamedReads;
use named_prefix::NamedPrefix;

#[path = "term_scope_projection_cache.rs"]
mod projection_cache;
use projection_cache::{ContextCandidates, RebaseMode};

#[path = "term_scope_uniform_shift.rs"]
mod uniform_shift;

#[path = "term_scope_output_nodes.rs"]
mod output_nodes;

#[path = "term_scope_observations.rs"]
mod observations;
use observations::Observations;
pub use observations::{
    TermScopeCacheDiagnostics, TermScopeCacheRoute, TermScopeDiagnostics, TermScopeStop,
    TermScopeStopPhase,
};

/// Monotonic observations of all preparation and closure calls on this thread.
/// These counters do not grant work allowances or change any refusal policy.
#[derive(Clone, Copy, Debug, Default)]
pub struct TermScopeWork {
    pub interning_calls: u64,
    pub interning_visits: u64,
    pub closing_calls: u64,
    pub closing_visits: u64,
}
thread_local! { static TOTAL_WORK: std::cell::Cell<TermScopeWork> = const { std::cell::Cell::new(TermScopeWork { interning_calls: 0, interning_visits: 0, closing_calls: 0, closing_visits: 0 }) }; }
pub fn observed_work() -> TermScopeWork {
    TOTAL_WORK.get()
}
fn record_interning(visits: usize) {
    TOTAL_WORK.with(|total| {
        let mut work = total.get();
        work.interning_calls += 1;
        work.interning_visits += visits as u64;
        total.set(work);
    });
}
fn record_closing(visits: usize) {
    TOTAL_WORK.with(|total| {
        let mut work = total.get();
        work.closing_calls += 1;
        work.closing_visits += visits as u64;
        total.set(work);
    });
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum BinderKind {
    Lambda,
    Pi,
    Let,
}

struct Binding {
    id: FVarId,
    // Keep this allocation alive so its address cannot be recycled.
    _body: Arc<Expr>,
}

/// Builder-owned identities for deferred lambda, Pi, and let binders.
///
/// IDs must identify named locals consistently. Reusing an ID in disjoint
/// scopes is supported; nesting two binders with the same ID is rejected.
/// Registered IDs used outside their binder's body (including its own type or
/// let value) are rejected. Unregistered FVars are left as outer locals.
/// Use `FVar(id)` to refer to a generated binder: preexisting BVars continue to
/// refer to ordinary kernel binders or the outer loose-variable context, and
/// do not count any binders introduced by this builder.
#[derive(Default)]
pub struct TermScope {
    bindings: HashMap<(BinderKind, usize), Binding>,
    registered: HashSet<FVarId>,
}

/// Caller-owned bounds for the closing walk, including DAG-context expansion.
#[derive(Clone, Copy, Debug)]
pub struct TermScopeLimits {
    /// Every traversal request counts, including memo hits and named-declaration
    /// footprint requests needed to validate cross-context reuse.
    pub max_visits: usize,
    /// Maximum actual traversal depth, independent of binder depth. Memoized
    /// subgraphs are not traversed again; this is not total expression height.
    pub max_depth: u32,
}

impl Default for TermScopeLimits {
    fn default() -> Self {
        Self {
            max_visits: 1_000_000,
            max_depth: 16_384,
        }
    }
}

/// Structural work counters; these do not measure kernel normalization cost.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TermScopeStats {
    pub visits: usize,
    /// Distinct input/context nodes examined, including unchanged nodes.
    pub transformed_nodes: usize,
    pub memo_hits: usize,
    /// Cross-context closed-result hits, included in `memo_hits`.
    pub closed_memo_hits: usize,
    /// Declaration-footprint requests, included in `visits`.
    pub scope_check_visits: usize,
    /// External binding-dependency probes, included in `visits`.
    pub context_check_visits: usize,
    /// Maximum binder depth actually traversed, excluding memoized subgraphs.
    pub max_binder_depth: u32,
    /// Successfully closed forest roots before a possible later refusal;
    /// zero for the original single-root API.
    pub completed_roots: usize,
}

pub struct ClosedTerm {
    pub term: Expr,
    pub stats: TermScopeStats,
}

/// The original close result and counters, including partial counters on error.
/// No partial expression is returned when closing refuses.
#[derive(Debug)]
pub struct TermScopeCloseReport {
    pub result: Result<Expr, TermScopeError>,
    pub stats: TermScopeStats,
    pub diagnostics: TermScopeDiagnostics,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TermScopeError {
    OutOfScope(FVarId),
    ShadowedLocal(FVarId),
    IndexOverflow,
    VisitLimit,
    DepthLimit,
}

impl fmt::Display for TermScopeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OutOfScope(id) => {
                write!(f, "registered local {id:?} is outside its binder scope")
            }
            Self::ShadowedLocal(id) => write!(f, "named local {id:?} is bound twice in one scope"),
            Self::IndexOverflow => f.write_str("closed term exceeds Clean's bound-variable range"),
            Self::VisitLimit => f.write_str("term scope traversal visit limit exceeded"),
            Self::DepthLimit => f.write_str("term scope traversal depth limit exceeded"),
        }
    }
}

impl std::error::Error for TermScopeError {}

impl TermScope {
    pub fn new() -> Self {
        Self::default()
    }

    fn body(&mut self, kind: BinderKind, id: FVarId, body: Expr) -> Arc<Expr> {
        let body = Arc::new(body);
        self.bindings.insert(
            (kind, Arc::as_ptr(&body) as usize),
            Binding {
                id,
                _body: body.clone(),
            },
        );
        self.registered.insert(id);
        body
    }

    /// Wrap an open body without traversing or abstracting it.
    pub fn lam(&mut self, id: FVarId, data: impl Into<BinderData>, ty: Expr, body: Expr) -> Expr {
        let body = self.body(BinderKind::Lambda, id, body);
        Expr::lam_arc(data, Arc::new(ty), body)
    }

    /// Wrap an open dependent codomain without traversing or abstracting it.
    pub fn pi(&mut self, id: FVarId, data: impl Into<BinderData>, ty: Expr, body: Expr) -> Expr {
        let body = self.body(BinderKind::Pi, id, body);
        Expr::pi_arc(data, Arc::new(ty), body)
    }

    /// Wrap an open body, preserving the let name and `non_dep` flag exactly.
    pub fn let_named(
        &mut self,
        id: FVarId,
        name: Name,
        ty: Expr,
        value: Expr,
        body: Expr,
        non_dep: bool,
    ) -> Expr {
        let body = self.body(BinderKind::Let, id, body);
        Expr::let_named_arc(name, Arc::new(ty), Arc::new(value), body, non_dep)
    }

    pub(crate) fn component_binder_id(&self, expression: &Expr) -> Option<FVarId> {
        let (kind, body) = match expression.kind() {
            ExprKind::Lam(_, _, body) => (BinderKind::Lambda, body),
            ExprKind::Pi(_, _, body) => (BinderKind::Pi, body),
            ExprKind::Let(_, _, _, body, _) => (BinderKind::Let, body),
            _ => return None,
        };
        self.bindings
            .get(&(kind, Arc::as_ptr(body) as usize))
            .map(|binding| binding.id)
    }

    pub fn close(&self, expression: &Expr) -> Result<Expr, TermScopeError> {
        Ok(self
            .close_with_limits(expression, TermScopeLimits::default())?
            .term)
    }

    pub fn close_with_limits(
        &self,
        expression: &Expr,
        limits: TermScopeLimits,
    ) -> Result<ClosedTerm, TermScopeError> {
        let report = self.close_impl(expression, limits, false);
        report.result.map(|term| ClosedTerm {
            term,
            stats: report.stats,
        })
    }

    /// Close with the same traversal, limits and refusal order, retaining
    /// partial counters on failure. Only this opt-in path allocates the input
    /// address/cached-hash census (at most one entry of each per charged input
    /// visit). There is no prewalk or structural equality check, and these
    /// observations never change traversal accounting or authorize memo reuse.
    pub fn close_with_diagnostics(
        &self,
        expression: &Expr,
        limits: TermScopeLimits,
    ) -> TermScopeCloseReport {
        self.close_impl(expression, limits, true)
    }

    /// Close all internal binders of a scoped artifact with one aggregate
    /// traversal. Explicit external locals retain their original identities;
    /// every other unbound or shadowing local is refused.
    pub fn close_external_forest(
        &self,
        expressions: &[Expr],
        external: &[FVarId],
        visible: &[usize],
        limits: TermScopeLimits,
    ) -> (Result<Vec<Expr>, TermScopeError>, TermScopeStats) {
        let (result, stats, _) =
            self.close_external_forest_impl(expressions, external, visible, limits, false, false);
        (result, stats)
    }

    /// Close an external forest and collect cache and traversal diagnostics.
    pub fn close_external_forest_with_diagnostics(
        &self,
        expressions: &[Expr],
        external: &[FVarId],
        visible: &[usize],
        limits: TermScopeLimits,
    ) -> (
        Result<Vec<Expr>, TermScopeError>,
        TermScopeStats,
        TermScopeDiagnostics,
    ) {
        self.close_external_forest_impl(expressions, external, visible, limits, true, false)
    }

    /// Materialize every input/context node and enforce complete subtree
    /// heights, for a consumer that must subsequently substitute ordinary BVars.
    /// Uses the same binder translation and external visibility rules as close.
    pub(crate) fn close_external_forest_fully(
        &self,
        expressions: &[Expr],
        external: &[FVarId],
        visible: &[usize],
        limits: TermScopeLimits,
    ) -> (Result<Vec<Expr>, TermScopeError>, TermScopeStats) {
        let (result, stats, _) =
            self.close_external_forest_impl(expressions, external, visible, limits, false, true);
        (result, stats)
    }

    /// Complete walk under one immutable, already owned external inventory.
    /// Every root has the SAME full visibility. Optional owned-prefix reuse
    /// admits only fully walked unchanged ordinary/named-free graphs.
    pub(crate) fn close_prepared_external_forest_fully(
        &self,
        expressions: &[Expr],
        external: &HashSet<FVarId>,
        limits: TermScopeLimits,
        reuse: Option<fully::FullScopeReuse<'_>>,
    ) -> (Result<Vec<Expr>, TermScopeError>, TermScopeStats) {
        let mut folder = Closer::new(self, limits, false);
        folder.strict_external = true;
        folder.full = Some(Box::default());
        folder.borrowed_external = Some(external);
        folder.ordinary_reuse = reuse;
        if limits.max_depth >= (1 << 31) {
            record_closing(0);
            return (Err(TermScopeError::DepthLimit), folder.stats);
        }
        let mut output = Vec::with_capacity(expressions.len());
        for expression in expressions {
            folder.dependency = None;
            folder.footprint = None;
            if let Some(full) = folder.full.as_mut() {
                full.height = 0;
                full.deferred = false;
                full.prefix = 0;
            }
            let term = expression.fold_opt_or_clone(&mut folder);
            if let Some(error) = folder.error.clone() {
                record_closing(folder.stats.visits);
                return (Err(error), folder.stats);
            }
            output.push(term);
            folder.stats.completed_roots += 1;
        }
        record_closing(folder.stats.visits);
        (Ok(output), folder.stats)
    }

    fn close_external_forest_impl(
        &self,
        expressions: &[Expr],
        external: &[FVarId],
        visible: &[usize],
        limits: TermScopeLimits,
        observe: bool,
        fully_traversed: bool,
    ) -> (
        Result<Vec<Expr>, TermScopeError>,
        TermScopeStats,
        TermScopeDiagnostics,
    ) {
        let mut folder = Closer::new(self, limits, observe);
        folder.strict_external = true;
        folder.full = fully_traversed.then(Box::default);
        if expressions.len() != visible.len() || limits.max_depth >= (1 << 31) {
            record_closing(folder.stats.visits);
            return (
                Err(TermScopeError::DepthLimit),
                folder.stats,
                folder.diagnostic_report(),
            );
        }
        let mut admitted = 0;
        let mut output = Vec::with_capacity(expressions.len());
        for (expression, &count) in expressions.iter().zip(visible) {
            if count < admitted || count > external.len() {
                record_closing(folder.stats.visits);
                return (
                    Err(TermScopeError::DepthLimit),
                    folder.stats,
                    folder.diagnostic_report(),
                );
            }
            for &id in &external[admitted..count] {
                folder.external.insert(id);
                // External variables retain FVars, never de Bruijn depths. A
                // disjoint sentinel prevents old internal-read projections
                // from equating one with a subsequently admitted external.
                // Admission occurs between roots, with an empty lexical
                // stack. It cannot replace a live lexical binder.
                debug_assert!(folder.context_stack.is_empty());
                folder.active.insert_scoped(id, 1 << 31);
                folder.active_envelope = Some(match folder.active_envelope {
                    Some(envelope) => envelope.union(IdEnvelope::singleton(id)),
                    None => IdEnvelope::singleton(id),
                });
                folder.context =
                    folder.intern_context(folder.context, ContextFrame::External(id), Some(0));
            }
            admitted = count;
            folder.dependency = None;
            folder.footprint = None;
            if let Some(full) = folder.full.as_mut() {
                full.height = 0;
                full.prefix = 0;
            }
            let term = expression.fold_opt_or_clone(&mut folder);
            if let Some(error) = folder.error.clone() {
                record_closing(folder.stats.visits);
                return (Err(error), folder.stats, folder.diagnostic_report());
            }
            output.push(term);
            folder.stats.completed_roots += 1;
        }
        record_closing(folder.stats.visits);
        (Ok(output), folder.stats, folder.diagnostic_report())
    }

    fn close_impl(
        &self,
        expression: &Expr,
        limits: TermScopeLimits,
        diagnose: bool,
    ) -> TermScopeCloseReport {
        let mut folder = Closer::new(self, limits, diagnose);
        let term = expression.fold_opt_or_clone(&mut folder);
        record_closing(folder.stats.visits);
        let diagnostics = folder.diagnostic_report();
        TermScopeCloseReport {
            result: match folder.error {
                Some(error) => Err(error),
                None => Ok(term),
            },
            stats: folder.stats,
            diagnostics,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Frame {
    Ordinary,
    Named(FVarId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum ContextFrame {
    Ordinary,
    Named(FVarId),
    External(FVarId),
}

impl From<Frame> for ContextFrame {
    fn from(frame: Frame) -> Self {
        match frame {
            Frame::Ordinary => Self::Ordinary,
            Frame::Named(id) => Self::Named(id),
        }
    }
}

#[derive(Clone)]
struct MemoEntry {
    replacement: Option<Arc<Expr>>,
    // One-based private storage keeps None and a live arena index in one word.
    // Decoding does not authenticate an index or change arena ownership.
    declarations: Option<NonZeroUsize>,
    dependencies: Option<NonZeroUsize>,
}

impl MemoEntry {
    fn compact(index: Option<usize>) -> Option<NonZeroUsize> {
        index.map(|index| {
            index
                .checked_add(1)
                .and_then(NonZeroUsize::new)
                .expect("a live arena index fits the one-based memo representation")
        })
    }

    fn declarations(&self) -> Option<usize> {
        self.declarations.map(|index| index.get() - 1)
    }

    fn dependencies(&self) -> Option<usize> {
        self.dependencies.map(|index| index.get() - 1)
    }
}

#[derive(Clone)]
struct ContextEntry {
    entry: MemoEntry,
    context: usize,
    binder_depth: u32,
    ordinary_count: usize,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Dependency {
    Named(FVarId, u32),
    Ordinary(usize, u32),
    Join(usize, usize),
}

struct DependencyNode {
    dependency: Dependency,
    // Dependencies bound at/under a subtree's entry depth are internal to it.
    min_depth: u32,
    last_probe: usize,
    named_prefix: Option<NamedPrefix>,
}

#[derive(Clone)]
struct ClosedEntry {
    entry: MemoEntry,
    // One last validated context, not a new table indexed by every context.
    // Repeated hits in that context need no repeated declaration probe.
    context: usize,
}

#[derive(Clone, Copy)]
enum Declarations {
    Local(FVarId),
    Join(usize, usize),
}

/// Conservative envelope of a nonempty set of named IDs. Comparisons require
/// no arithmetic or allocator-order assumptions; gaps are deliberately retained.
#[derive(Clone, Copy)]
struct IdEnvelope {
    min: FVarId,
    max: FVarId,
}

impl IdEnvelope {
    fn singleton(id: FVarId) -> Self {
        Self { min: id, max: id }
    }

    fn union(self, other: Self) -> Self {
        Self {
            min: self.min.min(other.min),
            max: self.max.max(other.max),
        }
    }

    fn is_disjoint(self, other: Self) -> bool {
        self.max < other.min || other.max < self.min
    }
}

struct Footprint {
    declarations: Declarations,
    last_probe: usize,
    // Two IDs per arena entry, never a copied or expanded declaration set.
    envelope: IdEnvelope,
}

struct Closer<'a> {
    scope: &'a TermScope,
    full: Option<Box<fully::FullTraversal>>,
    ordinary_reuse: Option<fully::FullScopeReuse<'a>>,
    external: HashSet<FVarId>,
    borrowed_external: Option<&'a HashSet<FVarId>>,
    strict_external: bool,
    limits: TermScopeLimits,
    stats: TermScopeStats,
    error: Option<TermScopeError>,
    memo: HashMap<(usize, usize), MemoEntry>,
    // Keep the compact unchanged-ordinary cache: most closed data has no
    // declarations or replacement to retain. Input addresses remain live.
    closed: HashSet<usize>,
    // Entries have exhaustively traversed, closed outputs. A named footprint
    // still needs scope validation in a different context.
    named_closed: HashMap<usize, ClosedEntry>,
    // Bounded candidate projections, not scope authority. No cache outlives close.
    contextual: ContextCandidates,
    // Completed uniform translations and their one-hop composition witnesses.
    // All owners and coordinates are exact; neither table is scope authority.
    shifted_outputs: HashMap<uniform_shift::OutputShiftKey, uniform_shift::CompletedOutputShift>,
    named_outputs: HashMap<(usize, u32), uniform_shift::CompletedNamedOutput>,
    shift_origins: HashMap<(usize, u32), uniform_shift::OutputShiftOrigin>,
    output_nodes: output_nodes::OutputNodes,
    dependencies: Vec<DependencyNode>,
    dependency_nodes: HashMap<Dependency, usize>,
    dependency: Option<usize>,
    // Arena DAGs share descendant declarations instead of copying a growing set
    // at every ancestor. Integer edges also make destruction non-recursive.
    footprints: Vec<Footprint>,
    footprint: Option<usize>,
    probe_stack: Vec<usize>,
    // Exact context identity includes external visibility and binder kind.
    contexts: HashMap<(usize, ContextFrame), usize>,
    context: usize,
    // Forest-only projection, indexed by full context ID minus one. Retain
    // one word per context, not a second context key per expression memo.
    lexical_contexts: Vec<usize>,
    // One live stack of lexical prefixes, excluding admitted externals.
    context_stack: Vec<(usize, Frame)>,
    // One lazy canonical read handle per LIVE named binding, not a new map.
    active: NamedReads,
    // Saved/restored at binders, so leaving a min/max ID needs no set scan.
    active_envelope: Option<IdEnvelope>,
    ordinary: Vec<u32>,
    binder_depth: u32,
    walk_depth: u32,
    // None on legacy close paths: no observer or input-census allocation.
    observations: Option<Box<Observations>>,
}

impl Closer<'_> {
    fn is_external(&self, id: &FVarId) -> bool {
        self.borrowed_external
            .unwrap_or(&self.external)
            .contains(id)
    }
    fn intern_context(
        &mut self,
        parent: usize,
        frame: ContextFrame,
        lexical: Option<usize>,
    ) -> usize {
        let next = self.contexts.len() + 1;
        *self.contexts.entry((parent, frame)).or_insert_with(|| {
            if self.strict_external {
                debug_assert_eq!(self.lexical_contexts.len() + 1, next);
                self.lexical_contexts.push(lexical.unwrap_or(next));
            }
            next
        })
    }

    fn same_forest_lexical_context(&self, cached: usize) -> bool {
        let lexical = |id: usize| {
            id.checked_sub(1)
                .and_then(|index| self.lexical_contexts.get(index))
        };
        self.strict_external
            && self.active.stack_consistent()
            && lexical(cached)
                .zip(lexical(self.context))
                .is_some_and(|(a, b)| a == b)
    }

    fn dependency_node(&mut self, dependency: Dependency) -> usize {
        let min_depth = match dependency {
            Dependency::Named(_, depth) | Dependency::Ordinary(_, depth) => depth,
            Dependency::Join(left, right) => self.dependencies[left]
                .min_depth
                .min(self.dependencies[right].min_depth),
        };
        let named_prefix = self.dependency_named_prefix(dependency);
        let index = self.dependencies.len();
        self.dependencies.push(DependencyNode {
            dependency,
            min_depth,
            last_probe: 0,
            named_prefix,
        });
        index
    }

    fn same_dependency_value(&self, left: usize, right: usize) -> bool {
        left == right || self.dependencies[left].dependency == self.dependencies[right].dependency
    }

    fn immediate_dependency_member(&self, root: usize, incoming: usize) -> bool {
        self.same_dependency_value(root, incoming)
            || match self.dependencies[root].dependency {
                Dependency::Join(left, right) => {
                    self.same_dependency_value(left, incoming)
                        || self.same_dependency_value(right, incoming)
                }
                _ => false,
            }
    }

    fn immediate_dependency_subset(&self, root: usize, incoming: usize) -> bool {
        self.immediate_dependency_member(root, incoming)
            || match self.dependencies[incoming].dependency {
                Dependency::Join(left, right) => {
                    self.immediate_dependency_member(root, left)
                        && self.immediate_dependency_member(root, right)
                }
                _ => false,
            }
    }

    fn union_dependencies(&mut self, left: usize, right: usize) -> usize {
        // This is bounded construction bookkeeping, not a probe or cache.
        // Exact child identities/values prove absorption of a redundant union:
        // (A union B) union A and (A union B) union (B union A).
        // No recursive set search, copied footprint, or additional storage.
        // Keep the left probe prefix: retaining a covering RIGHT root could
        // move a first failing left read later and waste a finite probe budget.
        // A retained footprint still goes through every existing charged
        // exact/relative/declaration guard when a context attempts reuse.
        if self.same_dependency_value(left, right) {
            right
        } else if self.immediate_dependency_subset(left, right) {
            left
        } else {
            self.intern_dependency_node(Dependency::Join(left, right))
        }
    }

    fn include_dependency(&mut self, incoming: Option<usize>) {
        if let Some(incoming) = incoming {
            self.dependency = Some(match self.dependency {
                Some(previous) => self.union_dependencies(previous, incoming),
                None => incoming,
            });
        }
    }

    fn visit(&mut self) -> bool {
        if self.stats.visits >= self.limits.max_visits {
            self.fail(TermScopeError::VisitLimit);
            false
        } else {
            self.stats.visits += 1;
            true
        }
    }

    fn declarations(&mut self, declarations: Declarations) -> usize {
        let envelope = match declarations {
            Declarations::Local(id) => IdEnvelope::singleton(id),
            Declarations::Join(left, right) => self.footprints[left]
                .envelope
                .union(self.footprints[right].envelope),
        };
        let index = self.footprints.len();
        self.footprints.push(Footprint {
            declarations,
            last_probe: 0,
            envelope,
        });
        index
    }

    fn include(&mut self, incoming: Option<usize>) {
        if let Some(incoming) = incoming {
            self.footprint = Some(match self.footprint {
                Some(previous) if previous != incoming => {
                    self.declarations(Declarations::Join(previous, incoming))
                }
                _ => incoming,
            });
        }
    }

    fn fail(&mut self, error: TermScopeError) -> Option<Expr> {
        if self.error.is_none() {
            self.observe_stop(&error);
        }
        self.error.get_or_insert(error);
        None
    }

    fn index(&mut self, index: Option<u32>) -> Option<Expr> {
        match index {
            Some(index) if index <= Expr::MAX_BVAR_INDEX => Some(Expr::bvar(index)),
            _ => self.fail(TermScopeError::IndexOverflow),
        }
    }

    fn under(&mut self, frame: Frame, body: &Expr) -> Option<Arc<Expr>> {
        self.observe_phase(TermScopeStopPhase::BinderEntry);
        if self.error.is_some() {
            return None;
        }
        if self.binder_depth > Expr::MAX_BVAR_INDEX {
            self.fail(TermScopeError::IndexOverflow);
            return None;
        }
        let old_envelope = self.active_envelope;
        match frame {
            Frame::Named(id) => {
                if self.active.contains_key(&id) || self.is_external(&id) {
                    self.fail(TermScopeError::ShadowedLocal(id));
                    return None;
                }
                self.active.insert_scoped(id, self.binder_depth);
                self.active_envelope = Some(match old_envelope {
                    Some(active) => active.union(IdEnvelope::singleton(id)),
                    None => IdEnvelope::singleton(id),
                });
                let declaration = self.declarations(Declarations::Local(id));
                self.include(Some(declaration));
            }
            Frame::Ordinary => self.ordinary.push(self.binder_depth),
        }
        let old_context = self.context;
        let lexical_parent = if self.strict_external {
            self.context_stack.last().map_or(0, |(id, _)| *id)
        } else {
            old_context
        };
        let context_frame = ContextFrame::from(frame);
        let lexical = self.intern_context(lexical_parent, context_frame, None);
        self.context = if lexical_parent == old_context {
            lexical
        } else {
            self.intern_context(old_context, context_frame, Some(lexical))
        };
        self.context_stack.push((lexical, frame));
        self.binder_depth += 1;
        self.stats.max_binder_depth = self.stats.max_binder_depth.max(self.binder_depth);
        let result = self.fold_shared(body);
        self.binder_depth -= 1;
        self.context_stack.pop();
        self.context = old_context;
        self.active_envelope = old_envelope;
        match frame {
            Frame::Named(id) => {
                self.active.remove_scoped(&id);
            }
            Frame::Ordinary => {
                self.ordinary.pop();
            }
        }
        result
    }

    fn named(&self, kind: BinderKind, body: &Arc<Expr>) -> Option<FVarId> {
        self.scope
            .bindings
            .get(&(kind, Arc::as_ptr(body) as usize))
            .map(|binding| binding.id)
    }

    fn node(&mut self, expression: &Expr) -> Option<Expr> {
        match expression.kind() {
            ExprKind::Lam(data, ty, body) => {
                if let Some(id) = self.named(BinderKind::Lambda, body) {
                    let ty_new = self.fold_expr_arc_opt(ty);
                    let body_new = self.under(Frame::Named(id), body);
                    // The original body Arc carries this scope's deferred
                    // binder identity, even if the binder is unused. Closed
                    // output must not retain it: consumers may re-embed that
                    // ordinary term in this same scope. Detach only an
                    // unchanged body root; changed bodies and memo hits keep
                    // their existing sharing. Input scope checks stay above.
                    Some(Expr::lam_arc(
                        *data,
                        replacement(ty, ty_new),
                        body_new.unwrap_or_else(|| Arc::new(body.as_ref().clone())),
                    ))
                } else {
                    self.fold_expr_opt_inner(expression)
                }
            }
            ExprKind::Pi(data, ty, body) => {
                if let Some(id) = self.named(BinderKind::Pi, body) {
                    let ty_new = self.fold_expr_arc_opt(ty);
                    let body_new = self.under(Frame::Named(id), body);
                    Some(Expr::pi_arc(
                        *data,
                        replacement(ty, ty_new),
                        body_new.unwrap_or_else(|| Arc::new(body.as_ref().clone())),
                    ))
                } else {
                    self.fold_expr_opt_inner(expression)
                }
            }
            ExprKind::Let(name, ty, value, body, non_dep) => {
                if let Some(id) = self.named(BinderKind::Let, body) {
                    let ty_new = self.fold_expr_arc_opt(ty);
                    let value_new = self.fold_expr_arc_opt(value);
                    let body_new = self.under(Frame::Named(id), body);
                    Some(Expr::let_named_arc(
                        name.clone(),
                        replacement(ty, ty_new),
                        replacement(value, value_new),
                        body_new.unwrap_or_else(|| Arc::new(body.as_ref().clone())),
                        *non_dep,
                    ))
                } else {
                    self.fold_expr_opt_inner(expression)
                }
            }
            // Clean's exhaustive visitor owns all other syntax, including
            // cubical and ZFC binders, via fold_binder_body_opt below.
            _ => self.fold_expr_opt_inner(expression),
        }
    }
}

fn replacement(original: &Arc<Expr>, changed: Option<Arc<Expr>>) -> Arc<Expr> {
    changed.unwrap_or_else(|| original.clone())
}

// Keep Clean's public folder entry point as the recursion boundary: its
// default fold_expr_opt supplies Clean's stack-growth protection. Overriding
// only the inner dispatch here avoids silently losing that protection when
// the memoizing Closer overrides fold_expr_opt.
struct StackBoundary<'a, 'b>(&'a mut Closer<'b>);

impl ExprFolderOpt for StackBoundary<'_, '_> {
    fn fold_expr_opt_inner(&mut self, expression: &Expr) -> Option<Expr> {
        self.0.node(expression)
    }
}

impl Closer<'_> {
    /// Retain the changed root allocation as well as its descendant sharing.
    /// The legacy Expr-returning hook clones only at its API boundary; child
    /// hooks pass this exact Arc through the visitor and named-binder paths.
    fn fold_shared(&mut self, expression: &Expr) -> Option<Arc<Expr>> {
        if self.full.is_some() {
            return self.fold_shared_fully(expression);
        }
        if self.error.is_some() {
            return None;
        }
        self.observe_phase(TermScopeStopPhase::Expression);
        if !self.visit() {
            return None;
        }
        self.observe_input(expression);
        if self.walk_depth >= self.limits.max_depth {
            self.fail(TermScopeError::DepthLimit);
            return None;
        }
        let address = expression as *const Expr as usize;
        if self.closed.contains(&address) {
            self.observe_route(TermScopeCacheRoute::OrdinaryClosed);
            self.stats.memo_hits += 1;
            self.stats.closed_memo_hits += 1;
            return None;
        }
        // Prefer the exact context: its scope checks have already succeeded.
        let key = (address, self.context);
        if let Some(entry) = self.memo.get(&key).cloned() {
            self.observe_route(TermScopeCacheRoute::ExactContext);
            self.stats.memo_hits += 1;
            self.include(entry.declarations());
            self.include_dependency(entry.dependencies());
            return entry.replacement;
        }
        if let Some(mut closed) = self.named_closed.get(&address).cloned() {
            self.observe_named_candidate();
            if closed.context == self.context || self.reusable(closed.entry.declarations()) {
                self.observe_route(TermScopeCacheRoute::NamedClosed);
                self.stats.memo_hits += 1;
                self.stats.closed_memo_hits += 1;
                self.include(closed.entry.declarations());
                closed.context = self.context;
                let result = closed.entry.replacement.clone();
                self.named_closed.insert(address, closed);
                return result;
            }
            if self.error.is_some() {
                return None;
            }
        }
        self.observe_candidate(address, expression);
        let candidate = self
            .contextual
            .get(address, self.binder_depth, self.ordinary.len())
            .map(|entry| (entry.clone(), None))
            .or_else(|| {
                self.contextual
                    .named_only(address, self.binder_depth, expression)
                    .map(|(entry, route)| (entry.clone(), Some(route)))
            });
        if let Some((mut cached, named_only_route)) = candidate {
            // Rebased dependency IDs remain private to this attempt until
            // both guards succeed below. Rejecting either guard must not
            // retain that unpublished suffix across later cache attempts.
            let dependency_checkpoint = self.dependencies.len();
            let exact = cached.binder_depth == self.binder_depth
                && cached.ordinary_count == self.ordinary.len();
            let mut dependencies = if let Some(route) = named_only_route {
                self.observe_named_only_candidate(route, &cached);
                self.relative_dependencies(&cached, RebaseMode::NamedOnly)
            } else if exact {
                self.same_cached_dependencies(&cached)
                    .then_some(cached.entry.dependencies())
            } else {
                self.relative_dependencies(&cached, RebaseMode::Ordinary)
            };
            let mut output_projection = None;
            if named_only_route.is_some() && dependencies.is_none() && self.error.is_none() {
                // The failed old probe is paid but its private arena suffix
                // must not survive even a subsequently successful shift.
                self.truncate_dependencies(dependency_checkpoint);
                if let Some((entry, mapped)) = self.named_output_projection(&cached, expression) {
                    cached.entry = entry;
                    dependencies = Some(cached.entry.dependencies());
                    output_projection = Some(mapped);
                }
            }
            if let Some(dependencies) = dependencies
                && (cached.context == self.context || self.reusable(cached.entry.declarations()))
            {
                self.observe_contextual_hit(named_only_route.is_some());
                match output_projection {
                    Some(true) => self
                        .observe_named_projection(observations::OutputProjectionObservation::Hit),
                    Some(false) => {
                        self.observe_uniform_shift(observations::OutputProjectionObservation::Hit)
                    }
                    None => {}
                }
                self.stats.memo_hits += 1;
                self.include(cached.entry.declarations());
                self.include_dependency(dependencies);
                // This exact context has now passed the same checks as a
                // transformed entry. Retain its alias before another context
                // displaces this contextual candidate. The Arc and arena
                // Declaration IDs and the output Arc remain shared; an
                // outward hit carries the newly validated dependency IDs.
                cached.entry.dependencies = MemoEntry::compact(dependencies);
                self.memo.insert(key, cached.entry.clone());
                cached.context = self.context;
                cached.binder_depth = self.binder_depth;
                cached.ordinary_count = self.ordinary.len();
                let result = cached.entry.replacement.clone();
                self.contextual.insert(address, cached);
                return result;
            }
            self.observe_contextual_rejection();
            self.truncate_dependencies(dependency_checkpoint);
            if self.error.is_some() {
                return None;
            }
        }
        let parent_footprint = self.footprint.take();
        let parent_dependency = self.dependency.take();
        self.walk_depth += 1;
        let result = StackBoundary(self).fold_expr_opt(expression).map(Arc::new);
        self.walk_depth -= 1;
        let result = if self.error.is_none() {
            result.map(|node| self.intern_output_node(node))
        } else {
            result
        };
        let declarations = self.footprint.take();
        let dependencies = self
            .dependency
            .take()
            .filter(|index| self.dependencies[*index].min_depth < self.binder_depth);
        self.footprint = parent_footprint;
        self.dependency = parent_dependency;
        self.include(declarations);
        self.include_dependency(dependencies);
        if self.error.is_none() {
            self.stats.transformed_nodes += 1;
            let output = result.as_deref().unwrap_or(expression);
            let entry = MemoEntry {
                replacement: result.clone(),
                declarations: MemoEntry::compact(declarations),
                dependencies: MemoEntry::compact(dependencies),
            };
            if !output.has_fvar_quick() && !output.has_loose_bvars_quick() {
                if declarations.is_none() && result.is_none() {
                    self.closed.insert(address);
                } else {
                    self.named_closed.insert(
                        address,
                        ClosedEntry {
                            entry,
                            context: self.context,
                        },
                    );
                }
            } else {
                self.memo.insert(key, entry.clone());
                self.contextual.insert(
                    address,
                    ContextEntry {
                        entry,
                        context: self.context,
                        binder_depth: self.binder_depth,
                        ordinary_count: self.ordinary.len(),
                    },
                );
            }
        }
        result
    }
}

impl ExprFolderOpt for Closer<'_> {
    fn fold_expr_opt(&mut self, expression: &Expr) -> Option<Expr> {
        self.fold_shared(expression)
            .map(|replacement| replacement.as_ref().clone())
    }

    fn fold_expr_arc_opt(&mut self, expression: &Arc<Expr>) -> Option<Arc<Expr>> {
        self.fold_shared(expression)
    }

    fn fold_fvar_opt(&mut self, id: FVarId) -> Option<Expr> {
        if let Some(full) = self.full.as_mut() {
            full.include_fvars(Some(IdEnvelope::singleton(id)));
        }
        self.observe_phase(TermScopeStopPhase::Expression);
        // The exact owned inventory's index replaces the existing external
        // membership probe; no second lookup or caller-supplied read receipt.
        let external = if let Some(reuse) = &self.ordinary_reuse {
            if let Some(&position) = reuse.positions.get(&id) {
                if let Some(full) = self.full.as_mut() {
                    let prefix = if position < reuse.initial_len {
                        0
                    } else {
                        position - reuse.initial_len + 1
                    };
                    full.prefix = full.prefix.max(prefix);
                }
                true
            } else {
                false
            }
        } else {
            self.is_external(&id)
        };
        if external {
            return None;
        }
        if let Some(depth) = self.active.get(&id).copied() {
            let dependency = self.named_read_dependency(id, depth);
            self.include_dependency(Some(dependency));
            self.index(self.binder_depth.checked_sub(depth + 1))
        } else if self.scope.registered.contains(&id) || self.strict_external {
            self.fail(TermScopeError::OutOfScope(id))
        } else {
            None
        }
    }

    fn fold_bvar_opt(&mut self, index: u32) -> Option<Expr> {
        self.observe_phase(TermScopeStopPhase::Expression);
        // Input BVars refer only to original, ordinary binders. Newly
        // introduced named binders must not capture them, including when an
        // ordinary binder and a named binder are interleaved.
        let ordinary_count = self.ordinary.len() as u32;
        let translated = if index < ordinary_count {
            let position = (ordinary_count - 1 - index) as usize;
            let depth = self.ordinary[position];
            let dependency = self.dependency_node(Dependency::Ordinary(position, depth));
            self.include_dependency(Some(dependency));
            self.binder_depth.checked_sub(depth + 1)
        } else {
            index.checked_add(self.binder_depth - ordinary_count)
        };
        if translated == Some(index) {
            None
        } else {
            self.index(translated)
        }
    }

    fn fold_binder_body_opt(&mut self, expression: &Expr) -> Option<Expr> {
        self.under(Frame::Ordinary, expression)
            .map(|replacement| replacement.as_ref().clone())
    }

    fn fold_binder_body_arc_opt(&mut self, expression: &Arc<Expr>) -> Option<Arc<Expr>> {
        self.under(Frame::Ordinary, expression)
    }
}

#[cfg(test)]
#[path = "term_scope_memo_storage_tests.rs"]
mod memo_storage_tests;

#[path = "term_scope_fully.rs"]
mod fully;
pub(crate) use fully::{CompleteFVarEnvelope, FullScopeCache, FullScopeReuse};

#[cfg(test)]
#[path = "term_scope_diagnostics_tests.rs"]
mod diagnostics_tests;

#[cfg(test)]
#[path = "term_scope_observation_tests.rs"]
mod observation_tests;

#[cfg(test)]
#[path = "term_scope_named_only_tests.rs"]
mod named_only_tests;

#[cfg(test)]
#[path = "term_scope_named_only_inward_tests.rs"]
mod named_only_inward_tests;

#[cfg(test)]
#[path = "term_scope_named_only_depth_screen_tests.rs"]
mod named_only_depth_screen_tests;

#[cfg(test)]
#[path = "term_scope_ordinary_depth_screen_tests.rs"]
mod ordinary_depth_screen_tests;

#[cfg(test)]
#[path = "term_scope_relative_leaf_tests.rs"]
mod relative_leaf_tests;

#[cfg(test)]
#[path = "term_scope_exact_leaf_tests.rs"]
mod exact_leaf_tests;

#[cfg(test)]
#[path = "term_scope_named_projection_oracle_tests.rs"]
mod named_projection_oracle_tests;

#[cfg(test)]
#[path = "term_scope_rejection_tests.rs"]
mod rejection_tests;

#[cfg(test)]
#[path = "term_scope_closed_tests.rs"]
mod closed_tests;

#[cfg(test)]
#[path = "term_scope_named_closed_tests.rs"]
mod named_closed_tests;

#[cfg(test)]
#[path = "term_scope_named_guard_tests.rs"]
mod named_guard_tests;

#[cfg(test)]
#[path = "term_scope_envelope_tests.rs"]
mod envelope_tests;

#[cfg(test)]
#[path = "term_scope_context_tests.rs"]
mod context_tests;

#[cfg(test)]
#[path = "term_scope_idempotent_dependency_tests.rs"]
mod idempotent_dependency_tests;

#[cfg(test)]
#[path = "term_scope_dependency_absorption_tests.rs"]
mod dependency_absorption_tests;

#[cfg(test)]
#[path = "term_scope_binding_read_tests.rs"]
mod binding_read_tests;

#[cfg(test)]
#[path = "term_scope_projection_tests.rs"]
mod projection_tests;

#[cfg(test)]
#[path = "term_scope_relative_context_tests.rs"]
mod relative_context_tests;

#[cfg(test)]
#[path = "term_scope_arc_tests.rs"]
mod arc_tests;

#[cfg(test)]
#[path = "term_scope_output_identity_tests.rs"]
mod output_identity_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::env::Environment;
    use clean_kernel::expr::{Multiplicity, ZFCSetExpr};
    use clean_kernel::{BinderInfo, TypeChecker};

    fn id(n: u64) -> FVarId {
        FVarId::new(n)
    }

    fn old_lam(id: FVarId, ty: Expr, body: Expr) -> Expr {
        Expr::lam(BinderInfo::Default, ty, body.abstract_fvar(id))
    }

    #[test]
    fn mixed_dependent_telescope_matches_repeated_abstraction_and_kernel_checks() {
        let mut scope = TermScope::new();
        let (a, x, y) = (id(1), id(2), id(3));
        let name = Name::from_string("retainedLetName");
        let body = scope.let_named(
            y,
            name.clone(),
            Expr::fvar(a),
            Expr::fvar(x),
            Expr::fvar(y),
            false,
        );
        let body = scope.lam(x, BinderInfo::Default, Expr::fvar(a), body);
        let body = scope.lam(a, BinderInfo::Default, Expr::type_(), body);
        let expected = old_lam(
            a,
            Expr::type_(),
            old_lam(
                x,
                Expr::fvar(a),
                Expr::let_named(
                    name,
                    Expr::fvar(a),
                    Expr::fvar(x),
                    Expr::fvar(y).abstract_fvar(y),
                    false,
                ),
            ),
        );
        let closed = scope.close(&body).unwrap();
        assert_eq!(closed, expected);

        let ty = scope.pi(x, BinderInfo::Default, Expr::fvar(a), Expr::fvar(a));
        let ty = scope.pi(a, BinderInfo::Default, Expr::type_(), ty);
        let ty = scope.close(&ty).unwrap();
        let env = Environment::new();
        TypeChecker::new(&env).check_type(&closed, &ty).unwrap();
    }

    #[test]
    fn one_builder_closes_multiple_roots_repeatedly_without_mutating_inputs() {
        let mut scope = TermScope::new();
        let (a, x) = (id(1), id(2));
        let proof = scope.lam(x, BinderInfo::Default, Expr::fvar(a), Expr::fvar(x));
        let proof = scope.lam(a, BinderInfo::Default, Expr::type_(), proof);
        let claim = scope.pi(x, BinderInfo::Default, Expr::fvar(a), Expr::fvar(a));
        let claim = scope.pi(a, BinderInfo::Default, Expr::type_(), claim);
        let proof_before = proof.clone();
        let claim_before = claim.clone();
        let closed_proof = scope.close(&proof).unwrap();
        let closed_claim = scope.close(&claim).unwrap();
        assert_eq!(scope.close(&proof).unwrap(), closed_proof);
        assert_eq!(scope.close(&claim).unwrap(), closed_claim);
        assert_eq!(scope.close(&closed_proof).unwrap(), closed_proof);
        assert_eq!(scope.close(&closed_claim).unwrap(), closed_claim);
        assert_eq!(proof, proof_before);
        assert_eq!(claim, claim_before);
        let env = Environment::new();
        TypeChecker::new(&env)
            .check_type(&closed_proof, &closed_claim)
            .unwrap();
    }

    #[test]
    fn preserves_binder_data_and_let_metadata() {
        let mut scope = TermScope::new();
        let data = BinderData::new(BinderInfo::InstImplicit, Multiplicity::Zero);
        let name = Name::from_string("exact.name");
        let body = scope.let_named(
            id(2),
            name.clone(),
            Expr::type_(),
            Expr::fvar(id(1)),
            Expr::fvar(id(1)),
            true,
        );
        let body = scope.pi(id(1), data, Expr::type_(), body);
        let closed = scope.close(&body).unwrap();
        let ExprKind::Pi(actual_data, _, body) = closed.kind() else {
            panic!("Pi")
        };
        assert_eq!(*actual_data, data);
        let ExprKind::Let(actual_name, _, _, _, non_dep) = body.kind() else {
            panic!("Let")
        };
        assert_eq!(actual_name, &name);
        assert!(*non_dep);
    }

    #[test]
    fn interleaved_ordinary_and_generated_binders_preserve_loose_bvars() {
        let mut scope = TermScope::new();
        let raw = Expr::apps(
            Expr::fvar(id(1)),
            [Expr::bvar(0), Expr::bvar(1), Expr::bvar(2)],
        );
        let inner = scope.lam(id(2), BinderInfo::Default, Expr::type_(), raw.clone());
        let inner = Expr::lam(BinderInfo::Default, Expr::type_(), inner);
        let outer = scope.lam(id(1), BinderInfo::Default, Expr::type_(), inner);
        let expected = old_lam(
            id(1),
            Expr::type_(),
            Expr::lam(
                BinderInfo::Default,
                Expr::type_(),
                old_lam(id(2), Expr::type_(), raw),
            ),
        );
        assert_eq!(scope.close(&outer).unwrap(), expected);
    }

    #[test]
    fn ordinary_closed_subterms_remain_shared() {
        let mut scope = TermScope::new();
        let identity = Arc::new(Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)));
        let body = Expr::app_arc(identity.clone(), Arc::new(Expr::fvar(id(1))));
        let body = scope.lam(id(1), BinderInfo::Default, Expr::type_(), body);
        let closed = scope.close(&body).unwrap();
        let ExprKind::Lam(_, _, body) = closed.kind() else {
            panic!("Lam")
        };
        let ExprKind::App(actual, _) = body.kind() else {
            panic!("App")
        };
        assert!(Arc::ptr_eq(actual, &identity));
    }

    #[test]
    fn all_extension_binder_hooks_match_repeated_abstraction() {
        let mut scope = TermScope::new();
        let body = Arc::new(Expr::apps(
            Expr::fvar(id(1)),
            [Expr::bvar(0), Expr::bvar(1)],
        ));
        let domain = Arc::new(Expr::fvar(id(1)));
        let variants = [
            Expr::from_kind(ExprKind::CubicalPathLam { body: body.clone() }),
            Expr::from_kind(ExprKind::ZFCComprehension {
                domain: domain.clone(),
                pred: body.clone(),
            }),
            Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Separation {
                set: domain.clone(),
                pred: body.clone(),
            })),
            Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Replacement {
                set: domain,
                func: body,
            })),
        ];
        for body in variants {
            let expected = old_lam(id(1), Expr::type_(), body.clone());
            let open = scope.lam(id(1), BinderInfo::Default, Expr::type_(), body);
            assert_eq!(scope.close(&open).unwrap(), expected);
        }
    }

    #[test]
    fn ordinary_pi_and_let_bodies_and_values_match_repeated_abstraction() {
        let mut scope = TermScope::new();
        let raw = Expr::pi(
            BinderInfo::StrictImplicit,
            Expr::fvar(id(1)),
            Expr::let_named(
                Name::anon(),
                Expr::bvar(0),
                Expr::fvar(id(1)),
                Expr::apps(
                    Expr::fvar(id(1)),
                    [Expr::bvar(0), Expr::bvar(1), Expr::bvar(2)],
                ),
                false,
            ),
        );
        let expected = old_lam(id(1), Expr::type_(), raw.clone());
        let open = scope.lam(id(1), BinderInfo::Default, Expr::type_(), raw);
        assert_eq!(scope.close(&open).unwrap(), expected);
    }

    #[test]
    fn rejects_self_and_forward_references_in_types_and_values() {
        for in_type in [true, false] {
            let mut scope = TermScope::new();
            let ty = if in_type {
                Expr::fvar(id(1))
            } else {
                Expr::type_()
            };
            let value = if in_type {
                Expr::type_()
            } else {
                Expr::fvar(id(1))
            };
            let open = scope.let_named(id(1), Name::anon(), ty, value, Expr::fvar(id(1)), false);
            assert!(
                matches!(scope.close(&open), Err(TermScopeError::OutOfScope(local)) if local == id(1))
            );
        }
        let mut scope = TermScope::new();
        let body = scope.lam(id(2), BinderInfo::Default, Expr::type_(), Expr::fvar(id(1)));
        let open = scope.lam(id(1), BinderInfo::Default, Expr::fvar(id(2)), body);
        assert!(
            matches!(scope.close(&open), Err(TermScopeError::OutOfScope(local)) if local == id(2))
        );
    }

    #[test]
    fn rejects_duplicate_active_ids_but_allows_disjoint_reuse() {
        let mut scope = TermScope::new();
        let inner = scope.lam(id(1), BinderInfo::Default, Expr::type_(), Expr::fvar(id(1)));
        let outer = scope.lam(id(1), BinderInfo::Default, Expr::type_(), inner.clone());
        assert!(
            matches!(scope.close(&outer), Err(TermScopeError::ShadowedLocal(local)) if local == id(1))
        );
        let disjoint = Expr::app(inner.clone(), inner);
        assert!(scope.close(&disjoint).is_ok());
    }

    #[test]
    fn unknown_outer_locals_remain_free_and_registered_escaped_locals_reject() {
        let mut scope = TermScope::new();
        let open = scope.lam(id(1), BinderInfo::Default, Expr::type_(), Expr::fvar(id(2)));
        assert_eq!(
            scope.close(&open).unwrap(),
            old_lam(id(1), Expr::type_(), Expr::fvar(id(2)))
        );
        assert!(matches!(
            scope.close(&Expr::fvar(id(1))),
            Err(TermScopeError::OutOfScope(_))
        ));
    }

    #[test]
    fn shared_dag_under_distinct_named_and_ordinary_contexts_is_not_conflated() {
        let mut scope = TermScope::new();
        let shared = Arc::new(Expr::app(Expr::fvar(id(1)), Expr::bvar(0)));
        let inner = scope.lam(id(2), BinderInfo::Default, Expr::type_(), (*shared).clone());
        let body = Expr::app_arc(shared.clone(), Arc::new(inner));
        let body = Expr::lam(BinderInfo::Default, Expr::type_(), body);
        let open = scope.lam(id(1), BinderInfo::Default, Expr::type_(), body);
        let expected = old_lam(
            id(1),
            Expr::type_(),
            Expr::lam(
                BinderInfo::Default,
                Expr::type_(),
                Expr::app(
                    (*shared).clone(),
                    old_lam(id(2), Expr::type_(), (*shared).clone()),
                ),
            ),
        );
        assert_eq!(scope.close(&open).unwrap(), expected);
    }

    #[test]
    fn memoizes_repeated_shared_dag_nodes_in_the_same_context() {
        let mut scope = TermScope::new();
        let mut dag = Arc::new(Expr::fvar(id(1)));
        for _ in 0..20 {
            dag = Arc::new(Expr::app_arc(dag.clone(), dag));
        }
        let open = scope.lam(id(1), BinderInfo::Default, Expr::type_(), (*dag).clone());
        let result = scope
            .close_with_limits(&open, TermScopeLimits::default())
            .unwrap();
        assert_eq!(result.stats.memo_hits, 20);
        assert_eq!(result.stats.visits, 43);
        assert_eq!(result.stats.transformed_nodes, 23);
    }

    #[test]
    fn construction_closes_a_growing_suffix_in_exactly_linear_structural_visits() {
        for n in [128, 256, 512] {
            let mut scope = TermScope::new();
            let mut open = Expr::fvar(id(1));
            for local in 2..n + 2 {
                open = scope.let_named(
                    id(local),
                    Name::anon(),
                    Expr::type_(),
                    Expr::fvar(id(1)),
                    open,
                    false,
                );
            }
            open = scope.lam(id(1), BinderInfo::Default, Expr::type_(), open);
            let result = scope
                .close_with_limits(&open, TermScopeLimits::default())
                .unwrap();
            assert_eq!(result.stats.visits, 3 * n as usize + 3);
            assert_eq!(result.stats.transformed_nodes, result.stats.visits);
            assert_eq!(result.stats.max_binder_depth, n as u32 + 1);
        }
    }

    #[test]
    fn index_and_work_limits_fail_closed_without_panicking() {
        let mut scope = TermScope::new();
        let open = scope.lam(
            id(1),
            BinderInfo::Default,
            Expr::type_(),
            Expr::bvar(Expr::MAX_BVAR_INDEX),
        );
        assert!(matches!(
            scope.close(&open),
            Err(TermScopeError::IndexOverflow)
        ));
        let atom = Expr::type_();
        assert!(matches!(
            scope.close_with_limits(
                &atom,
                TermScopeLimits {
                    max_visits: 0,
                    max_depth: 10
                }
            ),
            Err(TermScopeError::VisitLimit)
        ));
        assert!(matches!(
            scope.close_with_limits(
                &atom,
                TermScopeLimits {
                    max_visits: 10,
                    max_depth: 0
                }
            ),
            Err(TermScopeError::DepthLimit)
        ));
        let open = scope.lam(id(2), BinderInfo::Default, Expr::type_(), Expr::fvar(id(2)));
        assert!(matches!(
            scope.close_with_limits(
                &open,
                TermScopeLimits {
                    max_visits: 2,
                    max_depth: 10
                }
            ),
            Err(TermScopeError::VisitLimit)
        ));
        assert!(matches!(
            scope.close_with_limits(
                &open,
                TermScopeLimits {
                    max_visits: 10,
                    max_depth: 1
                }
            ),
            Err(TermScopeError::DepthLimit)
        ));
        assert!(
            scope.close(&open).is_ok(),
            "a bounded failure must not mutate builder state"
        );
    }
}
