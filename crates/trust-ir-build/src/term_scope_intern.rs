// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interning-aware preparation of a deferred graph, INSIDE registered bodies.
//!
//! A producer that wraps a proof step by step re-embeds the same closed
//! subterms — reflected contexts, applications, literals, constants — at every
//! consumption site. A consumer-side hash-consing pass can only reach the
//! nodes it is allowed to rebuild, and it may not rebuild anything under a
//! deferred named binder: [`TermScope`] identifies such a binder by the exact
//! `Arc` of its body, so replacing a node inside that body changes the body
//! allocation and silently destroys the binder's identity.
//!
//! This pass is that rebuild, performed by the owner of the registry. It walks
//! the whole open graph, replaces every structurally equal BINDER-FREE subterm
//! with one canonical allocation, and RE-REGISTERS each rebuilt binder body
//! under the same `(kind, id)` before returning. The closing walk memoizes by
//! input allocation address and binder context, so collapsing duplicates is
//! exactly what removes repeated closing work.
//!
//! **Exactness.** The result is structurally equal to its input (`Expr::eq`)
//! and closes to a structurally equal term. Two rules make that true, and
//! neither may be relaxed:
//!
//! * A node whose subtree contains a registered binder is NEVER shared. Two
//!   structurally equal deferred binders can carry different local IDs (an
//!   unused binder, or a body that mentions only an outer local), so merging
//!   them would rebind a local. Ordinary kernel binders carry no such identity
//!   and are shared like any other node.
//! * A registered binder's body allocation is never interned and never entered
//!   into the canonical table. It stays unique to its binder: an allocation
//!   shared with any other position would make that position read as this
//!   binder's body. Its CONTENT is rebuilt and shared normally.
//!   An ordinary input alias of that allocation also stays outside both
//!   sharing tables, and makes its ancestors non-shareable.
//!
//! This is a representation change, not proof authority: no declaration,
//! axiom, or interpretation is installed, and every consumer must still close
//! the complete graph and independently kernel-check it.
//!
//! Earlier registrations are retained, so the ORIGINAL graph still closes to
//! the same term after a pass. That is what lets a caller compare both.

use super::{BinderKind, TermScope, TermScopeError, TermScopeLimits, replacement};
use clean_kernel::Expr;
use clean_kernel::expr::{ExprFolderOpt, ExprKind, FVarId};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
/// Structural work counters for one interning pass. These measure producer
/// representation only; they are not kernel, replay or memory bounds.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TermScopeInternStats {
    /// Every traversal request, including memo hits. Bounded by `max_visits`.
    pub visits: usize,
    /// Distinct input allocations actually examined.
    pub examined: usize,
    /// Positions replaced by an EXISTING canonical allocation.
    pub shared: usize,
    /// Fresh allocations because a child changed.
    pub rebuilt: usize,
    /// Registered binder bodies rebuilt and re-registered under the same ID.
    pub rebound: usize,
    /// Canonical allocations retained by the table when the pass ended.
    pub canonical: usize,
    /// Maximum traversal depth actually reached, excluding memoized subgraphs.
    pub max_depth: u32,
}

/// The interned graph and the counters of the walk that produced it.
pub struct InternedTerm {
    pub term: Expr,
    pub stats: TermScopeInternStats,
}

/// Forest representation shared under one interning allowance.
pub struct InternedForest {
    pub terms: Vec<Expr>,
    pub stats: TermScopeInternStats,
}

/// The traversal entry that first refused preparation. This observes the
/// existing walk; it does not describe unchecked descendants of that entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TermScopeInternPhase {
    Node,
    RegisteredBody,
}

/// Partial work retained after a bounded interning refusal. No partial term
/// is returned, and these measurements grant no proof or resource authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TermScopeInternFailure {
    pub error: TermScopeError,
    pub stats: TermScopeInternStats,
    /// Successfully prepared roots; also the zero-based failing root index.
    pub completed_roots: usize,
    pub phase: TermScopeInternPhase,
    /// Active traversal depth at the refusing request, before entering it.
    pub walk_depth: u32,
}

impl TermScope {
    /// Share structurally equal binder-free subterms across the whole open
    /// graph, INCLUDING inside registered deferred binder bodies, and
    /// re-register every rebuilt body under its original binder.
    ///
    /// The returned term is structurally equal to `expression` and closes to a
    /// structurally equal term. Traversal is bounded by `limits` and refuses
    /// with the same typed errors as closing; a refusal returns no partial
    /// term, and the registry keeps every body it re-registered before it.
    pub fn intern_with_limits(
        &mut self,
        expression: &Expr,
        limits: TermScopeLimits,
    ) -> Result<InternedTerm, TermScopeError> {
        let forest = self.intern_forest_with_limits(std::slice::from_ref(expression), limits)?;
        Ok(InternedTerm {
            term: forest.terms.into_iter().next().expect("one root"),
            stats: forest.stats,
        })
    }

    /// Share a retained forest with a single bounded walk. Every shallow root
    /// copy stays owned until all address-keyed memo operations have ended.
    pub fn intern_forest_with_limits(
        &mut self,
        expressions: &[Expr],
        limits: TermScopeLimits,
    ) -> Result<InternedForest, TermScopeError> {
        self.intern_forest_impl(expressions, limits)
            .map_err(|failure| failure.error)
    }

    /// The same bounded pass as [`Self::intern_forest_with_limits`], retaining
    /// charged work and the first refusing root/entry on failure. No prewalk,
    /// retry, partial expression or additional allowance is introduced. Earlier
    /// binder registrations remain retained exactly as with the ordinary API.
    pub fn intern_forest_with_diagnostics(
        &mut self,
        expressions: &[Expr],
        limits: TermScopeLimits,
    ) -> Result<InternedForest, TermScopeInternFailure> {
        self.intern_forest_impl(expressions, limits)
    }

    fn intern_forest_impl(
        &mut self,
        expressions: &[Expr],
        limits: TermScopeLimits,
    ) -> Result<InternedForest, TermScopeInternFailure> {
        let roots: Vec<_> = expressions.iter().cloned().map(Arc::new).collect();
        let mut interner = Interner {
            scope: self,
            limits,
            stats: TermScopeInternStats::default(),
            error: None,
            canonical: HashSet::new(),
            memo: HashMap::new(),
            input_apps: HashMap::new(),
            binder_free: true,
            walk_depth: 0,
        };
        let mut terms = Vec::with_capacity(roots.len());
        for root in &roots {
            interner.binder_free = true;
            let folded = interner.fold_shared(root);
            if let Some((error, phase, walk_depth)) = interner.error {
                interner.stats.canonical = interner.canonical.len();
                super::record_interning(interner.stats.visits);
                return Err(TermScopeInternFailure {
                    error,
                    stats: interner.stats,
                    completed_roots: terms.len(),
                    phase,
                    walk_depth,
                });
            }
            terms.push(
                folded
                    .map(|node| node.as_ref().clone())
                    .unwrap_or_else(|| root.as_ref().clone()),
            );
        }
        interner.stats.canonical = interner.canonical.len();
        super::record_interning(interner.stats.visits);
        Ok(InternedForest {
            terms,
            stats: interner.stats,
        })
    }

    /// [`Self::intern_with_limits`] under the default traversal limits.
    pub fn intern(&mut self, expression: &Expr) -> Result<Expr, TermScopeError> {
        Ok(self
            .intern_with_limits(expression, TermScopeLimits::default())?
            .term)
    }
}

struct Interner<'a> {
    scope: &'a mut TermScope,
    limits: TermScopeLimits,
    stats: TermScopeInternStats,
    error: Option<(TermScopeError, TermScopeInternPhase, u32)>,
    // Retains one allocation per distinct binder-free structure for the pass.
    canonical: HashSet<Arc<Expr>>,
    // Input address -> (replacement, binder-free). The input graph is held by
    // the caller for the whole call, so these addresses stay live and stable.
    memo: HashMap<usize, (Option<Arc<Expr>>, bool)>,
    // Exact child addresses of completed binder-free INPUT applications. All
    // original children stay live in the retained forest, even when preparing
    // them changed the output children. This is call-local representation
    // reuse, with at most one entry per charged completed input, not a proof
    // cache or a structural equality/hash walk over unvisited descendants.
    input_apps: HashMap<(usize, usize), Arc<Expr>>,
    // Conjunction accumulator for the node currently being folded, in the same
    // save/restore style the closing walk uses for declaration footprints.
    binder_free: bool,
    walk_depth: u32,
}

impl Interner<'_> {
    fn visit(&mut self, phase: TermScopeInternPhase) -> bool {
        if self.stats.visits >= self.limits.max_visits {
            self.fail(TermScopeError::VisitLimit, phase);
            false
        } else {
            self.stats.visits += 1;
            true
        }
    }

    fn fail(&mut self, error: TermScopeError, phase: TermScopeInternPhase) {
        self.error.get_or_insert((error, phase, self.walk_depth));
    }

    fn named(&self, kind: BinderKind, body: &Arc<Expr>) -> Option<FVarId> {
        self.scope
            .bindings
            .get(&(kind, Arc::as_ptr(body) as usize))
            .map(|binding| binding.id)
    }

    fn registered_root(&self, address: usize) -> bool {
        // A registered body root keeps its allocation identity, including
        // when the same allocation also occurs at an ordinary input position.
        [BinderKind::Lambda, BinderKind::Pi, BinderKind::Let]
            .iter()
            .any(|kind| self.scope.bindings.contains_key(&(*kind, address)))
    }

    fn input_app(expression: &Arc<Expr>) -> Option<(usize, usize)> {
        let ExprKind::App(function, argument) = expression.kind() else {
            return None;
        };
        Some((
            Arc::as_ptr(function) as usize,
            Arc::as_ptr(argument) as usize,
        ))
    }

    /// Replace a binder-free node with its canonical allocation. Never called
    /// for a registered binder body or for any node above a registered binder.
    fn intern(&mut self, node: Arc<Expr>) -> Arc<Expr> {
        if let Some(existing) = self.canonical.get(node.as_ref()) {
            if !Arc::ptr_eq(existing, &node) {
                self.stats.shared += 1;
                return existing.clone();
            }
            return node;
        }
        self.canonical.insert(node.clone());
        node
    }

    fn fold_shared(&mut self, expression: &Arc<Expr>) -> Option<Arc<Expr>> {
        if self.error.is_some() {
            return None;
        }
        if !self.visit(TermScopeInternPhase::Node) {
            return None;
        }
        let address = Arc::as_ptr(expression) as usize;
        if let Some((replacement, binder_free)) = self.memo.get(&address).cloned() {
            self.binder_free &= binder_free;
            return replacement;
        }
        if self.walk_depth >= self.limits.max_depth {
            self.fail(TermScopeError::DepthLimit, TermScopeInternPhase::Node);
            return None;
        }
        self.stats.examined += 1;
        self.stats.max_depth = self.stats.max_depth.max(self.walk_depth + 1);
        let registered_root = self.registered_root(address);
        let input_app = if registered_root {
            None
        } else {
            Self::input_app(expression)
        };
        if let Some(node) = input_app.and_then(|key| self.input_apps.get(&key)).cloned() {
            // The request and this fresh shell's depth were checked above.
            // Exact live child identities select a completed binder-free
            // result; no descendant is examined speculatively or for free.
            let replacement = (!Arc::ptr_eq(&node, expression)).then_some(node);
            if replacement.is_some() {
                self.stats.shared += 1;
            }
            self.memo.insert(address, (replacement.clone(), true));
            return replacement;
        }
        let parent_free = std::mem::replace(&mut self.binder_free, true);
        self.walk_depth += 1;
        self.stats.max_depth = self.stats.max_depth.max(self.walk_depth);
        let rebuilt = StackBoundary(self).fold_expr_opt(expression);
        self.walk_depth -= 1;
        // Identity belongs to the allocation, not only to its visit position.
        // An ordinary alias must not put a registered body into canonical,
        // nor let an ancestor bypass this exclusion through another memo.
        let binder_free = std::mem::replace(&mut self.binder_free, parent_free) && !registered_root;
        self.binder_free &= binder_free;
        if self.error.is_some() {
            return None;
        }
        if rebuilt.is_some() {
            self.stats.rebuilt += 1;
        }
        let node = rebuilt.map(Arc::new).unwrap_or_else(|| expression.clone());
        let node = if binder_free { self.intern(node) } else { node };
        if binder_free && let Some(key) = input_app {
            self.input_apps.insert(key, node.clone());
        }
        let replacement = (!Arc::ptr_eq(&node, expression)).then_some(node);
        self.memo
            .insert(address, (replacement.clone(), binder_free));
        replacement
    }

    /// A REGISTERED binder body. Its content is rebuilt and shared normally,
    /// but the body allocation itself is never interned, never memoized and
    /// never handed to another position: it is this binder's identity.
    fn registered_body(
        &mut self,
        kind: BinderKind,
        id: FVarId,
        body: &Arc<Expr>,
    ) -> Option<Arc<Expr>> {
        if self.error.is_some() {
            return None;
        }
        if !self.visit(TermScopeInternPhase::RegisteredBody) {
            return None;
        }
        if self.walk_depth >= self.limits.max_depth {
            self.fail(
                TermScopeError::DepthLimit,
                TermScopeInternPhase::RegisteredBody,
            );
            return None;
        }
        self.stats.examined += 1;
        let parent_free = std::mem::replace(&mut self.binder_free, true);
        self.walk_depth += 1;
        self.stats.max_depth = self.stats.max_depth.max(self.walk_depth);
        let rebuilt = StackBoundary(self).fold_expr_opt(body);
        self.walk_depth -= 1;
        // A binder node is never binder-free; its body's own flag never leaves.
        self.binder_free = parent_free;
        if self.error.is_some() {
            return None;
        }
        // Unchanged content keeps the ORIGINAL allocation, which is already
        // registered. Only a rebuilt body needs a new registered allocation.
        let rebuilt = rebuilt?;
        self.stats.rebuilt += 1;
        self.stats.rebound += 1;
        Some(self.scope.body(kind, id, rebuilt))
    }

    fn node(&mut self, expression: &Expr) -> Option<Expr> {
        match expression.kind() {
            ExprKind::Lam(data, ty, body) => match self.named(BinderKind::Lambda, body) {
                Some(id) => {
                    let ty_new = self.fold_expr_arc_opt(ty);
                    let body_new = self.registered_body(BinderKind::Lambda, id, body);
                    self.binder_free = false;
                    (ty_new.is_some() || body_new.is_some()).then(|| {
                        Expr::lam_arc(*data, replacement(ty, ty_new), replacement(body, body_new))
                    })
                }
                None => self.fold_expr_opt_inner(expression),
            },
            ExprKind::Pi(data, ty, body) => match self.named(BinderKind::Pi, body) {
                Some(id) => {
                    let ty_new = self.fold_expr_arc_opt(ty);
                    let body_new = self.registered_body(BinderKind::Pi, id, body);
                    self.binder_free = false;
                    (ty_new.is_some() || body_new.is_some()).then(|| {
                        Expr::pi_arc(*data, replacement(ty, ty_new), replacement(body, body_new))
                    })
                }
                None => self.fold_expr_opt_inner(expression),
            },
            ExprKind::Let(name, ty, value, body, non_dep) => {
                match self.named(BinderKind::Let, body) {
                    Some(id) => {
                        let ty_new = self.fold_expr_arc_opt(ty);
                        let value_new = self.fold_expr_arc_opt(value);
                        let body_new = self.registered_body(BinderKind::Let, id, body);
                        self.binder_free = false;
                        (ty_new.is_some() || value_new.is_some() || body_new.is_some()).then(|| {
                            Expr::let_named_arc(
                                name.clone(),
                                replacement(ty, ty_new),
                                replacement(value, value_new),
                                replacement(body, body_new),
                                *non_dep,
                            )
                        })
                    }
                    None => self.fold_expr_opt_inner(expression),
                }
            }
            // Clean's exhaustive visitor owns all other syntax, including
            // cubical and ZFC binders, through the ordinary Arc child hooks.
            _ => self.fold_expr_opt_inner(expression),
        }
    }
}

// Keep Clean's public folder entry point as the recursion boundary, exactly as
// the closing walk does: its default `fold_expr_opt` supplies the kernel's
// stack-growth protection, which an override on the memoizing folder would
// silently lose.
struct StackBoundary<'a, 'b>(&'a mut Interner<'b>);

impl ExprFolderOpt for StackBoundary<'_, '_> {
    fn fold_expr_opt_inner(&mut self, expression: &Expr) -> Option<Expr> {
        self.0.node(expression)
    }
}

impl ExprFolderOpt for Interner<'_> {
    /// Not reached by child dispatch: every child goes through the Arc hooks
    /// below. A caller entering here keeps the memo correct at the cost of one
    /// shallow root copy, because a bare `&Expr` carries no allocation to reuse.
    fn fold_expr_opt(&mut self, expression: &Expr) -> Option<Expr> {
        let node = Arc::new(expression.clone());
        self.fold_shared(&node)
            .map(|replacement| replacement.as_ref().clone())
    }

    fn fold_expr_arc_opt(&mut self, expression: &Arc<Expr>) -> Option<Arc<Expr>> {
        self.fold_shared(expression)
    }

    /// An ORDINARY kernel binder's body carries no allocation identity, so it
    /// is shared like any other node. Registered bodies never reach this hook:
    /// `node` intercepts their binders above.
    fn fold_binder_body_arc_opt(&mut self, expression: &Arc<Expr>) -> Option<Arc<Expr>> {
        self.fold_shared(expression)
    }
}

#[cfg(test)]
#[path = "term_scope_intern_tests.rs"]
mod tests;
