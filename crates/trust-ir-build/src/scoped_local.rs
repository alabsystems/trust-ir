// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fallible named locals over the shared deferred [`TermScope`].
//!
//! Use ONE [`LocalScope`] for every open term in a composed claim/proof graph.
//! Independent scopes start at the same local ID; their open expressions must
//! not be mixed. Cloning a [`ScopedLocal`] retains its owner, not a new allocator.
//! No term or Rust wrapper returned here is proof authority: close the complete
//! graph and independently check both its proposition and proof in the kernel.

use crate::term_scope::{
    ClosedTerm, InternedForest, InternedTerm, TermScope, TermScopeDiagnostics, TermScopeError,
    TermScopeInternFailure, TermScopeLimits, TermScopeStats,
};
use clean_kernel::{BinderInfo, Expr, Name, expr::FVarId};
use std::{
    cell::RefCell,
    fmt,
    rc::{Rc, Weak},
};

#[path = "scoped_external_context.rs"]
mod external_context;
pub(crate) use external_context::{OwnedExternalContext, PreparedOrdinaryView};

/// Construction and closing limits are distinct. These are structural caps,
/// not an aggregate memory/work bound for expression construction or replay.
#[derive(Clone, Copy, Debug)]
pub struct LocalScopeLimits {
    pub max_locals: usize,
    pub closing: TermScopeLimits,
}

impl Default for LocalScopeLimits {
    fn default() -> Self {
        Self {
            max_locals: 1_000_000,
            closing: TermScopeLimits::default(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LocalScopeError {
    LocalLimit { limit: usize },
    IdExhausted,
    UnboundFreeVariable,
    Closure(TermScopeError),
}

impl fmt::Display for LocalScopeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LocalLimit { limit } => {
                write!(f, "named local allocation limit {limit} exceeded")
            }
            Self::IdExhausted => f.write_str("named local identifier space exhausted"),
            Self::UnboundFreeVariable => {
                f.write_str("closed term still contains an unbound free variable")
            }
            Self::Closure(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for LocalScopeError {}

/// Complete-graph close result with counters retained even after refusal.
#[derive(Debug)]
pub struct LocalScopeCloseReport {
    pub result: Result<Expr, LocalScopeError>,
    pub stats: TermScopeStats,
    pub diagnostics: TermScopeDiagnostics,
}

/// A named variable and the owner needed to wrap its binders without repeated
/// abstraction. Fields are read-only; all bindings retain the allocated ID and
/// type. The expression is still untrusted, and the type is checked at replay.
#[derive(Clone)]
pub struct ScopedLocal {
    id: FVarId,
    ty: Expr,
    term: Expr,
    scope: Rc<RefCell<TermScope>>,
}

impl ScopedLocal {
    pub fn id(&self) -> FVarId {
        self.id
    }
    pub fn ty(&self) -> &Expr {
        &self.ty
    }
    pub fn term(&self) -> &Expr {
        &self.term
    }

    pub fn lam(&self, body: Expr) -> Expr {
        self.scope
            .borrow_mut()
            .lam(self.id, BinderInfo::Default, self.ty.clone(), body)
    }

    pub fn pi(&self, body: Expr) -> Expr {
        self.scope
            .borrow_mut()
            .pi(self.id, BinderInfo::Default, self.ty.clone(), body)
    }

    pub fn let_(&self, value: Expr, body: Expr) -> Expr {
        self.scope.borrow_mut().let_named(
            self.id,
            Name::anon(),
            self.ty.clone(),
            value,
            body,
            false,
        )
    }

    pub fn let_named(&self, name: Name, value: Expr, body: Expr, non_dep: bool) -> Expr {
        self.scope
            .borrow_mut()
            .let_named(self.id, name, self.ty.clone(), value, body, non_dep)
    }
}

/// A single allocator and its one deferred scope. Deliberately not Clone.
/// The interior scope is private: no callback is invoked while it is borrowed.
pub struct LocalScope {
    next: Option<u64>,
    allocated: usize,
    limits: LocalScopeLimits,
    terms: Rc<RefCell<TermScope>>,
}

/// Opaque owner identity for call-local producer memoization. Weak ownership
/// pins the allocation identity without retaining its entire binder registry.
/// It exposes neither the deferred bindings nor a way to mutate this scope.
#[derive(Clone)]
pub(crate) struct LocalScopeOwner(Weak<RefCell<TermScope>>);

impl LocalScopeOwner {
    pub(crate) fn matches(&self, other: &Self) -> bool {
        Weak::ptr_eq(&self.0, &other.0)
    }

    pub(crate) fn owns(&self, local: &ScopedLocal) -> bool {
        Weak::ptr_eq(&self.0, &Rc::downgrade(&local.scope))
    }

    pub(crate) fn address(&self) -> usize {
        self.0.as_ptr() as usize
    }

    #[cfg(test)]
    pub(crate) fn is_alive(&self) -> bool {
        self.0.upgrade().is_some()
    }
}

pub(crate) mod allocator_seal {
    pub trait Sealed {}
}

/// Narrow local-allocation interface for compositional proof construction.
///
/// Implemented only by the shared scope and its budgeted execution assembler.
/// A continuation keeps the SAME allocator, so opening a dependent witness
/// inside an execution neither exposes mutable scope replacement nor resets
/// the assembler's operation/local budgets. These locals remain untrusted
/// candidates; the complete consuming proposition/proof must be checked.
pub trait ScopedLocalAllocator: allocator_seal::Sealed {
    fn allocate_local(&mut self, ty: Expr) -> Result<ScopedLocal, String>;
    fn local_scope(&self) -> &LocalScope;
}

impl allocator_seal::Sealed for LocalScope {}

impl ScopedLocalAllocator for LocalScope {
    fn local_scope(&self) -> &LocalScope {
        self
    }
    fn allocate_local(&mut self, ty: Expr) -> Result<ScopedLocal, String> {
        self.try_local(ty).map_err(|error| error.to_string())
    }
}

impl Default for LocalScope {
    fn default() -> Self {
        Self::with_limits(LocalScopeLimits::default())
    }
}

impl LocalScope {
    pub fn new() -> Self {
        Self::default()
    }

    /// Zero is a refusing cap, not an unlimited sentinel.
    pub fn with_limits(limits: LocalScopeLimits) -> Self {
        Self {
            next: Some(0),
            allocated: 0,
            limits,
            terms: Rc::new(RefCell::new(TermScope::new())),
        }
    }

    pub(crate) fn component_prefix_body(
        &self,
        local: &ScopedLocal,
        definition: bool,
        expression: &Expr,
    ) -> Option<Expr> {
        if !self.owns(local)
            || self.terms.borrow().component_binder_id(expression) != Some(local.id())
        {
            return None;
        }
        match (definition, expression.kind()) {
            (false, clean_kernel::ExprKind::Lam(_, _, body))
            | (true, clean_kernel::ExprKind::Let(_, _, _, body, _)) => Some(body.as_ref().clone()),
            _ => None,
        }
    }
    pub(crate) fn named_binder_id(&self, expression: &Expr) -> Option<FVarId> {
        self.terms.borrow().component_binder_id(expression)
    }

    /// Preserve an existing named binder when candidate substitution changes
    /// its type/body. This registers metadata only; strict closing and kernel
    /// replay remain mandatory and no new local identity is authorized.
    pub(crate) fn preserve_candidate_binder(&self, original: &Expr, output: Expr) -> Expr {
        let mut scope = self.terms.borrow_mut();
        let Some(id) = scope.component_binder_id(original) else {
            return output;
        };
        match output.kind() {
            clean_kernel::ExprKind::Lam(data, ty, body) => {
                scope.lam(id, *data, ty.as_ref().clone(), body.as_ref().clone())
            }
            clean_kernel::ExprKind::Pi(data, ty, body) => {
                scope.pi(id, *data, ty.as_ref().clone(), body.as_ref().clone())
            }
            clean_kernel::ExprKind::Let(name, ty, value, body, non_dep) => scope.let_named(
                id,
                name.clone(),
                ty.as_ref().clone(),
                value.as_ref().clone(),
                body.as_ref().clone(),
                *non_dep,
            ),
            _ => output,
        }
    }

    pub fn intern_external_forest(
        &self,
        expressions: &[Expr],
        limits: TermScopeLimits,
    ) -> Result<InternedForest, LocalScopeError> {
        self.terms
            .borrow_mut()
            .intern_forest_with_limits(expressions, limits)
            .map_err(LocalScopeError::Closure)
    }

    /// Prepare the same forest under the same limits, retaining partial work
    /// on refusal. Preparation has only the underlying [`TermScopeError`]
    /// errors; no partially prepared expressions are returned.
    pub fn intern_external_forest_with_diagnostics(
        &self,
        expressions: &[Expr],
        limits: TermScopeLimits,
    ) -> Result<InternedForest, TermScopeInternFailure> {
        self.terms
            .borrow_mut()
            .intern_forest_with_diagnostics(expressions, limits)
    }

    pub fn close_external_forest(
        &self,
        expressions: &[Expr],
        external: &[ScopedLocal],
        visible: &[usize],
    ) -> (Result<Vec<Expr>, LocalScopeError>, TermScopeStats) {
        let (result, stats, _) =
            self.close_external_forest_observed(expressions, external, visible, false);
        (result, stats)
    }

    /// Narrow a forest walk to the caller's remaining budget. Requested caps
    /// are intersected with this owner's limits; this cannot enlarge either.
    pub fn close_external_forest_with_limits(
        &self,
        expressions: &[Expr],
        external: &[ScopedLocal],
        visible: &[usize],
        limits: TermScopeLimits,
    ) -> (Result<Vec<Expr>, LocalScopeError>, TermScopeStats) {
        let limits = TermScopeLimits {
            max_visits: limits.max_visits.min(self.limits.closing.max_visits),
            max_depth: limits.max_depth.min(self.limits.closing.max_depth),
        };
        let (result, stats, _) = self.close_external_forest_bounded_observed(
            expressions,
            external,
            visible,
            false,
            limits,
            false,
        );
        (result, stats)
    }

    pub(crate) fn close_external_forest_fully_with_limits(
        &self,
        expressions: &[Expr],
        external: &[ScopedLocal],
        visible: &[usize],
        limits: TermScopeLimits,
    ) -> (Result<Vec<Expr>, LocalScopeError>, TermScopeStats) {
        let limits = TermScopeLimits {
            max_visits: limits.max_visits.min(self.limits.closing.max_visits),
            max_depth: limits.max_depth.min(self.limits.closing.max_depth),
        };
        let (result, stats, _) = self.close_external_forest_bounded_observed(
            expressions,
            external,
            visible,
            false,
            limits,
            true,
        );
        (result, stats)
    }

    pub(crate) fn close_external_forest_observed(
        &self,
        expressions: &[Expr],
        external: &[ScopedLocal],
        visible: &[usize],
        observe: bool,
    ) -> (
        Result<Vec<Expr>, LocalScopeError>,
        TermScopeStats,
        Option<crate::term_scope::TermScopeDiagnostics>,
    ) {
        self.close_external_forest_bounded_observed(
            expressions,
            external,
            visible,
            observe,
            self.limits.closing,
            false,
        )
    }

    fn close_external_forest_bounded_observed(
        &self,
        expressions: &[Expr],
        external: &[ScopedLocal],
        visible: &[usize],
        observe: bool,
        limits: TermScopeLimits,
        fully_traversed: bool,
    ) -> (
        Result<Vec<Expr>, LocalScopeError>,
        TermScopeStats,
        Option<crate::term_scope::TermScopeDiagnostics>,
    ) {
        let mut ids = std::collections::HashSet::new();
        for local in external {
            if !self.owns(local) || !ids.insert(local.id()) {
                return (
                    Err(LocalScopeError::UnboundFreeVariable),
                    TermScopeStats::default(),
                    None,
                );
            }
        }
        let ids: Vec<_> = external.iter().map(ScopedLocal::id).collect();
        let terms = self.terms.borrow();
        if fully_traversed {
            let (result, stats) =
                terms.close_external_forest_fully(expressions, &ids, visible, limits);
            (result.map_err(LocalScopeError::Closure), stats, None)
        } else if observe {
            let (result, stats, diagnostics) =
                terms.close_external_forest_with_diagnostics(expressions, &ids, visible, limits);
            (
                result.map_err(LocalScopeError::Closure),
                stats,
                Some(diagnostics),
            )
        } else {
            let (result, stats) = terms.close_external_forest(expressions, &ids, visible, limits);
            (result.map_err(LocalScopeError::Closure), stats, None)
        }
    }

    pub fn closing_limits(&self) -> TermScopeLimits {
        self.limits.closing
    }

    pub fn allocated(&self) -> usize {
        self.allocated
    }

    pub fn owns(&self, local: &ScopedLocal) -> bool {
        Rc::ptr_eq(&self.terms, &local.scope)
    }

    pub(crate) fn memo_owner(&self) -> LocalScopeOwner {
        LocalScopeOwner(Rc::downgrade(&self.terms))
    }

    pub fn try_local(&mut self, ty: Expr) -> Result<ScopedLocal, LocalScopeError> {
        if self.allocated >= self.limits.max_locals {
            return Err(LocalScopeError::LocalLimit {
                limit: self.limits.max_locals,
            });
        }
        let raw = self.next.ok_or(LocalScopeError::IdExhausted)?;
        if raw >= FVarId::SENTINEL_RANGE_START {
            return Err(LocalScopeError::IdExhausted);
        }
        let allocated = self
            .allocated
            .checked_add(1)
            .ok_or(LocalScopeError::LocalLimit {
                limit: self.limits.max_locals,
            })?;
        let id = FVarId::new(raw);
        self.next = raw.checked_add(1);
        self.allocated = allocated;
        Ok(ScopedLocal {
            id,
            ty,
            term: Expr::fvar(id),
            scope: self.terms.clone(),
        })
    }

    /// Share structurally equal BINDER-FREE subterms across the whole open
    /// graph, including inside this scope's registered binder bodies, and
    /// re-register every rebuilt body under its original binder.
    ///
    /// A consumer cannot do this from the outside: rebuilding a node under a
    /// deferred binder changes the body allocation this scope uses as that
    /// binder's identity. The returned graph is structurally equal to its
    /// input and closes to a structurally equal term; the ORIGINAL graph also
    /// still closes, because earlier registrations are retained. This shares
    /// representation only — it installs nothing and grants no proof authority,
    /// and the complete graph must still be closed and kernel-checked.
    pub fn intern_shared(&self, expression: &Expr) -> Result<Expr, LocalScopeError> {
        self.intern_shared_with_limits(expression, self.limits.closing)
            .map(|interned| interned.term)
    }

    /// The same pass under caller-chosen traversal limits, with its counters.
    /// A refusal returns no partial term and preserves the typed closure error.
    pub fn intern_shared_with_limits(
        &self,
        expression: &Expr,
        limits: TermScopeLimits,
    ) -> Result<InternedTerm, LocalScopeError> {
        self.terms
            .borrow_mut()
            .intern_with_limits(expression, limits)
            .map_err(LocalScopeError::Closure)
    }

    pub fn close(&self, expression: &Expr) -> Result<Expr, LocalScopeError> {
        Ok(self
            .close_with_limits(expression, self.limits.closing)?
            .term)
    }

    /// Preserve the underlying traversal counters and caller-chosen limits.
    /// Unlike raw TermScope, a complete graph must contain no remaining FVars.
    pub fn close_with_limits(
        &self,
        expression: &Expr,
        limits: TermScopeLimits,
    ) -> Result<ClosedTerm, LocalScopeError> {
        let closed = self
            .terms
            .borrow()
            .close_with_limits(expression, limits)
            .map_err(LocalScopeError::Closure)?;
        if closed.term.has_fvar_quick() {
            return Err(LocalScopeError::UnboundFreeVariable);
        }
        Ok(closed)
    }

    /// Opt-in diagnostics for the same complete-graph close contract, including
    /// the final refusal of unbound FVars. No partial term is returned on error.
    /// Input-node counting and its bounded extra storage are opt-in; see
    /// `TermScope::close_with_diagnostics` for the precise counter meanings.
    pub fn close_with_diagnostics(
        &self,
        expression: &Expr,
        limits: TermScopeLimits,
    ) -> LocalScopeCloseReport {
        let report = self
            .terms
            .borrow()
            .close_with_diagnostics(expression, limits);
        let result = report
            .result
            .map_err(LocalScopeError::Closure)
            .and_then(|term| {
                if term.has_fvar_quick() {
                    Err(LocalScopeError::UnboundFreeVariable)
                } else {
                    Ok(term)
                }
            });
        LocalScopeCloseReport {
            result,
            stats: report.stats,
            diagnostics: report.diagnostics,
        }
    }
}

#[cfg(test)]
#[path = "scoped_local_diagnostics_tests.rs"]
mod diagnostics_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Environment, TypeChecker};

    #[test]
    fn shared_owner_closes_dependent_lambda_pi_and_let_and_kernel_checks() {
        let mut scope = LocalScope::new();
        let ty = scope.try_local(Expr::type_()).unwrap();
        let value = scope.try_local(ty.term().clone()).unwrap();
        let alias = scope.try_local(ty.term().clone()).unwrap();
        let body = alias.let_(value.term().clone(), alias.term().clone());
        let proof = scope.close(&ty.lam(value.lam(body))).unwrap();
        let claim = scope.close(&ty.pi(value.pi(ty.term().clone()))).unwrap();
        TypeChecker::new(&Environment::new())
            .check_type(&proof, &claim)
            .unwrap();
        assert_eq!(scope.close(&proof).unwrap(), proof);
        assert!(scope.owns(&value));
        assert!(scope.owns(&value.clone()));
        assert!(!LocalScope::new().owns(&value));
    }

    #[test]
    fn allocations_are_fresh_and_cap_failure_does_not_change_the_allocator() {
        let mut scope = LocalScope::with_limits(LocalScopeLimits {
            max_locals: 2,
            ..LocalScopeLimits::default()
        });
        let first = scope.try_local(Expr::type_()).unwrap();
        let second = scope.try_local(Expr::type_()).unwrap();
        assert_ne!(first.id(), second.id());
        assert!(matches!(
            scope.try_local(Expr::type_()),
            Err(LocalScopeError::LocalLimit { limit: 2 })
        ));
        assert_eq!(scope.allocated(), 2);
        assert_eq!(scope.next, Some(2));
        let mut zero = LocalScope::with_limits(LocalScopeLimits {
            max_locals: 0,
            ..LocalScopeLimits::default()
        });
        assert!(matches!(
            zero.try_local(Expr::type_()),
            Err(LocalScopeError::LocalLimit { limit: 0 })
        ));
        assert_eq!(zero.allocated(), 0);
    }

    #[test]
    fn final_identifier_is_issued_once_and_then_exhaustion_is_typed() {
        let mut scope = LocalScope::new();
        scope.next = Some(FVarId::SENTINEL_RANGE_START - 1);
        let final_local = scope.try_local(Expr::type_()).unwrap();
        assert_eq!(
            final_local.id(),
            FVarId::new(FVarId::SENTINEL_RANGE_START - 1)
        );
        assert!(matches!(
            scope.try_local(Expr::type_()),
            Err(LocalScopeError::IdExhausted)
        ));
        assert_eq!(scope.allocated(), 1);
    }

    #[test]
    fn unbound_and_escaped_allocated_locals_are_refused() {
        let mut scope = LocalScope::new();
        let local = scope.try_local(Expr::type_()).unwrap();
        assert_eq!(
            scope.close(local.term()),
            Err(LocalScopeError::UnboundFreeVariable)
        );
        let bound = local.lam(local.term().clone());
        let escaped = Expr::app(bound, local.term().clone());
        assert_eq!(
            scope.close(&escaped),
            Err(LocalScopeError::Closure(TermScopeError::OutOfScope(
                local.id()
            )))
        );
        let shadow = local.lam(local.lam(local.term().clone()));
        assert_eq!(
            scope.close(&shadow),
            Err(LocalScopeError::Closure(TermScopeError::ShadowedLocal(
                local.id()
            )))
        );
    }

    #[test]
    fn close_enforces_explicit_visit_and_depth_limits() {
        let mut scope = LocalScope::new();
        let ty = scope.try_local(Expr::type_()).unwrap();
        let value = scope.try_local(ty.term().clone()).unwrap();
        let proof = ty.lam(value.lam(value.term().clone()));
        assert!(matches!(
            scope.close_with_limits(
                &proof,
                TermScopeLimits {
                    max_visits: 1,
                    max_depth: 100
                }
            ),
            Err(LocalScopeError::Closure(TermScopeError::VisitLimit))
        ));
        assert!(matches!(
            scope.close_with_limits(
                &proof,
                TermScopeLimits {
                    max_visits: 100,
                    max_depth: 1
                }
            ),
            Err(LocalScopeError::Closure(TermScopeError::DepthLimit))
        ));
        let closed = scope
            .close_with_limits(&proof, TermScopeLimits::default())
            .unwrap();
        assert!(closed.stats.visits > 1);
        assert!(!closed.term.has_fvar_quick());
    }
    #[test]
    fn external_forest_remaining_budget_can_narrow_but_never_raise_owner_limits() {
        let mut scope = LocalScope::with_limits(LocalScopeLimits {
            closing: TermScopeLimits {
                max_visits: 2,
                max_depth: 16,
            },
            ..Default::default()
        });
        let local = scope.try_local(Expr::const_str("Nat")).unwrap();
        let term = local.lam(Expr::app(Expr::const_str("Nat.succ"), local.term().clone()));
        for requested in [0, 1, 2, usize::MAX] {
            let (result, stats) = scope.close_external_forest_with_limits(
                std::slice::from_ref(&term),
                &[],
                &[0],
                TermScopeLimits {
                    max_visits: requested,
                    max_depth: u32::MAX,
                },
            );
            assert!(result.is_err());
            assert!(stats.visits <= requested.min(2));
        }
        let (leaf, stats) = scope.close_external_forest_with_limits(
            &[Expr::nat_lit(0)],
            &[],
            &[0],
            TermScopeLimits {
                max_visits: 1,
                max_depth: 1,
            },
        );
        assert!(leaf.is_ok());
        assert_eq!(stats.visits, 1);
        let mut foreign = LocalScope::new();
        let other = foreign.try_local(Expr::const_str("Nat")).unwrap();
        let (result, stats) = scope.close_external_forest_with_limits(
            &[other.term().clone()],
            &[other],
            &[1],
            TermScopeLimits {
                max_visits: 0,
                max_depth: 0,
            },
        );
        assert!(matches!(result, Err(LocalScopeError::UnboundFreeVariable)));
        assert_eq!(stats.visits, 0);
    }
}

#[path = "scoped_local_materialized.rs"]
pub(crate) mod materialized;
