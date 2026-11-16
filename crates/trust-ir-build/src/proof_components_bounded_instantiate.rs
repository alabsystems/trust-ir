// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Paid simultaneous substitution over materialized terms and closed arguments.
//! This constructs untrusted terms, not equations, typing or compiler authority.
use super::*;
use clean_kernel::{ExprKind, expr::ExprFolderOpt};
use std::hash::{Hash, Hasher};

#[derive(Clone)]
struct Key(Expr, u32, bool);
impl PartialEq for Key {
    fn eq(&self, other: &Self) -> bool {
        self.1 == other.1 && self.2 == other.2 && same_graph(&self.0, &other.0)
    }
}
impl Eq for Key {}
impl Hash for Key {
    fn hash<H: Hasher>(&self, state: &mut H) {
        crate::proof_assembly::normalize::hash_graph(&self.0, state);
        self.1.hash(state);
        self.2.hash(state);
    }
}
#[derive(Clone)]
struct Entry {
    result: Option<Expr>,
    height: u32,
}
struct Walk<'a> {
    scope: &'a LocalScope,
    values: &'a [Expr],
    count: u32,
    closed_argument: bool,
    materialized: bool,
    depth: u32,
    nesting: u32,
    height: u32,
    max_depth: u32,
    work: usize,
    limit: usize,
    memo: HashMap<Key, Entry>,
    error: Option<String>,
}
struct Stack<'a, 'b>(&'a mut Walk<'b>);
enum ExternalInputs<'a> {
    #[cfg(test)]
    Handles(&'a [ScopedLocal]),
    Prepared(&'a ExternalContext),
}
#[derive(Default)]
pub(crate) struct TelescopeWork {
    pub(crate) materialization: usize,
    pub(crate) substitution: usize,
}
impl ExprFolderOpt for Stack<'_, '_> {
    fn fold_expr_opt_inner(&mut self, expr: &Expr) -> Option<Expr> {
        self.0.fold_expr_opt_inner(expr)
    }
}
impl Walk<'_> {
    fn charge(&mut self, amount: usize) -> bool {
        let Some(next) = self.work.checked_add(amount).filter(|n| *n <= self.limit) else {
            self.error = Some("bounded equation substitution work limit".into());
            return false;
        };
        self.work = next;
        true
    }
    fn root(&mut self, expr: &Expr, closed_argument: bool) -> Option<Expr> {
        self.closed_argument = closed_argument;
        self.depth = 0;
        self.nesting = 0;
        self.height = 0;
        self.fold_expr_opt(expr)
    }
}
impl ExprFolderOpt for Walk<'_> {
    fn fold_bvar_opt(&mut self, index: u32) -> Option<Expr> {
        if index < self.depth {
            return None;
        }
        if self.closed_argument {
            self.error = Some("equation substitution argument has loose bound variable".into());
            return None;
        }
        let offset = index - self.depth;
        if offset < self.count {
            // Every argument was fully walked and checked as ordinary-closed.
            // There is consequently no incoming BVar to lift under this binder.
            Some(self.values[offset as usize].clone())
        } else {
            Some(Expr::bvar(index - self.count))
        }
    }
    fn fold_binder_body_opt(&mut self, expr: &Expr) -> Option<Expr> {
        let Some(depth) = self.depth.checked_add(1) else {
            self.error = Some("equation substitution binder depth overflow".into());
            return None;
        };
        self.depth = depth;
        let result = self.fold_expr_opt(expr);
        self.depth -= 1;
        result
    }
    fn fold_expr_opt(&mut self, expr: &Expr) -> Option<Expr> {
        if self.error.is_some() || !self.charge(1) {
            return None;
        }
        if self.nesting >= self.max_depth {
            self.error = Some("bounded equation substitution depth limit".into());
            return None;
        }
        if self.scope.named_binder_id(expr).is_some() {
            self.error = Some("equation substitution retains deferred named binder".into());
            return None;
        }
        // This mode is reachable only after fresh complete materialization in
        // the SAME component call. All names, visibility and full input heights
        // were checked there. The kernel's constructor-maintained BVar range
        // is a complete conservative bound; it has no unknown/empty shortcut.
        if self.materialized && self.depth >= expr.loose_bvar_range() {
            return None;
        }
        if let ExprKind::BVar(index) = expr.kind() {
            if *index < self.depth {
                self.height = self.height.max(1);
                return None;
            }
            let offset = *index - self.depth;
            if !self.closed_argument && offset < self.count {
                // Direct indexing reuses an already validated argument. There
                // is no rebuilt node or memo entry to allocate/publish here.
                self.height = self.height.max(1);
                return Some(self.values[offset as usize].clone());
            }
        }
        let key = Key(expr.clone(), self.depth, self.closed_argument);
        if let Some(old) = self.memo.get(&key).cloned() {
            if self
                .nesting
                .checked_add(old.height)
                .is_none_or(|n| n > self.max_depth)
            {
                self.error = Some("bounded equation substitution cached depth limit".into());
                return None;
            }
            self.height = self.height.max(old.height);
            return old.result;
        }
        // Prepay memo publication and any potential rebuild BEFORE traversing.
        // Closed-argument validation never replaces a leaf, so the canonical
        // optional folder cannot rebuild any parent in that mode.
        // Failure spends this reservation too. No unknown footprint shortcut:
        // every new node/relative depth is walked, including every high BVar.
        if !self.charge(if self.closed_argument { 1 } else { 2 }) {
            return None;
        }
        let enclosing = std::mem::take(&mut self.height);
        self.nesting += 1;
        let result = Stack(self).fold_expr_opt(expr);
        self.nesting -= 1;
        let Some(height) = self.height.checked_add(1) else {
            self.error = Some("bounded equation substitution height overflow".into());
            return None;
        };
        self.height = enclosing.max(height);
        if self.error.is_none() {
            self.memo.insert(
                key,
                Entry {
                    result: result.clone(),
                    height,
                },
            );
        }
        result
    }
}
impl ProofComponents {
    /// Close the actual telescope/arguments and instantiate that fresh result.
    /// No materialized label, replacement statement or closure receipt is
    /// accepted from the caller. All work stays on this component's ledger.
    #[cfg(test)]
    pub(crate) fn charged_instantiate_scoped_telescope(
        &mut self,
        scope: &LocalScope,
        external: &[ScopedLocal],
        statement: &Expr,
        arguments: &[Expr],
    ) -> Result<Expr, String> {
        self.instantiate_scoped_telescope_impl(
            scope,
            ExternalInputs::Handles(external),
            statement,
            arguments,
            &mut TelescopeWork::default(),
        )
    }

    #[cfg(test)]
    pub(crate) fn charged_instantiate_in_external_context(
        &mut self,
        scope: &LocalScope,
        external: &ExternalContext,
        statement: &Expr,
        arguments: &[Expr],
    ) -> Result<Expr, String> {
        let result = self.instantiate_scoped_telescope_impl(
            scope,
            ExternalInputs::Prepared(external),
            statement,
            arguments,
            &mut TelescopeWork::default(),
        );
        if result.is_err() {
            self.poison_external_materialization(scope, external);
        }
        result
    }

    pub(crate) fn charged_instantiate_in_external_context_observed(
        &mut self,
        scope: &LocalScope,
        external: &ExternalContext,
        statement: &Expr,
        arguments: &[Expr],
    ) -> (Result<Expr, String>, TelescopeWork) {
        let mut work = TelescopeWork::default();
        let result = self.instantiate_scoped_telescope_impl(
            scope,
            ExternalInputs::Prepared(external),
            statement,
            arguments,
            &mut work,
        );
        if result.is_err() {
            self.poison_external_materialization(scope, external);
        }
        (result, work)
    }

    fn instantiate_scoped_telescope_impl(
        &mut self,
        scope: &LocalScope,
        external: ExternalInputs<'_>,
        statement: &Expr,
        arguments: &[Expr],
        work: &mut TelescopeWork,
    ) -> Result<Expr, String> {
        self.spend_context_work(
            arguments
                .len()
                .checked_mul(4)
                .and_then(|work| work.checked_add(4))
                .ok_or("equation telescope inventory overflow")?,
        )?;
        if arguments.len() > self.limits.captures {
            return Err("equation substitution argument inventory limit".into());
        }
        let mut roots = Vec::with_capacity(arguments.len() + 1);
        roots.push(statement.clone());
        roots.extend(arguments.iter().cloned());
        // This is a full named/ordinary walk, including complete relative
        // heights. It deliberately uses no closed-subtree projection shortcut.
        let before = self.counts().3;
        let forest = match external {
            #[cfg(test)]
            ExternalInputs::Handles(external) => self.charged_materialize_forest_fully(
                scope,
                external,
                &roots,
                &vec![external.len(); roots.len()],
            ),
            ExternalInputs::Prepared(external) => {
                self.charged_materialize_equation_context_fully(scope, external, &roots)
            }
        };
        work.materialization += self.counts().3.saturating_sub(before);
        let forest = forest?;
        let mut body = forest[0].clone();
        for _ in arguments {
            self.spend_context_work(1)?;
            let ExprKind::Pi(_, _, next) = body.kind() else {
                return Err("actual call equation telescope arity".into());
            };
            body = next.as_ref().clone();
        }
        let reversed = forest[1..].iter().rev().cloned().collect::<Vec<_>>();
        let before = self.counts().3;
        let result = self.instantiate_closed_rev_impl(scope, &body, &reversed, true);
        work.substitution += self.counts().3.saturating_sub(before);
        result
    }

    /// `values[0]` replaces BVar(0), exactly as the kernel's instantiate_rev.
    /// Values must be closed in ordinary BVars; owner/scope materialization
    /// remains the caller's separate obligation. Every attempt shares this
    /// component's existing ledger, and failed work is never refunded.
    #[cfg(test)]
    pub(crate) fn charged_instantiate_closed_rev(
        &mut self,
        scope: &LocalScope,
        body: &Expr,
        values: &[Expr],
    ) -> Result<Expr, String> {
        self.instantiate_closed_rev_impl(scope, body, values, false)
    }

    fn instantiate_closed_rev_impl(
        &mut self,
        scope: &LocalScope,
        body: &Expr,
        values: &[Expr],
        materialized: bool,
    ) -> Result<Expr, String> {
        self.spend_context_work(1)?;
        if !self
            .owner
            .as_ref()
            .is_some_and(|owner| owner.matches(&scope.memo_owner()))
        {
            return Err("equation substitution has another scope owner".into());
        }
        let count =
            u32::try_from(values.len()).map_err(|_| "equation substitution arity overflow")?;
        if values.len() > self.limits.captures {
            return Err("equation substitution argument inventory limit".into());
        }
        self.spend_context_work(values.len())?;
        if materialized && values.iter().any(|value| value.loose_bvar_range() != 0) {
            return Err("equation substitution argument has loose bound variable".into());
        }
        let mut walk = Walk {
            scope,
            values,
            count,
            closed_argument: true,
            materialized,
            depth: 0,
            nesting: 0,
            height: 0,
            max_depth: scope.closing_limits().max_depth.min(16_384),
            work: 0,
            limit: self.context_work_remaining()?,
            memo: HashMap::new(),
            error: None,
        };
        if !materialized {
            for value in values {
                walk.root(value, true);
                if walk.error.is_some() {
                    break;
                }
            }
        }
        let result = if walk.error.is_none() {
            walk.root(body, false)
        } else {
            None
        };
        let work = walk.work;
        let error = walk.error;
        self.spend_context_work(work)?;
        if let Some(error) = error {
            return Err(error);
        }
        Ok(result.unwrap_or_else(|| body.clone()))
    }
}

/// Contract an introduced application over terms freshly materialized by the
/// same substitution call. Closed arguments need no lifting under the body's
/// binders. This spends the substitution walk's existing aggregate ledger.
pub(super) fn apply_materialized_closed_argument(
    scope: &LocalScope,
    body: &Expr,
    argument: &Expr,
    work: &mut usize,
    limit: usize,
) -> Result<Expr, String> {
    let Some(next) = work.checked_add(2).filter(|next| *next <= limit) else {
        *work = limit;
        return Err("scoped application reduction work limit".into());
    };
    *work = next;
    if argument.has_loose_bvars() {
        return Err("scoped application reduction argument has a loose bound variable".into());
    }
    let values = [argument.clone()];
    let mut walk = Walk {
        scope,
        values: &values,
        count: 1,
        closed_argument: true,
        materialized: true,
        depth: 0,
        nesting: 0,
        height: 0,
        max_depth: scope.closing_limits().max_depth.min(16_384),
        work: 0,
        limit: limit - *work,
        memo: HashMap::new(),
        error: None,
    };
    let result = walk.root(body, false);
    *work = work
        .checked_add(walk.work)
        .ok_or("scoped application reduction work overflow")?;
    if let Some(error) = walk.error {
        return Err(error);
    }
    Ok(result.unwrap_or_else(|| body.clone()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Environment, Level, TypeChecker};
    fn n() -> Expr {
        Expr::const_str("Nat")
    }
    fn parts(scope: &LocalScope, operations: usize) -> ProofComponents {
        let mut p = ProofComponents::new(
            "substitution",
            ProofLimits {
                operations,
                ..Default::default()
            },
        );
        p.set_base(scope, vec![]).unwrap();
        p
    }
    #[test]
    fn bounded_substitution_matches_kernel_at_shared_relative_depths_and_all_core_binders() {
        let scope = LocalScope::new();
        let mut p = parts(&scope, 100_000);
        let shared = Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0));
        let inputs = [
            shared.clone(),
            Expr::lam(BinderInfo::Default, n(), shared.clone()),
            Expr::pi(BinderInfo::Default, n(), shared.clone()),
            Expr::let_named(Name::anon(), n(), Expr::bvar(0), shared.clone(), false),
            Expr::mdata(Vec::new(), shared.clone()),
            Expr::bvar(1_000_000),
        ];
        for body in inputs {
            for values in [
                vec![Expr::nat_lit(3)],
                vec![Expr::nat_lit(5), Expr::nat_lit(7)],
            ] {
                assert_eq!(
                    p.charged_instantiate_closed_rev(&scope, &body, &values)
                        .unwrap(),
                    body.instantiate_rev(&values)
                );
            }
        }
        let body = Expr::app(shared.clone(), Expr::lam(BinderInfo::Default, n(), shared));
        assert_eq!(
            p.charged_instantiate_closed_rev(&scope, &body, &[Expr::nat_lit(3)])
                .unwrap(),
            body.instantiate_rev(&[Expr::nat_lit(3)])
        );
    }
    #[test]
    fn bounded_substitution_retains_typing_and_does_not_capture_closed_argument() {
        let scope = LocalScope::new();
        let mut p = parts(&scope, 100_000);
        let mut env = Environment::new();
        env.init_nat().unwrap();
        env.init_eq().unwrap();
        let body = Expr::lam(
            BinderInfo::Default,
            n(),
            Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.refl"),
                    vec![Level::succ(Level::zero())],
                ),
                [n(), Expr::bvar(1)],
            ),
        );
        let proof = p
            .charged_instantiate_closed_rev(&scope, &body, &[Expr::nat_lit(3)])
            .unwrap();
        let equality = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [n(), Expr::nat_lit(3), Expr::nat_lit(3)],
        );
        TypeChecker::new(&env)
            .check_type(&proof, &Expr::arrow(n(), equality))
            .unwrap();
    }
    #[test]
    fn bounded_substitution_refuses_high_loose_arguments_deferred_binders_and_foreign_owner() {
        let mut scope = LocalScope::new();
        let mut p = parts(&scope, 100_000);
        for index in [0, 63, 64, 1024, 1_000_000] {
            assert!(
                p.charged_instantiate_closed_rev(&scope, &Expr::bvar(0), &[Expr::bvar(index)])
                    .unwrap_err()
                    .contains("loose bound")
            );
        }
        let local = scope.try_local(n()).unwrap();
        let named = local.lam(local.term().clone());
        assert!(
            p.charged_instantiate_closed_rev(&scope, &named, &[Expr::nat_lit(0)])
                .unwrap_err()
                .contains("deferred named")
        );
        assert!(
            p.charged_instantiate_closed_rev(
                &LocalScope::new(),
                &Expr::bvar(0),
                &[Expr::nat_lit(0)]
            )
            .unwrap_err()
            .contains("another scope owner")
        );
    }
    #[test]
    fn bounded_substitution_exhaustion_is_paid_and_new_calls_have_fresh_arguments() {
        let scope = LocalScope::new();
        let mut p = parts(&scope, 32);
        let mut body = Expr::bvar(0);
        for _ in 0..100 {
            body = Expr::app(Expr::const_str("Nat.succ"), body);
        }
        assert!(
            p.charged_instantiate_closed_rev(&scope, &body, &[Expr::nat_lit(3)])
                .unwrap_err()
                .contains("work limit")
        );
        assert!(p.counts().3 > 0);
        assert!(p.context_work_remaining().unwrap() < 4);
        let mut p = parts(&scope, 100_000);
        for value in [3, 5] {
            assert_eq!(
                p.charged_instantiate_closed_rev(&scope, &Expr::bvar(0), &[Expr::nat_lit(value)])
                    .unwrap(),
                Expr::nat_lit(value)
            );
        }
    }

    #[test]
    fn bounded_substitution_cached_graph_cannot_bypass_a_deeper_parent_limit() {
        let scope = LocalScope::with_limits(crate::scoped_local::LocalScopeLimits {
            closing: crate::term_scope::TermScopeLimits {
                max_visits: 1000,
                max_depth: 5,
            },
            ..Default::default()
        });
        let shared = Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0));
        let body = |wrappers| {
            let mut nested = shared.clone();
            for _ in 0..wrappers {
                nested = Expr::app(Expr::const_str("Nat.succ"), nested);
            }
            // The left occurrence warms the same graph at a shallower depth.
            Expr::app(shared.clone(), nested)
        };
        let mut p = parts(&scope, 100_000);
        let admitted = body(2);
        assert_eq!(
            p.charged_instantiate_closed_rev(&scope, &admitted, &[Expr::nat_lit(3)])
                .unwrap(),
            admitted.instantiate_rev(&[Expr::nat_lit(3)])
        );
        let before = p.context_work_remaining().unwrap();
        assert!(
            p.charged_instantiate_closed_rev(&scope, &body(3), &[Expr::nat_lit(3)])
                .unwrap_err()
                .contains("cached depth limit")
        );
        assert!(p.context_work_remaining().unwrap() < before);
    }

    #[test]
    fn bounded_substitution_closed_validation_pays_no_disabled_rebuilds() {
        let scope = LocalScope::new();
        let value = |leaf| {
            let mut value = leaf;
            for _ in 0..24 {
                value = Expr::app(Expr::const_str("Nat.succ"), value);
            }
            value
        };
        let body = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [n(), Expr::bvar(0)],
        );
        let argument = value(Expr::nat_lit(0));
        let proof = parts(&scope, 100)
            .charged_instantiate_closed_rev(&scope, &body, std::slice::from_ref(&argument))
            .unwrap();
        assert_eq!(proof, body.instantiate_rev(std::slice::from_ref(&argument)));
        let mut env = Environment::new();
        env.init_nat().unwrap();
        env.init_eq().unwrap();
        TypeChecker::new(&env)
            .check_type(
                &proof,
                &Expr::apps(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    [n(), argument.clone(), argument],
                ),
            )
            .unwrap();
        let mut p = parts(&scope, 100);
        assert!(
            p.charged_instantiate_closed_rev(&scope, &body, &[value(Expr::bvar(1_000_000))])
                .unwrap_err()
                .contains("loose bound")
        );
        assert!(p.context_work_remaining().unwrap() < 100);
    }

    #[test]
    fn bounded_substitution_argument_references_need_no_memo_entry_or_rebuilt_leaf() {
        let mut scope = LocalScope::new();
        let mut env = Environment::new();
        env.init_nat().unwrap();
        env.init_eq().unwrap();
        let value = parts(&scope, 5)
            .charged_instantiate_closed_rev(&scope, &Expr::bvar(0), &[Expr::nat_lit(3)])
            .unwrap();
        assert_eq!(value, Expr::nat_lit(3));
        TypeChecker::new(&env).check_type(&value, &n()).unwrap();
        let parameter = scope.try_local(n()).unwrap();
        let statement = parameter.pi(equality(parameter.term().clone(), parameter.term().clone()));
        let mut p = parts(&scope, 40);
        let context = p.charged_external_context(&scope, &[]).unwrap();
        let goal = p
            .charged_instantiate_in_external_context(
                &scope,
                &context,
                &statement,
                &[Expr::nat_lit(3)],
            )
            .unwrap();
        let proof = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [n(), Expr::nat_lit(3)],
        );
        TypeChecker::new(&env).check_type(&proof, &goal).unwrap();
        assert!(p.counts().3 <= 40);
    }

    fn equality(left: Expr, right: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [n(), left, right],
        )
    }

    #[test]
    fn fused_scoped_instantiation_matches_kernel_after_complete_materialization() {
        let mut scope = LocalScope::new();
        let parameter = scope.try_local(n()).unwrap();
        let statement = parameter.pi(equality(parameter.term().clone(), parameter.term().clone()));
        let mut argument = Expr::nat_lit(0);
        for _ in 0..300 {
            argument = Expr::app(Expr::const_str("Nat.succ"), argument);
        }
        let mut p = parts(&scope, 10_000);
        let context = p.charged_external_context(&scope, &[]).unwrap();
        let result = p
            .charged_instantiate_in_external_context(
                &scope,
                &context,
                &statement,
                &[argument.clone()],
            )
            .unwrap();
        let closed = scope.close(&statement).unwrap();
        let ExprKind::Pi(_, _, body) = closed.kind() else {
            panic!("closed telescope")
        };
        assert_eq!(result, body.instantiate_rev(&[argument.clone()]));
        let mut env = Environment::new();
        env.init_nat().unwrap();
        env.init_eq().unwrap();
        let proof = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [n(), argument],
        );
        TypeChecker::new(&env).check_type(&proof, &result).unwrap();
        assert!(p.context_work_remaining().unwrap() < 10_000);
    }

    #[test]
    fn fused_scoped_instantiation_does_not_capture_ambient_or_high_bvars() {
        let mut scope = LocalScope::new();
        let parameter = scope.try_local(n()).unwrap();
        let ambient = scope.try_local(n()).unwrap();
        let statement = parameter.pi(equality(parameter.term().clone(), parameter.term().clone()));
        for argument in [Expr::bvar(1_000_000), ambient.lam(Expr::bvar(0))] {
            let mut p = parts(&scope, 10_000);
            assert!(
                p.charged_instantiate_scoped_telescope(&scope, &[], &statement, &[argument])
                    .unwrap_err()
                    .contains("loose bound")
            );
            assert!(p.context_work_remaining().unwrap() < 10_000);
        }
        let mut p = parts(&scope, 10_000);
        assert!(
            p.charged_instantiate_scoped_telescope(
                &LocalScope::new(),
                &[],
                &statement,
                &[Expr::nat_lit(0)],
            )
            .unwrap_err()
            .contains("another owner")
        );
    }

    #[test]
    fn fused_scoped_instantiation_checks_closed_subtree_height_and_failed_work() {
        let mut scope = LocalScope::with_limits(crate::scoped_local::LocalScopeLimits {
            closing: crate::term_scope::TermScopeLimits {
                max_visits: 10_000,
                max_depth: 5,
            },
            ..Default::default()
        });
        let parameter = scope.try_local(n()).unwrap();
        let statement = parameter.pi(parameter.term().clone());
        let mut argument = Expr::nat_lit(0);
        for _ in 0..5 {
            argument = Expr::app(Expr::const_str("Nat.succ"), argument);
        }
        let mut p = parts(&scope, 10_000);
        assert!(
            p.charged_instantiate_scoped_telescope(&scope, &[], &statement, &[argument])
                .unwrap_err()
                .contains("depth limit")
        );
        assert!(p.context_work_remaining().unwrap() < 10_000);
        let mut argument = Expr::nat_lit(0);
        for _ in 0..100 {
            argument = Expr::app(Expr::const_str("Nat.succ"), argument);
        }
        // Use an ordinary scope here so the aggregate work, rather than the
        // deliberately narrow depth above, is the refusing boundary.
        let mut scope = LocalScope::new();
        let parameter = scope.try_local(n()).unwrap();
        let statement = parameter.pi(parameter.term().clone());
        let mut p = parts(&scope, 32);
        assert!(
            p.charged_instantiate_scoped_telescope(&scope, &[], &statement, &[argument])
                .is_err()
        );
        assert!(p.context_work_remaining().unwrap() < 32);
        assert!(
            p.charged_instantiate_scoped_telescope(&scope, &[], &statement, &[Expr::nat_lit(0)])
                .is_err()
        );
    }

    #[test]
    fn fused_scoped_instantiation_never_hides_an_unused_invalid_definition() {
        let mut scope = LocalScope::new();
        let parameter = scope.try_local(n()).unwrap();
        let statement = parameter.pi(equality(parameter.term().clone(), parameter.term().clone()));
        let mut p = parts(&scope, 100_000);
        p.bind_scoped_owned(&mut scope, &[], n(), Expr::const_str("True.intro"))
            .unwrap();
        let context = p.charged_external_context(&scope, &[]).unwrap();
        let goal = p
            .charged_instantiate_in_external_context(
                &scope,
                &context,
                &statement,
                &[Expr::nat_lit(3)],
            )
            .unwrap();
        let proof = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [n(), Expr::nat_lit(3)],
        );
        let claim = scope.close(&goal).unwrap();
        let bundle = p
            .close_scoped(&scope, proof, goal, Default::default())
            .unwrap();
        let wire = bundle.encode_with_claim(&claim).unwrap();
        let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
        assert_eq!(claim, transported);
        let mut env = Environment::new();
        env.init_nat().unwrap();
        env.init_eq().unwrap();
        env.init_true_false().unwrap();
        let error = decoded.replay(&env, &claim, 2_000_000).err().unwrap();
        assert!(error.contains("TypeMismatch") && !error.contains("BudgetExhausted"));
    }
}
