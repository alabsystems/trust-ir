// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Structured CPS candidates preserve correlated state/outcome Cases.
//! Reuse shared checked CASE_MAP laws; all generated endpoints remain untrusted
//! until complete original strict replay. Published projected support stays separate.
use super::*;
fn at(name: &str, levels: Vec<Level>, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(name), levels), args)
}
fn refl(u: &Level, ty: Expr, value: Expr) -> Expr {
    at("Eq.refl", vec![Level::succ(u.clone())], [ty, value])
}
use clean_kernel::expr::ExprFolderOpt;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    hash::{Hash, Hasher},
};

#[derive(Clone)]
struct Key(Expr);
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
struct Work<'a> {
    components: &'a mut ProofComponents,
    used: &'a mut usize,
    limit: usize,
}
impl Work<'_> {
    fn remaining(&self) -> Result<usize, String> {
        self.limit
            .checked_sub(*self.used)
            .ok_or_else(|| "case-context aggregate work limit".into())
    }
    fn pay(&mut self, amount: usize) -> Result<(), String> {
        if amount > self.remaining()? {
            return Err("case-context aggregate work limit".into());
        }
        self.components.spend_context_work(amount)?;
        *self.used += amount;
        Ok(())
    }
    fn close_prepared(
        &mut self,
        scope: &crate::scoped_local::LocalScope,
        external: &crate::proof_components::ExternalContext,
        roots: &[Expr],
    ) -> Result<Vec<Expr>, String> {
        self.pay(
            roots
                .len()
                .checked_mul(3)
                .ok_or("Case root storage overflow")?,
        )?;
        let before = self.components.counts().3;
        let result = self
            .components
            .charged_materialize_prepared_context_with_limit(
                scope,
                external,
                roots,
                self.remaining()?,
            );
        let spent = self.components.counts().3 - before;
        *self.used = self
            .used
            .checked_add(spent)
            .ok_or("Case closure work overflow")?;
        result
    }
}
fn intrinsic_atom(expression: &Expr) -> bool {
    matches!(
        expression.kind(),
        ExprKind::BVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_)
    )
}
fn atom_shape(expression: &Expr) -> bool {
    intrinsic_atom(expression) || matches!(expression.kind(), ExprKind::FVar(_))
}
fn stuck_atom(
    expression: &Expr,
    checker: &TypeChecker<'_>,
    work: &mut Work<'_>,
) -> Result<bool, String> {
    if intrinsic_atom(expression) {
        return Ok(true);
    }
    if let ExprKind::FVar(id) = expression.kind() {
        work.pay(1)?; // current local-context probe; never retained as a scope fact
        return Ok(checker
            .local_context()
            .get(*id)
            .is_none_or(|declaration| declaration.value.is_none()));
    }
    Ok(false)
}
struct Case {
    term: Expr,
    name: &'static str,
    levels: Vec<Level>,
    args: Vec<Expr>,
    params: usize,
    fields: Vec<Vec<Expr>>,
    theorem: &'static str,
    result: Expr,
}
fn case(
    term: &Expr,
    checker: &TypeChecker<'_>,
    work: &mut Work<'_>,
) -> Result<Option<Case>, String> {
    work.pay(1)?;
    if !matches!(term.kind(), ExprKind::App(..)) {
        return Ok(None);
    }
    // First inspect at most seven borrowed heads. Unknown heads stay cold:
    // they allocate no argument inventory and trigger no subtree traversal.
    let mut head = term;
    let mut arity = 0usize;
    loop {
        work.pay(1)?;
        let ExprKind::App(fun, _) = head.kind() else {
            break;
        };
        if arity == 6 {
            return Ok(None);
        }
        arity += 1;
        head = fun.as_ref();
    }
    let ExprKind::Const(name, levels) = head.kind() else {
        return Ok(None);
    };
    work.pay(4)?;
    let (name, params, theorem) =
        if *name == Name::from_string("Prod.rec") && arity == 5 && levels.len() == 3 {
            ("Prod.rec", 2, CASE_MAP_PROD)
        } else if *name == Name::from_string("Except.rec") && arity == 6 && levels.len() == 3 {
            ("Except.rec", 2, CASE_MAP_EXCEPT)
        } else if *name == Name::from_string("Option.rec") && arity == 5 && levels.len() == 2 {
            ("Option.rec", 1, CASE_MAP_OPTION)
        } else if *name == Name::from_string("Bool.rec") && arity == 4 && levels.len() == 1 {
            ("Bool.rec", 0, CASE_MAP_BOOL)
        } else {
            return Ok(None);
        };
    work.pay(arity + 2)?;
    let mut args = Vec::with_capacity(arity);
    let mut current = term;
    loop {
        work.pay(1)?;
        let ExprKind::App(fun, arg) = current.kind() else {
            break;
        };
        work.pay(2)?; // argument pin and insertion; second scan is paid too
        args.push(arg.as_ref().clone());
        current = fun.as_ref();
    }
    work.pay(arity + 20)?;
    args.reverse();
    let fields = match name {
        "Prod.rec" => vec![vec![args[0].clone(), args[1].clone()]],
        "Except.rec" => vec![vec![args[0].clone()], vec![args[1].clone()]],
        "Option.rec" => vec![vec![], vec![args[0].clone()]],
        _ => vec![vec![], vec![]],
    };
    let motive = checker.whnf(&args[params]);
    if checker.heartbeat_spent() {
        return Err("case-context kernel budget".into());
    }
    let ExprKind::Lam(_, _, body) = motive.kind() else {
        return Ok(None);
    };
    // Existing CASE_MAP contracts are nondependent. Never erase a dependency.
    if body.has_loose_bvars() || term.has_loose_bvars() {
        return Ok(None);
    }
    Ok(Some(Case {
        term: term.clone(),
        name,
        levels: levels.to_vec(),
        args,
        params,
        fields,
        theorem,
        result: body.as_ref().clone(),
    }))
}
struct Search<'a, 'b, 'e> {
    checker: &'a TypeChecker<'e>,
    work: &'a mut Work<'b>,
    depth: usize,
    max_depth: usize,
    seen: HashSet<(Key, usize)>,
    found: Option<Case>,
    error: Option<String>,
}
struct SearchStack<'a, 'b, 'c, 'e>(&'a mut Search<'b, 'c, 'e>);
impl ExprFolderOpt for SearchStack<'_, '_, '_, '_> {
    fn fold_expr_opt_inner(&mut self, e: &Expr) -> Option<Expr> {
        self.0.fold_expr_opt_inner(e)
    }
}
impl ExprFolderOpt for Search<'_, '_, '_> {
    fn fold_expr_opt(&mut self, e: &Expr) -> Option<Expr> {
        if self.found.is_some() || self.error.is_some() {
            return None;
        }
        if self.depth > self.max_depth {
            self.error = Some("case-context search depth limit".into());
            return None;
        }
        if atom_shape(e) {
            let atom = self
                .work
                .pay(1)
                .and_then(|()| stuck_atom(e, self.checker, self.work));
            match atom {
                Ok(true) => {
                    if self.checker.heartbeat_spent() {
                        self.error = Some("case-context kernel budget".into());
                    }
                    return None;
                }
                Ok(false) => {}
                Err(error) => {
                    self.error = Some(error);
                    return None;
                }
            }
        }
        if let Err(error) = self.work.pay(4) {
            self.error = Some(error);
            return None;
        }
        if !self.seen.insert((Key(e.clone()), self.depth)) {
            return None;
        }
        // Prefer the whole computed result below its projections. Never enter
        // a lambda/Pi merely to force an otherwise cold computation.
        if matches!(e.kind(), ExprKind::Lam(..) | ExprKind::Pi(..)) {
            return None;
        }
        self.depth += 1;
        let _unchanged = SearchStack(self).fold_expr_opt(e);
        self.depth -= 1;
        if self.found.is_none() && self.error.is_none() && !e.has_loose_bvars() {
            let normalized = self.checker.whnf(e);
            if self.checker.heartbeat_spent() {
                self.error = Some("case-context kernel budget".into());
                return None;
            }
            match case(&normalized, self.checker, self.work) {
                Ok(found) => self.found = found,
                Err(error) => self.error = Some(error),
            }
        }
        None
    }
    fn fold_binder_body_opt(&mut self, _: &Expr) -> Option<Expr> {
        None
    }
}
struct Replace<'a, 'b, 'e> {
    checker: &'a TypeChecker<'e>,
    target: &'a Expr,
    proper: &'a HashSet<Key>,
    hole: &'a Expr,
    work: &'a mut Work<'b>,
    depth: usize,
    max_depth: usize,
    memo: HashMap<(Key, usize), Option<Expr>>,
    changed: bool,
    error: Option<String>,
    scope: &'a crate::scoped_local::LocalScope,
    external: Option<&'a crate::proof_components::ExternalContext>,
    max_app_args: usize,
    support: Option<support::Support<'a, 'e>>,
}
fn administrative_redex(
    expression: &Expr,
    work: &mut Work<'_>,
    max_app_args: usize,
) -> Result<bool, String> {
    work.pay(1)?;
    match expression.kind() {
        ExprKind::Let(..) | ExprKind::Proj(..) => Ok(true),
        ExprKind::App(..) => {
            let mut head = expression;
            let mut arity = 0usize;
            loop {
                work.pay(1)?;
                let ExprKind::App(function, _) = head.kind() else {
                    break;
                };
                if arity == max_app_args {
                    return Ok(false);
                }
                arity += 1;
                head = function.as_ref();
            }
            match head.kind() {
                ExprKind::Lam(..) => Ok(true),
                ExprKind::Const(name, levels) if arity == 3 && levels.len() == 2 => {
                    work.pay(4)?;
                    Ok(*name == Name::from_string("Prod.fst")
                        || *name == Name::from_string("Prod.snd"))
                }
                _ => Ok(false),
            }
        }
        _ => Ok(false),
    }
}
struct ReplaceStack<'a, 'b, 'c, 'e>(&'a mut Replace<'b, 'c, 'e>);
impl ExprFolderOpt for ReplaceStack<'_, '_, '_, '_> {
    fn fold_expr_opt_inner(&mut self, e: &Expr) -> Option<Expr> {
        self.0.fold_expr_opt_inner(e)
    }
}
impl ExprFolderOpt for Replace<'_, '_, '_> {
    fn fold_expr_opt(&mut self, e: &Expr) -> Option<Expr> {
        if self.error.is_some() {
            return None;
        }
        if self.depth > self.max_depth {
            self.error = Some("case-context replacement depth limit".into());
            return None;
        }
        // These exact current WHNF atoms cannot equal or contain the selected
        // App. Omit the proper-set probe, WHNF, and temporary storage entirely.
        // A missing local-context entry has the same operational WHNF result;
        // it grants no scope/type authority and original endpoint closure stays strict.
        if matches!(self.target.kind(), ExprKind::App(..)) && atom_shape(e) {
            let atom = self
                .work
                .pay(1)
                .and_then(|()| stuck_atom(e, self.checker, self.work));
            match atom {
                Ok(true) => {
                    if self.checker.heartbeat_spent() {
                        self.error = Some("case-context kernel budget".into());
                    }
                    return None;
                }
                Ok(false) => {}
                Err(error) => {
                    self.error = Some(error);
                    return None;
                }
            }
        }
        if matches!(
            e.kind(),
            ExprKind::BVar(_)
                | ExprKind::FVar(_)
                | ExprKind::Sort(_)
                | ExprKind::Const(..)
                | ExprKind::Lit(_)
        ) {
            // Scalar inputs have no children or possible parent rebuild. Keep
            // the proper-frontier check and actual WHNF/target comparison:
            // an FVar/Const definition may reduce to the selected whole Case.
            // No temporary memo key/entry or rebuild reservation is needed.
            if let Err(error) = self.work.pay(4) {
                self.error = Some(error);
                return None;
            }
            if self.proper.contains(&Key(e.clone())) {
                return None;
            }
            if !e.has_loose_bvars() {
                if let Err(error) = self.work.pay(3) {
                    self.error = Some(error);
                    return None;
                }
                let normalized = self.checker.whnf(e);
                if self.checker.heartbeat_spent() {
                    self.error = Some("case-context kernel budget".into());
                    return None;
                }
                if crate::proof_assembly::normalize::same_graph(&normalized, self.target) {
                    if let Err(error) = self.work.pay(1) {
                        self.error = Some(error);
                        return None;
                    }
                    self.changed = true;
                    return Some(self.hole.clone());
                }
            }
            return None;
        }
        // One input visit, probes, retained memo entry and possible rebuilt
        // node/child pins are prepaid, even for unchanged or failed attempts.
        if let Err(error) = self.work.pay(12) {
            self.error = Some(error);
            return None;
        }
        let key = (Key(e.clone()), self.depth);
        if let Some(known) = self.memo.get(&key) {
            return known.clone();
        }
        if self.proper.contains(&key.0) {
            self.memo.insert(key, None);
            return None;
        }
        let mut reduced = None;
        if !e.has_loose_bvars() {
            let normalized = self.checker.whnf(e);
            if self.checker.heartbeat_spent() {
                self.error = Some("case-context kernel budget".into());
                return None;
            }
            if crate::proof_assembly::normalize::same_graph(&normalized, self.target) {
                self.changed = true;
                let result = Some(self.hole.clone());
                self.memo.insert(key, result.clone());
                return result;
            }
            if let Some(external) = self.external
                && !crate::proof_assembly::normalize::same_graph(e, &normalized)
            {
                match administrative_redex(e, self.work, self.max_app_args) {
                    Ok(true) => {
                        // Follow only an actual returned graph from the same
                        // exact prepared inventory. This is a producer path,
                        // not a scope/typing receipt for the raw input. The
                        // original endpoint still closes and strictly replays.
                        match self
                            .work
                            .close_prepared(self.scope, external, &[normalized])
                        {
                            Ok(mut roots) => match roots.pop() {
                                Some(root) => reduced = Some(root),
                                None => {
                                    self.error =
                                        Some("Case reduction lost its returned root".into());
                                    return None;
                                }
                            },
                            Err(error) => {
                                self.error = Some(error);
                                return None;
                            }
                        }
                    }
                    Ok(false) => {}
                    Err(error) => {
                        self.error = Some(error);
                        return None;
                    }
                }
            }
        }
        if reduced.is_none()
            && let Some(support) = self.support.as_mut()
        {
            match support.excludes(e, self.work, self.max_depth - self.depth) {
                Ok(true) => {
                    self.memo.insert(key, None);
                    return None;
                }
                Ok(false) => {}
                Err(error) => {
                    self.error = Some(error);
                    return None;
                }
            }
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
        // The memo is local to this attempt; no incomplete result escapes.
        if self.error.is_none() {
            self.memo.insert(key, result.clone());
        }
        result
    }
}
struct Context<'a, 'b, 'e, L> {
    allocator: &'a mut L,
    checker: &'a TypeChecker<'e>,
    captures: &'a [OwnedProofCapture],
    globals: &'a [ScopedLocal],
    external: Option<&'a crate::proof_components::ExternalContext>,
    work: Work<'b>,
    u: &'a Level,
    observed: &'a Expr,
    limits: ImageReplayLimits,
    cases: &'a mut usize,
}
impl<L: ScopedLocalAllocator> Context<'_, '_, '_, L> {
    fn close(
        &mut self,
        roots: &[Expr],
        extra: &[ScopedLocal],
        binder: Option<&ScopedLocal>,
    ) -> Result<Vec<Expr>, String> {
        if let Some(external) = self.external {
            // Private construction binds every fresh field before closure;
            // this path never silently adds it to the prepared inventory.
            if !extra.is_empty() {
                return Err("prepared Case closure has unbound private fields".into());
            }
            return self
                .work
                .close_prepared(self.allocator.local_scope(), external, roots);
        }
        let counts = self.work.components.counts();
        let retained_count = counts
            .0
            .checked_add(counts.1)
            .ok_or("case-context inventory overflow")?;
        let count = retained_count
            .checked_add(self.globals.len())
            .and_then(|n| n.checked_add(self.captures.len()))
            .and_then(|n| n.checked_add(extra.len()))
            .ok_or("case-context inventory overflow")?;
        self.work.pay(
            count
                .checked_mul(24)
                .and_then(|n| n.checked_add(roots.len().checked_mul(3)?))
                .ok_or("case-context inventory overflow")?,
        )?;
        let retained = self
            .work
            .components
            .retained_normalization_locals(self.allocator.local_scope())?;
        let mut allowed = Vec::with_capacity(count);
        let mut ids = HashSet::with_capacity(count);
        for local in retained
            .iter()
            .chain(self.globals)
            .chain(self.captures.iter().map(|c| c.local()))
            .chain(extra)
        {
            if !self.allocator.local_scope().owns(local) {
                return Err("foreign case-context local".into());
            }
            if binder.is_some_and(|binder| binder.id() == local.id()) {
                continue;
            }
            if ids.insert(local.id()) {
                allowed.push(local.clone());
            }
        }
        let before = self.work.components.counts().3;
        let result = self.work.components.charged_materialize_forest_with_limit(
            self.allocator.local_scope(),
            &allowed,
            roots,
            &vec![allowed.len(); roots.len()],
            self.work.remaining()?,
        );
        // The canonical closer enforces the same remaining local/component
        // budget internally. Charge successful and failed visits, no refunds.
        let spent = self.work.components.counts().3 - before;
        *self.work.used = self
            .work
            .used
            .checked_add(spent)
            .ok_or("case-context closure work overflow")?;
        result
    }
    fn abstract_local(
        &mut self,
        local: &ScopedLocal,
        body: Expr,
        extra: &[ScopedLocal],
    ) -> Result<Expr, String> {
        self.work.pay(3)?;
        self.close(&[local.lam(body)], extra, Some(local))?
            .pop()
            .ok_or_else(|| "case-context abstraction lost root".into())
    }
    fn projected_receiver(&mut self, major: &Expr) -> Result<Option<Case>, String> {
        self.work.pay(3)?; // query and current/result pins
        let mut current = self.checker.whnf(major);
        if self.checker.heartbeat_spent() {
            return Err("Case receiver kernel budget".into());
        }
        for _ in 0..=self.limits.max_depth {
            self.work.pay(2)?; // projection probe and receiver pin
            let ExprKind::Proj(_, _, receiver) = current.kind() else {
                return Ok(None);
            };
            current = self.checker.whnf(receiver);
            if self.checker.heartbeat_spent() {
                return Err("Case receiver kernel budget".into());
            }
            if let Some(found) = case(&current, self.checker, &mut self.work)? {
                return Ok(Some(found));
            }
        }
        Err("Case receiver depth limit".into())
    }
    fn commute(&mut self, source: &Expr) -> Result<Option<(Expr, Expr)>, String> {
        if self.limits.max_cases == 0 {
            return Ok(None);
        }
        let Some(outer) = case(source, self.checker, &mut self.work)? else {
            return Ok(None);
        };
        let major = outer.args.last().ok_or("case-context missing major")?;
        let direct = if self.external.is_some() {
            self.projected_receiver(major)?
        } else {
            None
        };
        let selected = if direct.is_some() {
            direct
        } else {
            let mut search = Search {
                checker: self.checker,
                work: &mut self.work,
                depth: 0,
                max_depth: self.limits.max_depth,
                seen: HashSet::new(),
                found: None,
                error: None,
            };
            let _unchanged = search.fold_expr_opt(major);
            if let Some(error) = search.error {
                return Err(error);
            }
            search.found
        };
        let Some(case) = selected else {
            return Ok(None);
        };
        // A bounded proper frontier is a search hint only. Every missed
        // occurrence still has to match the complete original kernel endpoint.
        self.work.pay(
            case.args
                .len()
                .checked_mul(3)
                .and_then(|n| n.checked_add(2))
                .ok_or("case-context frontier overflow")?,
        )?;
        let mut proper = HashSet::new();
        let mut frontier = VecDeque::from(case.args.clone());
        for _ in 0..self.limits.max_app_args {
            let Some(e) = frontier.pop_front() else { break };
            if intrinsic_atom(&e) {
                self.work.pay(1)?; // no children and cannot match a selected App
                continue;
            }
            self.work.pay(12)?; // graph probe/pin, entry, up to three children
            if crate::proof_assembly::normalize::same_graph(&e, &case.term)
                || !proper.insert(Key(e.clone()))
            {
                continue;
            }
            match e.kind() {
                ExprKind::App(f, a) => {
                    frontier.push_back(f.as_ref().clone());
                    frontier.push_back(a.as_ref().clone());
                }
                ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                    frontier.push_back(t.as_ref().clone());
                    frontier.push_back(b.as_ref().clone());
                }
                ExprKind::Let(_, t, v, b, _) => {
                    frontier.push_back(t.as_ref().clone());
                    frontier.push_back(v.as_ref().clone());
                    frontier.push_back(b.as_ref().clone());
                }
                ExprKind::Proj(_, _, e) | ExprKind::MData(_, e) => {
                    frontier.push_back(e.as_ref().clone())
                }
                _ => {}
            }
        }
        self.work.pay(4)?;
        let hole = self.allocator.allocate_local(case.result.clone())?;
        let support = if self.external.is_some() && self.limits.max_cache_entries > 0 {
            self.work.pay(2)?; // private map/target context headers
            Some(support::Support::new(
                self.checker,
                self.allocator.local_scope(),
                &case.term,
                self.limits.max_cache_entries,
                self.limits.max_app_args,
            ))
        } else {
            None
        };
        let mut replace = Replace {
            checker: self.checker,
            target: &case.term,
            proper: &proper,
            hole: hole.term(),
            work: &mut self.work,
            depth: 0,
            max_depth: self.limits.max_depth,
            memo: HashMap::new(),
            changed: false,
            error: None,
            scope: self.allocator.local_scope(),
            external: self.external,
            max_app_args: self.limits.max_app_args,
            support,
        };
        let template = if self.external.is_some() {
            // Preserve the actual source App-depth for every argument root.
            // Probe the complete non-discriminator context first. A case used
            // only inside the discriminator does not couple its state/data to
            // the branches and needs no new commuting proof. This is only a
            // producer choice; the original structural proof and endpoint
            // remain mandatory, and all search work stays charged.
            let arity = outer.args.len();
            replace.work.pay(
                arity
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(2))
                    .ok_or("Case context argument storage overflow")?,
            )?;
            let mut arguments = Vec::with_capacity(arity);
            for (index, argument) in outer.args[..arity - 1].iter().enumerate() {
                replace.depth = arity - index;
                let rewritten = replace
                    .fold_expr_opt(argument)
                    .unwrap_or_else(|| argument.clone());
                if let Some(error) = replace.error.take() {
                    return Err(error);
                }
                arguments.push(rewritten);
            }
            if !replace.changed {
                return Ok(None);
            }
            replace.depth = 1;
            let major = outer.args.last().ok_or("Case discriminator missing")?;
            let rewritten = replace
                .fold_expr_opt(major)
                .unwrap_or_else(|| major.clone());
            if let Some(error) = replace.error.take() {
                return Err(error);
            }
            arguments.push(rewritten);
            replace.work.pay(
                arity
                    .checked_mul(3)
                    .and_then(|n| n.checked_add(8))
                    .ok_or("Case spine reconstruction overflow")?,
            )?;
            at(outer.name, outer.levels, arguments)
        } else {
            replace
                .fold_expr_opt(source)
                .unwrap_or_else(|| source.clone())
        };
        if let Some(error) = replace.error {
            return Err(error);
        }
        if !replace.changed {
            return Err("selected case lost its owned context".into());
        }
        let context = self.abstract_local(&hole, template, &[])?;
        *self.cases = self
            .cases
            .checked_add(1)
            .ok_or("case-context count overflow")?;
        if *self.cases > self.limits.max_cases {
            return Err("case-context case limit".into());
        }
        self.work.pay(10 + case.fields.len() * 4)?;
        let mut mapped = Vec::with_capacity(case.fields.len());
        let mut identities = Vec::with_capacity(case.fields.len());
        for (index, fields) in case.fields.iter().enumerate() {
            self.work.pay(fields.len() * 4 + 12)?;
            let locals = fields
                .iter()
                .cloned()
                .map(|ty| self.allocator.allocate_local(ty))
                .collect::<Result<Vec<_>, _>>()?;
            let original = Expr::apps(
                case.args[case.params + 1 + index].clone(),
                locals.iter().map(|l| l.term().clone()),
            );
            let value = Expr::app(context.clone(), original);
            let mut mapped_branch = value.clone();
            let mut identity = refl(self.u, self.observed.clone(), value);
            for local in locals.iter().rev() {
                self.work.pay(6)?; // both named lambdas and their child pins
                mapped_branch = local.lam(mapped_branch);
                identity = local.lam(identity);
            }
            mapped.push(mapped_branch);
            identities.push(identity);
        }
        self.work.pay(100)?; // bounded motive, vectors, equality/application nodes
        let major = case
            .args
            .last()
            .ok_or("case-context missing major")?
            .clone();
        let major_type = match case.name {
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
        normalized_args.push(motive.lam(self.observed.clone()));
        normalized_args.extend(mapped.iter().cloned());
        normalized_args.push(major.clone());
        let mut levels = case.levels.clone();
        levels[0] = Level::succ(self.u.clone());
        let normalized = at(case.name, levels, normalized_args);
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
        let mut closed = self.close(&[normalized, equality], &[], None)?;
        let equality = closed.pop().ok_or("Case equality root missing")?;
        let normalized = closed.pop().ok_or("Case normalized root missing")?;
        Ok(Some((normalized, equality)))
    }
}
/// Shared untrusted producer. The original equality endpoint and all defining
/// values remain mandatory strict replay inputs. No cache escapes this call.
pub(crate) fn commute_candidate<L: ScopedLocalAllocator>(
    allocator: &mut L,
    components: &mut ProofComponents,
    checker: &TypeChecker<'_>,
    globals: &[ScopedLocal],
    captures: &[OwnedProofCapture],
    observed: &Expr,
    u: &Level,
    limits: ImageReplayLimits,
    cases: &mut usize,
    context_work: &mut usize,
    source: &Expr,
    external: Option<&crate::proof_components::ExternalContext>,
) -> Result<Option<(Expr, Expr)>, String> {
    let limit = limits
        .max_cases
        .checked_mul(limits.max_app_args.max(1))
        .ok_or("case-context work overflow")?
        .min(1_000_000);
    let mut context = Context {
        allocator,
        checker,
        captures,
        globals,
        external,
        work: Work {
            components,
            used: context_work,
            limit,
        },
        u,
        observed,
        limits,
        cases,
    };
    let result = context.commute(source);
    if result.is_err()
        && let Some(external) = external
    {
        context
            .work
            .components
            .poison_external_materialization(context.allocator.local_scope(), external);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scoped_local::LocalScope;

    fn scalar_replacement(
        checker: &TypeChecker<'_>,
        scope: &LocalScope,
        source: &Expr,
        target: &Expr,
        limit: usize,
        proper: bool,
        depth: usize,
    ) -> (Option<Expr>, Option<String>, usize, bool) {
        let mut parts = ProofComponents::new("Case.scalar.replacement", Default::default());
        parts.set_base(scope, vec![]).unwrap();
        let mut used = 0;
        let result = {
            let mut work = Work {
                components: &mut parts,
                used: &mut used,
                limit,
            };
            let proper = if proper {
                HashSet::from([Key(source.clone())])
            } else {
                HashSet::new()
            };
            let hole = Expr::nat_lit(99);
            let mut replace = Replace {
                checker,
                target,
                proper: &proper,
                hole: &hole,
                work: &mut work,
                depth,
                max_depth: 8,
                memo: HashMap::new(),
                changed: false,
                error: None,
                scope,
                external: None,
                max_app_args: 64,
                support: None,
            };
            let output = replace.fold_expr_opt(source);
            assert!(
                replace.memo.is_empty(),
                "scalar path must allocate no memo entry"
            );
            (output, replace.error, replace.changed)
        };
        assert_eq!(parts.counts().3, used);
        assert!(used <= limit);
        (result.0, result.1, used, result.2)
    }

    #[test]
    fn scalar_case_replacement_still_follows_actual_constant_and_local_definitions() {
        let mut env = Environment::new();
        env.init_nat().unwrap();
        env.add_decl(clean_kernel::Declaration::Definition {
            name: Name::from_string("case.scalar.seven"),
            level_params: vec![],
            type_: Expr::const_str("Nat"),
            value: Expr::nat_lit(7),
            is_reducible: true,
        })
        .unwrap();
        let mut scope = LocalScope::new();
        let checker = TypeChecker::new(&env);
        let source = Expr::const_str("case.scalar.seven");
        let (output, error, used, changed) =
            scalar_replacement(&checker, &scope, &source, &Expr::nat_lit(7), 8, false, 0);
        assert!(error.is_none() && changed);
        assert_eq!(output, Some(Expr::nat_lit(99)));
        assert_eq!(used, 8);
        let (output, error, used, changed) =
            scalar_replacement(&checker, &scope, &source, &Expr::nat_lit(8), 7, false, 0);
        assert!(error.is_none() && !changed && output.is_none());
        assert_eq!(used, 7);

        let input = scope.try_local(Expr::const_str("Nat")).unwrap();
        let alias = scope.try_local(Expr::const_str("Nat")).unwrap();
        let target = Expr::app(Expr::const_str("Nat.succ"), input.term().clone());
        let mut context = clean_kernel::LocalContext::new();
        context.push_with_id(
            input.id(),
            Name::from_string("input"),
            Expr::const_str("Nat"),
            clean_kernel::BinderInfo::Default,
        );
        context.push_let_with_id(
            alias.id(),
            Name::from_string("alias"),
            Expr::const_str("Nat"),
            target.clone(),
        );
        let checker = TypeChecker::with_context(&env, context);
        let (output, error, used, changed) =
            scalar_replacement(&checker, &scope, alias.term(), &target, 10, false, 0);
        assert!(error.is_none() && changed);
        assert_eq!(output, Some(Expr::nat_lit(99)));
        assert_eq!(used, 10);
    }

    #[test]
    fn scalar_case_replacement_keeps_frontier_depth_and_every_payment_cutoff() {
        let mut env = Environment::new();
        env.init_nat().unwrap();
        let checker = TypeChecker::new(&env);
        let scope = LocalScope::new();
        let source = Expr::nat_lit(7);
        for limit in 0..=8 {
            let (output, error, used, changed) =
                scalar_replacement(&checker, &scope, &source, &source, limit, false, 0);
            assert_eq!(changed, limit == 8);
            assert_eq!(error.is_none(), limit == 8);
            assert_eq!(output.is_some(), limit == 8);
            assert!(used <= limit);
        }
        let (output, error, used, changed) =
            scalar_replacement(&checker, &scope, &source, &source, 4, true, 0);
        assert!(error.is_none() && output.is_none() && !changed);
        assert_eq!(used, 4);
        let (output, error, used, changed) =
            scalar_replacement(&checker, &scope, &source, &source, 100, false, 9);
        assert!(error.unwrap().contains("depth limit") && output.is_none() && !changed);
        assert_eq!(used, 0);
        let (output, error, used, changed) =
            scalar_replacement(&checker, &scope, &Expr::bvar(0), &source, 4, false, 8);
        assert!(error.is_none() && output.is_none() && !changed);
        assert_eq!(used, 4);
    }

    fn search_candidate(
        checker: &TypeChecker<'_>,
        scope: &LocalScope,
        source: &Expr,
        limit: usize,
    ) -> (Option<Expr>, Option<String>, usize, usize) {
        let mut parts = ProofComponents::new("Case.atom.search", Default::default());
        parts.set_base(scope, vec![]).unwrap();
        let mut used = 0;
        let (found, error, retained) = {
            let mut work = Work {
                components: &mut parts,
                used: &mut used,
                limit,
            };
            let mut search = Search {
                checker,
                work: &mut work,
                depth: 0,
                max_depth: 8,
                seen: HashSet::new(),
                found: None,
                error: None,
            };
            let _unchanged = search.fold_expr_opt(source);
            (
                search.found.map(|case| case.term),
                search.error,
                search.seen.len(),
            )
        };
        assert_eq!(parts.counts().3, used);
        assert!(used <= limit);
        (found, error, used, retained)
    }

    #[test]
    fn case_atoms_skip_storage_and_prepay_every_remaining_cutoff() {
        let mut env = Environment::new();
        env.init_nat().unwrap();
        let mut scope = LocalScope::new();
        let parameter = scope.try_local(Expr::const_str("Nat")).unwrap();
        let missing = Expr::fvar(clean_kernel::expr::FVarId::new(900));
        let mut context = clean_kernel::LocalContext::new();
        context.push_with_id(
            parameter.id(),
            Name::from_string("parameter"),
            Expr::const_str("Nat"),
            clean_kernel::BinderInfo::Default,
        );
        let checker = TypeChecker::with_context(&env, context);
        let target = Expr::app(Expr::const_str("Nat.succ"), parameter.term().clone());
        for (source, required) in [
            (Expr::bvar(0), 1),
            (Expr::type_(), 1),
            (Expr::nat_lit(7), 1),
            (parameter.term().clone(), 2),
            (missing.clone(), 2),
        ] {
            assert_eq!(checker.whnf(&source), source);
            for limit in 0..=required + 1 {
                let (output, error, used, changed) =
                    scalar_replacement(&checker, &scope, &source, &target, limit, true, 0);
                assert!(output.is_none() && !changed);
                assert_eq!(error.is_none(), limit >= required);
                assert_eq!(used, limit.min(required));
                let (found, error, used, retained) =
                    search_candidate(&checker, &scope, &source, limit);
                assert!(found.is_none());
                assert_eq!(error.is_none(), limit >= required);
                assert_eq!(used, limit.min(required));
                assert_eq!(retained, 0);
            }
        }
        // Operational WHNF classification is never scope admission. The raw
        // absent FVar remains in the original graph and canonical close refuses it.
        assert!(scope.close(&missing).is_err());
        assert!(scope.close(parameter.term()).is_err());
    }

    #[test]
    fn case_atom_search_follows_a_current_let_definition_to_the_actual_case() {
        let mut env = Environment::new();
        env.init_nat().unwrap();
        let mut scope = LocalScope::new();
        let major = scope.try_local(Expr::const_str("Bool")).unwrap();
        let alias = scope.try_local(Expr::const_str("Nat")).unwrap();
        let target = at(
            "Bool.rec",
            vec![Level::zero()],
            [
                Expr::lam(
                    clean_kernel::BinderInfo::Default,
                    Expr::const_str("Bool"),
                    Expr::const_str("Nat"),
                ),
                Expr::nat_lit(0),
                Expr::nat_lit(1),
                major.term().clone(),
            ],
        );
        let mut context = clean_kernel::LocalContext::new();
        context.push_let_with_id(
            alias.id(),
            Name::from_string("alias"),
            Expr::const_str("Nat"),
            target.clone(),
        );
        let checker = TypeChecker::with_context(&env, context);
        let (found, error, _, retained) = search_candidate(&checker, &scope, alias.term(), 10_000);
        assert_eq!(found, Some(target));
        assert!(error.is_none());
        assert_eq!(retained, 1);
    }

    #[test]
    fn case_search_propagates_kernel_exhaustion_even_for_noncase_whnf() {
        let mut env = Environment::new();
        env.init_nat().unwrap();
        let scope = LocalScope::new();
        let mut checker = TypeChecker::new(&env);
        checker.set_heartbeat_limit(1);
        let (_, error, _, _) = search_candidate(&checker, &scope, &Expr::const_str("Nat.add"), 100);
        assert!(checker.heartbeat_spent());
        assert!(error.unwrap().contains("kernel budget"));
        let target = Expr::app(Expr::const_str("Nat.succ"), Expr::nat_lit(0));
        let (_, error, used, changed) =
            scalar_replacement(&checker, &scope, &Expr::nat_lit(7), &target, 1, false, 0);
        assert!(!changed && error.unwrap().contains("kernel budget"));
        assert_eq!(used, 1);
        let (_, error, used, retained) = search_candidate(&checker, &scope, &Expr::nat_lit(7), 1);
        assert!(error.unwrap().contains("kernel budget"));
        assert_eq!((used, retained), (1, 0));
    }

    fn cold() -> Expr {
        (0..80).fold(Expr::nat_lit(0), |value, _| {
            Expr::app(Expr::const_str("Nat.succ"), value)
        })
    }

    fn replacement(prepared: bool, numeric: bool, limit: usize) -> (bool, Option<String>, usize) {
        let mut env = Environment::new();
        env.init_nat().unwrap();
        let checker = TypeChecker::new(&env);
        let mut scope = LocalScope::new();
        let input = scope.try_local(Expr::const_str("Nat")).unwrap();
        let hole = scope.try_local(Expr::const_str("Nat")).unwrap();
        let mut parts = ProofComponents::new("Case.administrative.control", Default::default());
        parts
            .set_base(&scope, vec![OwnedProofCapture::Parameter(input.clone())])
            .unwrap();
        let mut external = parts
            .charged_external_context(&scope, std::slice::from_ref(&input))
            .unwrap();
        parts
            .charged_enable_external_materialization_reuse(&scope, &mut external)
            .unwrap();
        let expression = if numeric {
            Expr::apps(Expr::const_str("Nat.add"), [cold(), Expr::nat_lit(0)])
        } else {
            Expr::app(
                Expr::lam(
                    clean_kernel::BinderInfo::Default,
                    Expr::const_str("Nat"),
                    Expr::app(Expr::const_str("Nat.succ"), input.term().clone()),
                ),
                cold(),
            )
        };
        let before = parts.counts();
        let mut used = 0;
        let (changed, error) = {
            let mut work = Work {
                components: &mut parts,
                used: &mut used,
                limit,
            };
            let proper = HashSet::new();
            let mut replace = Replace {
                checker: &checker,
                target: input.term(),
                proper: &proper,
                hole: hole.term(),
                work: &mut work,
                depth: 0,
                max_depth: 20,
                memo: HashMap::new(),
                changed: false,
                error: None,
                scope: &scope,
                external: prepared.then_some(&external),
                max_app_args: 256,
                support: None,
            };
            let result = replace.fold_expr_opt(&expression);
            if replace.error.is_none() {
                assert_eq!(
                    result.unwrap(),
                    Expr::app(Expr::const_str("Nat.succ"), hole.term().clone())
                );
            }
            (replace.changed, replace.error)
        };
        assert!(used <= limit);
        assert_eq!(parts.counts().3 - before.3, used);
        assert_eq!(parts.counts().0, before.0);
        (changed, error, used)
    }

    #[test]
    fn prepared_administrative_replacement_uses_the_actual_closed_kernel_result() {
        let (changed, error, _) = replacement(true, false, 100_000);
        assert!(changed && error.is_none(), "{error:?}");
        let (_, error, _) = replacement(false, false, 100_000);
        assert!(error.unwrap().contains("depth limit"));
        let (_, error, _) = replacement(true, true, 100_000);
        assert!(error.unwrap().contains("depth limit"));
    }

    #[test]
    fn prepared_administrative_replacement_prepays_every_caller_cutoff() {
        let mut passed = 0;
        let mut refused = 0;
        for limit in 0..160 {
            let (_, error, _) = replacement(true, false, limit);
            if error.is_some() {
                refused += 1;
            } else {
                passed += 1;
            }
        }
        assert!(passed > 0 && refused > 0);
    }

    #[test]
    fn prepared_administrative_replacement_cannot_hide_an_unused_shadow_in_returned_graph() {
        let mut env = Environment::new();
        env.init_nat().unwrap();
        let checker = TypeChecker::new(&env);
        let mut scope = LocalScope::new();
        let input = scope.try_local(Expr::const_str("Nat")).unwrap();
        let shadow = scope.try_local(Expr::const_str("Nat")).unwrap();
        let hole = scope.try_local(Expr::const_str("Nat")).unwrap();
        let mut parts = ProofComponents::new("Case.administrative.shadow", Default::default());
        parts
            .set_base(
                &scope,
                vec![
                    OwnedProofCapture::Parameter(input.clone()),
                    OwnedProofCapture::Parameter(shadow.clone()),
                ],
            )
            .unwrap();
        let external = parts
            .charged_external_context(&scope, &[input.clone(), shadow.clone()])
            .unwrap();
        let expression = Expr::app(
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                Expr::const_str("Nat"),
                Expr::app(Expr::const_str("Nat.succ"), shadow.lam(Expr::nat_lit(0))),
            ),
            Expr::nat_lit(0),
        );
        let mut used = 0;
        let mut work = Work {
            components: &mut parts,
            used: &mut used,
            limit: 10_000,
        };
        let proper = HashSet::new();
        let mut replace = Replace {
            checker: &checker,
            target: input.term(),
            proper: &proper,
            hole: hole.term(),
            work: &mut work,
            depth: 0,
            max_depth: 20,
            memo: HashMap::new(),
            changed: false,
            error: None,
            scope: &scope,
            external: Some(&external),
            max_app_args: 256,
            support: None,
        };
        replace.fold_expr_opt(&expression);
        let error = replace.error.unwrap();
        assert_eq!(
            error,
            crate::term_scope::TermScopeError::ShadowedLocal(shadow.id()).to_string()
        );
        assert_eq!(parts.counts().0, 0);
    }
}

#[path = "cps_image_case_support.rs"]
mod support;
