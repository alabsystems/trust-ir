// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Untrusted projected-equality evidence over existing kernel observation terms.
//! Complete scoped closure, endpoint matching, kernel replay and rooted audit
//! are mandatory. This does not infer a CPS image, provider fidelity or ownership.
use crate::{
    cps_image_replay::ImageReplayLimits,
    proof_components::{OwnedProofCapture, ProofComponents},
    scoped_local::{ScopedLocal, ScopedLocalAllocator},
    semantic_evaluation::{
        CASE_MAP_BOOL, CASE_MAP_EXCEPT, CASE_MAP_OPTION, CASE_MAP_PROD, CASE_MAP_THEOREMS,
        LIST_PROJECTION,
    },
};
use clean_kernel::{Environment, Expr, Level, Name, TypeChecker, expr::ExprKind};
#[path = "projected_case_context.rs"]
mod case_context;
fn at(name: &str, levels: Vec<Level>, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(name), levels), args)
}
fn eq(u: &Level, ty: Expr, left: Expr, right: Expr) -> Expr {
    at("Eq", vec![Level::succ(u.clone())], [ty, left, right])
}
fn refl(u: &Level, ty: Expr, value: Expr) -> Expr {
    at("Eq.refl", vec![Level::succ(u.clone())], [ty, value])
}
#[derive(Debug)]
pub struct ProjectedEqualityCandidate {
    pub proposition: Expr,
    pub component_proposition: Expr,
    pub proof: Expr,
    pub cases: usize,
}
/// Candidate construction only; every strategy requires complete replay of the
/// same original external claim. Structural replay retains the direct case-map
/// path; correlated replay may commute a demanded state/outcome computation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProjectedCaseStrategy {
    Structural,
    Correlated,
}

/// Producer work observations, never evidence or an additional work allowance.
/// `initialization_complete` distinguishes unavailable initialization counters
/// from a completed initialization that happened to consume zero visits.
/// These count the existing case-context ledger, not initial input-forest closure or
/// kernel heartbeats, which retain their separate limits.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ProjectedEqualityWork {
    pub initialization_complete: bool,
    pub normalization_dependency_visits: usize,
    pub normalization_materialization_visits: usize,
    pub normalization_inventory_visits: usize,
    /// Charged identity/prefix checks for explicitly materialized definitions.
    pub normalization_cached_definition_visits: usize,
    pub identity_materialization_visits: usize,
    pub search_visits: usize,
    pub search_calls: usize,
    /// Unique/duplicate graph visits summed separately for each search call.
    pub search_unique_visits: usize,
    pub search_duplicate_visits: usize,
    /// Summary construction/probes, charged to the same context ledger.
    pub case_support_visits: usize,
    pub search_case_support_hits: usize,
    pub replacement_case_support_hits: usize,
    pub comparison_materialization_visits: usize,
    pub materialized_case_comparisons: usize,
    pub materialized_case_matches: usize,
    pub replacement_reduction_visits: usize,
    pub replacement_reductions: usize,
    /// The shared ledger immediately before the first search, if one ran.
    pub first_search_entry_work: Option<usize>,
    pub receiver_visits: usize,
    pub index_visits: usize,
    pub replacement_visits: usize,
    pub abstraction_visits: usize,
    pub computation_materialization_visits: usize,
    pub validation_visits: usize,
    pub structural_visits: usize,
    pub total_context_visits: usize,
    pub cases: usize,
}

impl ProjectedEqualityWork {
    fn record(&mut self, context_visits: usize, cases: usize) {
        self.total_context_visits = context_visits;
        self.cases = cases;
    }
}
#[derive(Clone, Copy, Eq, PartialEq)]
enum MaterializedValidationMode {
    PerReplace,
    #[cfg(test)]
    FreshInventory,
}
struct Node {
    source: Expr,
    proof: Expr,
    pending: usize,
}
struct Replay<'a, 'e, L> {
    allocator: &'a mut L,
    components: &'a mut ProofComponents,
    checker: TypeChecker<'e>,
    observed: Expr,
    result: Expr,
    project: Expr,
    expected: Expr,
    constant: Expr,
    captures: Vec<OwnedProofCapture>,
    globals: Vec<ScopedLocal>,
    u: Level,
    limits: ImageReplayLimits,
    cases: usize,
    strategy: ProjectedCaseStrategy,
    validation_mode: MaterializedValidationMode,
    context_work: usize,
    materialized_cache: crate::scoped_local::materialized::MaterializedCache,
    case_support: case_context::CaseSupportCache,
    list_projection_available: bool,
    work: &'a mut ProjectedEqualityWork,
}
impl<L: ScopedLocalAllocator> Replay<'_, '_, L> {
    fn visit_list(
        &mut self,
        args: Vec<Expr>,
        levels: Vec<Level>,
        depth: usize,
    ) -> Result<Node, String> {
        if !self.list_projection_available {
            return Err("projected list equality lacks checked list projection contract".into());
        }
        self.cases = self
            .cases
            .checked_add(1)
            .ok_or("projected list case overflow")?;
        if self.cases > self.limits.max_cases {
            return Err("projected equality case limit".into());
        }
        let zero = self.visit(args[2].clone(), depth + 1)?;
        let list = at("List", vec![levels[1].clone()], [args[0].clone()]);
        let locals = [args[0].clone(), list, self.observed.clone()]
            .into_iter()
            .map(|ty| self.allocator.allocate_local(ty))
            .collect::<Result<Vec<_>, _>>()?;
        let before = self.captures.len();
        self.captures
            .extend(locals.iter().cloned().map(OwnedProofCapture::Parameter));
        let branch = self.visit(
            Expr::apps(args[3].clone(), locals.iter().map(|l| l.term().clone())),
            depth + 1,
        );
        self.captures.truncate(before);
        let branch = branch?;
        let bind = |body| {
            locals
                .iter()
                .rev()
                .fold(body, |body, local| local.lam(body))
        };
        let step = bind(branch.source);
        let mut source = at(
            "List.rec",
            levels,
            [
                args[0].clone(),
                args[1].clone(),
                zero.source.clone(),
                step.clone(),
                args[4].clone(),
            ],
        );
        let proof = at(
            LIST_PROJECTION,
            vec![self.u.clone()],
            [
                args[0].clone(),
                self.observed.clone(),
                self.result.clone(),
                self.project.clone(),
                self.expected.clone(),
                zero.source,
                step,
                zero.proof,
                bind(branch.proof),
                args[4].clone(),
            ],
        );
        source = self.components.bind_scoped(
            self.allocator,
            &self.captures,
            self.observed.clone(),
            source,
        )?;
        let proposition = eq(
            &self.u,
            self.result.clone(),
            Expr::app(self.project.clone(), source.clone()),
            self.expected.clone(),
        );
        let proof =
            self.components
                .bind_scoped(self.allocator, &self.captures, proposition, proof)?;
        Ok(Node {
            source,
            proof,
            pending: 0,
        })
    }
    fn visit(&mut self, input: Expr, depth: usize) -> Result<Node, String> {
        if depth > self.limits.max_depth {
            return Err("projected equality depth limit".into());
        }
        let source = self.checker.whnf(&input);
        if source.get_app_num_args() > self.limits.max_app_args {
            return Err("projected equality application limit".into());
        }
        if self.strategy == ProjectedCaseStrategy::Structural
            && matches!(source.get_app_fn().kind(), ExprKind::Const(name, _)
                if matches!(name.to_string().as_str(), "Prod.rec" | "Except.rec" | "Option.rec" | "Bool.rec"))
        {
            // Demanded structural cases share correlated processing's fixed
            // preparation/work cap. Unread constructor fields remain cold.
            let limit = self
                .limits
                .max_cases
                .checked_mul(self.limits.max_app_args.max(1))
                .ok_or("projected structural case work overflow")?
                .min(1_000_000);
            if self.context_work >= limit {
                return Err("projected structural case aggregate work limit".into());
            }
            self.context_work += 1;
            self.work.structural_visits += 1;
        }
        if (self.strategy == ProjectedCaseStrategy::Correlated
            || matches!(source.kind(), ExprKind::Proj(..)))
            && let Some((normalized, equality)) = self.commute_nested_case(&source)?
        {
            let child = self.visit(normalized, depth + 1)?;
            let left = Expr::app(self.project.clone(), source.clone());
            let middle = Expr::app(self.project.clone(), child.source.clone());
            let mapped = at(
                "congrArg",
                vec![Level::succ(self.u.clone()), Level::succ(self.u.clone())],
                [
                    self.observed.clone(),
                    self.result.clone(),
                    source.clone(),
                    child.source,
                    self.project.clone(),
                    equality,
                ],
            );
            let proof = at(
                "Eq.trans",
                vec![Level::succ(self.u.clone())],
                [
                    self.result.clone(),
                    left,
                    middle,
                    self.expected.clone(),
                    mapped,
                    child.proof,
                ],
            );
            return Ok(Node {
                source,
                proof,
                pending: child.pending + 1,
            });
        }
        let head = source.get_app_fn().clone();
        let args = source
            .get_app_args()
            .iter()
            .map(|e| (*e).clone())
            .collect::<Vec<_>>();
        if let ExprKind::Const(name, levels) = head.kind()
            && name.to_string() == "List.rec"
            && args.len() == 5
            && levels.len() == 2
        {
            return self.visit_list(args, levels.to_vec(), depth);
        }
        let shape = if let ExprKind::Const(name, levels) = head.kind() {
            let name = name.to_string();
            let found = match name.as_str() {
                "Prod.rec" if args.len() == 5 && levels.len() == 3 => Some((
                    2,
                    vec![vec![args[0].clone(), args[1].clone()]],
                    CASE_MAP_PROD,
                )),
                "Except.rec" if args.len() == 6 && levels.len() == 3 => Some((
                    2,
                    vec![vec![args[0].clone()], vec![args[1].clone()]],
                    CASE_MAP_EXCEPT,
                )),
                "Option.rec" if args.len() == 5 && levels.len() == 2 => {
                    Some((1, vec![vec![], vec![args[0].clone()]], CASE_MAP_OPTION))
                }
                "Bool.rec" if args.len() == 4 && levels.len() == 1 => {
                    Some((0, vec![vec![], vec![]], CASE_MAP_BOOL))
                }
                _ => None,
            };
            found.map(|(p, f, t)| (name, levels.to_vec(), p, f, t))
        } else {
            None
        };
        let Some((name, levels, params, fields, theorem)) = shape else {
            // A constructor observation can hide a case inside the field read
            // by its projector. Replay that actual projected computation too;
            // no invariant or branch truth is introduced as a premise.
            let projected = self
                .checker
                .whnf(&Expr::app(self.project.clone(), source.clone()));
            let projected_case = match projected.get_app_fn().kind() {
                ExprKind::Const(name, _) => matches!(
                    name.to_string().as_str(),
                    "Prod.rec" | "Except.rec" | "Option.rec" | "Bool.rec" | "List.rec"
                ),
                _ => matches!(projected.kind(), ExprKind::Proj(..)),
            };
            // Progress only, never binder authentication or a proof premise.
            // WHNF can rebuild equal projections with new child allocations.
            if projected_case && projected != source {
                let argument = self.allocator.allocate_local(self.result.clone())?;
                let identity = argument.lam(argument.term().clone());
                // This fresh named binder was created after initial forest
                // materialization. Close it in this owner before the checker
                // evaluates applications; a named body is not a de Bruijn
                // identity until that scope walk has authenticated it.
                let limit = self
                    .limits
                    .max_cases
                    .checked_mul(self.limits.max_app_args.max(1))
                    .ok_or("projected identity work overflow")?
                    .min(1_000_000);
                let identity = self.materialize_case_computation(identity, limit)?;
                let observed = std::mem::replace(&mut self.observed, self.result.clone());
                let project = std::mem::replace(&mut self.project, identity);
                let candidate = self.visit(projected, depth + 1);
                self.observed = observed;
                self.project = project;
                let candidate = candidate?;
                return Ok(Node {
                    source,
                    proof: candidate.proof,
                    pending: candidate.pending,
                });
            }
            // This is a candidate proof, never a postcondition hypothesis.
            // A false projected leaf is rejected by complete kernel replay.
            return Ok(Node {
                source,
                proof: refl(&self.u, self.result.clone(), self.expected.clone()),
                pending: 0,
            });
        };
        self.cases = self
            .cases
            .checked_add(1)
            .ok_or("projected equality case overflow")?;
        if self.cases > self.limits.max_cases {
            return Err("projected equality case limit".into());
        }
        let mut compact = args[..params + 1].to_vec();
        let mut projected = Vec::new();
        let mut constants = Vec::new();
        let mut branch_equalities = Vec::new();
        let mut branch_reflexivities = Vec::new();
        let mut pending = 1usize;
        for (index, types) in fields.into_iter().enumerate() {
            let locals = types
                .into_iter()
                .map(|t| self.allocator.allocate_local(t))
                .collect::<Result<Vec<_>, _>>()?;
            let count = self.captures.len();
            self.captures
                .extend(locals.iter().cloned().map(OwnedProofCapture::Parameter));
            let branch = Expr::apps(
                args[params + 1 + index].clone(),
                locals.iter().map(|l| l.term().clone()),
            );
            let child = self.visit(branch, depth + 1);
            self.captures.truncate(count);
            let child = child?;
            pending = pending
                .checked_add(child.pending)
                .ok_or("projected equality grouping overflow")?;
            let bind = |body| locals.iter().rev().fold(body, |body, l| l.lam(body));
            let projection = Expr::app(self.project.clone(), child.source.clone());
            compact.push(bind(child.source));
            projected.push(bind(projection.clone()));
            constants.push(bind(self.expected.clone()));
            branch_reflexivities.push(bind(refl(&self.u, self.result.clone(), projection)));
            branch_equalities.push(bind(child.proof));
        }
        let major = args.last().unwrap().clone();
        compact.push(major.clone());
        let mut result_levels = levels.clone();
        result_levels[0] = Level::succ(self.u.clone());
        let mut projected_case = args[..params].to_vec();
        // All case motives are nondependent at this checked boundary. The
        // fixed case-map theorem and final replay reject incompatible motives.
        let major_type = match name.as_str() {
            "Prod.rec" => at("Prod", levels[1..].to_vec(), args[..params].to_vec()),
            "Except.rec" => at("Except", levels[1..].to_vec(), args[..params].to_vec()),
            "Option.rec" => at("Option", levels[1..].to_vec(), [args[0].clone()]),
            _ => Expr::const_str("Bool"),
        };
        let motive = self.allocator.allocate_local(major_type)?;
        projected_case.push(motive.lam(self.result.clone()));
        projected_case.extend(projected.iter().cloned());
        projected_case.push(major.clone());
        let middle = at(&name, result_levels, projected_case);
        let mut natural = args[..params].to_vec();
        natural.extend([
            self.observed.clone(),
            self.result.clone(),
            self.project.clone(),
        ]);
        natural.extend(projected.iter().cloned());
        natural.extend(compact[params + 1..compact.len() - 1].iter().cloned());
        natural.extend(branch_reflexivities);
        natural.push(major.clone());
        let natural = at(theorem, vec![self.u.clone()], natural);
        let mut constant = args[..params].to_vec();
        constant.extend([
            self.result.clone(),
            self.result.clone(),
            self.constant.clone(),
        ]);
        constant.extend(projected);
        constant.extend(constants);
        constant.extend(branch_equalities);
        constant.push(major);
        let constant = at(theorem, vec![self.u.clone()], constant);
        let mut compact = at(&name, levels, compact);
        let projected = Expr::app(self.project.clone(), compact.clone());
        let backwards = at(
            "Eq.symm",
            vec![Level::succ(self.u.clone())],
            [
                self.result.clone(),
                middle.clone(),
                projected.clone(),
                natural,
            ],
        );
        let proof = at(
            "Eq.trans",
            vec![Level::succ(self.u.clone())],
            [
                self.result.clone(),
                projected,
                middle,
                self.expected.clone(),
                backwards,
                constant,
            ],
        );
        let retain = depth == 0 || pending >= 32;
        let proof = if retain {
            compact = self.components.bind_scoped(
                self.allocator,
                &self.captures,
                self.observed.clone(),
                compact,
            )?;
            let proposition = eq(
                &self.u,
                self.result.clone(),
                Expr::app(self.project.clone(), compact.clone()),
                self.expected.clone(),
            );
            pending = 0;
            self.components
                .bind_scoped(self.allocator, &self.captures, proposition, proof)?
        } else {
            proof
        };
        Ok(Node {
            source: compact,
            proof,
            pending,
        })
    }
}
/// Both expressions are untrusted data. `dynamic` carries actual same-owner
/// local binders surrounding this proof; it never supplies a truth hypothesis.
pub fn replay_projected_equality<L: ScopedLocalAllocator>(
    env: &Environment,
    allocator: &mut L,
    globals: &[ScopedLocal],
    dynamic: &[OwnedProofCapture],
    observed_type: Expr,
    result_type: Expr,
    project: Expr,
    source: Expr,
    expected: Expr,
    u: Level,
    limits: ImageReplayLimits,
    components: &mut ProofComponents,
) -> Result<ProjectedEqualityCandidate, String> {
    replay_projected_equality_with_strategy(
        env,
        allocator,
        globals,
        dynamic,
        observed_type,
        result_type,
        project,
        source,
        expected,
        u,
        limits,
        components,
        ProjectedCaseStrategy::Correlated,
    )
}
/// Select an untrusted case producer without changing any verification gate.
pub fn replay_projected_equality_with_strategy<L: ScopedLocalAllocator>(
    env: &Environment,
    allocator: &mut L,
    globals: &[ScopedLocal],
    dynamic: &[OwnedProofCapture],
    observed_type: Expr,
    result_type: Expr,
    project: Expr,
    source: Expr,
    expected: Expr,
    u: Level,
    limits: ImageReplayLimits,
    components: &mut ProofComponents,
    strategy: ProjectedCaseStrategy,
) -> Result<ProjectedEqualityCandidate, String> {
    replay_projected_equality_with_diagnostics(
        env,
        allocator,
        globals,
        dynamic,
        observed_type,
        result_type,
        project,
        source,
        expected,
        u,
        limits,
        components,
        strategy,
    )
    .0
}

/// Run the same producer and return its measured work on success or refusal.
/// Counters do not authorize a candidate, reset a budget or replace complete
/// scoped/kernel replay. Initialization failures leave its flag false.
pub fn replay_projected_equality_with_diagnostics<L: ScopedLocalAllocator>(
    env: &Environment,
    allocator: &mut L,
    globals: &[ScopedLocal],
    dynamic: &[OwnedProofCapture],
    observed_type: Expr,
    result_type: Expr,
    project: Expr,
    source: Expr,
    expected: Expr,
    u: Level,
    limits: ImageReplayLimits,
    components: &mut ProofComponents,
    strategy: ProjectedCaseStrategy,
) -> (
    Result<ProjectedEqualityCandidate, String>,
    ProjectedEqualityWork,
) {
    let mut work = ProjectedEqualityWork::default();
    let result = replay_projected_equality_profiled(
        env,
        allocator,
        globals,
        dynamic,
        observed_type,
        result_type,
        project,
        source,
        expected,
        u,
        limits,
        components,
        strategy,
        MaterializedValidationMode::PerReplace,
        &mut work,
    );
    (result, work)
}

fn replay_projected_equality_profiled<L: ScopedLocalAllocator>(
    env: &Environment,
    allocator: &mut L,
    globals: &[ScopedLocal],
    dynamic: &[OwnedProofCapture],
    observed_type: Expr,
    result_type: Expr,
    project: Expr,
    source: Expr,
    expected: Expr,
    u: Level,
    limits: ImageReplayLimits,
    components: &mut ProofComponents,
    strategy: ProjectedCaseStrategy,
    validation_mode: MaterializedValidationMode,
    work: &mut ProjectedEqualityWork,
) -> Result<ProjectedEqualityCandidate, String> {
    if limits.max_depth > 256
        || limits.max_cases > 65536
        || limits.max_app_args > 4096
        || limits.heartbeats == 0
    {
        return Err("unsupported projected equality structural/kernel limits".into());
    }
    for name in CASE_MAP_THEOREMS {
        if env.get_const(&Name::from_string(name)).is_none() {
            return Err(format!("projected equality lacks {name}"));
        }
    }
    // Retained component references are registered locals too. Authenticate
    // their actual handles through the same owner before materialization;
    // never admit an erased id or a caller-supplied defining value instead.
    let retained = components.retained_normalization_locals(allocator.local_scope())?;
    let mut allowed = globals.to_vec();
    let mut ids = std::collections::HashSet::new();
    for local in globals {
        if !allocator.local_scope().owns(local) || !ids.insert(local.id()) {
            return Err("foreign or duplicate projected normalization global".into());
        }
    }
    for local in retained {
        if ids.insert(local.id()) {
            allowed.push(local);
        }
    }
    let input = [observed_type, result_type, project, source, expected];
    let (materialized, _) =
        allocator
            .local_scope()
            .close_external_forest(&input, &allowed, &[allowed.len(); 5]);
    let input = materialized.map_err(|e| e.to_string())?;
    let (context, _, normalization) =
        components.untrusted_normalization_context_profiled(allocator.local_scope(), &input)?;
    let observed = input[0].clone();
    let result = input[1].clone();
    let project = input[2].clone();
    let source = input[3].clone();
    let expected = input[4].clone();
    let ignored = allocator.allocate_local(result.clone())?;
    let constant = ignored.lam(expected.clone());
    // Transport only the requested result. The original frozen external claim
    // still names `project source`; discarded observation fields supply no
    // premise. Materialize the same owner's identity binder before WHNF.
    let identity_local = allocator.allocate_local(result.clone())?;
    let identity = identity_local.lam(identity_local.term().clone());
    let (identity, identity_work) =
        allocator
            .local_scope()
            .close_external_forest(&[identity], &allowed, &[allowed.len()]);
    let identity = identity.map_err(|e| e.to_string())?.remove(0);
    let normalization_work = normalization.total()?.saturating_add(identity_work.visits);
    work.normalization_dependency_visits = normalization.dependency_visits;
    work.normalization_materialization_visits = normalization.materialization_visits;
    work.normalization_inventory_visits = normalization.inventory_visits;
    work.normalization_cached_definition_visits = normalization.cached_definition_visits;
    work.identity_materialization_visits = identity_work.visits;
    work.initialization_complete = true;
    work.total_context_visits = normalization_work;
    let projected_source = Expr::app(project.clone(), source.clone());
    // Freeze the same owner's existing untrusted definitions once. They are
    // normalization inputs, not checked premises; complete replay still checks
    // all of them, including unused/ill-typed entries. No checker budget resets.
    let mut checker = TypeChecker::with_context(env, context);
    checker.set_heartbeat_limit(limits.heartbeats);
    checker.set_max_cache_entries(limits.max_cache_entries);
    let projected_head = checker.whnf(&projected_source);
    let original_head = checker.whnf(&source);
    // Keep the existing List projection contract (with its explicit recursive
    // observation premise), and retain ordinary case admission when projection
    // erased the entire discriminator. Only demanded nonrecursive cases move
    // into the projected-result context.
    let project_first = strategy == ProjectedCaseStrategy::Correlated
        && matches!(projected_head.get_app_fn().kind(),
        ExprKind::Const(name, _) if matches!(name.to_string().as_str(),
            "Prod.rec" | "Except.rec" | "Option.rec" | "Bool.rec"))
        && !matches!(original_head.get_app_fn().kind(),
            ExprKind::Const(name, _) if name.to_string() == "List.rec");
    let output_projection = if project_first {
        identity
    } else {
        project.clone()
    };
    let replay_source = if project_first {
        projected_head
    } else {
        source.clone()
    };
    let mut replay = Replay {
        allocator,
        components,
        checker,
        observed: if project_first {
            result.clone()
        } else {
            observed
        },
        result: result.clone(),
        project: output_projection.clone(),
        expected: expected.clone(),
        constant,
        captures: dynamic.to_vec(),
        globals: allowed,
        u: u.clone(),
        limits,
        cases: 0,
        strategy,
        validation_mode,
        context_work: normalization_work,
        materialized_cache: Default::default(),
        case_support: Default::default(),
        list_projection_available: env.get_const(&Name::from_string(LIST_PROJECTION)).is_some(),
        work,
    };
    let output = replay.visit(replay_source, 0);
    replay.work.record(replay.context_work, replay.cases);
    let output = output?;
    Ok(ProjectedEqualityCandidate {
        proposition: eq(
            &u,
            result.clone(),
            Expr::app(project.clone(), source),
            expected.clone(),
        ),
        component_proposition: eq(
            &u,
            result,
            Expr::app(output_projection, output.source),
            expected,
        ),
        proof: output.proof,
        cases: replay.cases,
    })
}

#[cfg(test)]
#[path = "projected_equality_work_tests.rs"]
mod work_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        proof_assembly::ProofLimits, scoped_local::LocalScope, semantic_evaluation,
        term_scope::TermScopeLimits,
    };
    pub(super) fn n() -> Expr {
        Expr::const_str("Nat")
    }
    fn a(name: &str, count: usize, args: impl IntoIterator<Item = Expr>) -> Expr {
        at(name, vec![Level::zero(); count], args)
    }
    pub(super) fn fixture(sc: &mut LocalScope) -> (Vec<ScopedLocal>, Expr, Expr, Expr, Expr) {
        let flag = sc.allocate_local(Expr::const_str("Bool")).unwrap();
        let state_type = a("Prod", 2, [n(), n()]);
        let state = sc.allocate_local(state_type.clone()).unwrap();
        let status = a("Except", 2, [n(), n()]);
        let observed = a("Prod", 2, [state_type.clone(), status.clone()]);
        let frame = a("Prod.snd", 2, [n(), n(), state.term().clone()]);
        let leaf = |user, ok| {
            a(
                "Prod.mk",
                2,
                [
                    state_type.clone(),
                    status.clone(),
                    a("Prod.mk", 2, [n(), n(), Expr::nat_lit(user), frame.clone()]),
                    a(
                        if ok { "Except.ok" } else { "Except.error" },
                        2,
                        [n(), n(), Expr::nat_lit(if ok { 7 } else { 6 })],
                    ),
                ],
            )
        };
        let motive = sc.allocate_local(Expr::const_str("Bool")).unwrap();
        let source = at(
            "Bool.rec",
            vec![Level::succ(Level::zero())],
            [
                motive.lam(observed.clone()),
                leaf(8, false),
                leaf(9, true),
                flag.term().clone(),
            ],
        );
        let input = sc.allocate_local(observed.clone()).unwrap();
        let project = input.lam(a(
            "Prod.snd",
            2,
            [
                n(),
                n(),
                a("Prod.fst", 2, [state_type, status, input.term().clone()]),
            ],
        ));
        (vec![flag, state], observed, project, source, frame)
    }
    pub(super) fn environment() -> Environment {
        let mut env = semantic_evaluation::build_environment().unwrap();
        semantic_evaluation::install_case_maps_into(&mut env).unwrap();
        env.init_nat().unwrap();
        env
    }
    #[test]
    fn projected_equality_checks_frame_paths_and_refuses_a_well_typed_false_property() {
        let env = environment();
        for (strategy, correct) in [
            (ProjectedCaseStrategy::Structural, true),
            (ProjectedCaseStrategy::Structural, false),
            (ProjectedCaseStrategy::Correlated, true),
            (ProjectedCaseStrategy::Correlated, false),
        ] {
            let mut sc = LocalScope::new();
            let (globals, observed, project, source, expected) = fixture(&mut sc);
            let expected = if correct { expected } else { Expr::nat_lit(5) };
            let mut parts = ProofComponents::new("projection.frame", ProofLimits::default());
            parts
                .set_base(
                    &sc,
                    globals
                        .iter()
                        .cloned()
                        .map(OwnedProofCapture::Parameter)
                        .collect(),
                )
                .unwrap();
            let candidate = replay_projected_equality_with_strategy(
                &env,
                &mut sc,
                &globals,
                &[],
                observed,
                n(),
                project,
                source,
                expected,
                Level::zero(),
                ImageReplayLimits::default(),
                &mut parts,
                strategy,
            )
            .unwrap();
            assert_eq!(candidate.cases, 1);
            let claim = sc
                .close(
                    &globals
                        .iter()
                        .rev()
                        .fold(candidate.proposition, |b, l| l.pi(b)),
                )
                .unwrap();
            assert!(TypeChecker::new(&env).infer_type(&claim).is_ok());
            let root = globals.iter().rev().fold(candidate.proof, |b, l| l.lam(b));
            let bundle = parts
                .close_scoped(
                    &sc,
                    root,
                    candidate.component_proposition,
                    TermScopeLimits::default(),
                )
                .unwrap();
            let wire = bundle.encode_with_claim(&claim).unwrap();
            let (decoded, transported) =
                crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&wire)
                    .unwrap();
            assert_eq!(claim, transported);
            let result = decoded.replay(&env, &claim, 2_000_000);
            if correct {
                result.unwrap();
            } else {
                assert!(
                    result.is_err(),
                    "false frame postcondition must not be a hypothesis"
                );
            }
        }
    }
    #[test]
    fn projected_equality_replays_cases_exposed_by_a_constructor_projection() {
        let env = environment();
        for (mode, strategy) in (0..5).flat_map(|mode| {
            [
                ProjectedCaseStrategy::Structural,
                ProjectedCaseStrategy::Correlated,
            ]
            .map(|strategy| (mode, strategy))
        }) {
            let correct = mode != 1;
            let mut sc = LocalScope::new();
            let flag = sc.allocate_local(Expr::const_str("Bool")).unwrap();
            let observed = a("Prod", 2, [Expr::const_str("Bool"), n()]);
            let source = a(
                "Prod.mk",
                2,
                [
                    Expr::const_str("Bool"),
                    n(),
                    flag.term().clone(),
                    Expr::nat_lit(13),
                ],
            );
            let input = sc.allocate_local(observed.clone()).unwrap();
            let motive = sc.allocate_local(Expr::const_str("Bool")).unwrap();
            let project = input.lam(at(
                "Bool.rec",
                vec![Level::succ(Level::zero())],
                [
                    motive.lam(n()),
                    Expr::nat_lit(7),
                    Expr::nat_lit(if correct { 7 } else { 9 }),
                    a(
                        "Prod.fst",
                        2,
                        [Expr::const_str("Bool"), n(), input.term().clone()],
                    ),
                ],
            ));
            let globals = vec![flag];
            let mut parts = ProofComponents::new("projection.constructor", ProofLimits::default());
            parts
                .set_base(
                    &sc,
                    globals
                        .iter()
                        .cloned()
                        .map(OwnedProofCapture::Parameter)
                        .collect(),
                )
                .unwrap();
            let external = eq(
                &Level::zero(),
                n(),
                Expr::app(project.clone(), source.clone()),
                Expr::nat_lit(7),
            );
            let source = if mode >= 3 {
                let argument = sc.allocate_local(Expr::const_str("Bool")).unwrap();
                let type_ = argument.pi(observed.clone());
                let value = argument.lam(a(
                    "Prod.mk",
                    2,
                    [
                        Expr::const_str("Bool"),
                        n(),
                        argument.term().clone(),
                        Expr::nat_lit(13),
                    ],
                ));
                let function = parts
                    .bind_scoped(&mut sc, &[], type_.clone(), value)
                    .unwrap();
                let function = if mode == 4 {
                    // Reachable aliases must include the transitive defining
                    // function; an unrelated owned function stays in the final
                    // artifact but is not a producer normalization dependency.
                    let argument = sc.allocate_local(n()).unwrap();
                    let mut unused = argument.term().clone();
                    for _ in 0..300 {
                        unused = Expr::app(Expr::const_str("Nat.succ"), unused);
                    }
                    let _retained = parts
                        .bind_scoped(&mut sc, &[], argument.pi(n()), argument.lam(unused))
                        .unwrap();
                    parts.bind_scoped(&mut sc, &[], type_, function).unwrap()
                } else {
                    function
                };
                Expr::app(function, globals[0].term().clone())
            } else {
                parts
                    .bind_scoped(&mut sc, &[], observed.clone(), source)
                    .unwrap()
            };
            if mode == 2 {
                let false_claim = eq(&Level::zero(), n(), Expr::nat_lit(0), Expr::nat_lit(1));
                let false_proof = refl(&Level::zero(), n(), Expr::nat_lit(0));
                let _untrusted_definition = parts
                    .bind_scoped(&mut sc, &[], false_claim, false_proof)
                    .unwrap();
            }
            let candidate = replay_projected_equality_with_strategy(
                &env,
                &mut sc,
                &globals,
                &[],
                observed,
                n(),
                project,
                source,
                Expr::nat_lit(7),
                Level::zero(),
                ImageReplayLimits::default(),
                &mut parts,
                strategy,
            )
            .unwrap();
            assert_eq!(candidate.cases, 1);
            let claim = sc
                .close(&globals.iter().rev().fold(external, |b, l| l.pi(b)))
                .unwrap();
            assert!(TypeChecker::new(&env).infer_type(&claim).is_ok());
            let root = globals.iter().rev().fold(candidate.proof, |b, l| l.lam(b));
            let bundle = parts
                .close_scoped(
                    &sc,
                    root,
                    candidate.component_proposition,
                    TermScopeLimits::default(),
                )
                .unwrap();
            let wire = bundle.encode_with_claim(&claim).unwrap();
            let (decoded, transported) =
                crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&wire)
                    .unwrap();
            assert_eq!(claim, transported);
            let checked = decoded.replay(&env, &claim, 2_000_000);
            assert_eq!(
                checked.is_ok(),
                mode == 0 || mode >= 3,
                "a hidden false branch must remain rejected"
            );
        }
    }
    #[test]
    fn projected_equality_keeps_correlated_state_and_outcome_cases() {
        let env = environment();
        for correct in [true, false] {
            let mut sc = LocalScope::new();
            let outcome = a("Except", 2, [n(), n()]);
            let state = a("Prod", 2, [n(), n()]);
            let observed = a("Prod", 2, [state.clone(), outcome.clone()]);
            let raw = sc.allocate_local(outcome.clone()).unwrap();
            let frame = sc.allocate_local(n()).unwrap();
            let base_function = sc.allocate_local(Expr::arrow(n(), n())).unwrap();
            let mut base = Expr::nat_lit(8);
            for _ in 0..300 {
                base = Expr::app(base_function.term().clone(), base);
            }

            let raw_major = sc.allocate_local(outcome.clone()).unwrap();
            let error = sc.allocate_local(n()).unwrap();
            let value = sc.allocate_local(n()).unwrap();
            let pair = |frame, status| {
                a(
                    "Prod.mk",
                    2,
                    [
                        state.clone(),
                        outcome.clone(),
                        a("Prod.mk", 2, [n(), n(), base.clone(), frame]),
                        status,
                    ],
                )
            };
            let run = at(
                "Except.rec",
                vec![Level::succ(Level::zero()), Level::zero(), Level::zero()],
                [
                    n(),
                    n(),
                    raw_major.lam(observed.clone()),
                    error.lam(pair(
                        error.term().clone(),
                        a("Except.error", 2, [n(), n(), Expr::nat_lit(0)]),
                    )),
                    value.lam(pair(
                        if correct {
                            frame.term().clone()
                        } else {
                            Expr::nat_lit(99)
                        },
                        a("Except.ok", 2, [n(), n(), value.term().clone()]),
                    )),
                    raw.term().clone(),
                ],
            );
            let post = a(
                "Prod.mk",
                2,
                [
                    n(),
                    n(),
                    base.clone(),
                    a(
                        "Prod.snd",
                        2,
                        [
                            n(),
                            n(),
                            a("Prod.fst", 2, [state.clone(), outcome.clone(), run.clone()]),
                        ],
                    ),
                ],
            );
            let status = a("Prod.snd", 2, [state.clone(), outcome.clone(), run]);
            let major = sc.allocate_local(outcome.clone()).unwrap();
            let failure = sc.allocate_local(n()).unwrap();
            let success = sc.allocate_local(n()).unwrap();
            let output = |status| {
                a(
                    "Prod.mk",
                    2,
                    [state.clone(), outcome.clone(), post.clone(), status],
                )
            };
            let source = at(
                "Except.rec",
                vec![Level::succ(Level::zero()), Level::zero(), Level::zero()],
                [
                    n(),
                    n(),
                    major.lam(observed.clone()),
                    failure.lam(output(a(
                        "Except.error",
                        2,
                        [n(), n(), failure.term().clone()],
                    ))),
                    success.lam(output(a("Except.ok", 2, [n(), n(), Expr::nat_lit(7)]))),
                    status,
                ],
            );
            let input = sc.allocate_local(observed.clone()).unwrap();
            let ignored = sc.allocate_local(outcome.clone()).unwrap();
            let err = sc.allocate_local(n()).unwrap();
            let ok = sc.allocate_local(n()).unwrap();
            let projection = at(
                "Except.rec",
                vec![Level::succ(Level::zero()), Level::zero(), Level::zero()],
                [
                    n(),
                    n(),
                    ignored.lam(n()),
                    err.lam(frame.term().clone()),
                    ok.lam(a(
                        "Prod.snd",
                        2,
                        [
                            n(),
                            n(),
                            a(
                                "Prod.fst",
                                2,
                                [state, outcome.clone(), input.term().clone()],
                            ),
                        ],
                    )),
                    a(
                        "Prod.snd",
                        2,
                        [a("Prod", 2, [n(), n()]), outcome, input.term().clone()],
                    ),
                ],
            );
            let project = input.lam(projection);
            let globals = vec![raw, frame.clone(), base_function];
            let mut parts = ProofComponents::new("projection.correlated", ProofLimits::default());
            parts
                .set_base(
                    &sc,
                    globals
                        .iter()
                        .cloned()
                        .map(OwnedProofCapture::Parameter)
                        .collect(),
                )
                .unwrap();
            let (candidate, work) = replay_projected_equality_with_diagnostics(
                &env,
                &mut sc,
                &globals,
                &[],
                observed,
                n(),
                project,
                source,
                frame.term().clone(),
                Level::zero(),
                ImageReplayLimits::default(),
                &mut parts,
                ProjectedCaseStrategy::Correlated,
            );
            let candidate = candidate.unwrap();
            assert_eq!(work.total_context_visits, super::work_tests::counted(&work));
            assert_eq!(
                work.search_visits,
                work.search_unique_visits + work.search_duplicate_visits
            );
            assert!(work.index_visits > 0 && work.replacement_visits > 0);
            assert!(work.abstraction_visits > 0 && work.validation_visits > 0);
            eprintln!("projected correlated work (correct={correct}): {work:?}");
            let claim = sc
                .close(
                    &globals
                        .iter()
                        .rev()
                        .fold(candidate.proposition, |b, l| l.pi(b)),
                )
                .unwrap();
            assert!(TypeChecker::new(&env).infer_type(&claim).is_ok());
            let root = globals.iter().rev().fold(candidate.proof, |b, l| l.lam(b));
            let bundle = parts
                .close_scoped(
                    &sc,
                    root,
                    candidate.component_proposition,
                    TermScopeLimits::default(),
                )
                .unwrap();
            let wire = bundle.encode_with_claim(&claim).unwrap();
            let (decoded, transported) =
                crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&wire)
                    .unwrap();
            assert_eq!(claim, transported);
            let checked = decoded.replay(&env, &claim, 2_000_000);
            assert_eq!(
                checked.is_ok(),
                correct,
                "a changed successful frame is not a premise"
            );
        }
    }
    #[test]
    fn projected_equality_strategies_share_demanded_case_preparation_budget() {
        let env = environment();
        for strategy in [
            ProjectedCaseStrategy::Structural,
            ProjectedCaseStrategy::Correlated,
        ] {
            let mut sc = LocalScope::new();
            let (mut globals, observed, project, source, frame) = fixture(&mut sc);
            fn tree(
                sc: &mut LocalScope,
                globals: &mut Vec<ScopedLocal>,
                depth: u32,
            ) -> (Expr, Expr) {
                if depth == 0 {
                    let leaf = sc.allocate_local(n()).unwrap();
                    globals.push(leaf.clone());
                    return (n(), leaf.term().clone());
                }
                let (left_ty, left) = tree(sc, globals, depth - 1);
                let (right_ty, right) = tree(sc, globals, depth - 1);
                (
                    a("Prod", 2, [left_ty.clone(), right_ty.clone()]),
                    a("Prod.mk", 2, [left_ty, right_ty, left, right]),
                )
            }
            let (ty, data) = tree(&mut sc, &mut globals, 7);
            let selector = sc
                .allocate_local(Expr::arrow(ty, Expr::const_str("Bool")))
                .unwrap();
            globals.push(selector.clone());
            let mut args = source
                .get_app_args()
                .iter()
                .map(|arg| (*arg).clone())
                .collect::<Vec<_>>();
            *args.last_mut().unwrap() = Expr::app(selector.term().clone(), data);
            let source = Expr::apps(source.get_app_fn().clone(), args);
            let mut parts =
                ProofComponents::new("projection.strategy.budget", ProofLimits::default());
            parts
                .set_base(
                    &sc,
                    globals
                        .iter()
                        .cloned()
                        .map(OwnedProofCapture::Parameter)
                        .collect(),
                )
                .unwrap();
            let error = replay_projected_equality_with_strategy(
                &env,
                &mut sc,
                &globals,
                &[],
                observed,
                n(),
                project,
                source,
                frame,
                Level::zero(),
                ImageReplayLimits {
                    max_cases: 1,
                    ..Default::default()
                },
                &mut parts,
                strategy,
            )
            .expect_err("a demanded case cannot bypass preparation work by selecting a producer");
            assert!(error.contains("work limit"), "unexpected refusal: {error}");
        }
    }
    #[test]
    fn projected_equality_keeps_unobserved_base_cases_cold_under_the_case_budget() {
        let env = environment();
        for correct in [true, false] {
            let mut sc = LocalScope::new();
            let flag = sc.allocate_local(Expr::const_str("Bool")).unwrap();
            let frame = sc.allocate_local(n()).unwrap();
            let motive = sc.allocate_local(Expr::const_str("Bool")).unwrap();
            let base = at(
                "Bool.rec",
                vec![Level::succ(Level::zero())],
                [
                    motive.lam(n()),
                    Expr::nat_lit(3),
                    Expr::nat_lit(4),
                    flag.term().clone(),
                ],
            );
            let state = a("Prod", 2, [n(), n()]);
            let outcome = a("Except", 2, [n(), n()]);
            let observed = a("Prod", 2, [state.clone(), outcome.clone()]);
            let source = a(
                "Prod.mk",
                2,
                [
                    state.clone(),
                    outcome.clone(),
                    a(
                        "Prod.mk",
                        2,
                        [
                            n(),
                            n(),
                            base,
                            if correct {
                                frame.term().clone()
                            } else {
                                Expr::nat_lit(99)
                            },
                        ],
                    ),
                    a("Except.ok", 2, [n(), n(), Expr::nat_lit(7)]),
                ],
            );
            let input = sc.allocate_local(observed.clone()).unwrap();
            let project = input.lam(a(
                "Prod.snd",
                2,
                [
                    n(),
                    n(),
                    a("Prod.fst", 2, [state, outcome, input.term().clone()]),
                ],
            ));
            let globals = vec![flag, frame.clone()];
            let mut parts = ProofComponents::new("projection.cold.base", ProofLimits::default());
            parts
                .set_base(
                    &sc,
                    globals
                        .iter()
                        .cloned()
                        .map(OwnedProofCapture::Parameter)
                        .collect(),
                )
                .unwrap();
            let limits = ImageReplayLimits {
                max_cases: 1,
                ..Default::default()
            };
            let candidate = replay_projected_equality(
                &env,
                &mut sc,
                &globals,
                &[],
                observed,
                n(),
                project,
                source,
                frame.term().clone(),
                Level::zero(),
                limits,
                &mut parts,
            )
            .unwrap();
            assert_eq!(
                candidate.cases, 0,
                "unread base cases do not require case elimination"
            );
            let claim = sc
                .close(
                    &globals
                        .iter()
                        .rev()
                        .fold(candidate.proposition, |b, l| l.pi(b)),
                )
                .unwrap();
            assert!(TypeChecker::new(&env).infer_type(&claim).is_ok());
            let root = globals.iter().rev().fold(candidate.proof, |b, l| l.lam(b));
            let bundle = parts
                .close_scoped(
                    &sc,
                    root,
                    candidate.component_proposition,
                    TermScopeLimits::default(),
                )
                .unwrap();
            let wire = bundle.encode_with_claim(&claim).unwrap();
            let (decoded, transported) =
                crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&wire)
                    .unwrap();
            assert_eq!(claim, transported);
            let checked = decoded.replay(&env, &claim, 2_000_000);
            assert_eq!(
                checked.is_ok(),
                correct,
                "a false observed frame remains rejected even when its base is cold"
            );
        }
    }
    #[test]
    fn projected_equality_list_branches_never_assume_recursive_frame_fidelity() {
        let mut env = environment();
        semantic_evaluation::install_list_projection_into(&mut env).unwrap();
        for mode in 0..3 {
            let mut sc = LocalScope::new();
            let list = at("List", vec![Level::zero()], [n()]);
            let xs = sc.allocate_local(list.clone()).unwrap();
            let frame = sc.allocate_local(n()).unwrap();
            let observed = a("Prod", 2, [n(), n()]);
            let pair = |user, fr| a("Prod.mk", 2, [n(), n(), user, fr]);
            let major = sc.allocate_local(list.clone()).unwrap();
            let head = sc.allocate_local(n()).unwrap();
            let tail = sc.allocate_local(list).unwrap();
            let previous = sc.allocate_local(observed.clone()).unwrap();
            let body = match mode {
                0 => pair(head.term().clone(), frame.term().clone()),
                1 => pair(head.term().clone(), Expr::nat_lit(99)),
                _ => previous.term().clone(),
            };
            let next = head.lam(tail.lam(previous.lam(body)));
            let source = at(
                "List.rec",
                vec![Level::succ(Level::zero()), Level::zero()],
                [
                    n(),
                    major.lam(observed.clone()),
                    pair(Expr::nat_lit(0), frame.term().clone()),
                    next,
                    xs.term().clone(),
                ],
            );
            let input = sc.allocate_local(observed.clone()).unwrap();
            let project = input.lam(a("Prod.snd", 2, [n(), n(), input.term().clone()]));
            let globals = vec![xs, frame.clone()];
            let mut parts = ProofComponents::new("projection.list", ProofLimits::default());
            parts
                .set_base(
                    &sc,
                    globals
                        .iter()
                        .cloned()
                        .map(OwnedProofCapture::Parameter)
                        .collect(),
                )
                .unwrap();
            let candidate = replay_projected_equality(
                &env,
                &mut sc,
                &globals,
                &[],
                observed,
                n(),
                project,
                source,
                frame.term().clone(),
                Level::zero(),
                ImageReplayLimits::default(),
                &mut parts,
            )
            .unwrap();
            let claim = sc
                .close(
                    &globals
                        .iter()
                        .rev()
                        .fold(candidate.proposition, |b, l| l.pi(b)),
                )
                .unwrap();
            assert!(TypeChecker::new(&env).infer_type(&claim).is_ok());
            let root = globals.iter().rev().fold(candidate.proof, |b, l| l.lam(b));
            let bundle = parts
                .close_scoped(
                    &sc,
                    root,
                    candidate.component_proposition,
                    TermScopeLimits::default(),
                )
                .unwrap();
            let wire = bundle.encode_with_claim(&claim).unwrap();
            let (bundle, transported) =
                crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&wire)
                    .unwrap();
            assert_eq!(claim, transported);
            let checked = bundle.replay(&env, &claim, 2_000_000);
            if mode == 0 {
                checked.unwrap();
            } else {
                assert!(
                    checked.is_err(),
                    "neither a false frame nor unproved recursive observation invariant is a premise"
                );
            }
        }
    }
    #[test]
    fn projected_equality_refuses_same_erased_id_foreign_handle_and_case_budget() {
        let env = environment();
        let mut sc = LocalScope::new();
        let (globals, observed, project, source, expected) = fixture(&mut sc);
        let mut other = LocalScope::new();
        let foreign = (0..16)
            .map(|_| other.allocate_local(globals[0].ty().clone()).unwrap())
            .find(|l| l.id() == globals[0].id())
            .unwrap();
        assert_eq!(foreign.term(), globals[0].term());
        assert_eq!(foreign.ty(), globals[0].ty());
        let mut parts = ProofComponents::new("projection.foreign", ProofLimits::default());
        parts
            .set_base(
                &sc,
                globals
                    .iter()
                    .cloned()
                    .map(OwnedProofCapture::Parameter)
                    .collect(),
            )
            .unwrap();
        assert!(
            replay_projected_equality(
                &env,
                &mut sc,
                &[foreign, globals[1].clone()],
                &[],
                observed.clone(),
                n(),
                project.clone(),
                source.clone(),
                expected.clone(),
                Level::zero(),
                ImageReplayLimits::default(),
                &mut parts
            )
            .is_err()
        );
        let limits = ImageReplayLimits {
            max_cases: 0,
            ..ImageReplayLimits::default()
        };
        assert!(
            replay_projected_equality(
                &env,
                &mut sc,
                &globals,
                &[],
                observed,
                n(),
                project,
                source,
                expected,
                Level::zero(),
                limits,
                &mut parts
            )
            .is_err()
        );
    }
}

#[cfg(test)]
#[path = "projected_equality_service_tests.rs"]
mod service_tests;

#[cfg(test)]
#[path = "projected_equality_recomputed_tests.rs"]
mod recomputed_tests;

#[cfg(test)]
#[path = "projected_materialized_context_tests.rs"]
mod materialized_context_tests;

#[cfg(test)]
#[path = "projected_equality_list_receiver_tests.rs"]
mod list_receiver_tests;
