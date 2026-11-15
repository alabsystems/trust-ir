// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Produce an untrusted first-order image candidate from an existing CPS term.
//!
//! This is proof replay over kernel terms, not an IR compiler. Only actual final
//! callbacks and nonrecursive kernel data eliminators are recognized. Opaque CPS
//! providers refuse; callers must first supply their genuine first-order meaning.
//! The original source term remains the endpoint of the returned proposition.
//! Close the complete graph with the SAME allocator, kernel check and audit it.
use crate::proof_components::{OwnedProofCapture, OwnedScopedDefinition, ProofComponents};
use crate::scoped_local::{ScopedLocal, ScopedLocalAllocator};
use crate::semantic_evaluation::{
    CASE_MAP_BOOL, CASE_MAP_EXCEPT, CASE_MAP_OPTION, CASE_MAP_PROD, CASE_MAP_THEOREMS, CPS_IMAGE,
    TO_CPS,
};
use clean_kernel::{Expr, Level, Name, TypeChecker, env::Environment, expr::ExprKind};
use std::collections::{HashMap, HashSet};

/// Candidate pointwise code equality for one exact retained owned operation.
/// Both the operation and proof must be real component DEFINITIONS, not truth
/// parameters. The complete original values/claim must still replay; no field
/// here is certification or physical-provider authority.
#[derive(Clone)]
pub struct CpsCallEquation {
    pub operator: ScopedLocal,
    pub replacement: Expr,
    pub proof: crate::proof_components::OwnedScopedDefinition,
    pub arity: usize,
}
/// Actual owned equation declaration for structured replay. No stand-in code
/// field is consumed. Its authentic type is prepared only at a reached call;
/// every unused definition/value still MUST pass complete original replay.
#[derive(Clone)]
pub struct OwnedCpsCallEquation {
    pub operator: ScopedLocal,
    pub proof: crate::proof_components::OwnedScopedDefinition,
    pub arity: usize,
}
impl From<&CpsCallEquation> for OwnedCpsCallEquation {
    fn from(e: &CpsCallEquation) -> Self {
        Self {
            operator: e.operator.clone(),
            proof: e.proof.clone(),
            arity: e.arity,
        }
    }
}
impl From<CpsCallEquation> for OwnedCpsCallEquation {
    fn from(e: CpsCallEquation) -> Self {
        Self {
            operator: e.operator,
            proof: e.proof,
            arity: e.arity,
        }
    }
}
enum EquationProfile<'a> {
    Legacy(&'a [CpsCallEquation]),
    Structured(&'a [OwnedCpsCallEquation]),
}
struct EquationReference<'a> {
    operator: &'a ScopedLocal,
    proof: &'a crate::proof_components::OwnedScopedDefinition,
    arity: usize,
}
impl EquationProfile<'_> {
    fn len(&self) -> usize {
        match self {
            Self::Legacy(e) => e.len(),
            Self::Structured(e) => e.len(),
        }
    }
    fn get(&self, i: usize) -> EquationReference<'_> {
        match self {
            Self::Legacy(e) => EquationReference {
                operator: &e[i].operator,
                proof: &e[i].proof,
                arity: e[i].arity,
            },
            Self::Structured(e) => EquationReference {
                operator: &e[i].operator,
                proof: &e[i].proof,
                arity: e[i].arity,
            },
        }
    }
}
#[derive(Clone)]
struct PreparedCallEquation {
    operator: Option<ScopedLocal>,
    replacement: Option<Expr>,
    proof: Expr,
    arity: usize,
    statement: Option<Expr>,
}

#[derive(Clone)]
pub struct ImageTypes {
    pub state: Expr,
    pub error: Expr,
    pub value: Expr,
    pub answer: Expr,
}
#[derive(Clone, Copy)]
pub struct ImageReplayLimits {
    pub max_cases: usize,
    pub max_depth: usize,
    pub max_app_args: usize,
    pub heartbeats: u32,
    pub max_cache_entries: usize,
}
impl Default for ImageReplayLimits {
    fn default() -> Self {
        Self {
            max_cases: 4096,
            max_depth: 256,
            max_app_args: 64,
            heartbeats: 2_000_000,
            max_cache_entries: 16384,
        }
    }
}
/// No field is certification authority. In particular `run` is not executable
/// provider fidelity and a proposition is not evidence until independently checked.
#[derive(Debug)]
pub struct ImageCandidate {
    pub run: Expr,
    pub proposition: Expr,
    /// Compact open goal for the complete scoped carrier only. Its retained
    /// definitions must all check, and replay must match the independently
    /// reconstructed full endpoint proposition before returning authority.
    pub component_proposition: Option<Expr>,
    pub proof: Expr,
    pub cases: usize,
}
/// Structured-mode custody remains untrusted producer data. The original
/// image and all independently frozen source/Frame claims still must replay.
#[derive(Debug)]
pub struct StructuredImageCandidate {
    pub image: ImageCandidate,
    pub construction: StructuredRunConstruction,
}
fn constant(n: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_string(n), levels)
}
fn apply(n: &str, u: &Level, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(constant(n, vec![u.clone()]), args)
}
fn pair_type(u: &Level, a: Expr, b: Expr) -> Expr {
    Expr::apps(constant("Prod", vec![u.clone(), u.clone()]), [a, b])
}
struct ImageNode {
    observation: Expr,
    references: Option<crate::proof_components::ConstructedObservation>,
    source: Expr,
    compact_observation: Expr,
    proof: Expr,
    pending_cases: usize,
    construction: Option<Box<StructuredObservationConstruction>>,
}
#[derive(Debug, Default)]
struct ConstructionWork {
    equations: usize,
    equation_materialization: usize,
    equation_substitution: usize,
    redirection: usize,
    independence: usize,
    independence_inputs: usize,
    independence_observations: usize,
    bookkeeping: usize,
}
struct Replay<'a, 'e, L> {
    allocator: &'a mut L,
    components: Option<&'a mut ProofComponents>,
    captures: Vec<OwnedProofCapture>,
    checker: TypeChecker<'e>,
    types: ImageTypes,
    u: Level,
    mapper: ScopedLocal,
    ok: ScopedLocal,
    err: ScopedLocal,
    limits: ImageReplayLimits,
    cases: usize,
    max_depth_seen: usize,
    case_context_work: usize,
    equations: HashMap<clean_kernel::expr::FVarId, PreparedCallEquation>,
    equation_mode: bool,
    structured_calls: bool,
    mapper_definition: Expr,
    work: ConstructionWork,
    external: Option<crate::proof_components::ExternalContext>,
    observation_references: Option<crate::proof_components::ObservationReferences>,
}
impl<L: ScopedLocalAllocator> Replay<'_, '_, L> {
    fn spent(&self) -> usize {
        self.components.as_ref().map_or(0, |parts| parts.counts().3)
    }
    fn retain_observation(
        &mut self,
        term: &Expr,
    ) -> Result<Option<crate::proof_components::ConstructedObservation>, String> {
        let Some(memo) = self.observation_references.as_ref() else {
            return Ok(None);
        };
        let before = self.spent();
        let result = self
            .components
            .as_mut()
            .ok_or("constructed observation lost components")?
            .constructed_observation(self.allocator.local_scope(), memo, term);
        self.work.independence += self.spent().saturating_sub(before);
        self.work.independence_observations += self.spent().saturating_sub(before);
        result.map(Some)
    }
    fn independent_observation_of(
        &mut self,
        forbidden: &[ScopedLocal],
        node: &ImageNode,
    ) -> Result<(), String> {
        let before = self.spent();
        let result = self
            .components
            .as_mut()
            .ok_or("constructed observation lost components")?
            .charged_constructed_observation_independent_of(
                self.allocator.local_scope(),
                self.observation_references
                    .as_mut()
                    .ok_or("constructed observation lost replay memo")?,
                node.references
                    .as_ref()
                    .ok_or("constructed observation lost private root")?,
                &node.observation,
                forbidden,
            );
        self.work.independence += self.spent().saturating_sub(before);
        self.work.independence_observations += self.spent().saturating_sub(before);
        result
    }
    fn push_external_scope(&mut self, locals: &[ScopedLocal]) -> Result<Option<usize>, String> {
        let Some(context) = self.external.as_ref() else {
            return if self.structured_calls {
                Err("structured replay lost external inventory".into())
            } else {
                Ok(None)
            };
        };
        let checkpoint = context.checkpoint();
        let before = self.spent();
        let result = self
            .components
            .as_mut()
            .ok_or("structured replay lost external owner")?
            .charged_extend_external_context(
                self.allocator.local_scope(),
                self.external
                    .as_mut()
                    .ok_or("structured replay lost external inventory")?,
                locals,
            );
        self.work.bookkeeping += self.spent().saturating_sub(before);
        result?;
        Ok(Some(checkpoint))
    }
    fn restore_external_scope(&mut self, checkpoint: Option<usize>) -> Result<(), String> {
        if let Some(checkpoint) = checkpoint {
            self.external
                .as_mut()
                .ok_or("structured replay lost external inventory")?
                .restore(checkpoint)?;
        }
        Ok(())
    }
    fn charge_equation_work(&mut self, work: usize) -> Result<(), String> {
        if self.equation_mode {
            self.components
                .as_mut()
                .ok_or("call equations require complete components")?
                .spend_context_work(work)?;
            self.work.bookkeeping += work;
        }
        Ok(())
    }
    fn local(&mut self, ty: Expr) -> Result<ScopedLocal, String> {
        self.allocator.allocate_local(ty)
    }
    fn outcome(&self) -> Expr {
        Expr::apps(
            constant("Except", vec![self.u.clone(), self.u.clone()]),
            [self.types.error.clone(), self.types.value.clone()],
        )
    }
    fn observation(&self) -> Expr {
        pair_type(&self.u, self.types.state.clone(), self.outcome())
    }
    fn independent(&mut self, term: &Expr) -> Result<(), String> {
        if self.equation_mode {
            let forbidden = [self.ok.clone(), self.err.clone()];
            return self.independent_of(&forbidden, term);
        }
        // Materialized input terms have no loose variables. Abstraction detects
        // continuation occurrences under every supported kernel expression form.
        if term.has_loose_bvars()
            || term.abstract_fvar(self.ok.id()).has_loose_bvars()
            || term.abstract_fvar(self.err.id()).has_loose_bvars()
        {
            return Err("first-order data depends on final CPS callbacks".into());
        }
        Ok(())
    }
    fn independent_of(&mut self, forbidden: &[ScopedLocal], term: &Expr) -> Result<(), String> {
        self.independent_forest_of(forbidden, &[term])
    }
    fn independent_forest_of(
        &mut self,
        forbidden: &[ScopedLocal],
        roots: &[&Expr],
    ) -> Result<(), String> {
        let before = self.spent();
        let result = self
            .components
            .as_mut()
            .ok_or("owned equations lost component owner")?
            .charged_independent_forest_of(self.allocator.local_scope(), forbidden, roots);
        self.work.independence += self.spent().saturating_sub(before);
        self.work.independence_inputs += self.spent().saturating_sub(before);
        result
    }
    fn independent_forest(&mut self, roots: &[&Expr]) -> Result<(), String> {
        if self.equation_mode {
            return self.independent_forest_of(&[self.ok.clone(), self.err.clone()], roots);
        }
        for root in roots {
            self.independent(root)?;
        }
        Ok(())
    }
    fn frame_state_candidate(&mut self, actual: &Expr) -> Result<Expr, String> {
        self.charge_equation_work(3)?; // query, original/result graph pins
        let normalized = self.checker.whnf(actual);
        if self.checker.heartbeat_spent() {
            return Err("CPS Frame state normalization kernel budget".into());
        }
        Ok(normalized)
    }
    fn expression(&mut self, original: Expr, depth: usize) -> Result<ImageNode, String> {
        self.max_depth_seen = self.max_depth_seen.max(depth);
        if depth > self.limits.max_depth {
            return Err("CPS image replay depth limit".into());
        }
        self.charge_equation_work(1)?;
        let source = self.checker.whnf(&original);
        if self.checker.heartbeat_spent() {
            return Err("CPS image replay kernel budget".into());
        }
        if self.structured_calls {
            let before = self.spent();
            let commuted = case_context::commute_candidate(
                self.allocator,
                self.components
                    .as_mut()
                    .ok_or("structured case lost components")?,
                &self.checker,
                &[],
                &self.captures,
                &self.types.answer,
                &self.u,
                self.limits,
                &mut self.cases,
                &mut self.case_context_work,
                &source,
                Some(
                    self.external
                        .as_ref()
                        .ok_or("structured Case lost prepared inventory")?,
                ),
            );
            self.work.bookkeeping += self.spent().saturating_sub(before);
            if let Some((normalized, equality)) = commuted? {
                let mut child = self.expression(normalized, depth + 1)?;
                self.charge_equation_work(32)?;
                child.proof = Expr::apps(
                    constant("Eq.trans", vec![Level::succ(self.u.clone())]),
                    [
                        self.types.answer.clone(),
                        source.clone(),
                        child.source.clone(),
                        Expr::app(
                            self.mapper.term().clone(),
                            child.compact_observation.clone(),
                        ),
                        equality,
                        child.proof,
                    ],
                );
                child.source = source;
                child.pending_cases = child
                    .pending_cases
                    .checked_add(1)
                    .ok_or("correlated image proof grouping overflow")?;
                return Ok(child);
            }
        }
        let (head, args) = if self.equation_mode {
            // Charge each probe and clone BEFORE traversing/collecting it;
            // malformed oversized spines never receive a free full scan.
            let mut current = source.clone();
            let mut reversed = Vec::new();
            loop {
                self.charge_equation_work(1)?;
                let ExprKind::App(function, argument) = current.kind() else {
                    break;
                };
                if reversed.len() >= self.limits.max_app_args {
                    return Err("CPS image replay application limit".into());
                }
                self.charge_equation_work(3)?;
                reversed.push(argument.as_ref().clone());
                current = function.as_ref().clone();
            }
            self.charge_equation_work(reversed.len())?;
            reversed.reverse();
            (current, reversed)
        } else {
            if source.get_app_num_args() > self.limits.max_app_args {
                return Err("CPS image replay application limit".into());
            }
            (
                source.get_app_fn().clone(),
                source.get_app_args().iter().map(|e| (*e).clone()).collect(),
            )
        };
        if let ExprKind::FVar(id) = head.kind()
            && let Some(equation) = self.equations.get(id).cloned()
        {
            if args.len() != equation.arity {
                return Err("owned CPS equation application arity mismatch".into());
            }
            if self.structured_calls {
                return self.structured_call(source, args, equation, depth);
            }
            self.charge_equation_work(
                args.len()
                    .checked_mul(6)
                    .and_then(|n| n.checked_add(32))
                    .ok_or("equation construction work overflow")?,
            )?;
            let rewritten = Expr::apps(
                equation
                    .replacement
                    .ok_or("legacy equation lost replacement")?,
                args.clone(),
            );
            let child = self.expression(rewritten, depth + 1)?;
            let first = Expr::apps(equation.proof, args);
            let finish = Expr::app(
                self.mapper.term().clone(),
                child.compact_observation.clone(),
            );
            let proof = Expr::apps(
                constant("Eq.trans", vec![Level::succ(self.u.clone())]),
                [
                    self.types.answer.clone(),
                    source.clone(),
                    child.source.clone(),
                    finish,
                    first,
                    child.proof,
                ],
            );
            let observation_type = self.observation();
            let components = self
                .components
                .as_mut()
                .ok_or("owned equations lost component owner")?;
            let compact_source = components.bind_scoped(
                self.allocator,
                &self.captures,
                self.types.answer.clone(),
                source,
            )?;
            let compact_observation = components.bind_scoped(
                self.allocator,
                &self.captures,
                observation_type,
                child.compact_observation,
            )?;
            let goal = Expr::apps(
                constant("Eq", vec![Level::succ(self.u.clone())]),
                [
                    self.types.answer.clone(),
                    compact_source.clone(),
                    Expr::app(self.mapper.term().clone(), compact_observation.clone()),
                ],
            );
            let proof = components.bind_scoped(self.allocator, &self.captures, goal, proof)?;
            return Ok(ImageNode {
                observation: child.observation,
                references: child.references,
                source: compact_source,
                compact_observation,
                proof,
                pending_cases: 0,
                construction: None,
            });
        }
        if head == *self.ok.term() || head == *self.err.term() {
            if args.len() != 2 {
                return Err("final CPS callback arity".into());
            }
            self.independent_forest(&[&args[0], &args[1]])?;
            let tag = if head == *self.ok.term() {
                "Except.ok"
            } else {
                "Except.error"
            };
            let payload = Expr::apps(
                constant(tag, vec![self.u.clone(), self.u.clone()]),
                [
                    self.types.error.clone(),
                    self.types.value.clone(),
                    args[1].clone(),
                ],
            );
            let observed = Expr::apps(
                constant("Prod.mk", vec![self.u.clone(), self.u.clone()]),
                [
                    self.types.state.clone(),
                    self.outcome(),
                    args[0].clone(),
                    payload,
                ],
            );
            let proof = Expr::apps(
                constant("Eq.refl", vec![Level::succ(self.u.clone())]),
                [self.types.answer.clone(), source.clone()],
            );
            let construction = if self.structured_calls {
                self.charge_equation_work(8)?;
                Some(Box::new(StructuredObservationConstruction {
                    observation: observed.clone(),
                    step: StructuredObservationStep::Return {
                        normal: head == *self.ok.term(),
                        state: self.frame_state_candidate(&args[0])?,
                        payload: args[1].clone(),
                    },
                }))
            } else {
                None
            };
            return Ok(ImageNode {
                references: self.retain_observation(&observed)?,
                observation: observed.clone(),
                source,
                compact_observation: observed,
                proof,
                pending_cases: 0,
                construction,
            });
        }
        let ExprKind::Const(name, levels) = head.kind() else {
            return Err("opaque CPS return has no checked first-order image".into());
        };
        let name = name.to_string();
        // Parameter count and constructor field types, in actual recursor order.
        let (params, fields): (usize, Vec<Vec<Expr>>) = match name.as_str() {
            "Prod.rec" if args.len() == 5 && levels.len() == 3 => {
                (2, vec![vec![args[0].clone(), args[1].clone()]])
            }
            "Except.rec" if args.len() == 6 && levels.len() == 3 => {
                (2, vec![vec![args[0].clone()], vec![args[1].clone()]])
            }
            "Option.rec" if args.len() == 5 && levels.len() == 2 => {
                (1, vec![vec![], vec![args[0].clone()]])
            }
            "Bool.rec" if args.len() == 4 && levels.len() == 1 => (0, vec![vec![], vec![]]),
            _ => return Err(format!("unsupported CPS image head {name}")),
        };
        self.cases = self.cases.checked_add(1).ok_or("CPS image case overflow")?;
        if self.cases > self.limits.max_cases {
            return Err("CPS image replay case limit".into());
        }
        if self.equation_mode && params > 0 {
            self.charge_equation_work(params + 1)?;
            let roots = args
                .iter()
                .take(params)
                .chain(args.last())
                .collect::<Vec<_>>();
            self.independent_forest(&roots)?;
        } else {
            for data in args.iter().take(params).chain(args.last()) {
                self.independent(data)?;
            }
        }
        let major = args.last().unwrap().clone();
        let major_ty = match name.as_str() {
            "Prod.rec" => Expr::apps(
                constant("Prod", levels[1..].to_vec()),
                args[..params].to_vec(),
            ),
            "Except.rec" => Expr::apps(
                constant("Except", levels[1..].to_vec()),
                args[..params].to_vec(),
            ),
            "Option.rec" => Expr::app(constant("Option", levels[1..].to_vec()), args[0].clone()),
            _ => constant("Bool", vec![]),
        };
        let mut observed = args[..params].to_vec();
        let m = self.local(major_ty.clone())?;
        observed.push(m.lam(self.observation()));
        let mut compact_observed = observed.clone();
        let mut compact_source = args[..params + 1].to_vec();
        let mut proofs = Vec::new();
        let mut pending_cases = 1usize;
        let mut construction_branches = Vec::new();
        for (i, tys) in fields.into_iter().enumerate() {
            let mut locals = Vec::new();
            for ty in tys {
                locals.push(self.local(ty)?);
            }
            let branch = Expr::apps(
                args[params + 1 + i].clone(),
                locals.iter().map(|l| l.term().clone()),
            );
            let capture_count = self.captures.len();
            let external_checkpoint = self.push_external_scope(&locals)?;
            self.captures
                .extend(locals.iter().cloned().map(OwnedProofCapture::Parameter));
            let result = self.expression(branch, depth + 1);
            self.captures.truncate(capture_count);
            self.restore_external_scope(external_checkpoint)?;
            let branch = result?;
            pending_cases = pending_cases
                .checked_add(branch.pending_cases)
                .ok_or("image proof grouping overflow")?;
            let abstract_fields = |body| locals.iter().rev().fold(body, |body, l| l.lam(body));
            observed.push(abstract_fields(branch.observation));
            compact_observed.push(abstract_fields(branch.compact_observation));
            compact_source.push(abstract_fields(branch.source));
            proofs.push(abstract_fields(branch.proof));
            if self.structured_calls {
                self.charge_equation_work(
                    locals
                        .len()
                        .checked_mul(2)
                        .and_then(|n| n.checked_add(4))
                        .ok_or("case construction custody work overflow")?,
                )?;
                construction_branches.push((
                    locals,
                    *branch
                        .construction
                        .ok_or("structured case lost actual branch construction")?,
                ));
            }
        }
        observed.push(major.clone());
        compact_observed.push(major.clone());
        compact_source.push(major.clone());
        let mut out_levels = levels.to_vec();
        out_levels[0] = Level::succ(self.u.clone());
        let observed_term = Expr::apps(constant(&name, out_levels.clone()), observed.clone());
        let theorem = match name.as_str() {
            "Prod.rec" => CASE_MAP_PROD,
            "Except.rec" => CASE_MAP_EXCEPT,
            "Option.rec" => CASE_MAP_OPTION,
            _ => CASE_MAP_BOOL,
        };
        let mut proof_args = args[..params].to_vec();
        proof_args.extend([
            self.observation(),
            self.types.answer.clone(),
            self.mapper.term().clone(),
        ]);
        let source_arms = if self.components.is_some() {
            &compact_source[params + 1..compact_source.len() - 1]
        } else {
            &args[params + 1..args.len() - 1]
        };
        proof_args.extend(source_arms.iter().cloned());
        proof_args.extend(
            compact_observed[params + 1..compact_observed.len() - 1]
                .iter()
                .cloned(),
        );
        proof_args.extend(proofs);
        proof_args.push(major);
        let proof = Expr::apps(constant(theorem, vec![self.u.clone()]), proof_args);
        let mut compact_source = if self.components.is_some() {
            Expr::apps(constant(&name, levels.to_vec()), compact_source)
        } else {
            source
        };
        let mut compact_observed = Expr::apps(constant(&name, out_levels), compact_observed);
        // Packaging grain only: every recognized case is replayed unchanged.
        // Group adjacent derivations so tiny branches do not each repeat a
        // dynamic telescope. This is unrelated to loop fuel or termination.
        let retain = depth == 0 || pending_cases >= 32;
        let observation_type = self.observation();
        let proof = if let Some(components) = self.components.as_mut().filter(|_| retain) {
            // Definitions carry real source/data terms; they are not premises.
            // Complete scoped replay checks every defining value before it can
            // be used to match the independently reconstructed full endpoint.
            compact_source = components.bind_scoped(
                self.allocator,
                &self.captures,
                self.types.answer.clone(),
                compact_source,
            )?;
            compact_observed = components.bind_scoped(
                self.allocator,
                &self.captures,
                observation_type,
                compact_observed,
            )?;
            let proposition = Expr::apps(
                constant("Eq", vec![Level::succ(self.u.clone())]),
                [
                    self.types.answer.clone(),
                    compact_source.clone(),
                    Expr::app(self.mapper.term().clone(), compact_observed.clone()),
                ],
            );
            pending_cases = 0;
            components.bind_scoped(self.allocator, &self.captures, proposition, proof)?
        } else {
            proof
        };
        let construction = if self.structured_calls {
            self.charge_equation_work(
                params
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(12))
                    .ok_or("case construction custody work overflow")?,
            )?;
            Some(Box::new(StructuredObservationConstruction {
                observation: observed_term.clone(),
                step: StructuredObservationStep::Case {
                    head: constant(&name, levels.to_vec()),
                    parameters: args[..params].to_vec(),
                    major: args
                        .last()
                        .ok_or("case construction major missing")?
                        .clone(),
                    branches: construction_branches,
                },
            }))
        } else {
            None
        };
        Ok(ImageNode {
            references: self.retain_observation(&observed_term)?,
            observation: observed_term,
            source: compact_source,
            compact_observation: compact_observed,
            proof,
            pending_cases,
            construction,
        })
    }
}

/// Globals are authenticated handles belonging to `allocator`; they are not
/// recreated by raw free-variable ID. Normalization uses the existing kernel.
pub fn replay_image<L: ScopedLocalAllocator>(
    env: &Environment,
    allocator: &mut L,
    globals: &[ScopedLocal],
    types: ImageTypes,
    source: Expr,
    u: Level,
    limits: ImageReplayLimits,
) -> Result<ImageCandidate, String> {
    replay_image_impl(
        env,
        allocator,
        globals,
        &[],
        types,
        source,
        u,
        limits,
        None,
        None,
        None,
        &[],
    )
}

/// Retain recursive case proofs as complete scoped definitions in the existing
/// component carrier. The caller must initialize `components` with the exact
/// same-owner global telescope, close its complete bundle, and independently
/// replay it against its independently reconstructed claim. No open expression
/// returned here is a closed proof, and no scope or checking budget is reset.
pub fn replay_image_with_components<L: ScopedLocalAllocator>(
    env: &Environment,
    allocator: &mut L,
    globals: &[ScopedLocal],
    types: ImageTypes,
    source: Expr,
    u: Level,
    limits: ImageReplayLimits,
    components: &mut ProofComponents,
) -> Result<ImageCandidate, String> {
    replay_image_impl(
        env,
        allocator,
        globals,
        &[],
        types,
        source,
        u,
        limits,
        Some(components),
        None,
        None,
        &[],
    )
}

/// Build a parameterized body image inside an existing component owner.
/// Parameters are actual same-owner local binders, not truth assumptions or
/// retained globals. All resulting definitions retain their parameter lambdas;
/// the caller must close and replay the complete original root claim.
pub fn replay_image_with_parameters<L: ScopedLocalAllocator>(
    env: &Environment,
    allocator: &mut L,
    globals: &[ScopedLocal],
    parameters: &[ScopedLocal],
    types: ImageTypes,
    source: Expr,
    u: Level,
    limits: ImageReplayLimits,
    components: &mut ProofComponents,
) -> Result<ImageCandidate, String> {
    replay_image_impl(
        env,
        allocator,
        globals,
        parameters,
        types,
        source,
        u,
        limits,
        Some(components),
        None,
        None,
        &[],
    )
}

/// Replay actual opaque calls only through supplied owned pointwise equations.
/// This builds untrusted kernel candidates, not an IR compiler or provider
/// witness. Original source endpoints, values and all proof definitions must
/// survive complete independent frozen-claim/wire/rooted checking.
pub fn replay_image_with_call_equations<L: ScopedLocalAllocator>(
    env: &Environment,
    allocator: &mut L,
    globals: &[ScopedLocal],
    parameters: &[ScopedLocal],
    types: ImageTypes,
    source: Expr,
    u: Level,
    limits: ImageReplayLimits,
    components: &mut ProofComponents,
    equations: &[CpsCallEquation],
) -> Result<ImageCandidate, String> {
    replay_image_impl(
        env,
        allocator,
        globals,
        parameters,
        types,
        source,
        u,
        limits,
        Some(components),
        Some(EquationProfile::Legacy(equations)),
        None,
        &[],
    )
}

/// Keep exact retained data definitions opaque to producer normalization.
///
/// Each handle must name a preceding definition in this component owner and
/// appear in `globals`. Its actual type and value remain mandatory inputs to
/// complete frozen-claim/wire/kernel replay. This changes no equation, grants
/// no image premise and never substitutes for final-callback independence.
/// An opaque CPS call still needs its own actual checked call equation.
#[allow(clippy::too_many_arguments)]
pub fn replay_image_with_call_equations_and_retained_data<L: ScopedLocalAllocator>(
    env: &Environment,
    allocator: &mut L,
    globals: &[ScopedLocal],
    parameters: &[ScopedLocal],
    types: ImageTypes,
    source: Expr,
    u: Level,
    limits: ImageReplayLimits,
    components: &mut ProofComponents,
    equations: &[CpsCallEquation],
    retained_data: &[OwnedScopedDefinition],
) -> Result<ImageCandidate, String> {
    replay_image_impl(
        env,
        allocator,
        globals,
        parameters,
        types,
        source,
        u,
        limits,
        Some(components),
        Some(EquationProfile::Legacy(equations)),
        None,
        retained_data,
    )
}

/// Compose genuine owned call equations with BOTH actual continuation images.
/// Only an actual retained equation type exposing literal TO_CPS is supported.
/// All fields remain untrusted until complete original declaration/claim replay.
pub fn replay_image_with_structured_call_equations<L: ScopedLocalAllocator>(
    env: &Environment,
    allocator: &mut L,
    globals: &[ScopedLocal],
    parameters: &[ScopedLocal],
    types: ImageTypes,
    source: Expr,
    u: Level,
    limits: ImageReplayLimits,
    components: &mut ProofComponents,
    equations: &[OwnedCpsCallEquation],
) -> Result<StructuredImageCandidate, String> {
    let mut construction = None;
    let image = replay_image_impl(
        env,
        allocator,
        globals,
        parameters,
        types,
        source,
        u,
        limits,
        Some(components),
        Some(EquationProfile::Structured(equations)),
        Some(&mut construction),
        &[],
    )?;
    Ok(StructuredImageCandidate {
        image,
        construction: construction.ok_or("structured replay lost actual construction")?,
    })
}

fn replay_image_impl<L: ScopedLocalAllocator>(
    env: &Environment,
    allocator: &mut L,
    globals: &[ScopedLocal],
    parameters: &[ScopedLocal],
    types: ImageTypes,
    source: Expr,
    u: Level,
    limits: ImageReplayLimits,
    mut components: Option<&mut ProofComponents>,
    equations: Option<EquationProfile<'_>>,
    construction_output: Option<&mut Option<StructuredRunConstruction>>,
    retained_data: &[OwnedScopedDefinition],
) -> Result<ImageCandidate, String> {
    let structured_calls = matches!(&equations, Some(EquationProfile::Structured(_)));
    if structured_calls
        && env
            .get_const(&Name::from_string(
                crate::semantic_evaluation::CPS_IMAGE_HANDLE,
            ))
            .is_none()
    {
        return Err("structured call replay lacks checked HANDLE composition".into());
    }
    if limits.max_depth > 256 || limits.max_cases > 65_536 || limits.max_app_args > 4096 {
        return Err("CPS image replay structural limits exceed supported profile".into());
    }
    if limits.heartbeats == 0 {
        return Err("CPS image replay requires a finite kernel heartbeat budget".into());
    }
    for name in [CPS_IMAGE, TO_CPS].into_iter().chain(CASE_MAP_THEOREMS) {
        if env.get_const(&Name::from_string(name)).is_none() {
            return Err(format!("CPS image replay lacks prerequisite {name}"));
        }
    }
    if parameters.len() > limits.max_app_args {
        return Err("CPS image parameter arity exceeds supported profile".into());
    }
    let mut opaque = Vec::new();
    if equations.is_some() && env.get_const(&Name::from_string("Eq.trans")).is_none() {
        return Err("owned CPS equations lack checked equality composition".into());
    }
    if let Some(equations) = &equations {
        if equations.len() > limits.max_cases || retained_data.len() > limits.max_cases {
            return Err("owned CPS equation inventory limit".into());
        }
        let parts = components
            .as_mut()
            .ok_or("owned equations require complete components")?;
        let (internal, base, _, _) = parts.counts();
        let setup = internal
            .checked_add(base)
            .and_then(|n| n.checked_mul(8))
            .and_then(|n| n.checked_add(globals.len().checked_mul(4)?))
            .and_then(|n| n.checked_add(parameters.len().checked_mul(4)?))
            .and_then(|n| n.checked_add(equations.len().checked_mul(16)?))
            .and_then(|n| n.checked_add(retained_data.len().checked_mul(8)?))
            .ok_or("owned equation inventory overflow")?;
        parts.spend_context_work(setup)?;
        let ids = globals.iter().map(ScopedLocal::id).collect::<HashSet<_>>();
        let mut operators = HashSet::new();
        let mut opaque_ids = HashSet::new();
        for index in 0..equations.len() {
            let equation = equations.get(index);
            if !allocator.local_scope().owns(&equation.operator)
                || !allocator.local_scope().owns(&equation.proof.local)
                || !ids.contains(&equation.operator.id())
                || !ids.contains(&equation.proof.local.id())
                || !operators.insert(equation.operator.id())
                || &equation.proof.reference != equation.proof.local.term()
                || equation.arity == 0
                || equation.arity > limits.max_app_args
            {
                return Err("foreign, missing, duplicate or incomplete owned CPS equation".into());
            }
            for local in [equation.operator, &equation.proof.local] {
                if opaque_ids.insert(local.id()) {
                    opaque.push(local.clone());
                }
            }
        }
        for data in retained_data {
            if !allocator.local_scope().owns(&data.local)
                || !ids.contains(&data.local.id())
                || &data.reference != data.local.term()
                || !opaque_ids.insert(data.local.id())
            {
                return Err("foreign, missing, duplicate or applied retained CPS data".into());
            }
            // The charged context below requires the actual preceding defining
            // value; a same-typed parameter cannot authorize producer opacity.
            opaque.push(data.local.clone());
        }
    }
    let mut allowed = globals.to_vec();
    if !parameters.is_empty() {
        let retained = components
            .as_ref()
            .ok_or("CPS image parameters require complete scoped components")?
            .retained_normalization_locals(allocator.local_scope())?;
        let retained = retained
            .iter()
            .map(|local| local.id())
            .collect::<std::collections::HashSet<_>>();
        let mut ids = globals
            .iter()
            .map(|local| local.id())
            .collect::<std::collections::HashSet<_>>();
        for parameter in parameters {
            if !allocator.local_scope().owns(parameter) || !ids.insert(parameter.id()) {
                return Err("foreign or duplicate CPS image parameter".into());
            }
            if retained.contains(&parameter.id()) {
                return Err("retained CPS image declaration cannot become a parameter".into());
            }
            allowed.push(parameter.clone());
        }
    }
    // A forest admits external locals monotonically. Validate the parameter
    // telescope before the body roots, so a later parameter cannot authorize
    // an earlier type and no root asks the closer to revoke admitted locals.
    let mut input = parameters
        .iter()
        .map(|parameter| parameter.ty().clone())
        .collect::<Vec<_>>();
    input.extend([types.state, types.error, types.value, types.answer, source]);
    if let Some(EquationProfile::Legacy(equations)) = &equations {
        for equation in *equations {
            input.extend([
                equation.replacement.clone(),
                equation.proof.reference.clone(),
            ]);
        }
    }
    input.extend(retained_data.iter().map(|data| data.reference.clone()));
    let mut visible = (0..parameters.len())
        .map(|index| globals.len() + index)
        .collect::<Vec<_>>();
    visible.extend(std::iter::repeat_n(
        allowed.len(),
        input.len() - parameters.len(),
    ));
    let input = if equations.is_some() {
        components
            .as_mut()
            .ok_or("owned equations lost components")?
            .charged_materialize_forest(allocator.local_scope(), &allowed, &input, &visible)
            .map_err(|error| format!("owned CPS initial materialization: {error}"))?
    } else {
        let (materialized, _) = allocator
            .local_scope()
            .close_external_forest(&input, &allowed, &visible);
        materialized.map_err(|e| e.to_string())?
    };
    let input = &input[parameters.len()..];
    let types = ImageTypes {
        state: input[0].clone(),
        error: input[1].clone(),
        value: input[2].clone(),
        answer: input[3].clone(),
    };
    let source = input[4].clone();
    let mut prepared = HashMap::new();
    if let Some(equations) = &equations {
        for index in 0..equations.len() {
            let equation = equations.get(index);
            prepared.insert(
                equation.operator.id(),
                PreparedCallEquation {
                    operator: structured_calls.then(|| equation.operator.clone()),
                    replacement: if structured_calls {
                        None
                    } else {
                        Some(input[5 + 2 * index].clone())
                    },
                    proof: if structured_calls {
                        equation.proof.reference.clone()
                    } else {
                        input[6 + 2 * index].clone()
                    },
                    arity: equation.arity,
                    // This is the ACTUAL retained type, not an assumed statement.
                    // actual_equation pays owner closure at the reached scope.
                    statement: structured_calls.then(|| equation.proof.local.ty().clone()),
                },
            );
        }
    }
    let normalization = if equations.is_some() {
        Some(
            components
                .as_mut()
                .ok_or("owned equations lost normalization owner")?
                .charged_normalization_context_with_opaque(
                    allocator.local_scope(),
                    globals,
                    input,
                    &opaque,
                )
                .map_err(|error| format!("owned CPS normalization context: {error}"))?
                .0,
        )
    } else {
        None
    };
    let state = allocator.allocate_local(types.state.clone())?;
    let ok = allocator.allocate_local(Expr::arrow(
        types.state.clone(),
        Expr::arrow(types.value.clone(), types.answer.clone()),
    ))?;
    let err = allocator.allocate_local(Expr::arrow(
        types.state.clone(),
        Expr::arrow(types.error.clone(), types.answer.clone()),
    ))?;
    let observation = pair_type(
        &u,
        types.state.clone(),
        Expr::apps(
            constant("Except", vec![u.clone(), u.clone()]),
            [types.error.clone(), types.value.clone()],
        ),
    );
    let mapper =
        allocator.allocate_local(Expr::arrow(observation.clone(), types.answer.clone()))?;
    let observed = allocator.allocate_local(observation)?;
    let ignored = allocator.allocate_local(types.state.clone())?;
    let mapper_definition = observed.lam(apply(
        TO_CPS,
        &u,
        [
            types.state.clone(),
            types.error.clone(),
            types.value.clone(),
            types.answer.clone(),
            ignored.lam(observed.term().clone()),
            state.term().clone(),
            ok.term().clone(),
            err.term().clone(),
        ],
    ));
    let mut checker = match normalization {
        Some(context) => TypeChecker::with_context(env, context),
        None => TypeChecker::new(env),
    };
    checker.set_heartbeat_limit(limits.heartbeats);
    checker.set_max_cache_entries(limits.max_cache_entries);
    let mut captures = parameters
        .iter()
        .cloned()
        .map(OwnedProofCapture::Parameter)
        .collect::<Vec<_>>();
    captures.extend([
        OwnedProofCapture::Parameter(state.clone()),
        OwnedProofCapture::Parameter(ok.clone()),
        OwnedProofCapture::Parameter(err.clone()),
        OwnedProofCapture::Definition {
            local: mapper.clone(),
            value: std::sync::Arc::new(mapper_definition.clone()),
        },
    ]);
    let external = if structured_calls {
        let parts = components
            .as_mut()
            .ok_or("structured replay lost external owner")?;
        let mut context = parts.charged_external_context(allocator.local_scope(), &allowed)?;
        parts
            .charged_enable_external_materialization_reuse(allocator.local_scope(), &mut context)?;
        parts.charged_extend_external_context(
            allocator.local_scope(),
            &mut context,
            &[state.clone(), ok.clone(), err.clone(), mapper.clone()],
        )?;
        Some(context)
    } else {
        None
    };
    let observation_references = if structured_calls {
        Some(
            components
                .as_mut()
                .ok_or("structured replay lost observation owner")?
                .observation_references_shared_children(allocator.local_scope())?,
        )
    } else {
        None
    };
    let mut replay = Replay {
        allocator,
        components,
        captures,
        checker,
        types: types.clone(),
        u: u.clone(),
        mapper: mapper.clone(),
        ok: ok.clone(),
        err: err.clone(),
        limits,
        cases: 0,
        max_depth_seen: 0,
        case_context_work: 0,
        equations: prepared,
        equation_mode: equations.is_some(),
        structured_calls,
        mapper_definition: mapper_definition.clone(),
        work: ConstructionWork::default(),
        external,
        observation_references,
    };
    let construction_start = replay.components.as_ref().map(|parts| parts.counts());
    let construction_ledger = replay
        .components
        .as_ref()
        .map(|parts| parts.context_work_totals());
    let image = replay
        .expression(
            Expr::apps(
                source.clone(),
                [state.term().clone(), ok.term().clone(), err.term().clone()],
            ),
            0,
        )
        .map_err(|error| {
            if replay.equation_mode {
                format!(
                    "owned CPS construction (cases={}, max_depth={}, start={construction_start:?}, current={:?}, ledger_start={construction_ledger:?}, ledger_now={:?}, work={:?}, reference_sets={:?}): {error}",
                    replay.cases,
                    replay.max_depth_seen,
                    replay.components.as_ref().map(|parts| parts.counts()),
                    replay.components.as_ref().map(|parts| parts.context_work_totals()),
                    replay.work,
                    replay.observation_references.as_ref().map(|memo|memo.diagnostics()),
                )
            } else {
                error
            }
        })?;
    let component_proposition = replay.components.as_ref().map(|_| {
        apply(
            CPS_IMAGE,
            &u,
            [
                types.state.clone(),
                types.error.clone(),
                types.value.clone(),
                types.answer.clone(),
                state.lam(image.compact_observation),
                state.lam(ok.lam(err.lam(image.source))),
            ],
        )
    });
    let run = state.lam(image.observation);
    let proposition = apply(
        CPS_IMAGE,
        &u,
        [
            types.state,
            types.error,
            types.value,
            types.answer,
            run.clone(),
            source,
        ],
    );
    let proof = state.lam(ok.lam(err.lam(mapper.let_(mapper_definition, image.proof))));
    if let Some(output) = construction_output {
        *output = image
            .construction
            .map(|root| StructuredRunConstruction { input: state, root });
    }
    Ok(ImageCandidate {
        run,
        proposition,
        component_proposition,
        proof,
        cases: replay.cases,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{scoped_local::LocalScope, semantic_evaluation};
    fn nat() -> Expr {
        constant("Nat", vec![])
    }
    fn fixture(scope: &mut LocalScope, family: usize) -> (Vec<ScopedLocal>, ImageTypes, Expr) {
        let u = Level::zero();
        let n = nat();
        let types = ImageTypes {
            state: n.clone(),
            error: n.clone(),
            value: n.clone(),
            answer: n.clone(),
        };
        let s = scope.allocate_local(n.clone()).unwrap();
        let callback = Expr::arrow(n.clone(), Expr::arrow(n.clone(), n.clone()));
        let ok = scope.allocate_local(callback.clone()).unwrap();
        let err = scope.allocate_local(callback).unwrap();
        let yes = Expr::apps(ok.term().clone(), [Expr::nat_lit(9), Expr::nat_lit(7)]);
        let no = Expr::apps(err.term().clone(), [Expr::nat_lit(8), Expr::nat_lit(6)]);
        let (ty, rec, fields, params, arms, levels) = match family {
            0 => (
                constant("Bool", vec![]),
                "Bool.rec",
                vec![],
                vec![],
                vec![no, yes],
                vec![Level::succ(u.clone())],
            ),
            1 => {
                let a = scope.allocate_local(n.clone()).unwrap();
                (
                    Expr::app(constant("Option", vec![u.clone()]), n.clone()),
                    "Option.rec",
                    vec![a.clone()],
                    vec![n.clone()],
                    vec![
                        no,
                        a.lam(Expr::apps(
                            ok.term().clone(),
                            [s.term().clone(), a.term().clone()],
                        )),
                    ],
                    vec![Level::succ(u.clone()), u.clone()],
                )
            }
            2 => {
                let a = scope.allocate_local(n.clone()).unwrap();
                let b = scope.allocate_local(n.clone()).unwrap();
                (
                    Expr::apps(
                        constant("Except", vec![u.clone(), u.clone()]),
                        [n.clone(), n.clone()],
                    ),
                    "Except.rec",
                    vec![a.clone(), b.clone()],
                    vec![n.clone(), n.clone()],
                    vec![
                        a.lam(Expr::apps(
                            err.term().clone(),
                            [s.term().clone(), a.term().clone()],
                        )),
                        b.lam(Expr::apps(
                            ok.term().clone(),
                            [s.term().clone(), b.term().clone()],
                        )),
                    ],
                    vec![Level::succ(u.clone()), u.clone(), u.clone()],
                )
            }
            _ => {
                let a = scope.allocate_local(n.clone()).unwrap();
                let b = scope.allocate_local(n.clone()).unwrap();
                (
                    pair_type(&u, n.clone(), n.clone()),
                    "Prod.rec",
                    vec![a.clone(), b.clone()],
                    vec![n.clone(), n.clone()],
                    vec![a.lam(b.lam(Expr::apps(
                        ok.term().clone(),
                        [a.term().clone(), b.term().clone()],
                    )))],
                    vec![Level::succ(u.clone()), u.clone(), u.clone()],
                )
            }
        };
        let _ = fields;
        let major = scope.allocate_local(ty.clone()).unwrap();
        let motive = scope.allocate_local(ty).unwrap();
        let mut args = params;
        args.push(motive.lam(n));
        args.extend(arms);
        args.push(major.term().clone());
        let body = Expr::apps(constant(rec, levels), args);
        (vec![major], types, s.lam(ok.lam(err.lam(body))))
    }
    fn parameter_environment() -> Environment {
        let mut env = semantic_evaluation::build_environment().unwrap();
        semantic_evaluation::install_handle_into(&mut env).unwrap();
        semantic_evaluation::install_case_maps_into(&mut env).unwrap();
        env.init_nat().unwrap();
        env
    }
    #[test]
    fn cps_image_replay_parameters_are_bound_in_complete_case_components() {
        let env = parameter_environment();
        for (family, bind_parameter) in
            (0..4).flat_map(|family| [false, true].map(|bind| (family, bind)))
        {
            let mut scope = LocalScope::new();
            let (parameters, types, source) = fixture(&mut scope, family);
            let mut parts = ProofComponents::new(
                "image.parameters",
                crate::proof_assembly::ProofLimits::default(),
            );
            parts.set_base(&scope, vec![]).unwrap();
            let image = replay_image_with_parameters(
                &env,
                &mut scope,
                &[],
                &parameters,
                types,
                source,
                Level::zero(),
                Default::default(),
                &mut parts,
            )
            .unwrap();
            let compact = image.component_proposition.unwrap();
            let claim = scope.close(&parameters[0].pi(image.proposition)).unwrap();
            // Each branch is an independent owned test instance: the component
            // builder stays non-cloneable and its cumulative budget is intact.
            let root = if bind_parameter {
                parameters[0].lam(image.proof)
            } else {
                image.proof
            };
            let goal = if bind_parameter {
                parameters[0].pi(compact)
            } else {
                compact
            };
            let closed = parts.close_scoped(&scope, root, goal, Default::default());
            if !bind_parameter {
                if let Ok(open) = closed {
                    assert!(open.replay(&env, &claim, 2_000_000).is_err());
                }
                continue;
            }
            let bundle = closed.unwrap();
            let bytes = bundle.encode_with_claim(&claim).unwrap();
            let (decoded, transported) =
                crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&bytes)
                    .unwrap();
            assert_eq!(transported, claim);
            decoded.replay(&env, &claim, 2_000_000).unwrap();
        }
    }
    #[test]
    fn cps_image_replay_parameters_preserve_dependent_telescope_order() {
        let env = parameter_environment();
        let mut scope = LocalScope::new();
        let alpha = scope
            .allocate_local(Expr::sort(Level::succ(Level::zero())))
            .unwrap();
        let value = scope.allocate_local(alpha.term().clone()).unwrap();
        let n = Expr::const_str("Nat");
        let state = scope.allocate_local(n.clone()).unwrap();
        let ok = scope
            .allocate_local(Expr::arrow(
                n.clone(),
                Expr::arrow(alpha.term().clone(), n.clone()),
            ))
            .unwrap();
        let err = scope
            .allocate_local(Expr::arrow(n.clone(), Expr::arrow(n.clone(), n.clone())))
            .unwrap();
        let source = state.lam(ok.lam(err.lam(Expr::apps(
            ok.term().clone(),
            [state.term().clone(), value.term().clone()],
        ))));
        let types = ImageTypes {
            state: n.clone(),
            error: n.clone(),
            value: alpha.term().clone(),
            answer: n,
        };
        let mut parts = ProofComponents::new(
            "image.parameter.order",
            crate::proof_assembly::ProofLimits::default(),
        );
        parts.set_base(&scope, vec![]).unwrap();
        assert!(
            replay_image_with_parameters(
                &env,
                &mut scope,
                &[],
                &[value.clone(), alpha.clone()],
                types.clone(),
                source.clone(),
                Level::zero(),
                Default::default(),
                &mut parts
            )
            .is_err()
        );
        let image = replay_image_with_parameters(
            &env,
            &mut scope,
            &[],
            &[alpha.clone(), value.clone()],
            types,
            source,
            Level::zero(),
            Default::default(),
            &mut parts,
        )
        .unwrap();
        let claim = scope.close(&alpha.pi(value.pi(image.proposition))).unwrap();
        let bundle = parts
            .close_scoped(
                &scope,
                alpha.lam(value.lam(image.proof)),
                alpha.pi(value.pi(image.component_proposition.unwrap())),
                Default::default(),
            )
            .unwrap();
        let bytes = bundle.encode_with_claim(&claim).unwrap();
        let (decoded, transported) =
            crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
        assert_eq!(transported, claim);
        decoded.replay(&env, &claim, 2_000_000).unwrap();
    }
    #[test]
    fn cps_image_replay_parameters_refuse_foreign_duplicates_and_retained_definitions() {
        let env = parameter_environment();
        let mut scope = LocalScope::new();
        let (parameters, types, source) = fixture(&mut scope, 0);
        let mut parts = ProofComponents::new(
            "image.parameter.hostile",
            crate::proof_assembly::ProofLimits::default(),
        );
        parts.set_base(&scope, vec![]).unwrap();
        let mut foreign_scope = LocalScope::new();
        assert!(parameters[0].id().as_u64() < 64);
        let foreign = (0..=parameters[0].id().as_u64())
            .map(|_| {
                foreign_scope
                    .allocate_local(parameters[0].ty().clone())
                    .unwrap()
            })
            .last()
            .unwrap();
        assert_eq!(foreign.id(), parameters[0].id());
        assert!(
            replay_image_with_parameters(
                &env,
                &mut scope,
                &[],
                &[foreign],
                types.clone(),
                source.clone(),
                Level::zero(),
                Default::default(),
                &mut parts
            )
            .is_err()
        );
        assert!(
            replay_image_with_parameters(
                &env,
                &mut scope,
                &[],
                &[parameters[0].clone(), parameters[0].clone()],
                types.clone(),
                source.clone(),
                Level::zero(),
                Default::default(),
                &mut parts
            )
            .is_err()
        );
        let mut retained = ProofComponents::new(
            "image.parameter.retained",
            crate::proof_assembly::ProofLimits::default(),
        );
        retained
            .set_base(
                &scope,
                parameters
                    .iter()
                    .cloned()
                    .map(OwnedProofCapture::Parameter)
                    .collect(),
            )
            .unwrap();
        let _definition = retained
            .bind_scoped(
                &mut scope,
                &[],
                Expr::const_str("Bool"),
                Expr::const_str("Bool.true"),
            )
            .unwrap();
        let definition = retained
            .retained_normalization_locals(&scope)
            .unwrap()
            .last()
            .unwrap()
            .clone();
        let error = replay_image_with_parameters(
            &env,
            &mut scope,
            &parameters,
            &[definition],
            types,
            source,
            Level::zero(),
            Default::default(),
            &mut retained,
        )
        .err()
        .expect("a retained definition is not an independent parameter");
        assert!(error.contains("retained"), "unexpected refusal: {error}");
    }
    #[test]
    fn cps_image_replay_scoped_components_preserve_complete_checked_case_proofs() {
        use crate::{
            proof_assembly::ProofLimits, proof_components::ScopedProofComponentBundle,
            term_scope::TermScopeLimits,
        };
        let mut env = semantic_evaluation::build_environment().unwrap();
        semantic_evaluation::install_handle_into(&mut env).unwrap();
        semantic_evaluation::install_case_maps_into(&mut env).unwrap();
        env.init_nat().unwrap();
        for family in 0..4 {
            let mut scope = LocalScope::new();
            let (globals, types, source) = fixture(&mut scope, family);
            let mut components = ProofComponents::new("image.case", ProofLimits::default());
            components
                .set_base(
                    &scope,
                    globals
                        .iter()
                        .cloned()
                        .map(OwnedProofCapture::Parameter)
                        .collect(),
                )
                .unwrap();
            let candidate = replay_image_with_components(
                &env,
                &mut scope,
                &globals,
                types,
                source,
                Level::zero(),
                ImageReplayLimits::default(),
                &mut components,
            )
            .unwrap();
            let claim = scope
                .close(&globals[0].pi(candidate.proposition.clone()))
                .unwrap();
            let bundle = components
                .close_scoped(
                    &scope,
                    globals[0].lam(candidate.proof),
                    candidate.component_proposition.unwrap(),
                    TermScopeLimits::default(),
                )
                .unwrap();
            assert!(bundle.declarations.len() > bundle.outer_count);
            let wire = bundle.encode_with_claim(&claim).unwrap();
            let (mut decoded, transported) =
                ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
            assert_eq!(claim, transported);
            decoded.replay(&env, &claim, 2_000_000).unwrap();
            let different = Expr::apps(
                constant("Eq", vec![Level::succ(Level::zero())]),
                [nat(), Expr::nat_lit(0), Expr::nat_lit(0)],
            );
            let different = scope.close(&globals[0].pi(different)).unwrap();
            assert_eq!(
                TypeChecker::new(&env).infer_type(&different).unwrap(),
                Expr::prop()
            );
            assert!(
                decoded.replay(&env, &different, 2_000_000).is_err(),
                "compact goal must match the complete independently supplied endpoint"
            );
            fn zero_body(term: &Expr) -> Expr {
                match term.kind() {
                    ExprKind::Lam(binder, ty, body) => {
                        Expr::lam(*binder, ty.as_ref().clone(), zero_body(body))
                    }
                    _ => Expr::nat_lit(0),
                }
            }
            let data = decoded.outer_count;
            let original = decoded.declarations[data].value.clone().unwrap();
            let wrong = zero_body(&original);
            TypeChecker::new(&env)
                .check_type(&wrong, &decoded.declarations[data].type_)
                .unwrap();
            decoded.declarations[data].value = Some(wrong);
            assert!(
                decoded.replay(&env, &claim, 2_000_000).is_err(),
                "well-typed wrong source data definition must not become an assumption"
            );
            decoded.declarations[data].value = Some(original);
            // Replace a retained equality proof by a valid, closed Nat term.
            // Complete replay must check every defining value, not just a root.
            decoded.declarations.last_mut().unwrap().value = Some(Expr::nat_lit(0));
            assert!(decoded.replay(&env, &claim, 2_000_000).is_err());
        }
    }
    #[test]
    fn cps_image_replay_scoped_groups_branching_derivation_without_discarding_cases() {
        use crate::{proof_assembly::ProofLimits, term_scope::TermScopeLimits};
        let mut env = semantic_evaluation::build_environment().unwrap();
        semantic_evaluation::install_handle_into(&mut env).unwrap();
        semantic_evaluation::install_case_maps_into(&mut env).unwrap();
        env.init_nat().unwrap();
        let mut scope = LocalScope::new();
        let major = scope.allocate_local(constant("Bool", vec![])).unwrap();
        let state = scope.allocate_local(nat()).unwrap();
        let callback = Expr::arrow(nat(), Expr::arrow(nat(), nat()));
        let ok = scope.allocate_local(callback.clone()).unwrap();
        let err = scope.allocate_local(callback).unwrap();
        fn tree(
            scope: &mut LocalScope,
            state: &ScopedLocal,
            ok: &ScopedLocal,
            err: &ScopedLocal,
            major: &ScopedLocal,
            depth: usize,
            seed: u64,
        ) -> Expr {
            if depth == 0 {
                return if seed % 2 == 0 {
                    Expr::apps(
                        ok.term().clone(),
                        [state.term().clone(), Expr::nat_lit(seed)],
                    )
                } else {
                    Expr::apps(
                        err.term().clone(),
                        [Expr::nat_lit(seed + 8), Expr::nat_lit(seed)],
                    )
                };
            }
            let motive = scope.allocate_local(constant("Bool", vec![])).unwrap();
            let left = tree(scope, state, ok, err, major, depth - 1, seed * 2);
            let right = tree(scope, state, ok, err, major, depth - 1, seed * 2 + 1);
            Expr::apps(
                constant("Bool.rec", vec![Level::succ(Level::zero())]),
                [motive.lam(nat()), left, right, major.term().clone()],
            )
        }
        let body = tree(&mut scope, &state, &ok, &err, &major, 7, 0);
        let source = state.lam(ok.lam(err.lam(body)));
        let types = ImageTypes {
            state: nat(),
            error: nat(),
            value: nat(),
            answer: nat(),
        };
        let mut components = ProofComponents::new("image.grouped", ProofLimits::default());
        components
            .set_base(&scope, vec![OwnedProofCapture::Parameter(major.clone())])
            .unwrap();
        let image = replay_image_with_components(
            &env,
            &mut scope,
            std::slice::from_ref(&major),
            types,
            source,
            Level::zero(),
            ImageReplayLimits::default(),
            &mut components,
        )
        .unwrap();
        assert_eq!(image.cases, 127, "packaging must replay all cases");
        let claim = scope.close(&major.pi(image.proposition.clone())).unwrap();
        let bundle = components
            .close_scoped(
                &scope,
                major.lam(image.proof),
                image.component_proposition.unwrap(),
                TermScopeLimits::default(),
            )
            .unwrap();
        assert!(
            bundle.declarations.len() > 4 && bundle.declarations.len() < 20,
            "branching case tree must retain complete grouped definitions"
        );
        bundle.replay(&env, &claim, 2_000_000).unwrap();
    }
    #[test]
    fn cps_image_replay_scoped_components_refuse_foreign_plan_owner() {
        use crate::proof_assembly::ProofLimits;
        let mut env = semantic_evaluation::build_environment().unwrap();
        semantic_evaluation::install_handle_into(&mut env).unwrap();
        semantic_evaluation::install_case_maps_into(&mut env).unwrap();
        env.init_nat().unwrap();
        let foreign = LocalScope::new();
        let mut components = ProofComponents::new("image.foreign", ProofLimits::default());
        components.set_base(&foreign, vec![]).unwrap();
        let mut scope = LocalScope::new();
        let (globals, types, source) = fixture(&mut scope, 0);
        assert!(
            replay_image_with_components(
                &env,
                &mut scope,
                &globals,
                types,
                source,
                Level::zero(),
                ImageReplayLimits::default(),
                &mut components
            )
            .unwrap_err()
            .contains("matching root scope")
        );
    }
    #[test]
    fn cps_image_replay_checks_real_callback_eliminators_and_current_poststates() {
        let mut env = semantic_evaluation::build_environment().unwrap();
        semantic_evaluation::install_handle_into(&mut env).unwrap();
        semantic_evaluation::install_case_maps_into(&mut env).unwrap();
        env.init_nat().unwrap();
        env.init_option().unwrap();
        env.init_bool().unwrap();
        for family in 0..4 {
            let mut scope = LocalScope::new();
            let (globals, types, source) = fixture(&mut scope, family);
            let candidate = replay_image(
                &env,
                &mut scope,
                &globals,
                types.clone(),
                source.clone(),
                Level::zero(),
                ImageReplayLimits::default(),
            )
            .unwrap();
            assert_eq!(candidate.cases, 1);
            let goal = scope.close(&globals[0].pi(candidate.proposition)).unwrap();
            let proof = scope.close(&globals[0].lam(candidate.proof)).unwrap();
            let checker = TypeChecker::new(&env);
            let _checked_goal_type = checker.infer_type(&goal).unwrap();
            checker.check_type(&proof, &goal).unwrap();
            assert!(env.audit_certification(&goal, &proof).is_certified());
            let ignored = scope.allocate_local(nat()).unwrap();
            let outcome = Expr::apps(
                constant("Except.error", vec![Level::zero(), Level::zero()]),
                [nat(), nat(), Expr::nat_lit(0)],
            );
            let wrong = ignored.lam(Expr::apps(
                constant("Prod.mk", vec![Level::zero(), Level::zero()]),
                [
                    nat(),
                    Expr::apps(
                        constant("Except", vec![Level::zero(), Level::zero()]),
                        [nat(), nat()],
                    ),
                    Expr::nat_lit(0),
                    outcome,
                ],
            ));
            let bad = apply(
                CPS_IMAGE,
                &Level::zero(),
                [
                    types.state,
                    types.error,
                    types.value,
                    types.answer,
                    wrong,
                    source,
                ],
            );
            let bad = scope.close(&globals[0].pi(bad)).unwrap();
            let _ = checker.infer_type(&bad).unwrap();
            assert!(
                checker.check_type(&proof, &bad).is_err(),
                "false image observation accepted for family {family}"
            );
        }
    }
    #[test]
    fn cps_image_replay_refuses_opaque_returns_foreign_scope_and_missing_case_budget() {
        let mut env = semantic_evaluation::build_environment().unwrap();
        semantic_evaluation::install_handle_into(&mut env).unwrap();
        semantic_evaluation::install_case_maps_into(&mut env).unwrap();
        env.init_nat().unwrap();
        env.init_bool().unwrap();
        let mut scope = LocalScope::new();
        let (globals, types, source) = fixture(&mut scope, 0);
        let limits = ImageReplayLimits {
            max_cases: 0,
            ..ImageReplayLimits::default()
        };
        assert!(
            replay_image(
                &env,
                &mut scope,
                &globals,
                types.clone(),
                source.clone(),
                Level::zero(),
                limits
            )
            .is_err()
        );
        let limits = ImageReplayLimits {
            heartbeats: 0,
            ..ImageReplayLimits::default()
        };
        assert!(
            replay_image(
                &env,
                &mut scope,
                &globals,
                types.clone(),
                source.clone(),
                Level::zero(),
                limits
            )
            .is_err()
        );
        let mut other = LocalScope::new();
        // Erased expressions and types coincide: only the authenticated scope
        // handle distinguishes this foreign variable from the actual global.
        let foreign = (0..16)
            .map(|_| other.allocate_local(globals[0].ty().clone()).unwrap())
            .find(|local| local.id() == globals[0].id())
            .unwrap();
        assert_eq!(foreign.term(), globals[0].term());
        assert_eq!(foreign.ty(), globals[0].ty());
        assert!(
            replay_image(
                &env,
                &mut scope,
                &[foreign],
                types.clone(),
                source,
                Level::zero(),
                ImageReplayLimits::default()
            )
            .is_err()
        );
        let s = scope.allocate_local(nat()).unwrap();
        let cb = Expr::arrow(nat(), Expr::arrow(nat(), nat()));
        let ok = scope.allocate_local(cb.clone()).unwrap();
        let err = scope.allocate_local(cb).unwrap();
        let discarded = s.lam(ok.lam(err.lam(Expr::nat_lit(0))));
        assert!(
            replay_image(
                &env,
                &mut scope,
                &[],
                types,
                discarded,
                Level::zero(),
                ImageReplayLimits::default()
            )
            .is_err()
        );
    }
    #[test]
    fn cps_image_replay_refuses_well_typed_callback_dependent_first_order_data() {
        let mut env = semantic_evaluation::build_environment().unwrap();
        semantic_evaluation::install_handle_into(&mut env).unwrap();
        semantic_evaluation::install_case_maps_into(&mut env).unwrap();
        env.init_nat().unwrap();
        let mut scope = LocalScope::new();
        let value = Expr::arrow(nat(), Expr::arrow(nat(), nat()));
        let state = scope.allocate_local(nat()).unwrap();
        let ok = scope
            .allocate_local(Expr::arrow(nat(), Expr::arrow(value.clone(), nat())))
            .unwrap();
        let err = scope.allocate_local(value.clone()).unwrap();
        let source = state.lam(ok.lam(err.lam(Expr::apps(
            ok.term().clone(),
            [state.term().clone(), err.term().clone()],
        ))));
        let closed = scope.close(&source).unwrap();
        let _ = TypeChecker::new(&env).infer_type(&closed).unwrap();
        let types = ImageTypes {
            state: nat(),
            error: nat(),
            value,
            answer: nat(),
        };
        assert!(
            replay_image(
                &env,
                &mut scope,
                &[],
                types,
                source,
                Level::zero(),
                ImageReplayLimits::default()
            )
            .unwrap_err()
            .contains("depends on final CPS callbacks")
        );
    }
}

#[cfg(test)]
#[path = "cps_image_equation_tests.rs"]
mod equation_tests;

#[path = "cps_image_structured.rs"]
mod structured;
#[cfg(test)]
#[path = "cps_image_structured_tests.rs"]
mod structured_tests;

#[path = "cps_image_construction.rs"]
mod construction;
pub use construction::{
    StructuredContinuationConstruction, StructuredObservationConstruction,
    StructuredObservationStep, StructuredRunConstruction,
};

#[path = "cps_image_frame.rs"]
mod structured_frame;
pub use structured_frame::{
    FrameImageCandidate, FrameReplayTypes, OperationFrameEvidence,
    replay_success_frame_from_construction,
};
#[cfg(test)]
#[path = "cps_image_frame_tests.rs"]
mod structured_frame_tests;

#[cfg(test)]
#[path = "cps_image_retained_data_tests.rs"]
mod retained_data_tests;

#[path = "cps_image_case_context.rs"]
mod case_context;
