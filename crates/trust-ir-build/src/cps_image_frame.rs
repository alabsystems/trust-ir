// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Construct untrusted structured success-Frame proof candidates.
//! Resolver results and trace fields confer no authority. Complete original
//! definitions and independently frozen image/Frame endpoints MUST replay.
use super::*;
use crate::semantic_evaluation::{
    SUCCESS_FRAME_HANDLE_CONSTANT_OBSERVER, SUCCESS_FRAME_HANDLE_RELATED_OBSERVER,
    SUCCESS_FRAME_PROJECTION,
};

#[path = "cps_image_frame_relations.rs"]
mod relations;
use relations::ReachedRelations;

pub struct FrameReplayTypes {
    pub base: Expr,
    pub frame: Expr,
    pub error: Expr,
    pub value: Expr,
}
/// Candidate proof of normal Frame preservation of the ACTUAL operation Run.
/// The resolver must retain its original owned definitions in the same carrier;
/// no source provider fidelity, membership or physical custody is inferred.
pub struct OperationFrameEvidence {
    pub error: Expr,
    pub value: Expr,
    pub preserves: Expr,
}
pub struct FrameImageCandidate {
    pub proposition: Expr,
    pub proof: Expr,
}
struct FrameReplay<'a, L, R> {
    allocator: &'a mut L,
    parts: &'a mut ProofComponents,
    resolve: &'a mut R,
    types: FrameReplayTypes,
    u: Level,
    target: Expr,
    captures: Vec<OwnedProofCapture>,
    relations: ReachedRelations,
    nodes: usize,
}
// Failure-only, bounded syntax outline. It cannot authorize a transport.
fn frame_state_outline(expression: &Expr) -> String {
    fn walk(e: &Expr, depth: usize, left: &mut usize) -> String {
        if depth == 0 || *left == 0 {
            return "_".into();
        }
        *left -= 1;
        match e.kind() {
            ExprKind::FVar(id) => format!("{id:?}"),
            ExprKind::BVar(id) => format!("bvar{id}"),
            ExprKind::Const(name, levels) => {
                let label = ["Prod.mk", "Prod.snd", "Prod.fst", "Prod.rec"]
                    .into_iter()
                    .find(|n| name == &Name::from_string(n))
                    .unwrap_or("const");
                format!(
                    "{label}[n={},zero={:?}]",
                    levels.len(),
                    levels
                        .iter()
                        .take(2)
                        .map(|l| l == &Level::zero())
                        .collect::<Vec<_>>()
                )
            }
            ExprKind::App(..) => {
                let mut head = e;
                let mut args = Vec::new();
                while let ExprKind::App(fun, arg) = head.kind() {
                    if args.len() == 6 || *left == 0 {
                        break;
                    }
                    *left -= 1;
                    args.push(arg.as_ref());
                    head = fun.as_ref();
                }
                // Reverse arguments keep the actual frame field ahead of a
                // potentially large opaque base computation in the budget.
                let h = walk(head, depth - 1, left);
                let a = args
                    .into_iter()
                    .map(|a| walk(a, depth - 1, left))
                    .collect::<Vec<_>>();
                format!("app({h},rev={a:?})")
            }
            ExprKind::Proj(name, index, body) => format!(
                "proj(prod={},index={index},body={})",
                name == &Name::from_string("Prod"),
                walk(body, depth - 1, left)
            ),
            ExprKind::Let(_, ty, value, body, _) => format!(
                "let({},{},{})",
                walk(ty, depth - 1, left),
                walk(value, depth - 1, left),
                walk(body, depth - 1, left)
            ),
            _ => "other".into(),
        }
    }
    walk(expression, 4, &mut 48)
}

impl<L, R> FrameReplay<'_, L, R>
where
    L: ScopedLocalAllocator,
    R: FnMut(
        &mut L,
        &mut ProofComponents,
        &[OwnedProofCapture],
        &ScopedLocal,
        &[Expr],
    ) -> Result<OperationFrameEvidence, String>,
{
    fn frame(&self, state: Expr) -> Expr {
        Expr::apps(
            constant("Prod.snd", vec![self.u.clone(), self.u.clone()]),
            [self.types.base.clone(), self.types.frame.clone(), state],
        )
    }
    fn eq(&self, left: Expr, right: Expr) -> Expr {
        Expr::apps(
            constant("Eq", vec![Level::succ(self.u.clone())]),
            [self.types.frame.clone(), left, right],
        )
    }
    fn projection(&self, observation: Expr) -> Expr {
        apply(
            SUCCESS_FRAME_PROJECTION,
            &self.u,
            [
                self.types.base.clone(),
                self.types.frame.clone(),
                self.types.error.clone(),
                self.types.value.clone(),
                self.target.clone(),
                observation,
            ],
        )
    }
    fn goal(&self, observation: Expr) -> Expr {
        self.eq(self.projection(observation), self.target.clone())
    }
    fn available_relation(&mut self, state: &Expr) -> Result<Option<Expr>, String> {
        self.parts.spend_context_work(1)?; // current graph pin
        let mut current = state.clone();
        for depth in 0..=256 {
            self.parts.spend_context_work(1)?; // actual state kind
            if let ExprKind::FVar(id) = current.kind() {
                return self.relations.get(self.parts, *id);
            }
            if depth == 256 {
                return Ok(None);
            }
            let Some(previous) = self.projected_predecessor(&current)? else {
                return Ok(None);
            };
            current = previous;
        }
        unreachable!("bounded structural Frame transport returns from the loop")
    }
    fn relation(&mut self, state: &Expr) -> Result<Expr, String> {
        self.available_relation(state)?.ok_or_else(|| {
            if matches!(state.kind(), ExprKind::FVar(_)) {
                format!(
                    "structured Frame has no reached-state relation: state={:?}; reached={:?}; captures={:?}",
                    match state.kind() { ExprKind::FVar(id) => Some(*id), _ => None },
                    self.relations.ids().collect::<Vec<_>>(),
                    self.captures.iter().map(|capture| capture.local().id()).collect::<Vec<_>>(),
                )
            } else {
                "structured Frame needs an actual checked state transport".into()
            }
        })
    }
    fn case_spine(&mut self, expression: &Expr, arity: usize) -> Result<(Expr, Vec<Expr>), String> {
        let mut head = expression.clone();
        let mut args = Vec::new();
        loop {
            self.parts.spend_context_work(1)?;
            let ExprKind::App(f, a) = head.kind() else {
                break;
            };
            if args.len() >= arity {
                return Err("structured Frame case arity limit".into());
            }
            self.parts.spend_context_work(3)?;
            args.push(a.as_ref().clone());
            head = f.as_ref().clone();
        }
        self.parts.spend_context_work(args.len())?;
        args.reverse();
        if args.len() != arity {
            return Err("structured Frame case arity mismatch".into());
        }
        Ok((head, args))
    }
    fn expression(
        &mut self,
        node: &StructuredObservationConstruction,
        depth: usize,
    ) -> Result<Expr, String> {
        self.parts.spend_context_work(
            64usize
                .checked_add(self.captures.len())
                .ok_or("Frame construction work overflow")?,
        )?;
        if depth > 256 {
            return Err("structured Frame proof depth limit".into());
        }
        self.nodes = self
            .nodes
            .checked_add(1)
            .ok_or("Frame node count overflow")?;
        if self.nodes > 65_536 {
            return Err("structured Frame proof node limit".into());
        }
        let proof = match &node.step {
            StructuredObservationStep::Return { normal: false, .. } => Expr::apps(
                constant("Eq.refl", vec![Level::succ(self.u.clone())]),
                [self.types.frame.clone(), self.target.clone()],
            ),
            StructuredObservationStep::Return {
                normal: true,
                state,
                ..
            } => self.relation(state)?,
            StructuredObservationStep::Handle {
                operator,
                original_arguments,
                actual_run,
                actual_state,
                yes,
                no,
            } => {
                if !self.allocator.local_scope().owns(operator) {
                    return Err("structured Frame operator has another owner".into());
                }
                self.parts.spend_context_work(
                    original_arguments
                        .len()
                        .checked_mul(32)
                        .ok_or("Frame operation argument inventory overflow")?,
                )?;
                let evidence = (self.resolve)(
                    self.allocator,
                    self.parts,
                    &self.captures,
                    operator,
                    original_arguments,
                )?;
                let pre = self.available_relation(actual_state)?;
                let yes_run = yes
                    .payload
                    .lam(yes.poststate.lam(yes.body.observation.clone()));
                let no_run = no
                    .payload
                    .lam(no.poststate.lam(no.body.observation.clone()));
                for local in [&yes.payload, &yes.poststate, &no.payload, &no.poststate] {
                    if !self.allocator.local_scope().owns(local) {
                        return Err("foreign Frame continuation binder".into());
                    }
                }
                let relation = if pre.is_some() {
                    let ty = self.eq(
                        self.frame(yes.poststate.term().clone()),
                        self.target.clone(),
                    );
                    Some(self.allocator.allocate_local(ty)?)
                } else {
                    None
                };
                let capture_count = self.captures.len();
                let relation_count = self.relations.len();
                if let Some(relation) = &relation {
                    self.relations
                        .push(self.parts, &yes.poststate, relation.term())?;
                }
                self.captures.extend(
                    [yes.payload.clone(), yes.poststate.clone()]
                        .into_iter()
                        .map(OwnedProofCapture::Parameter),
                );
                if let Some(relation) = &relation {
                    self.captures
                        .push(OwnedProofCapture::Parameter(relation.clone()));
                }
                // Without a reached input relation, BOTH handlers must prove
                // the stronger observer for every actual postworld. No missing
                // relation becomes an assumption; budget failures propagate.
                let hy = self.expression(&yes.body, depth + 1);
                self.captures.truncate(capture_count);
                self.relations.restore(relation_count);
                let hy = hy.map_err(|error| {
                    format!(
                        "Frame Handle {:?} normal post={:?}, input={:?}, reached_input={}: {error}",
                        operator.id(),
                        yes.poststate.id(),
                        match actual_state.kind() {
                            ExprKind::FVar(id) => Some(*id),
                            _ => None,
                        },
                        pre.is_some(),
                    )
                }).map_err(|error| format!("{error}; input_syntax={}; expected_base={}; expected_frame={}", frame_state_outline(actual_state), frame_state_outline(&self.types.base), frame_state_outline(&self.types.frame)))?;
                let hy = yes.payload.lam(yes.poststate.lam(match relation {
                    Some(relation) => relation.lam(hy),
                    None => hy,
                }));
                self.captures.extend(
                    [no.payload.clone(), no.poststate.clone()]
                        .into_iter()
                        .map(OwnedProofCapture::Parameter),
                );
                let hn = self.expression(&no.body, depth + 1);
                self.captures.truncate(capture_count);
                let hn = hn.map_err(|error| {
                    format!(
                        "Frame Handle {:?} error post={:?}, input={:?}, reached_input={}: {error}",
                        operator.id(),
                        no.poststate.id(),
                        match actual_state.kind() {
                            ExprKind::FVar(id) => Some(*id),
                            _ => None,
                        },
                        pre.is_some(),
                    )
                })?;
                let hn = no.payload.lam(no.poststate.lam(hn));
                if let Some(pre) = pre {
                    apply(
                        SUCCESS_FRAME_HANDLE_RELATED_OBSERVER,
                        &self.u,
                        [
                            self.types.base.clone(),
                            self.types.frame.clone(),
                            evidence.error,
                            evidence.value,
                            self.types.error.clone(),
                            self.types.value.clone(),
                            actual_run.clone(),
                            yes_run,
                            no_run,
                            self.target.clone(),
                            actual_state.clone(),
                            evidence.preserves,
                            pre,
                            hy,
                            hn,
                        ],
                    )
                } else {
                    apply(
                        SUCCESS_FRAME_HANDLE_CONSTANT_OBSERVER,
                        &self.u,
                        [
                            self.types.base.clone(),
                            self.types.frame.clone(),
                            evidence.error,
                            evidence.value,
                            self.types.error.clone(),
                            self.types.value.clone(),
                            actual_run.clone(),
                            yes_run,
                            no_run,
                            self.target.clone(),
                            hy,
                            hn,
                            actual_state.clone(),
                        ],
                    )
                }
            }
            StructuredObservationStep::Case {
                head,
                parameters,
                major,
                branches,
            } => {
                let ExprKind::Const(name, levels) = head.kind() else {
                    return Err("Frame case head is not a recursor".into());
                };
                let name_str = if *name == Name::from_string("Prod.rec") {
                    "Prod.rec"
                } else if *name == Name::from_string("Except.rec") {
                    "Except.rec"
                } else if *name == Name::from_string("Option.rec") {
                    "Option.rec"
                } else if *name == Name::from_string("Bool.rec") {
                    "Bool.rec"
                } else {
                    return Err("unsupported structured Frame recursor".into());
                };
                let (arity, field_types, major_type) = match name_str {
                    "Prod.rec" if parameters.len() == 2 && levels.len() == 3 => (
                        5,
                        vec![parameters.clone()],
                        Expr::apps(constant("Prod", levels[1..].to_vec()), parameters.clone()),
                    ),
                    "Except.rec" if parameters.len() == 2 && levels.len() == 3 => (
                        6,
                        vec![vec![parameters[0].clone()], vec![parameters[1].clone()]],
                        Expr::apps(constant("Except", levels[1..].to_vec()), parameters.clone()),
                    ),
                    "Option.rec" if parameters.len() == 1 && levels.len() == 2 => (
                        5,
                        vec![vec![], vec![parameters[0].clone()]],
                        Expr::app(
                            constant("Option", levels[1..].to_vec()),
                            parameters[0].clone(),
                        ),
                    ),
                    "Bool.rec" if parameters.is_empty() && levels.len() == 1 => {
                        (4, vec![vec![], vec![]], constant("Bool", vec![]))
                    }
                    _ => return Err("unsupported structured Frame recursor".into()),
                };
                if branches.len() != field_types.len() {
                    return Err("structured Frame case coverage mismatch".into());
                }
                let (actual_head, args) = self.case_spine(&node.observation, arity)?;
                let ExprKind::Const(actual_name, actual_levels) = actual_head.kind() else {
                    return Err("structured Frame observation case head missing".into());
                };
                if actual_name != name
                    || actual_levels.len() != levels.len()
                    || actual_levels[1..] != levels[1..]
                {
                    return Err("structured Frame observation recursor mismatch".into());
                }
                let fresh = self.allocator.allocate_local(major_type)?;
                let mut at_major = args[..args.len() - 1]
                    .iter()
                    .map(|e| e.clone())
                    .collect::<Vec<_>>();
                at_major.push(fresh.term().clone());
                let motive = fresh.lam(self.goal(Expr::apps(actual_head, at_major)));
                let mut proof_args = parameters.clone();
                proof_args.push(motive);
                for (branch_index, ((locals, child), expected_types)) in
                    branches.iter().zip(field_types).enumerate()
                {
                    if locals.len() != expected_types.len()
                        || locals
                            .iter()
                            .zip(expected_types)
                            .any(|(l, t)| !self.allocator.local_scope().owns(l) || l.ty() != &t)
                    {
                        return Err(
                            "structured Frame case changed actual constructor fields".into()
                        );
                    }
                    self.parts.spend_context_work(
                        locals
                            .len()
                            .checked_mul(2)
                            .and_then(|n| n.checked_add(8))
                            .ok_or("Frame branch inventory overflow")?,
                    )?;
                    let capture_count = self.captures.len();
                    self.captures
                        .extend(locals.iter().cloned().map(OwnedProofCapture::Parameter));
                    let branch = self.expression(child, depth + 1);
                    self.captures.truncate(capture_count);
                    let branch = branch.map_err(|error| format!(
                        "Frame Case {name_str} branch={branch_index}, major={:?}, head={:?}, fields={:?}: {error}",
                        match major.kind() { ExprKind::FVar(id) => Some(*id), _ => None },
                        match major.get_app_fn().kind() { ExprKind::FVar(id) => Some(*id), _ => None },
                        locals.iter().map(ScopedLocal::id).collect::<Vec<_>>(),
                    ))?;
                    let branch = locals
                        .iter()
                        .rev()
                        .fold(branch, |body, local| local.lam(body));
                    proof_args.push(branch);
                }
                proof_args.push(major.clone());
                let mut proof_levels = levels.to_vec();
                proof_levels[0] = Level::zero();
                Expr::apps(constant(name_str, proof_levels), proof_args)
            }
        };
        // Check the ACTUAL observation from the original image construction,
        // never silently replace it with a reconstructed trace endpoint.
        let goal = self.goal(node.observation.clone());
        if depth > 0 {
            // Keep EVERY actual nested goal as a checked ordinary let
            // annotation, including Case/Handle nodes. The global root checks
            // the entire proof, and strict Let checking checks each nested
            // value against its actual annotation before using the body.
            // Lexically local proofs need no separate global helper or
            // repeated dynamic capture abstraction/inventory storage.
            self.parts.spend_context_work(5)?; // let, three child pins, BVar
            return Ok(Expr::let_(goal, proof, Expr::bvar(0)));
        }
        self.parts
            .bind_scoped(self.allocator, &self.captures, goal, proof)
    }
}

pub fn replay_success_frame_from_construction<L, R>(
    allocator: &mut L,
    parts: &mut ProofComponents,
    construction: &StructuredRunConstruction,
    types: FrameReplayTypes,
    u: Level,
    resolve: &mut R,
) -> Result<FrameImageCandidate, String>
where
    L: ScopedLocalAllocator,
    R: FnMut(
        &mut L,
        &mut ProofComponents,
        &[OwnedProofCapture],
        &ScopedLocal,
        &[Expr],
    ) -> Result<OperationFrameEvidence, String>,
{
    parts.spend_context_work(32)?;
    if !allocator.local_scope().owns(&construction.input) {
        return Err("structured Frame input has another owner".into());
    }
    let target = Expr::apps(
        constant("Prod.snd", vec![u.clone(), u.clone()]),
        [
            types.base.clone(),
            types.frame.clone(),
            construction.input.term().clone(),
        ],
    );
    let initial = Expr::apps(
        constant("Eq.refl", vec![Level::succ(u.clone())]),
        [types.frame.clone(), target.clone()],
    );
    let start = parts.counts();
    let mut relations = ReachedRelations::default();
    relations.push(parts, &construction.input, &initial)?;
    let mut replay = FrameReplay {
        allocator,
        parts,
        resolve,
        types,
        u,
        target,
        captures: vec![OwnedProofCapture::Parameter(construction.input.clone())],
        relations,
        nodes: 0,
    };
    let result = replay.expression(&construction.root, 0);
    let proof = result.map_err(|error| {
        format!(
            "structured Frame construction (nodes={}, start={start:?}, current={:?}): {error}",
            replay.nodes,
            replay.parts.counts()
        )
    })?;
    Ok(FrameImageCandidate {
        proposition: construction
            .input
            .pi(replay.goal(construction.root.observation.clone())),
        proof: construction.input.lam(proof),
    })
}

#[path = "cps_image_frame_transport.rs"]
mod transport;
