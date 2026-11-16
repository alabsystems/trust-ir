// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Candidate construction from actual retained pointwise equations. No CPS
//! function is assigned a Run: the Run must occur in its actual equation type.
use super::*;
use crate::semantic_evaluation::{CPS_IMAGE_HANDLE, HANDLE};

// The two callers have fixed arities3 and8. Borrow only that many App
// children plus the actual head; malformed tails allocate no argument vector.
// The existing64-unit statement/construction reservation remains unchanged.
fn exact_spine<const N: usize>(expression: &Expr) -> Option<(&Expr, [&Expr; N])> {
    let mut head = expression;
    let mut args = [expression; N];
    for slot in args.iter_mut().rev() {
        let ExprKind::App(function, argument) = head.kind() else {
            return None;
        };
        *slot = argument.as_ref();
        head = function.as_ref();
    }
    if matches!(head.kind(), ExprKind::App(..)) {
        return None;
    }
    Some((head, args))
}

#[cfg(test)]
#[path = "cps_image_statement_spine_tests.rs"]
mod spine_tests;

type ContinuationResult = (Expr, Expr, Expr, StructuredContinuationConstruction);

impl<L: ScopedLocalAllocator> Replay<'_, '_, L> {
    fn actual_equation(
        &mut self,
        equation: &PreparedCallEquation,
        args: &[Expr],
    ) -> Result<Expr, String> {
        let statement = equation
            .statement
            .as_ref()
            .ok_or("missing actual equation type")?;
        let before = self.spent();
        let (result, work) = self
            .components
            .as_mut()
            .ok_or("structured replay lost substitution owner")?
            .charged_instantiate_in_external_context_observed(
                self.allocator.local_scope(),
                self.external
                    .as_ref()
                    .ok_or("structured replay lost external inventory")?,
                statement,
                args,
            );
        let result = result.map_err(|error| format!("actual call equation substitution: {error}"));
        self.work.equations += self.spent().saturating_sub(before);
        self.work.equation_materialization += work.materialization;
        self.work.equation_substitution += work.substitution;
        result
    }
    fn continuation_pair(
        &mut self,
        callbacks: [(Expr, Expr); 2],
        depth: usize,
    ) -> Result<[ContinuationResult; 2], String> {
        // Sibling continuations bind these same fresh handles on disjoint
        // paths. No parent/child binder is reused. Redirect their actual roots
        // together so common callback graphs get one fresh substitution memo.
        self.charge_equation_work(8)?;
        let [(yes, yes_type), (no, no_type)] = callbacks;
        let yes_payload = self.local(yes_type)?;
        let yes_state = self.local(self.types.state.clone())?;
        let no_payload = self.local(no_type)?;
        let no_state = self.local(self.types.state.clone())?;
        let ok = self.local(self.ok.ty().clone())?;
        let err = self.local(self.err.ty().clone())?;
        let checkpoint = self.push_external_scope(&[
            yes_payload.clone(),
            yes_state.clone(),
            no_payload.clone(),
            no_state.clone(),
            ok.clone(),
            err.clone(),
        ])?;
        let before = self.spent();
        let redirected = self
            .components
            .as_mut()
            .ok_or("structured replay lost owner")?
            .substitute_materialized_in_external_context(
                self.allocator.local_scope(),
                self.external
                    .as_ref()
                    .ok_or("structured replay lost external inventory")?,
                &[
                    (self.ok.clone(), ok.term().clone()),
                    (self.err.clone(), err.term().clone()),
                ],
                &[
                    Expr::apps(yes, [yes_state.term().clone(), yes_payload.term().clone()]),
                    Expr::apps(no, [no_state.term().clone(), no_payload.term().clone()]),
                ],
            );
        self.work.redirection += self.spent().saturating_sub(before);
        let result = (|| {
            let [yes, no]: [Expr; 2] = redirected?
                .try_into()
                .map_err(|_| "structured redirection changed root count")?;
            let yes =
                self.continuation(yes, yes_payload, yes_state, ok.clone(), err.clone(), depth)?;
            let no = self.continuation(no, no_payload, no_state, ok, err, depth)?;
            Ok([yes, no])
        })();
        self.restore_external_scope(checkpoint)?;
        result
    }
    fn continuation(
        &mut self,
        expression: Expr,
        payload: ScopedLocal,
        state: ScopedLocal,
        ok: ScopedLocal,
        err: ScopedLocal,
        depth: usize,
    ) -> Result<ContinuationResult, String> {
        let mapper = self.local(Expr::arrow(self.observation(), self.types.answer.clone()))?;
        let observed = self.local(self.observation())?;
        let ignored = self.local(self.types.state.clone())?;
        let mapper_value = observed.lam(apply(
            TO_CPS,
            &self.u,
            [
                self.types.state.clone(),
                self.types.error.clone(),
                self.types.value.clone(),
                self.types.answer.clone(),
                ignored.lam(observed.term().clone()),
                state.term().clone(),
                ok.term().clone(),
                err.term().clone(),
            ],
        ));
        let external_checkpoint = self.push_external_scope(std::slice::from_ref(&mapper))?;
        let previous = (
            self.ok.clone(),
            self.err.clone(),
            self.mapper.clone(),
            self.mapper_definition.clone(),
        );
        let capture_count = self.captures.len();
        self.captures.extend(
            [payload.clone(), state.clone(), ok.clone(), err.clone()]
                .into_iter()
                .map(OwnedProofCapture::Parameter),
        );
        self.captures.push(OwnedProofCapture::Definition {
            local: mapper.clone(),
            value: std::sync::Arc::new(mapper_value.clone()),
        });
        self.ok = ok.clone();
        self.err = err.clone();
        self.mapper = mapper.clone();
        self.mapper_definition = mapper_value.clone();
        let child = self.expression(expression.clone(), depth + 1);
        self.captures.truncate(capture_count);
        self.restore_external_scope(external_checkpoint)?;
        (self.ok, self.err, self.mapper, self.mapper_definition) = previous;
        let child = child?;
        self.independent_observation_of(
            &[
                self.ok.clone(),
                self.err.clone(),
                self.mapper.clone(),
                ok.clone(),
                err.clone(),
                mapper.clone(),
            ],
            &child,
        )?;
        self.charge_equation_work(4)?;
        let construction = StructuredContinuationConstruction {
            payload: payload.clone(),
            poststate: state.clone(),
            body: child
                .construction
                .ok_or("structured continuation lost actual construction")?,
        };
        Ok((
            payload.lam(state.lam(child.observation)),
            payload.lam(state.lam(ok.lam(err.lam(expression)))),
            payload.lam(state.lam(ok.lam(err.lam(mapper.let_(mapper_value, child.proof))))),
            construction,
        ))
    }
    pub(super) fn structured_call(
        &mut self,
        source: Expr,
        args: Vec<Expr>,
        equation: PreparedCallEquation,
        depth: usize,
    ) -> Result<ImageNode, String> {
        self.cases = self
            .cases
            .checked_add(1)
            .ok_or("structured case overflow")?;
        if self.cases > self.limits.max_cases {
            return Err("CPS image replay case limit".into());
        }
        let statement = self.actual_equation(&equation, &args)?;
        self.charge_equation_work(64)?;
        let (eqhead, eqargs) =
            exact_spine::<3>(&statement).ok_or("actual call equation has unsupported endpoint")?;
        if eqhead != &constant("Eq", vec![Level::succ(self.u.clone())])
            || *eqargs[0] != self.types.answer
            || *eqargs[1] != source
        {
            return Err("actual call equation has unsupported endpoint".into());
        }
        let rhs = eqargs[2].clone();
        let (head, arguments) =
            exact_spine::<8>(&rhs).ok_or("actual call equation must expose literal TO_CPS Run")?;
        if head != &constant(TO_CPS, vec![self.u.clone()]) {
            return Err("actual call equation must expose literal TO_CPS Run".into());
        }
        let a = arguments.map(Expr::clone);
        if a[0] != self.types.state || a[3] != self.types.answer {
            return Err("actual TO_CPS state/Answer mismatch".into());
        }
        self.independent_forest_of(
            &[self.ok.clone(), self.err.clone(), self.mapper.clone()],
            &[&a[0], &a[1], &a[2], &a[3], &a[4], &a[5]],
        )?;
        let [
            (yes_run, yes_code, yes_image, yes_construction),
            (no_run, no_code, no_image, no_construction),
        ] = self.continuation_pair(
            [(a[6].clone(), a[2].clone()), (a[7].clone(), a[1].clone())],
            depth,
        )?;
        let operation_code = apply(TO_CPS, &self.u, a[..5].iter().cloned());
        let state = self.local(a[0].clone())?;
        let ky = self.local(Expr::arrow(
            a[0].clone(),
            Expr::arrow(a[2].clone(), a[3].clone()),
        ))?;
        let kn = self.local(Expr::arrow(
            a[0].clone(),
            Expr::arrow(a[1].clone(), a[3].clone()),
        ))?;
        let applied = Expr::apps(
            operation_code.clone(),
            [state.term().clone(), ky.term().clone(), kn.term().clone()],
        );
        let image = state.lam(ky.lam(kn.lam(Expr::apps(
            constant("Eq.refl", vec![Level::succ(self.u.clone())]),
            [a[3].clone(), applied],
        ))));
        let run = apply(
            HANDLE,
            &self.u,
            [
                a[0].clone(),
                a[1].clone(),
                a[2].clone(),
                self.types.error.clone(),
                self.types.value.clone(),
                a[4].clone(),
                yes_run.clone(),
                no_run.clone(),
            ],
        );
        let observation = Expr::app(run, a[5].clone());
        let finish = Expr::app(self.mapper.term().clone(), observation.clone());
        let composition = apply(
            CPS_IMAGE_HANDLE,
            &self.u,
            [
                a[0].clone(),
                a[1].clone(),
                a[2].clone(),
                self.types.error.clone(),
                self.types.value.clone(),
                a[3].clone(),
                a[4].clone(),
                operation_code,
                yes_run,
                no_run,
                yes_code,
                no_code,
                image,
                yes_image,
                no_image,
                a[5].clone(),
                self.ok.term().clone(),
                self.err.term().clone(),
            ],
        );
        self.charge_equation_work(
            args.len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(12))
                .ok_or("HANDLE construction custody work overflow")?,
        )?;
        let construction = Some(Box::new(StructuredObservationConstruction {
            observation: observation.clone(),
            step: StructuredObservationStep::Handle {
                operator: Box::new(
                    equation
                        .operator
                        .ok_or("structured call lost original owned operator")?,
                ),
                original_arguments: args.clone(),
                actual_run: a[4].clone(),
                actual_state: self.frame_state_candidate(&a[5])?,
                yes: Box::new(yes_construction),
                no: Box::new(no_construction),
            },
        }));
        let proof = Expr::apps(
            constant("Eq.trans", vec![Level::succ(self.u.clone())]),
            [
                self.types.answer.clone(),
                source.clone(),
                rhs,
                finish,
                Expr::apps(equation.proof, args),
                composition,
            ],
        );
        Ok(ImageNode {
            references: self.retain_observation(&observation)?,
            observation: observation.clone(),
            source,
            compact_observation: observation,
            proof,
            pending_cases: 0,
            construction,
        })
    }
}
