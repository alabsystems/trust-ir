// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! A rebuilt state retains only an ALREADY reached frame projection.
//! This constructs no premise. The existing proof is used at the actual
//! constructor goal, which still requires complete strict decoded replay.
use super::*;

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
    fn product_arguments(
        &mut self,
        expression: &Expr,
        name: &str,
        arity: usize,
    ) -> Result<Option<Vec<Expr>>, String> {
        self.parts.spend_context_work(1)?;
        if !matches!(expression.kind(), ExprKind::App(..)) {
            return Ok(None);
        }
        // Exact requested slots/header and the temporary head pin are paid
        // before allocation. At most arity+1 App heads can be inspected.
        self.parts.spend_context_work(
            arity
                .checked_add(2)
                .ok_or("Frame product inventory overflow")?,
        )?;
        let mut args = Vec::with_capacity(arity);
        let mut head = expression.clone();
        loop {
            self.parts.spend_context_work(1)?;
            let ExprKind::App(fun, arg) = head.kind() else {
                break;
            };
            if args.len() == arity {
                return Ok(None);
            }
            self.parts.spend_context_work(3)?; // argument pin, head pin, push
            args.push(arg.as_ref().clone());
            head = fun.as_ref().clone();
        }
        self.parts.spend_context_work(2)?; // exact head/level checks
        let ExprKind::Const(actual, levels) = head.kind() else {
            return Ok(None);
        };
        if args.len() != arity
            || *actual != Name::from_string(name)
            || levels.as_slice() != [self.u.clone(), self.u.clone()]
        {
            return Ok(None);
        }
        self.parts.spend_context_work(args.len())?;
        args.reverse();
        Ok(Some(args))
    }
    pub(super) fn projected_predecessor(&mut self, state: &Expr) -> Result<Option<Expr>, String> {
        self.parts.spend_context_work(1)?;
        if let ExprKind::Proj(name, 0, raw) = state.kind() {
            if *name == Name::from_string("Prod") {
                if let Some(pair) = self.product_arguments(raw, "Prod.mk", 4)? {
                    // A kernel product projection of its actual constructor
                    // reduces to that field. This remains only a candidate:
                    // the actual type/field/value must pass strict replay.
                    self.parts.spend_context_work(1)?;
                    return Ok(Some(pair[2].clone()));
                }
            }
        }
        let Some(pair) = self.product_arguments(state, "Prod.mk", 4)? else {
            return Ok(None);
        };
        self.parts.spend_context_work(2)?;
        if !crate::proof_assembly::normalize::same_graph(&pair[0], &self.types.base)
            || !crate::proof_assembly::normalize::same_graph(&pair[1], &self.types.frame)
        {
            return Ok(None);
        }
        let Some(projection) = self.product_arguments(&pair[3], "Prod.snd", 3)? else {
            return Ok(None);
        };
        self.parts.spend_context_work(3)?; // both exact types and returned pin
        if !crate::proof_assembly::normalize::same_graph(&projection[0], &self.types.base)
            || !crate::proof_assembly::normalize::same_graph(&projection[1], &self.types.frame)
        {
            return Ok(None);
        }
        // Prod.snd B F (Prod.mk B F base (Prod.snd B F previous)) is
        // definitionally Prod.snd B F previous. Nothing about `base` or a
        // normal-return label supplies a new frame equality.
        Ok(Some(projection[2].clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scoped_local::LocalScope;
    fn n() -> Expr {
        Expr::const_str("Nat")
    }
    fn project(state: Expr) -> Expr {
        Expr::apps(
            constant("Prod.snd", vec![Level::zero(), Level::zero()]),
            [n(), n(), state],
        )
    }
    fn rebuild(state: Expr) -> Expr {
        Expr::apps(
            constant("Prod.mk", vec![Level::zero(), Level::zero()]),
            [n(), n(), Expr::nat_lit(0), project(state)],
        )
    }
    fn query(
        scope: &mut LocalScope,
        parts: &mut ProofComponents,
        input: &ScopedLocal,
        state: &Expr,
    ) -> Result<Option<Expr>, String> {
        let target = project(input.term().clone());
        let initial = Expr::apps(
            constant("Eq.refl", vec![Level::succ(Level::zero())]),
            [n(), target.clone()],
        );
        let mut resolve = |_: &mut LocalScope,
                           _: &mut ProofComponents,
                           _: &[OwnedProofCapture],
                           _: &ScopedLocal,
                           _: &[Expr]|
         -> Result<OperationFrameEvidence, String> {
            panic!("structural transport must not invent an operation premise")
        };
        let mut relations = ReachedRelations::default();
        relations.push(parts, input, &initial)?;
        let mut replay = FrameReplay {
            allocator: scope,
            parts,
            resolve: &mut resolve,
            types: FrameReplayTypes {
                base: n(),
                frame: n(),
                error: n(),
                value: n(),
            },
            u: Level::zero(),
            target,
            captures: vec![OwnedProofCapture::Parameter(input.clone())],
            relations,
            nodes: 0,
        };
        let result = replay.available_relation(state);
        if let Ok(Some(proof)) = &result {
            assert!(
                crate::proof_assembly::normalize::same_graph(proof, replay.relations.proof_at(0)),
                "transport must return the actual stored proof graph"
            );
        }
        assert_eq!(replay.relations.len(), 1);
        assert_eq!(replay.relations.ids().next().unwrap(), input.id());
        assert_eq!(replay.captures.len(), 1);
        assert_eq!(replay.nodes, 0);
        assert_eq!(replay.parts.counts().0, 0);
        result
    }
    #[test]
    fn cps_image_replay_frame_product_transport_every_probe_and_storage_cutoff_is_paid_without_publication()
     {
        let mut scope = LocalScope::new();
        let input = scope
            .try_local(pair_type(&Level::zero(), n(), n()))
            .unwrap();
        let state = rebuild(rebuild(input.term().clone()));
        let expected = Expr::apps(
            constant("Eq.refl", vec![Level::succ(Level::zero())]),
            [n(), project(input.term().clone())],
        );
        let (mut success, mut refused) = (false, false);
        for cap in 0..=512 {
            let mut parts = ProofComponents::new(
                "frame.product.transport.cutoff",
                crate::proof_assembly::ProofLimits {
                    operations: cap,
                    ..Default::default()
                },
            );
            parts.set_base(&scope, vec![]).unwrap();
            match query(&mut scope, &mut parts, &input, &state) {
                Ok(Some(proof)) => {
                    success = true;
                    assert_eq!(proof, expected);
                }
                Ok(None) => panic!("an exact rebuilt reached projection must remain eligible"),
                Err(_) => refused = true,
            }
            assert!(
                parts.counts().3 <= cap,
                "cap={cap}, counts={:?}",
                parts.counts()
            );
        }
        assert!(success && refused);
    }
    #[test]
    fn cps_image_replay_frame_product_transport_unknown_projection_and_oversized_spine_stay_refused()
     {
        let mut scope = LocalScope::new();
        let input = scope
            .try_local(pair_type(&Level::zero(), n(), n()))
            .unwrap();
        let unknown = scope
            .try_local(pair_type(&Level::zero(), n(), n()))
            .unwrap();
        let mut parts =
            ProofComponents::new("frame.product.transport.negative", Default::default());
        parts.set_base(&scope, vec![]).unwrap();
        assert!(
            query(
                &mut scope,
                &mut parts,
                &input,
                &rebuild(unknown.term().clone())
            )
            .unwrap()
            .is_none()
        );
        let wrong_projection = Expr::apps(
            constant("Prod.mk", vec![Level::zero(), Level::zero()]),
            [
                n(),
                n(),
                Expr::nat_lit(0),
                Expr::apps(
                    constant("Prod.fst", vec![Level::zero(), Level::zero()]),
                    [n(), n(), input.term().clone()],
                ),
            ],
        );
        assert!(
            query(&mut scope, &mut parts, &input, &wrong_projection)
                .unwrap()
                .is_none()
        );
        let mut oversized = rebuild(input.term().clone());
        for _ in 0..1024 {
            oversized = Expr::app(oversized, Expr::nat_lit(0));
        }
        let before = parts.counts().3;
        assert!(
            query(&mut scope, &mut parts, &input, &oversized)
                .unwrap()
                .is_none()
        );
        assert!(
            parts.counts().3 - before < 64,
            "unsupported application inventories must inspect only a bounded prefix"
        );
    }
    #[test]
    fn cps_image_replay_frame_product_transport_keeps_a_finite_chain_boundary() {
        let mut scope = LocalScope::new();
        let input = scope
            .try_local(pair_type(&Level::zero(), n(), n()))
            .unwrap();
        let mut state = input.term().clone();
        for _ in 0..256 {
            state = rebuild(state);
        }
        let mut parts = ProofComponents::new("frame.product.transport.depth", Default::default());
        parts.set_base(&scope, vec![]).unwrap();
        assert!(
            query(&mut scope, &mut parts, &input, &state)
                .unwrap()
                .is_some()
        );
        assert!(
            query(&mut scope, &mut parts, &input, &rebuild(state))
                .unwrap()
                .is_none()
        );
    }
}
