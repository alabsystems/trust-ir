// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Actual owned declaration metadata for subsequent same-owner proof composition.
use super::*;

/// Candidate metadata, never certification authority. The complete defining
/// value and every consumer still require frozen-claim, wire and rooted replay.
#[derive(Clone)]
pub struct OwnedScopedDefinition {
    pub local: ScopedLocal,
    /// Includes the actual dynamic parameter applications, when any.
    pub reference: Expr,
}
impl ProofComponents {
    /// Return the actual declaration allocated by the existing binder. Do not
    /// reconstruct a ScopedLocal from an erased FVar ID in a later producer.
    pub fn bind_scoped_owned<A: ScopedLocalAllocator>(
        &mut self,
        allocator: &mut A,
        captures: &[OwnedProofCapture],
        type_: Expr,
        value: Expr,
    ) -> Result<OwnedScopedDefinition, String> {
        let reference = self.bind_scoped(allocator, captures, type_, value)?;
        let (local, _) = self
            .bindings
            .last()
            .ok_or("owned component declaration was not retained")?;
        if !allocator.local_scope().owns(local) || !same_graph(reference.get_app_fn(), local.term())
        {
            return Err("owned component reference lost its exact allocated declaration".into());
        }
        Ok(OwnedScopedDefinition {
            local: local.clone(),
            reference,
        })
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Environment, Level};
    fn n() -> Expr {
        Expr::const_str("Nat")
    }
    fn eq(a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [n(), a, b],
        )
    }
    fn refl(a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [n(), a],
        )
    }
    fn env() -> Environment {
        let mut e = Environment::new();
        e.init_nat().unwrap();
        e.init_eq().unwrap();
        e.init_true_false().unwrap();
        e
    }
    #[test]
    fn owned_component_definition_plain_and_dynamic_references_keep_actual_owner_and_replay() {
        for dynamic in [false, true] {
            let mut scope = LocalScope::new();
            let input = scope.try_local(n()).unwrap();
            let mut p = ProofComponents::new("owned.definition.reference", ProofLimits::default());
            p.set_base(
                &scope,
                if dynamic {
                    vec![]
                } else {
                    vec![OwnedProofCapture::Parameter(input.clone())]
                },
            )
            .unwrap();
            let captures = if dynamic {
                vec![OwnedProofCapture::Parameter(input.clone())]
            } else {
                vec![]
            };
            let owned = p
                .bind_scoped_owned(&mut scope, &captures, n(), input.term().clone())
                .unwrap();
            assert!(scope.owns(&owned.local));
            assert_ne!(owned.local.id(), input.id());
            assert!(same_graph(owned.reference.get_app_fn(), owned.local.term()));
            assert_eq!(owned.reference.get_app_num_args(), usize::from(dynamic));
            let proposition = eq(owned.reference, input.term().clone());
            let claim = scope
                .close(&input.pi(eq(input.term().clone(), input.term().clone())))
                .unwrap();
            let bundle = p
                .close_scoped(
                    &scope,
                    input.lam(refl(input.term().clone())),
                    if dynamic {
                        input.pi(proposition)
                    } else {
                        proposition
                    },
                    Default::default(),
                )
                .unwrap();
            let wire = bundle.encode_with_claim(&claim).unwrap();
            let (decoded, transported) =
                ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
            assert_eq!(claim, transported);
            decoded.replay(&env(), &claim, 2_000_000).unwrap();
        }
    }
    #[test]
    fn owned_component_definition_metadata_never_certifies_a_cold_invalid_value() {
        let mut scope = LocalScope::new();
        let mut p = ProofComponents::new("owned.definition.invalid", ProofLimits::default());
        p.set_base(&scope, vec![]).unwrap();
        let candidate = p
            .bind_scoped_owned(&mut scope, &[], n(), Expr::const_str("True.intro"))
            .unwrap();
        assert!(scope.owns(&candidate.local));
        let claim = Expr::const_str("True");
        let bundle = p
            .close_scoped(
                &scope,
                Expr::const_str("True.intro"),
                claim.clone(),
                Default::default(),
            )
            .unwrap();
        let wire = bundle.encode_with_claim(&claim).unwrap();
        let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
        assert_eq!(claim, transported);
        let error = decoded.replay(&env(), &claim, 2_000_000).err().unwrap();
        assert!(
            error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
            "{error}"
        );
    }
    #[test]
    fn owned_component_definition_refuses_another_allocator_owner_without_publication() {
        let scope = LocalScope::new();
        let mut foreign = LocalScope::new();
        let mut p = ProofComponents::new("owned.definition.foreign", ProofLimits::default());
        p.set_base(&scope, vec![]).unwrap();
        assert!(
            p.bind_scoped_owned(&mut foreign, &[], n(), Expr::nat_lit(0))
                .is_err()
        );
        assert_eq!(p.counts().0, 0);
    }
}
