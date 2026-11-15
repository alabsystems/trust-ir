// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Fixed32 pending modulus candidates shared by the Add and Mul adapters.
//! This installs no declaration, evaluator, remainder package or authority.

use super::*;

fn symmetric_nat(left: Expr, right: Expr, term: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [constant("Nat"), left, right, term],
    )
}

impl Assembler<'_> {
    // Six charged construction operations, on the SAME caller ledger. Close
    // the neutral proof before applying an arbitrary caller-owned expression.
    pub(super) fn wrapped_word32_mod(&mut self, input: Expr) -> Result<PendingEquality> {
        self.wrapped_word_mod(32, input)
    }
    pub(super) fn wrapped_word64_mod(&mut self, input: Expr) -> Result<PendingEquality> {
        self.wrapped_word_mod(64, input)
    }
    fn wrapped_word_mod(&mut self, bits: u64, input: Expr) -> Result<PendingEquality> {
        if bits != 32 && bits != 64 {
            return Err("word modulus supports32or64 only".into());
        }
        let predecessor = if bits == 64 {
            u64::MAX
        } else {
            u32::MAX.into()
        };
        // Charge the fixed root applications and neutral proof assembly in
        // addition to each charged congruence/conversion/composition below.
        self.charge()?;
        let ty = constant("Nat");
        let modulus = app("ir_nat_pow2", [nat(bits)]);
        let n = Expr::bvar(0);
        let quotient = app("ir_div_go", [n.clone(), n.clone(), modulus.clone()]);
        let residue = app("ir_div_rem_go", [modulus.clone(), n.clone(), n.clone()]);
        let custom_product = app("ir_nat_mul", [quotient.clone(), modulus.clone()]);
        let standard_product = app("Nat.mul", [quotient.clone(), modulus.clone()]);
        let custom_sum = app("Nat.add", [custom_product.clone(), residue.clone()]);
        let standard_sum = app("Nat.add", [standard_product.clone(), residue.clone()]);
        let product = PendingEquality::candidate(
            ty.clone(),
            custom_product,
            standard_product,
            app(
                "ir_nat_mul_canonical_agrees_v1",
                [quotient.clone(), modulus.clone()],
            ),
        );
        // Apply a CLOSED add-right function to the neutral residue. Inserting
        // the caller's n directly under an extra lambda would capture its BVar.
        let add_right = Expr::lam(
            clean_kernel::BinderInfo::Default,
            ty.clone(),
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                ty.clone(),
                app("Nat.add", [Expr::bvar(0), Expr::bvar(1)]),
            ),
        );
        let standard_sum_eq =
            self.congruence_function(product, ty.clone(), Expr::app(add_right, residue.clone()))?;
        let standard_sum_eq =
            self.convert_endpoints(standard_sum_eq, custom_sum.clone(), standard_sum.clone())?;
        let decomposition = PendingEquality::candidate(
            ty.clone(),
            n.clone(),
            custom_sum.clone(),
            symmetric_nat(
                custom_sum,
                n.clone(),
                app("ir_div_go_pair_eq", [modulus.clone(), n.clone(), n.clone()]),
            ),
        );
        let decomposition = self.compose(decomposition, standard_sum_eq)?;
        let residue_ltb = app("ir_nat_ltb", [residue.clone(), modulus.clone()]);
        let residue_walk = app("ir_nat_ltb_walk", [residue.clone(), modulus.clone()]);
        let comparison = self.compose(
            PendingEquality::candidate(
                constant("Bool"),
                residue_ltb,
                residue_walk.clone(),
                app("ir_nat_ltb_walk_eq", [residue.clone(), modulus.clone()]),
            ),
            PendingEquality::candidate(
                constant("Bool"),
                residue_walk,
                constant("Bool.true"),
                app(
                    "ir_div_rem_go_bound",
                    [
                        modulus.clone(),
                        n.clone(),
                        n.clone(),
                        app("ir_div_fuel_suffices_pos", [n.clone(), nat(predecessor)]),
                    ],
                ),
            ),
        )?;
        let residue_bound = app(
            "ir_byte_separation_lt_of_ltb_v1",
            [residue.clone(), modulus.clone(), comparison.term().clone()],
        );
        // Nat.lt 0 2^32 is Nat.le 1 (1 + 4294967295). Replay checks the
        // closed positive modulus; it is not an input or result-fit premise.
        let positive = app("Nat.le_add_right", [nat(1), nat(predecessor)]);
        let modulus_result = app("Nat.mod", [n.clone(), modulus.clone()]);
        let mod_unique = app(
            "ir_byte_mod_unique_v1",
            [
                n.clone(),
                modulus.clone(),
                quotient,
                residue.clone(),
                positive,
                residue_bound,
                decomposition.term().clone(),
            ],
        );
        let neutral = self.compose(
            PendingEquality::candidate(
                ty.clone(),
                app("ir_wrap", [nat(bits), n.clone()]),
                residue.clone(),
                app("ir_nat_rem_is_residue", [n.clone(), modulus.clone()]),
            ),
            PendingEquality::candidate(
                ty.clone(),
                residue.clone(),
                modulus_result.clone(),
                symmetric_nat(modulus_result, residue, mod_unique),
            ),
        )?;
        let closed = Expr::lam(
            clean_kernel::BinderInfo::Default,
            ty.clone(),
            neutral.term().clone(),
        );
        Ok(PendingEquality::candidate(
            ty,
            app("ir_wrap", [nat(bits), input.clone()]),
            app("Nat.mod", [input.clone(), modulus]),
            Expr::app(closed, input),
        ))
    }

    /// Pending actual raw uint32 Add modulus agreement and its strict range.
    ///
    /// No canonical input, result answer or bound premise is supplied. The
    /// word is exactly `ir_wrap 32 (Nat.add a b)`, related to prelude Nat.mod.
    /// Ten existing operations are charged on this caller's construction
    /// ledger; no locals or lookup cache are allocated. Complete independent
    /// strict rooted and lossless replay in the checked arithmetic owner is
    /// required; pending metadata grants no source, body or native authority.
    pub fn byte_add_word32_mod(
        &mut self,
        a: Expr,
        b: Expr,
    ) -> Result<(Expr, PendingEquality, PendingProof)> {
        let sum = app("Nat.add", [a, b]);
        let equality = self.wrapped_word32_mod(sum.clone())?;
        let bounded = self.wrapped_word_bound(32, sum)?;
        Ok((bounded.word, equality, bounded.strict_bound))
    }
    /// Pending raw full64 Add/modulus correspondence and exact result bound.
    /// No source, fetched-step or native authority follows before canonical replay.
    pub fn byte_add_word64_mod(
        &mut self,
        a: Expr,
        b: Expr,
    ) -> Result<(Expr, PendingEquality, PendingProof)> {
        let sum = app("Nat.add", [a, b]);
        let equality = self.wrapped_word64_mod(sum.clone())?;
        let bounded = self.wrapped_word_bound(64, sum)?;
        Ok((bounded.word, equality, bounded.strict_bound))
    }
    /// Closed canonical-word codec. Its explicit bound premise is preserved:
    /// forall n, n < 2^64 -> ir_wrap 64 n = n. This is pending proof data,
    /// never a Rust u64 assertion, input answer or unchecked native permission.
    pub fn byte_word64_codec(&mut self) -> Result<PendingProof> {
        let n = Expr::bvar(1);
        let h = Expr::bvar(0);
        let limit = app("ir_nat_pow2", [nat(64)]);
        let wrap_mod = self.wrapped_word64_mod(n.clone())?;
        // Use the existing checked prelude below-modulus theorem directly;
        // no enormous zero-product reduction is needed for 2^64.
        let mod_eq = app("Nat.mod_eq_of_lt", [n.clone(), limit.clone(), h]);
        let eq_mod = PendingEquality::candidate(
            constant("Nat"),
            app("Nat.mod", [n.clone(), limit.clone()]),
            n.clone(),
            mod_eq,
        );
        let result = self.compose(wrap_mod, eq_mod)?;
        let bound = app("Nat.lt", [Expr::bvar(0), limit]);
        let close_ty = |body| {
            Expr::pi(
                clean_kernel::BinderInfo::Default,
                constant("Nat"),
                Expr::pi(clean_kernel::BinderInfo::Default, bound.clone(), body),
            )
        };
        let close_proof = |body| {
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                constant("Nat"),
                Expr::lam(clean_kernel::BinderInfo::Default, bound.clone(), body),
            )
        };
        Ok(PendingProof::candidate(
            close_ty(result.proposition()),
            close_proof(result.term().clone()),
        ))
    }
}

#[cfg(all(test, feature = "source-value-operational"))]
mod word64_tests {
    use super::*;
    use clean_kernel::{BinderInfo, KernelTypeError};
    use std::sync::OnceLock;
    fn env() -> &'static Environment {
        static E: OnceLock<Environment> = OnceLock::new();
        E.get_or_init(|| {
            clean_verify::eval_ir::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack()
                .unwrap()
                .env()
                .clone()
        })
    }
    fn limits() -> Limits {
        Limits {
            max_operations: 100,
            max_locals: 1,
            max_list_items: 1,
            max_lookup_candidates: 1,
            lookup_heartbeats: 1,
            lookup_cache_entries: 1,
        }
    }
    fn replay(goal: &Expr, proof: &Expr) {
        let mut checker = TypeChecker::new(env());
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        checker.check_type(proof, goal)
            .expect("full64 arithmetic candidate must pass actual strict kernel typing before closed operational replay");
        crate::source_value_operational::strict_replay(env(), goal, proof).unwrap();
    }

    #[test]
    fn full64_wrap_matches_prelude_mod_for_neutral_input() {
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let input = Expr::bvar(0);
        let e = a.wrapped_word64_mod(input.clone()).unwrap();
        let expected = eq(
            &constant("Nat"),
            app("ir_wrap", [nat(64), input.clone()]),
            app("Nat.mod", [input, app("ir_nat_pow2", [nat(64)])]),
        );
        replay(
            &Expr::pi(BinderInfo::Default, constant("Nat"), expected),
            &Expr::lam(BinderInfo::Default, constant("Nat"), e.term().clone()),
        );
    }
    #[test]
    fn canonical_u64_argument_codec_is_closed_and_keeps_its_bound() {
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let codec = a.byte_word64_codec().unwrap();
        replay(codec.proposition(), codec.term());
        let mut checker = TypeChecker::new(env());
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        assert!(matches!(
            checker.check_type(codec.term(), &constant("False")),
            Err(KernelTypeError::TypeMismatch { .. })
        ));
        let n = Expr::bvar(0);
        let unbounded = Expr::pi(
            BinderInfo::Default,
            constant("Nat"),
            eq(&constant("Nat"), app("ir_wrap", [nat(64), n.clone()]), n),
        );
        assert!(matches!(
            checker.check_type(codec.term(), &unbounded),
            Err(KernelTypeError::TypeMismatch { .. })
        ));
    }
}
