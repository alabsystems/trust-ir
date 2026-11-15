// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kernel term replay with both source and actual TrustIR endpoints in scope.
//!
//! This supplies the missing *replay boundary*, not a language semantics. A
//! frontend must implement and review its own [`SourceTranslationModel`], which
//! reconstructs the complete proposition from the retained source and actual
//! target. In particular, a certificate cannot supply either denotation.
//!
//! A checked term proves the reconstructed model-specific proposition. It does
//! not establish that the model faithfully encodes a language, close imports or
//! runtime contracts, implement [`crate::validate::ModuleValidationReport`], or
//! admit Core/native execution. No production TLA model is provided here.

use clean_kernel::{Environment, Expr};
use std::{fmt, marker::PhantomData, num::NonZeroU32};
use trust_ir::{
    Module,
    proof::{decode_clean_expr_dag_v2, decode_clean_expr_v1},
};

#[path = "translation_scoped.rs"]
mod scoped;

#[cfg(test)]
#[path = "translation_scoped_tests.rs"]
mod scoped_tests;

/// Exact carrier selected by a replay entry point, not additional proof authority.
///
/// Persisted proof bytes must retain their carrier identity. A DAG proof is not
/// a legacy CleanCic payload: existing evidence schemas and consumers remain
/// unchanged until they explicitly adopt the new format and perform fresh replay.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TranslationProofEncoding {
    LegacyTreeV1,
    LosslessDagV2,
    /// Complete scoped declarations and root in the explicit v1 bundle carrier.
    ScopedComponentsV1,
}

/// Trusted semantic reconstruction, selected by a concrete Rust type.
///
/// Implementations are part of the frontend's semantic TCB, just as an IR
/// semantics interpreter is. The source type must contain all source/configuration
/// assumptions. `reconstruct` must derive its claim from BOTH actual endpoints,
/// checking their closure and relevant structural/typing premises; it must not
/// trust a producer's supplied interpretation, witness status, or target digest.
/// A deliberately incomplete model can only establish its deliberately weaker
/// proposition. Downstream consumers must require their exact reviewed model
/// type, never erase it into generic compilation authority.
/// Model-relevant source/configuration data must remain semantically immutable
/// while a checked result is retained. A shared Rust borrow alone is insufficient
/// if the source uses interior mutability; a model must exclude that mutation or
/// retain the appropriate read guard. Reconstruction must be deterministic from
/// these endpoints and the model's fixed semantic vocabulary.
///
/// The environment is immutable and shared across this checker's invocations.
/// Ground source/target data belongs in reconstructed expressions, not mutable
/// per-certificate declarations. This permits one checked semantic vocabulary
/// and shared theorem DAG per checker rather than rebuilding it per function.
pub trait SourceTranslationModel {
    type Source: ?Sized;

    fn build_environment() -> Result<Environment, String>;

    fn reconstruct(source: &Self::Source, target: &Module) -> Result<Expr, String>;
}

/// Verifier-owned kernel settings, never options supplied by a certificate.
///
/// These configure each rooted-audit/declaration TypeChecker. The scoped
/// component entry also uses `heartbeats` as its aggregate kernel-work limit.
/// These are not aggregate memory or work bounds on semantic reconstruction or
/// every non-kernel graph traversal. Frontends must bound those costs separately
/// before using this boundary for untrusted-source admission.
#[derive(Debug, Clone, Copy)]
pub struct TranslationCheckLimits {
    /// Kernel reduction allowance and scoped aggregate kernel-work limit.
    /// Zero (unlimited in the kernel) is impossible.
    pub heartbeats: NonZeroU32,
    /// Per-cache trimming threshold for the kernel's configurable reduction
    /// caches; not a byte limit or a bound on all retained checker data.
    pub cache_entries: NonZeroU32,
}

impl Default for TranslationCheckLimits {
    fn default() -> Self {
        Self {
            heartbeats: NonZeroU32::new(5_000_000).unwrap(),
            cache_entries: NonZeroU32::new(100_000).unwrap(),
        }
    }
}

/// A failed term replay, with no semantic or executable authority returned.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TranslationRecheckError {
    stage: &'static str,
    reason: String,
}

impl TranslationRecheckError {
    pub fn stage(&self) -> &'static str {
        self.stage
    }

    pub fn reason(&self) -> &str {
        &self.reason
    }

    fn new(stage: &'static str, reason: impl fmt::Display) -> Self {
        let mut reason = reason.to_string();
        // Keep diagnostics bounded; proof terms themselves remain with callers.
        const LIMIT: usize = 1024;
        if reason.len() > LIMIT {
            let mut end = LIMIT;
            while !reason.is_char_boundary(end) {
                end -= 1;
            }
            reason.truncate(end);
            reason.push_str(" (truncated)");
        }
        Self { stage, reason }
    }
}

impl fmt::Display for TranslationRecheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "translation {}: {}", self.stage, self.reason)
    }
}

impl std::error::Error for TranslationRecheckError {}

/// Immutable checked vocabulary plus model identity, reusable across endpoints.
///
/// There is intentionally no mutable environment accessor and no constructor
/// accepting an untrusted proposition. The actual claim is reconstructed anew
/// for each endpoint pair; only the immutable language vocabulary is reused.
pub struct TranslationRechecker<M: SourceTranslationModel> {
    environment: Environment,
    scoped_kernel_limit: u64,
    model: PhantomData<fn() -> M>,
}

impl<M: SourceTranslationModel> fmt::Debug for TranslationRechecker<M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TranslationRechecker")
            .field("model", &std::any::type_name::<M>())
            .finish_non_exhaustive()
    }
}

impl<M: SourceTranslationModel> TranslationRechecker<M> {
    /// Build the model vocabulary and bind the rooted kernel audit's limits.
    pub fn new(limits: TranslationCheckLimits) -> Result<Self, TranslationRecheckError> {
        let mut environment = M::build_environment()
            .map_err(|reason| TranslationRecheckError::new("vocabulary", reason))?;
        // Override even a vocabulary builder's accidental unlimited setting.
        // The rooted audit creates its own TypeChecker from these same options.
        environment.set_option("maxHeartbeats".into(), Some(limits.heartbeats.to_string()));
        environment.set_option(
            "tcMaxCacheEntries".into(),
            Some(limits.cache_entries.to_string()),
        );
        Ok(Self {
            environment,
            scoped_kernel_limit: u64::from(limits.heartbeats.get()),
            model: PhantomData,
        })
    }

    /// Borrow the exact model-built vocabulary used by [`Self::recheck`].
    ///
    /// This permits additional endpoint terms to be constructed and checked in
    /// the same environment without cloning it or exposing mutation. Separate
    /// checks remain responsible for their own resource controls and semantic
    /// claims: vocabulary access supplies no proof and does not enlarge the
    /// proposition established by a translation replay.
    pub fn environment(&self) -> &Environment {
        &self.environment
    }

    /// Recheck only a serialized proof TERM, never a certificate comparand.
    ///
    /// Exact decoding enforces the shared byte/node/depth limits and rejects
    /// trailing or noncanonical data before running semantic reconstruction.
    /// Kernel checking requires a Prop and audits the entire term/goal dependency
    /// closure. No extra axiom allow-list is accepted. The rooted kernel audit
    /// supplies the replay authority; no independent micro verdict is claimed.
    pub fn recheck<'a>(
        &'a self,
        source: &'a M::Source,
        target: &'a Module,
        proof_term: &'a [u8],
    ) -> Result<KernelCheckedTranslationTerm<'a, M>, TranslationRecheckError> {
        let term = decode_clean_expr_v1(proof_term)
            .map_err(|reason| TranslationRecheckError::new("decode", reason))?;
        self.recheck_decoded(
            source,
            target,
            proof_term,
            TranslationProofEncoding::LegacyTreeV1,
            term,
        )
    }

    /// Explicitly replay the lossless, sharing-preserving Clean Expr DAG v2.
    ///
    /// No format sniffing or fallback is performed. This has exactly the same
    /// endpoint reconstruction and rooted kernel audit as
    /// [`Self::recheck`]. The new carrier changes storage, not the proposition or
    /// the authority of a checked result. Byte, unique-node and graph-depth
    /// limits are enforced before model reconstruction.
    pub fn recheck_dag_v2<'a>(
        &'a self,
        source: &'a M::Source,
        target: &'a Module,
        proof_term: &'a [u8],
    ) -> Result<KernelCheckedTranslationTerm<'a, M>, TranslationRecheckError> {
        let term = decode_clean_expr_dag_v2(proof_term)
            .map_err(|reason| TranslationRecheckError::new("decode", reason))?;
        self.recheck_decoded(
            source,
            target,
            proof_term,
            TranslationProofEncoding::LosslessDagV2,
            term,
        )
    }

    fn recheck_decoded<'a>(
        &'a self,
        source: &'a M::Source,
        target: &'a Module,
        proof_term: &'a [u8],
        encoding: TranslationProofEncoding,
        term: Expr,
    ) -> Result<KernelCheckedTranslationTerm<'a, M>, TranslationRecheckError> {
        let claim = M::reconstruct(source, target)
            .map_err(|reason| TranslationRecheckError::new("reconstruct", reason))?;

        // audit_certification checks Prop + term type and traverses the complete
        // rooted declaration closure, including partial/unsafe/sorry markers,
        // unknown declaration provenance and non-foundational axioms.
        let audit = self.environment.audit_certification(&claim, &term);
        if let Some(issue) = audit.issues.first() {
            return Err(TranslationRecheckError::new(
                "kernel audit",
                format_args!("{issue:?}"),
            ));
        }

        // Release decoded terms, reconstructed denotations and transient audit
        // indexes here. Retain no second executable graph or cloned source.
        Ok(KernelCheckedTranslationTerm {
            checker: self,
            source,
            target,
            proof_term,
            encoding,
        })
    }
}

/// Model-specific proof replay tied to exact immutable endpoints and bytes.
///
/// This is NOT a Core/publication token and cannot discharge a target-only
/// obligation through `ModuleProofAuthority`. A language-specific consumer must
/// still establish its model's fidelity and all separate compilation contracts.
/// Retaining the concrete model type prevents a proof under a different model
/// from being mistaken for the language's reviewed relation.
///
/// ```compile_fail
/// use trust_ir_build::translation::{KernelCheckedTranslationTerm, SourceTranslationModel};
/// fn erase_model<'a, A: SourceTranslationModel, B: SourceTranslationModel>(
///     checked: KernelCheckedTranslationTerm<'a, A>,
/// ) -> KernelCheckedTranslationTerm<'a, B> {
///     checked
/// }
/// ```
pub struct KernelCheckedTranslationTerm<'a, M: SourceTranslationModel> {
    checker: &'a TranslationRechecker<M>,
    source: &'a M::Source,
    target: &'a Module,
    proof_term: &'a [u8],
    encoding: TranslationProofEncoding,
}

impl<M: SourceTranslationModel> fmt::Debug for KernelCheckedTranslationTerm<'_, M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("KernelCheckedTranslationTerm")
            .field("model", &std::any::type_name::<M>())
            .field("proof_bytes", &self.proof_term.len())
            .field("proof_encoding", &self.encoding)
            .finish_non_exhaustive()
    }
}

impl<M: SourceTranslationModel> KernelCheckedTranslationTerm<'_, M> {
    pub fn source(&self) -> &M::Source {
        self.source
    }

    pub fn target(&self) -> &Module {
        self.target
    }

    /// Original proof bytes in the explicitly reported [`Self::proof_encoding`].
    /// A scoped bundle is not a standalone closed expression.
    pub fn proof_term(&self) -> &[u8] {
        self.proof_term
    }

    /// The exact format used to decode [`Self::proof_term`].
    pub fn proof_encoding(&self) -> TranslationProofEncoding {
        self.encoding
    }

    pub fn checker(&self) -> &TranslationRechecker<M> {
        self.checker
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ModuleBuilder, validate_module};
    use clean_kernel::{Declaration, Level, Name};
    use trust_ir::{Constant, Inst, Ty, proof::encode_clean_expr_v1};

    fn boolean(value: bool) -> Expr {
        Expr::const_str(if value { "Bool.true" } else { "Bool.false" })
    }

    pub(super) fn bool_eq(source: bool, target: bool) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [Expr::const_str("Bool"), boolean(source), boolean(target)],
        )
    }

    pub(super) fn proof(value: bool) -> Vec<u8> {
        encode_clean_expr_v1(&Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [Expr::const_str("Bool"), boolean(value)],
        ))
        .unwrap()
    }

    pub(super) fn target(value: bool) -> Module {
        let mut builder = ModuleBuilder::new("endpoint_fixture");
        let signature = builder.add_func_type(vec![], vec![Ty::Bool]);
        let mut function = builder.function("entry", signature);
        let entry = function.create_block();
        function.switch_to_block(entry);
        let value = function.bool_const(value);
        function.ret(vec![value]);
        function.build();
        builder.build().expect("ModuleBuilder::build: test fixture")
    }

    // Deliberately a tiny TEST model, not a TLA encoder or a new compiler
    // fragment. These tests exercise endpoint binding and replay policy; the
    // generic production API imposes no scalar/CFG/value semantics restriction.
    pub(super) struct BooleanReturnModel;

    impl SourceTranslationModel for BooleanReturnModel {
        type Source = bool;

        fn build_environment() -> Result<Environment, String> {
            Ok(Environment::with_prelude())
        }

        fn reconstruct(source: &bool, target: &Module) -> Result<Expr, String> {
            let errors = validate_module(target);
            if !errors.is_empty() {
                return Err(format!("invalid target: {errors:?}"));
            }
            let [function] = target.functions.as_slice() else {
                return Err("fixture requires exactly one function".into());
            };
            let [block] = function.blocks.as_slice() else {
                return Err("fixture requires exactly one block".into());
            };
            let [constant, ret] = block.body.as_slice() else {
                return Err("fixture requires a constant and a return".into());
            };
            let (
                Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(value),
                },
                Inst::Return { values },
            ) = (&constant.inst, &ret.inst)
            else {
                return Err("fixture opcode mismatch".into());
            };
            if values.as_slice() != constant.results.as_slice() || values.len() != 1 {
                return Err("fixture return identity mismatch".into());
            }
            Ok(bool_eq(*source, *value))
        }
    }

    #[test]
    fn actual_endpoints_are_reconstructed_and_borrowed_without_cloning() {
        let checker = TranslationRechecker::<BooleanReturnModel>::new(Default::default()).unwrap();
        for value in [false, true] {
            let module = target(value);
            let bytes = proof(value);
            let checked = checker.recheck(&value, &module, &bytes).unwrap();
            assert!(std::ptr::eq(checked.source(), &value));
            assert!(std::ptr::eq(checked.target(), &module));
            assert!(std::ptr::eq(checked.checker(), &checker));
            assert_eq!(checked.proof_term().as_ptr(), bytes.as_ptr());
            assert_eq!(
                checked.proof_encoding(),
                TranslationProofEncoding::LegacyTreeV1
            );
        }
    }

    #[test]
    fn dag_replay_keeps_exact_owners_format_and_endpoint_refusals() {
        use trust_ir::proof::encode_clean_expr_dag_v2;
        let checker = TranslationRechecker::<BooleanReturnModel>::new(Default::default()).unwrap();
        for value in [false, true] {
            let module = target(value);
            let legacy = proof(value);
            let bytes = encode_clean_expr_dag_v2(&decode_clean_expr_v1(&legacy).unwrap()).unwrap();
            let checked = checker.recheck_dag_v2(&value, &module, &bytes).unwrap();
            assert!(std::ptr::eq(checked.source(), &value));
            assert!(std::ptr::eq(checked.target(), &module));
            assert!(std::ptr::eq(checked.checker(), &checker));
            assert_eq!(checked.proof_term().as_ptr(), bytes.as_ptr());
            assert_eq!(
                checked.proof_encoding(),
                TranslationProofEncoding::LosslessDagV2
            );
            assert!(checker.recheck_dag_v2(&!value, &module, &bytes).is_err());
            assert!(
                checker
                    .recheck_dag_v2(&value, &target(!value), &bytes)
                    .is_err()
            );
            let irrelevant = encode_clean_expr_dag_v2(&Expr::const_str("True.intro")).unwrap();
            assert!(
                checker
                    .recheck_dag_v2(&value, &module, &irrelevant)
                    .is_err()
            );
        }
    }

    #[test]
    fn dag_and_legacy_carriers_are_not_implicitly_interchangeable() {
        use trust_ir::proof::encode_clean_expr_dag_v2;
        struct MustNotReconstruct;
        impl SourceTranslationModel for MustNotReconstruct {
            type Source = ();
            fn build_environment() -> Result<Environment, String> {
                Ok(Environment::default())
            }
            fn reconstruct(_: &(), _: &Module) -> Result<Expr, String> {
                panic!("wrong or malformed carrier must reject before reconstruction")
            }
        }
        let checker = TranslationRechecker::<MustNotReconstruct>::new(Default::default()).unwrap();
        let module = target(true);
        let legacy = proof(true);
        let dag = encode_clean_expr_dag_v2(&decode_clean_expr_v1(&legacy).unwrap()).unwrap();
        assert_eq!(
            checker.recheck(&(), &module, &dag).unwrap_err().stage(),
            "decode"
        );
        assert_eq!(
            checker
                .recheck_dag_v2(&(), &module, &legacy)
                .unwrap_err()
                .stage(),
            "decode"
        );
        let mut suffixed = dag.clone();
        suffixed.push(0);
        for malformed in [
            vec![],
            vec![255; 8],
            dag[..dag.len() - 1].to_vec(),
            suffixed,
        ] {
            assert_eq!(
                checker
                    .recheck_dag_v2(&(), &module, &malformed)
                    .unwrap_err()
                    .stage(),
                "decode"
            );
        }
    }

    #[test]
    fn dag_replay_preserves_rooted_axiom_refusal() {
        use trust_ir::proof::encode_clean_expr_dag_v2;
        struct AxiomaticModel;
        impl SourceTranslationModel for AxiomaticModel {
            type Source = ();
            fn build_environment() -> Result<Environment, String> {
                let mut environment = Environment::with_prelude();
                environment
                    .add_decl(Declaration::Axiom {
                        name: Name::from_string("unproved_dag_translation"),
                        level_params: vec![],
                        type_: Expr::const_str("False"),
                    })
                    .map_err(|error| format!("{error:?}"))?;
                Ok(environment)
            }
            fn reconstruct(_: &(), _: &Module) -> Result<Expr, String> {
                Ok(Expr::const_str("False"))
            }
        }
        let checker = TranslationRechecker::<AxiomaticModel>::new(Default::default()).unwrap();
        let bytes = encode_clean_expr_dag_v2(&Expr::const_str("unproved_dag_translation")).unwrap();
        let error = checker
            .recheck_dag_v2(&(), &target(true), &bytes)
            .unwrap_err();
        assert_eq!(error.stage(), "kernel audit");
        assert!(error.reason().contains("NonFoundationalAxiom"), "{error}");
    }

    #[test]
    fn environment_access_borrows_the_same_model_vocabulary_used_for_replay() {
        let limits = TranslationCheckLimits {
            heartbeats: NonZeroU32::new(2_000_000).unwrap(),
            cache_entries: NonZeroU32::new(127).unwrap(),
        };
        let checker = TranslationRechecker::<BooleanReturnModel>::new(limits).unwrap();
        let environment = checker.environment();
        assert!(std::ptr::eq(environment, &checker.environment));
        assert_eq!(
            environment.get_option("maxHeartbeats"),
            Some(&Some("2000000".into()))
        );
        assert_eq!(
            environment.get_option("tcMaxCacheEntries"),
            Some(&Some("127".into()))
        );
        let module = target(true);
        let bytes = proof(true);
        let checked = checker.recheck(&true, &module, &bytes).unwrap();
        assert!(std::ptr::eq(checked.checker().environment(), environment));
        assert!(checker.recheck(&false, &module, &bytes).is_err());
    }

    #[test]
    fn wrong_source_wrong_target_and_wrong_proposition_cannot_reuse_a_term() {
        let checker = TranslationRechecker::<BooleanReturnModel>::new(Default::default()).unwrap();
        let true_target = target(true);
        let false_target = target(false);
        let true_proof = proof(true);
        assert!(checker.recheck(&true, &true_target, &true_proof).is_ok());
        assert!(checker.recheck(&false, &true_target, &true_proof).is_err());
        assert!(checker.recheck(&true, &false_target, &true_proof).is_err());
        assert!(checker.recheck(&false, &false_target, &true_proof).is_err());
        let irrelevant = encode_clean_expr_v1(&Expr::const_str("True.intro")).unwrap();
        assert!(checker.recheck(&true, &true_target, &irrelevant).is_err());
    }

    #[test]
    fn malformed_terms_reject_before_model_reconstruction() {
        struct MustNotReconstruct;
        impl SourceTranslationModel for MustNotReconstruct {
            type Source = ();
            fn build_environment() -> Result<Environment, String> {
                Ok(Environment::with_prelude())
            }
            fn reconstruct(_: &(), _: &Module) -> Result<Expr, String> {
                panic!("malformed proof must reject before semantic reconstruction")
            }
        }
        let checker = TranslationRechecker::<MustNotReconstruct>::new(Default::default()).unwrap();
        let module = target(true);
        let mut suffix = proof(true);
        suffix.push(0);
        for bytes in [vec![], vec![255, 255, 255, 255], suffix] {
            assert_eq!(
                checker.recheck(&(), &module, &bytes).unwrap_err().stage(),
                "decode"
            );
        }
    }

    #[test]
    fn target_reconstruction_failure_does_not_return_a_checked_term() {
        let checker = TranslationRechecker::<BooleanReturnModel>::new(Default::default()).unwrap();
        let mut module = target(true);
        module.functions.clear();
        let error = checker.recheck(&true, &module, &proof(true)).unwrap_err();
        assert_eq!(error.stage(), "reconstruct");
    }

    #[test]
    fn model_environment_axioms_cannot_launder_false_claims() {
        struct AxiomaticModel;
        impl SourceTranslationModel for AxiomaticModel {
            type Source = ();
            fn build_environment() -> Result<Environment, String> {
                let mut environment = Environment::with_prelude();
                environment
                    .add_decl(Declaration::Axiom {
                        name: Name::from_string("unproved_translation"),
                        level_params: vec![],
                        type_: Expr::const_str("False"),
                    })
                    .map_err(|error| format!("{error:?}"))?;
                Ok(environment)
            }
            fn reconstruct(_: &(), _: &Module) -> Result<Expr, String> {
                Ok(Expr::const_str("False"))
            }
        }
        let checker = TranslationRechecker::<AxiomaticModel>::new(Default::default()).unwrap();
        let bytes = encode_clean_expr_v1(&Expr::const_str("unproved_translation")).unwrap();
        let error = checker.recheck(&(), &target(true), &bytes).unwrap_err();
        assert_eq!(error.stage(), "kernel audit");
        assert!(error.reason().contains("NonFoundationalAxiom"), "{error}");
    }

    #[test]
    fn successful_type_check_of_data_is_not_a_proposition_proof() {
        struct NonProposition;
        impl SourceTranslationModel for NonProposition {
            type Source = ();
            fn build_environment() -> Result<Environment, String> {
                Ok(Environment::with_prelude())
            }
            fn reconstruct(_: &(), _: &Module) -> Result<Expr, String> {
                Ok(Expr::const_str("Bool"))
            }
        }
        let checker = TranslationRechecker::<NonProposition>::new(Default::default()).unwrap();
        let bytes = encode_clean_expr_v1(&boolean(true)).unwrap();
        let error = checker.recheck(&(), &target(true), &bytes).unwrap_err();
        assert_eq!(error.stage(), "kernel audit");
        assert!(error.reason().contains("GoalNotProposition"), "{error}");
    }

    #[test]
    fn root_audit_honors_requested_limits_without_any_constant_dependencies() {
        struct ClosedIdentity;
        impl SourceTranslationModel for ClosedIdentity {
            type Source = ();
            fn build_environment() -> Result<Environment, String> {
                Ok(Environment::default())
            }
            fn reconstruct(_: &(), _: &Module) -> Result<Expr, String> {
                use clean_kernel::BinderInfo::Default as Binder;
                // forall (P : Prop), P -> P. No stored declarations whose
                // recheck could accidentally make an ignored root cap look live.
                Ok(Expr::pi(
                    Binder,
                    Expr::sort(Level::zero()),
                    Expr::pi(Binder, Expr::bvar(0), Expr::bvar(1)),
                ))
            }
        }
        use clean_kernel::BinderInfo::Default as Binder;
        let term = Expr::lam(
            Binder,
            Expr::sort(Level::zero()),
            Expr::lam(Binder, Expr::bvar(0), Expr::bvar(0)),
        );
        let bytes = encode_clean_expr_v1(&term).unwrap();
        let dag_bytes = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
        let module = target(true);
        let ordinary = TranslationRechecker::<ClosedIdentity>::new(Default::default()).unwrap();
        ordinary.recheck(&(), &module, &bytes).unwrap();
        ordinary.recheck_dag_v2(&(), &module, &dag_bytes).unwrap();
        let limited = TranslationRechecker::<ClosedIdentity>::new(TranslationCheckLimits {
            heartbeats: NonZeroU32::new(1).unwrap(),
            cache_entries: NonZeroU32::new(1).unwrap(),
        })
        .unwrap();
        let error = limited.recheck(&(), &module, &bytes).unwrap_err();
        assert_eq!(error.stage(), "kernel audit");
        let dag_error = limited
            .recheck_dag_v2(&(), &module, &dag_bytes)
            .unwrap_err();
        assert_eq!(dag_error.stage(), "kernel audit");
    }
    /// `forall (P : Prop), P -> P` proved by `fun P h => h`: no constants, no
    /// free variables, exercising a closed kernel term as well as constant-based proofs.
    struct ClosedIdentityModel;
    impl SourceTranslationModel for ClosedIdentityModel {
        type Source = ();
        fn build_environment() -> Result<Environment, String> {
            Ok(Environment::default())
        }
        fn reconstruct(_: &(), _: &Module) -> Result<Expr, String> {
            use clean_kernel::BinderInfo::Default as Binder;
            Ok(Expr::pi(
                Binder,
                Expr::sort(Level::zero()),
                Expr::pi(Binder, Expr::bvar(0), Expr::bvar(1)),
            ))
        }
    }

    fn closed_identity_term() -> Expr {
        use clean_kernel::BinderInfo::Default as Binder;
        Expr::lam(
            Binder,
            Expr::sort(Level::zero()),
            Expr::lam(Binder, Expr::bvar(0), Expr::bvar(0)),
        )
    }

    #[test]
    fn rooted_replay_checks_closed_terms_without_optional_diversity_authority() {
        use clean_kernel::BinderInfo::Default as Binder;
        let term = closed_identity_term();
        let module = target(true);
        let checker = TranslationRechecker::<ClosedIdentityModel>::new(Default::default()).unwrap();
        let bytes = encode_clean_expr_v1(&term).unwrap();
        let dag = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
        checker.recheck(&(), &module, &bytes).unwrap();
        checker.recheck_dag_v2(&(), &module, &dag).unwrap();

        // The body returns the proposition P instead of its proof h. This is
        // a well-formed expression, but cannot inhabit forall P, P -> P.
        let wrong = Expr::lam(
            Binder,
            Expr::sort(Level::zero()),
            Expr::lam(Binder, Expr::bvar(0), Expr::bvar(1)),
        );
        let wrong_bytes = encode_clean_expr_v1(&wrong).unwrap();
        let wrong_dag = trust_ir::proof::encode_clean_expr_dag_v2(&wrong).unwrap();
        assert_eq!(
            checker
                .recheck(&(), &module, &wrong_bytes)
                .unwrap_err()
                .stage(),
            "kernel audit"
        );
        assert_eq!(
            checker
                .recheck_dag_v2(&(), &module, &wrong_dag)
                .unwrap_err()
                .stage(),
            "kernel audit"
        );
    }

    #[test]
    fn strict_replay_checks_both_carriers_and_rejects_a_forged_identity() {
        let module = target(true);
        let checker = TranslationRechecker::<ClosedIdentityModel>::new(Default::default()).unwrap();
        let valid = closed_identity_term();
        // Dropping the inner binder cannot inhabit forall P : Prop, P -> P.
        let forged = Expr::lam(
            clean_kernel::BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::bvar(0),
        );
        for (term, accepted) in [(&valid, true), (&forged, false)] {
            let tree = encode_clean_expr_v1(term).unwrap();
            let dag = trust_ir::proof::encode_clean_expr_dag_v2(term).unwrap();
            for result in [
                checker.recheck(&(), &module, &tree),
                checker.recheck_dag_v2(&(), &module, &dag),
            ] {
                if accepted {
                    result.unwrap();
                } else {
                    assert_eq!(result.unwrap_err().stage(), "kernel audit");
                }
            }
        }
    }
    #[test]
    fn rooted_endpoint_check_accepts_valid_carriers_and_rejects_substitutions() {
        use trust_ir::proof::encode_clean_expr_dag_v2;
        let legacy = proof(true);
        let term = decode_clean_expr_v1(&legacy).unwrap();
        let dag = encode_clean_expr_dag_v2(&term).unwrap();
        let module = target(true);
        let wrong_module = target(false);
        let irrelevant = encode_clean_expr_v1(&Expr::const_str("True.intro")).unwrap();
        let checker = TranslationRechecker::<BooleanReturnModel>::new(Default::default()).unwrap();
        let checked = checker.recheck(&true, &module, &legacy).unwrap();
        assert_eq!(
            checked.proof_encoding(),
            TranslationProofEncoding::LegacyTreeV1
        );
        let checked = checker.recheck_dag_v2(&true, &module, &dag).unwrap();
        assert_eq!(
            checked.proof_encoding(),
            TranslationProofEncoding::LosslessDagV2
        );
        for (source, module, bytes) in [
            (false, &module, &legacy),
            (true, &wrong_module, &legacy),
            (true, &module, &irrelevant),
        ] {
            let error = checker.recheck(&source, module, bytes).unwrap_err();
            assert_eq!(error.stage(), "kernel audit", "{error}");
        }
    }
}
