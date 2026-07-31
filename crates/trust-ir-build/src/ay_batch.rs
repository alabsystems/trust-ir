// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! AY Batch JIT integration builder.

use crate::builder::{FunctionBuilder, ModuleBuilder};
use trust_ir::Module;
use trust_ir::inst::{BinOp, ICmpOp};
use trust_ir::proof::ProofAnnotation;
use trust_ir::ty::Ty;
use trust_ir::value::ProofTag;

pub struct AYBatchBuilder {
    pub mb: ModuleBuilder,
}

impl AYBatchBuilder {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            mb: ModuleBuilder::new(name),
        }
    }

    /// Set up the `ay_chc_batch_eval` transition function with the required
    /// signature and the AY proof tags.
    ///
    /// # Soundness: the helper is NOT `Pure` (audit #25)
    ///
    /// `ay_chc_batch_eval` writes its results through the `output` and `status`
    /// pointer parameters, so it has observable side effects on caller memory.
    /// TrustIr defines [`ProofAnnotation::Pure`] as "no side effects" — the same
    /// claim [`trust_ir::Function::is_safe_for_gpu`] gates GPU offload on
    /// (`Pure + NoPanic + Deterministic`). Stamping a memory-writing helper
    /// `Pure` would be an unsound proof claim that falsely makes the function
    /// pass that gate. The `Pure` annotation is therefore deliberately omitted.
    ///
    /// What is left is sound for an output-buffer helper: `Deterministic`,
    /// `Terminates`, `NoPanic`, `NoUndef`, plus an `AppendOnlyBuffer`
    /// memory-role hint on the output buffer (a codegen hint, not a purity
    /// guarantee). Whether the helper should eventually carry a *scoped*
    /// "pure modulo its declared output buffer" claim is an ay-side protocol
    /// decision (it needs a new annotation that expresses that bounded effect);
    /// until that lands, nothing may rely on a blanket purity guarantee here.
    /// See `designs/2026-05-03-x86-chc-batch-jit-contract-plan.md`.
    pub fn transition_function(&mut self) -> FunctionBuilder<'_> {
        let ft = self.mb.add_func_type(
            vec![
                Ty::Ptr, // model_values
                Ty::U64, // model_len
                Ty::Ptr, // batch_meta
                Ty::U64, // batch_meta_len
                Ty::Ptr, // output
                Ty::U64, // output_len
                Ty::Ptr, // status
            ],
            vec![Ty::U32],
        );

        let mut fb = self.mb.function("ay_chc_batch_eval", ft);

        // NOTE: `Pure` intentionally omitted — see the doc comment above.
        fb.add_proof(ProofAnnotation::Deterministic);
        fb.add_proof(ProofAnnotation::Terminates);
        fb.add_proof(ProofAnnotation::NoPanic);
        fb.add_proof(ProofAnnotation::NoUndef);
        fb.add_proof(ProofAnnotation::AppendOnlyBuffer);

        // Add required proof obligations for ay batches
        fb.add_proof(ProofAnnotation::Custom(ProofTag::new(1001))); // ay.chc.batch.v1
        fb.add_proof(ProofAnnotation::Custom(ProofTag::new(1002))); // ay.chc.scalar_oracle
        fb.add_proof(ProofAnnotation::Custom(ProofTag::new(1003))); // ay.chc.layout_hash
        fb.add_proof(ProofAnnotation::Custom(ProofTag::new(1004))); // ay.chc.generation_domain
        fb.add_proof(ProofAnnotation::Custom(ProofTag::new(1005))); // ay.chc.batch_shape_version

        fb
    }

    /// Generate a module with a `<4 x i32>` transition evaluation.
    ///
    /// See [`AYBatchBuilder::emit_chc_transition_body`] for the body shape
    /// and its honest scope.
    pub fn emit_v4_i32_chc_transition(&mut self) {
        self.emit_chc_transition_body(Ty::Vector(Box::new(Ty::I32), 4));
    }

    /// Generate a module with a `<2 x i64>` transition evaluation.
    ///
    /// See [`AYBatchBuilder::emit_chc_transition_body`] for the body shape
    /// and its honest scope.
    pub fn emit_v2_i64_chc_transition(&mut self) {
        self.emit_chc_transition_body(Ty::Vector(Box::new(Ty::I64), 2));
    }

    /// Emit the real straight-line transition body (replacing the historical
    /// "dummy return" stub): a single-step CHC transition evaluation over
    /// batch element 0.
    ///
    /// ```text
    /// assume(model_values != null); … ; assume(status != null)   // caller contract
    /// state      = load <vec> model_values      [NotNull]
    /// delta      = load <vec> batch_meta        [NotNull]
    /// next_state = state + delta                                  // the transition step
    /// store <vec> output, next_state            [NotNull]
    /// store u32   status, 0                     [NotNull]
    /// return 0
    /// ```
    ///
    /// The non-null caller contract (batch-JIT plan §Proof Annotations) is
    /// lowered as explicit `Assume`s so the `NotNull` annotations on the
    /// accesses are *dischargeable* by the whole-function VC generator
    /// (`trust-ir-ay::verify_function`) instead of remaining bare claims.
    ///
    /// Honest scope: this evaluates ONE batch element (a straight-line body
    /// the VC generator can verify end to end). The `model_len`-bounded batch
    /// loop — and the `BoundedLoop(n)` annotation that must accompany it — is
    /// future work tracked in docs/roadmap/integration-ay-vc.md.
    fn emit_chc_transition_body(&mut self, vec_ty: Ty) {
        let mut fb = self.transition_function();
        let entry = fb.create_block();
        let model_values = fb.add_block_param(entry, Ty::Ptr);
        let _model_len = fb.add_block_param(entry, Ty::U64);
        let batch_meta = fb.add_block_param(entry, Ty::Ptr);
        let _batch_meta_len = fb.add_block_param(entry, Ty::U64);
        let output = fb.add_block_param(entry, Ty::Ptr);
        let _output_len = fb.add_block_param(entry, Ty::U64);
        let status = fb.add_block_param(entry, Ty::Ptr);

        fb.switch_to_block(entry);

        // Caller contract: every buffer pointer is non-null.
        for ptr in [model_values, batch_meta, output, status] {
            let null = fb.null_ptr();
            let non_null = fb.icmp(ICmpOp::Ne, Ty::Ptr, ptr, null);
            fb.assume(non_null);
        }

        // Single-step transition evaluation over batch element 0.
        let state = fb.load_proven(vec_ty.clone(), model_values, vec![ProofAnnotation::NotNull]);
        let delta = fb.load_proven(vec_ty.clone(), batch_meta, vec![ProofAnnotation::NotNull]);
        let next_state = fb.binop(BinOp::Add, vec_ty.clone(), state, delta);
        fb.store_proven(vec_ty, output, next_state, vec![ProofAnnotation::NotNull]);

        // Status slot: 0 = OK, doubling as the helper's return status.
        let ok = fb.iconst(Ty::U32, 0);
        fb.store_proven(Ty::U32, status, ok, vec![ProofAnnotation::NotNull]);
        fb.ret(vec![ok]);
        fb.build();
    }

    pub fn build(self) -> Module {
        self.mb.build()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::validate::validate_module;

    #[test]
    fn v4_i32_transition_body_is_real_and_valid() {
        let mut builder = AYBatchBuilder::new("chc_batch_v4i32");
        builder.emit_v4_i32_chc_transition();
        let module = builder.build();

        let errors = validate_module(&module);
        assert!(errors.is_empty(), "validation errors: {errors:?}");

        // The body is a genuine transition evaluation, not a dummy return:
        // it loads state and delta, adds them, and stores result + status.
        let body = &module.functions[0].blocks[0].body;
        let count =
            |pred: fn(&trust_ir::Inst) -> bool| body.iter().filter(|n| pred(&n.inst)).count();
        assert_eq!(count(|i| matches!(i, trust_ir::Inst::Load { .. })), 2);
        assert_eq!(count(|i| matches!(i, trust_ir::Inst::Store { .. })), 2);
        assert_eq!(
            count(|i| matches!(
                i,
                trust_ir::Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::Vector(..),
                    ..
                }
            )),
            1
        );
        assert_eq!(count(|i| matches!(i, trust_ir::Inst::Assume { .. })), 4);
    }

    #[test]
    fn v2_i64_transition_body_is_real_and_valid() {
        let mut builder = AYBatchBuilder::new("chc_batch_v2i64");
        builder.emit_v2_i64_chc_transition();
        let module = builder.build();

        let errors = validate_module(&module);
        assert!(errors.is_empty(), "validation errors: {errors:?}");

        let has_v2i64_add = module.functions[0].blocks[0].body.iter().any(|n| {
            matches!(
                &n.inst,
                trust_ir::Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::Vector(elem, 2),
                    ..
                } if **elem == Ty::I64
            )
        });
        assert!(has_v2i64_add, "expected a <2 x i64> add transition step");
    }
}
