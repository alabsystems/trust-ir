// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored Usize64 diagnostic wrapper, never relabelled as the U64 model.
//! These closed sequential runs do not establish source/native refinement,
//! concurrency, ownership, or discharge any carried obligation.

use super::*;

struct UsizeModel;
impl SourceTranslationModel for UsizeModel {
    type Source = Invocation;
    fn build_environment() -> Result<Environment, String> {
        SequentialAtomicModel::build_environment()
    }
    fn reconstruct(source: &Invocation, target: &Module) -> Result<Expr, String> {
        let reflected = reflect_core_module_v1(target, &[(FuncId(0), 4096)])
            .map_err(|error| error.to_string())?;
        let function = reflected.function(FuncId(0)).ok_or("missing wrapper")?;
        let signature = target.func_type(function.ty).ok_or("missing signature")?;
        if signature.params != [Ty::Ptr] || signature.returns != [Ty::Usize] {
            return Err("expected distinct target-indexed Usize wrapper signature".into());
        }
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        Ok(eq(
            model.config_type(),
            model.run(&NatTerm::literal(8), initial(&model, source.pointer)),
            terminal(source),
        ))
    }
}

fn checker() -> &'static TranslationRechecker<UsizeModel> {
    static CHECKER: OnceLock<TranslationRechecker<UsizeModel>> = OnceLock::new();
    CHECKER.get_or_init(|| TranslationRechecker::new(Default::default()).unwrap())
}

fn fixture() -> Module {
    // Reuse the eight-node diagnostic CFG, preserving its nominal wrapper
    // structure. Replace the semantic scalar type everywhere it occurs, not
    // just the instruction spelling; this is a NEW authored test module.
    let mut module = super::fixture();
    module.name = "relaxed_usize".into();
    module.func_types[0].returns = vec![Ty::Usize];
    module.structs[0].fields[0].ty = Ty::Usize;
    module.functions[0].name = "relaxed_usize".into();
    for index in [4, 5] {
        match &mut module.functions[0].blocks[0].body[index].inst {
            Inst::Const { ty, .. } | Inst::AtomicRMW { ty, .. } => *ty = Ty::Usize,
            _ => unreachable!(),
        }
    }
    for row in &mut module.proof_obligations {
        row.description =
            "authored Usize diagnostic; memory safety and ownership remain pending".into();
        // This synthetic fixture makes no claim to compiler source identities.
        row.source = None;
        row.formula = None;
    }
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}

fn atomic_evaluation(context: Expr) -> Expr {
    let layout = app(
        "IRByteLayoutV1.mk",
        [
            app("IRTy.usize_", [nat(64)]),
            nat(8),
            nat(8),
            list("IRTy", &[]),
            list("Nat", &[]),
        ],
    );
    app(
        "ir_byte_fetch_add_relaxed_usize64_seq_below_v1",
        [
            context,
            memory(77),
            nat(16),
            nat(41),
            nat(7),
            app("Nat.le_add_right", [nat(17), nat(u64::MAX - 16)]),
            refl(
                app("IROption", [c("IRByteLayoutV1")]),
                app("IROption.some", [c("IRByteLayoutV1"), layout]),
            ),
            refl(c("Bool"), c("Bool.true")),
            app(
                "ir_byte_usize64_rep_write_v1",
                [memory_from(background(77)), nat(16), nat(41)],
            ),
            app("Nat.le_add_right", [nat(49), nat(u64::MAX - 48)]),
        ],
    )
}

fn assemble(module: &Module, pc: bool, old: bool, destination: bool) -> Vec<u8> {
    super::assemble_with_evaluator(module, pc, old, destination, atomic_evaluation)
}

fn rejects(source: &Invocation, module: &Module, proof: &[u8]) {
    let error = checker().recheck_dag_v2(source, module, proof).unwrap_err();
    assert_eq!(error.stage(), "kernel audit", "{error}");
    for resource in [
        "heartbeat",
        "budget",
        "timeout",
        "fuel exhausted",
        "recursion limit",
    ] {
        assert!(
            !error.reason().to_ascii_lowercase().contains(resource),
            "semantic refusal required: {error}"
        );
    }
}

#[test]
fn whole_usize_wrapper_replays_distinct_representation_and_preserves_pending_claims() {
    let module = fixture();
    let before = module.clone();
    let invocation = Invocation::default();
    let proof = assemble(&module, false, false, false);
    let checked = checker()
        .recheck_dag_v2(&invocation, &module, &proof)
        .unwrap();
    assert!(std::ptr::eq(checked.target(), &module));
    assert!(std::ptr::eq(checked.source(), &invocation));
    assert_eq!(
        checked.proof_encoding(),
        TranslationProofEncoding::LosslessDagV2
    );
    assert_eq!(checked.proof_term(), proof);
    assert_eq!(module, before);
    assert!(
        module
            .proof_obligations
            .iter()
            .all(|row| row.status == ProofStatus::Pending)
    );
    assert!(module.proof_certificates.is_empty());
    // This model's type gate cannot silently accept an equal-layout U64 input.
    assert!(
        checker()
            .recheck_dag_v2(&invocation, &super::fixture(), &proof)
            .is_err()
    );
}

#[test]
fn whole_usize_wrapper_refuses_wrong_result_frame_world_and_live_pointer() {
    let module = fixture();
    let proof = assemble(&module, false, false, false);
    for changed in [
        Invocation {
            old: 48,
            ..Invocation::default()
        },
        Invocation {
            new: 41,
            ..Invocation::default()
        },
        Invocation {
            frame_word: 78,
            ..Invocation::default()
        },
        Invocation {
            host: 38,
            ..Invocation::default()
        },
        Invocation {
            next_owner: 8,
            ..Invocation::default()
        },
        Invocation {
            owners: vec![nat(8)],
            ..Invocation::default()
        },
        Invocation {
            pointer: 32,
            ..Invocation::default()
        },
    ] {
        rejects(&changed, &module, &proof);
    }
}

#[test]
fn whole_usize_wrapper_refuses_candidate_and_actual_instruction_mutations() {
    let module = fixture();
    for (pc, old, destination) in [
        (true, false, false),
        (false, true, false),
        (false, false, true),
    ] {
        rejects(
            &Invocation::default(),
            &module,
            &assemble(&module, pc, old, destination),
        );
    }
    let proof = assemble(&module, false, false, false);
    let mut changed = module.clone();
    changed.functions[0].blocks[0].body[4].inst = Inst::Const {
        ty: Ty::Usize,
        value: Constant::Int(8),
    };
    rejects(&Invocation::default(), &changed, &proof);
    let mut changed = module.clone();
    changed.functions[0].blocks[1].body[0].inst = Inst::Return {
        values: vec![ValueId(8)],
    };
    rejects(&Invocation::default(), &changed, &proof);
    let mut changed = module;
    changed.structs[1].fields[0].offset = Some(8);
    assert!(reflect_core_module_v1(&changed, &[(FuncId(0), 4096)]).is_err());
}

#[path = "usize_memory.rs"]
mod memory_tests;
