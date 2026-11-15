// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Connected actual ICmp/Core/world consumers. No source-language theorem,
//! branch-truth premise, alternate evaluator or native admission is implied.
//! Uses the existing audited comparison vocabulary and replay policy.

use super::*;
use clean_kernel::{BinderInfo, ExprKind};
use trust_ir::{Inst, Module, Ty, ValueId};
use trust_ir_build::{core_execution::NatTerm, translation::SourceTranslationModel};

#[path = "fetched_support.rs"]
mod fetched_support;
use fetched_support::*;

// Independently spell the actual fixture's root frame from its pinned input
// and destination IDs, never a candidate's claimed current/lookup endpoint.
fn authored_machine(words: [Expr; 2], compared: Option<Expr>, legacy_cursor: u64) -> Expr {
    let mut frame = app(
        "IRFrame.mk",
        [
            nat(0),
            nat(0),
            nat(0),
            app(
                "ir_bind_params",
                [
                    list("Nat", &[nat(0), nat(1)]),
                    list(
                        "IRScalar",
                        &[scalar(words[0].clone()), scalar(words[1].clone())],
                    ),
                    list("IRBinding", &[]),
                ],
            ),
            list("Nat", &[]),
        ],
    );
    if let Some(value) = compared {
        frame = app(
            "ir_frame_advance",
            [app(
                "ir_frame_set_many",
                [frame, list("Nat", &[nat(2)]), list("IRScalar", &[value])],
            )],
        );
    }
    app(
        "IRMachine.mk",
        [
            list("IRFrame", &[frame]),
            list("IRMemSlot", &[]),
            nat(legacy_cursor),
        ],
    )
}
fn running(machine: Expr) -> Expr {
    app(
        "IRByteConfigV1.running",
        [c("Nat"), machine, world(173, 37, &[nat(8)], 9)],
    )
}
fn lookup_goal(op: ICmpOp, words: [Expr; 2]) -> Expr {
    let value = boolean(observer(op, words[0].clone(), words[1].clone()));
    eq(
        c("IRScalar"),
        app(
            "ir_getd",
            [authored_machine(words, Some(value.clone()), 0), nat(2)],
        ),
        value,
    )
}

fn input_telescope_only(
    scope: &LocalScope,
    parameters: &[ScopedLocal; 4],
    term: &Expr,
    claim: &Expr,
) {
    let term = parameters
        .iter()
        .rev()
        .fold(term.clone(), |body, local| local.lam(body));
    let claim = parameters
        .iter()
        .rev()
        .fold(claim.clone(), |body, local| local.pi(body));
    let term = scope
        .close(&term)
        .expect("all internal helper locals are bound");
    let claim = scope
        .close(&claim)
        .expect("only the input telescope is open");
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    let (mut proof, mut proposition) = (&term, &claim);
    // At the third binder a is #1; at the fourth b is #1 (after a's
    // bound binder). These domains are independently authored, not inferred
    // from an assembler-local count or a supplied proof's proposition.
    for expected in [
        c("Nat"),
        c("Nat"),
        bound(Expr::bvar(1)),
        bound(Expr::bvar(1)),
    ] {
        let ExprKind::Lam(binder, domain, body) = proof.kind() else {
            panic!("exactly four input binders")
        };
        assert_eq!(binder.info, BinderInfo::Default);
        assert_eq!(domain.as_ref(), &expected);
        proof = body.as_ref();
        let ExprKind::Pi(binder, domain, body) = proposition.kind() else {
            panic!("exactly four input premises")
        };
        assert_eq!(binder.info, BinderInfo::Default);
        assert_eq!(domain.as_ref(), &expected);
        proposition = body.as_ref();
    }
    assert!(
        !matches!(proof.kind(), ExprKind::Lam(..)),
        "no extra assumption is abstracted into the proof"
    );
    let ExprKind::Const(name, _) = proposition.get_app_fn().kind() else {
        panic!("the input telescope concludes in the actual equality")
    };
    assert_eq!(*name, Name::from_string("Eq"));
}

fn concrete(module: &Module, claim: Claim) -> Vec<u8> {
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let (model, execution, lookup, _) = execute(
        module,
        claim.carrier,
        claim.op,
        [nat(claim.a), nat(claim.b)],
        [bounded(claim.a), bounded(claim.b)],
        &mut assembler,
    );
    let goal = WholeModel::reconstruct(&claim, module).unwrap();
    let end = assembler
        .conversion(
            model.config_type(),
            execution.right().clone(),
            terminal(boolean(flag(claim.answer)), world(173, 37, &[], 9)),
        )
        .unwrap();
    let complete = assembler.compose(execution, end).unwrap();
    replay(
        &scope,
        &[],
        lookup.term(),
        &lookup_goal(claim.op, [nat(claim.a), nat(claim.b)]),
        None,
    );
    replay(
        &scope,
        &[],
        complete.term(),
        &goal,
        Some(claim.carrier.law(claim.op)),
    );
    let closed = scope.close(complete.term()).unwrap();
    let bytes = trust_ir::proof::encode_clean_expr_dag_v2(&closed).unwrap();
    let checked = whole_checker()
        .recheck_dag_v2(&claim, module, &bytes)
        .unwrap();
    assert_eq!(checked.proof_term(), bytes);
    bytes
}

#[test]
fn symbolic_fetched_unsigned_comparison_derives_full_world_from_input_bounds_alone() {
    for carrier in [Carrier::Unsigned, Carrier::Signed] {
        for op in OPS {
            let module = fixture(carrier, op);
            let retained = module.clone();
            let mut scope = LocalScope::new();
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let a = assembler.local(c("Nat")).unwrap();
            let b = assembler.local(c("Nat")).unwrap();
            let a_bound = assembler.local(bound(a.term().clone())).unwrap();
            let b_bound = assembler.local(bound(b.term().clone())).unwrap();
            assert_eq!(
                assembler.local_scope().allocated(),
                4,
                "only two words and their input bounds are supplied"
            );
            let words = [a.term().clone(), b.term().clone()];
            let (model, execution, lookup, single) = execute(
                &module,
                carrier,
                op,
                words.clone(),
                [
                    PendingProof::candidate(bound(words[0].clone()), a_bound.term().clone()),
                    PendingProof::candidate(bound(words[1].clone()), b_bound.term().clone()),
                ],
                &mut assembler,
            );
            // Execution also builds closed polymorphic run-one/return helpers
            // and congruence lambdas. Their scoped binders are NOT incoming
            // hypotheses; audit the final closed telescope instead of counting
            // every temporary LocalScope allocation as an assumption.
            let expected = boolean(observer(op, words[0].clone(), words[1].clone()));
            let before_machine = authored_machine(words.clone(), None, 0);
            let after_machine = authored_machine(words.clone(), Some(expected.clone()), 0);
            let single_goal = eq(
                model.config_type(),
                model.run(&NatTerm::literal(1), running(before_machine)),
                running(after_machine),
            );
            let lookup_goal = lookup_goal(op, words.clone());
            let goal = eq(
                model.config_type(),
                model.run(&NatTerm::literal(2), initial(&model, words)),
                terminal(expected.clone(), world(173, 37, &[], 9)),
            );
            let end = assembler
                .conversion(
                    model.config_type(),
                    execution.right().clone(),
                    terminal(expected.clone(), world(173, 37, &[], 9)),
                )
                .unwrap();
            let execution = assembler.compose(execution, end).unwrap();
            let parameters = [a, b, a_bound, b_bound];
            input_telescope_only(&scope, &parameters, execution.term(), &goal);
            input_telescope_only(&scope, &parameters, single.term(), &single_goal);
            replay(
                &scope,
                &parameters,
                execution.term(),
                &goal,
                Some(carrier.law(op)),
            );
            replay(
                &scope,
                &parameters,
                single.term(),
                &single_goal,
                Some(carrier.law(op)),
            );
            replay(&scope, &parameters, lookup.term(), &lookup_goal, None);
            assert_eq!(module, retained);
        }
    }
}

#[test]
fn actual_full64_sign_and_equality_boundaries_replay_entry_icmp_and_root_retirement() {
    // Unsigned encodings cross the sign bit on BOTH nominal I64 and U64;
    // independently computed answers, never desired-answer premises.
    for (a, b) in [
        (0, u64::MAX),
        (u64::MAX, 0),
        (i64::MIN as u64, i64::MAX as u64),
        (u64::MAX, u64::MAX),
    ] {
        for carrier in [Carrier::Unsigned, Carrier::Signed] {
            for op in OPS {
                let claim = Claim {
                    carrier,
                    op,
                    a,
                    b,
                    answer: literal(op, a, b),
                };
                let module = fixture(carrier, op);
                let retained = module.clone();
                concrete(&module, claim);
                assert_eq!(
                    module, retained,
                    "proof construction never repairs the target"
                );
            }
        }
    }
}

#[test]
fn whole_replay_refuses_genuinely_false_source_operands_output_opcode_and_actual_operand_ids() {
    for carrier in [Carrier::Unsigned, Carrier::Signed] {
        let claim = Claim {
            carrier,
            op: ICmpOp::Ult,
            a: 1,
            b: 2,
            answer: true,
        };
        let module = fixture(carrier, claim.op);
        let bytes = concrete(&module, claim);
        for changed in [
            Claim { a: 3, ..claim },
            Claim { b: 0, ..claim },
            Claim {
                answer: false,
                ..claim
            },
        ] {
            let actual = literal(claim.op, changed.a, changed.b);
            if changed.a != claim.a || changed.b != claim.b {
                assert!(!actual);
            }
            let actual_claim = Claim {
                answer: actual,
                ..changed
            };
            concrete(&module, actual_claim);
            rejects(&changed, &module, &bytes);
        }
        for opcode in [false, true] {
            let mut changed = module.clone();
            let Inst::ICmp { op, lhs, rhs, .. } = &mut changed.functions[0].blocks[0].body[0].inst
            else {
                panic!("actual original ICmp")
            };
            if opcode {
                *op = ICmpOp::Uge;
            } else {
                std::mem::swap(lhs, rhs);
            }
            assert!(trust_ir_build::validate_module(&changed).is_empty());
            assert!(!if opcode {
                literal(ICmpOp::Uge, 1, 2)
            } else {
                literal(ICmpOp::Ult, 2, 1)
            });
            // Small independent actual target normal form, not a comparison
            // producer reused to endorse its own wrong opcode/operand route.
            let model = model(&changed);
            let mut scope = LocalScope::new();
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let normal = terminal(boolean(flag(false)), world(173, 37, &[], 9));
            let run = model.run(&NatTerm::literal(2), initial(&model, [nat(1), nat(2)]));
            let independent = assembler
                .conversion(model.config_type(), run.clone(), normal.clone())
                .unwrap();
            replay(
                &scope,
                &[],
                independent.term(),
                &eq(model.config_type(), run, normal),
                None,
            );
            rejects(&claim, &changed, &bytes);
        }
    }
}

#[test]
fn actual_narrow_width_mutation_cannot_reuse_full64_input_bounds_or_success() {
    for carrier in [Carrier::Unsigned, Carrier::Signed] {
        let claim = Claim {
            carrier,
            op: ICmpOp::Ult,
            a: 255,
            b: 256,
            answer: true,
        };
        let module = fixture(carrier, claim.op);
        let bytes = concrete(&module, claim);
        let mut changed = module;
        let narrow = match carrier {
            Carrier::Unsigned => Ty::U8,
            Carrier::Signed => Ty::I8,
        };
        changed.func_types[0].params = vec![narrow.clone(), narrow.clone()];
        for (_, ty) in &mut changed.functions[0].blocks[0].params {
            *ty = narrow.clone();
        }
        let Inst::ICmp { ty, .. } = &mut changed.functions[0].blocks[0].body[0].inst else {
            panic!("actual compare width")
        };
        *ty = narrow;
        assert!(trust_ir_build::validate_module(&changed).is_empty());
        let model = model(&changed);
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let run = model.run(&NatTerm::literal(2), initial(&model, [nat(255), nat(256)]));
        let normal = app(
            "IRByteConfigV1.halted",
            [
                c("Nat"),
                app("IROutcome.type_error", [c("IRFault.bad_field")]),
                world(173, 37, &[nat(8)], 9),
            ],
        );
        let independent = assembler
            .conversion(model.config_type(), run.clone(), normal.clone())
            .unwrap();
        replay(
            &scope,
            &[],
            independent.term(),
            &eq(model.config_type(), run, normal),
            None,
        );
        rejects(&claim, &changed, &bytes);
    }
}

#[test]
fn whole_claim_keeps_real_bytes_host_and_root_owner_retirement_epoch() {
    let claim = Claim {
        carrier: Carrier::Unsigned,
        op: ICmpOp::Ult,
        a: 1,
        b: 2,
        answer: true,
    };
    let module = fixture(claim.carrier, claim.op);
    let bytes = concrete(&module, claim);
    let proof = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
    let model = model(&module);
    let scope = LocalScope::new();
    for final_world in [
        world(174, 37, &[], 9),
        world(173, 38, &[], 9),
        world(173, 37, &[nat(8)], 9),
        world(173, 37, &[], 10),
    ] {
        let false_goal = eq(
            model.config_type(),
            model.run(&NatTerm::literal(2), initial(&model, [nat(1), nat(2)])),
            terminal(boolean(flag(true)), final_world),
        );
        refuses(&scope, &[], &proof, &false_goal);
    }
    // A genuine valid operand-id mutation with known true/false divergence:
    // compare lhs1 with itself2 changes strict comparison to false.
    let mut changed = module;
    let Inst::ICmp { lhs, rhs, .. } = &mut changed.functions[0].blocks[0].body[0].inst else {
        panic!("actual operands")
    };
    *rhs = *lhs;
    assert_eq!(*lhs, ValueId::new(0));
    assert!(trust_ir_build::validate_module(&changed).is_empty());
    rejects(&claim, &changed, &bytes);
}
