// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored adapter fixtures, NOT extracted Rust, Arc, abort or concurrency
//! evidence. Real reflection, fetched scalar/CondBr assembly and rooted kernel
//! replay establish one closed invocation and its entire terminal byte world.

use super::*;
use trust_ir::{ICmpOp, ValueId};
use trust_ir_build::core_execution::{
    BranchPremises, Current, FetchedSite, PendingEquality, ScalarTransfer,
};

const MAX: u64 = (1_u64 << 63) - 1;
const ENTRY: BlockId = BlockId::new(0);
const FUNCTION: FuncId = FuncId::new(0);

fn scalar(value: u64) -> Expr {
    app("IRScalar.int_", [nat(value)])
}
fn boolean(value: bool) -> Expr {
    app(
        "IRScalar.bool_",
        [c(if value { "Bool.true" } else { "Bool.false" })],
    )
}
fn refl(ty: Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, value],
    )
}
fn truth(assembler: &mut Assembler<'_>, term: Expr) -> PendingEquality {
    assembler
        .conversion(c("Bool"), term, c("Bool.true"))
        .unwrap()
}

#[derive(Clone, Copy)]
struct Claim {
    input: u64,
    result: bool,
}
struct ComparisonModel;
impl SourceTranslationModel for ComparisonModel {
    type Source = Claim;
    fn build_environment() -> Result<Environment, String> {
        LiteralReturnByteModel::build_environment()
    }
    fn reconstruct(source: &Claim, target: &Module) -> Result<Expr, String> {
        let reflected =
            reflect_core_module_v1(target, &[(FUNCTION, 4096)]).map_err(|e| e.to_string())?;
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        Ok(eq(
            model.config_type(),
            model.run(&NatTerm::literal(6), initial(&model, source.input)),
            expected_terminal(u64::from(source.result)),
        ))
    }
}
fn checker() -> &'static TranslationRechecker<ComparisonModel> {
    static CHECKER: OnceLock<TranslationRechecker<ComparisonModel>> = OnceLock::new();
    CHECKER.get_or_init(|| TranslationRechecker::new(Default::default()).unwrap())
}
fn initial(model: &MachineModel, input: u64) -> Expr {
    app(
        "ir_byte_init_v1",
        [
            c("Nat"),
            model.context().clone(),
            nat(0),
            list("IRScalar", &[scalar(input)]),
            memory(173),
            nat(37),
        ],
    )
}

fn fixture(ty: Ty) -> Module {
    let mut builder = ModuleBuilder::new_with_target_info(
        "authored_usize_comparison",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![ty.clone()], vec![Ty::U64]);
    let id = builder.declare_function("comparison_branch", signature);
    assert_eq!(id, FUNCTION);
    let mut function = builder.define_function(id).unwrap();
    let entry = function.create_block();
    let yes = function.create_block();
    let no = function.create_block();
    let input = function.add_block_param(entry, ty.clone());
    function.switch_to_block(entry);
    let threshold = function.uconst(ty.clone(), u128::from(MAX));
    let alternate = function.uconst(ty.clone(), u128::from(MAX - 1));
    let compared = function.icmp(ICmpOp::Ugt, ty, input, threshold);
    assert_eq!(
        (entry, input, alternate, compared),
        (ENTRY, ValueId::new(0), ValueId::new(2), ValueId::new(3))
    );
    function.condbr(compared, yes, vec![], no, vec![]);
    for (block, value) in [(yes, 1), (no, 0)] {
        function.switch_to_block(block);
        let result = function.uconst(Ty::U64, value);
        function.ret(vec![result]);
    }
    function.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}

fn ordered_evaluation(input: u64) -> Expr {
    // Only input bounds and Nat order are supplied. Neither a successful
    // evaluator answer nor a post-world equality is a fixture hypothesis.
    let (law, order) = match input.cmp(&MAX) {
        std::cmp::Ordering::Less => {
            assert_eq!(input, MAX - 1);
            (
                "ir_byte_icmp_usize64_ugt_le_v1",
                app(
                    "Nat.le.step",
                    [nat(input), nat(input), app("Nat.le.refl", [nat(input)])],
                ),
            )
        }
        std::cmp::Ordering::Equal => (
            "ir_byte_icmp_usize64_ugt_le_v1",
            app("Nat.le.refl", [nat(MAX)]),
        ),
        std::cmp::Ordering::Greater => {
            assert_eq!(input, MAX + 1);
            (
                "ir_byte_icmp_usize64_ugt_lt_v1",
                app("Nat.le.refl", [nat(input)]),
            )
        }
    };
    app(
        law,
        [
            nat(input),
            nat(MAX),
            refl(c("Bool"), c("Bool.true")),
            refl(c("Bool"), c("Bool.true")),
            order,
        ],
    )
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Fault {
    None,
    Result,
    Carrier,
    Destination,
    Site,
    Pc,
    Legacy,
    Branch,
}

fn transfer(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    current: &Current,
    before: PendingEquality,
    site: &FetchedSite,
    value: Expr,
    proof: Option<Expr>,
) -> ScalarTransfer {
    let checks = site.scalar_checks(model, current, value.clone()).unwrap();
    let evaluated = if let Some(proof) = proof {
        PendingEquality::candidate(
            c("IRStepResult"),
            checks.evaluation,
            app("IRStepResult.value", [value.clone()]),
            proof,
        )
    } else {
        assembler
            .conversion(
                c("IRStepResult"),
                checks.evaluation,
                app("IRStepResult.value", [value.clone()]),
            )
            .unwrap()
    };
    let operands = truth(assembler, checks.operands);
    let result = truth(assembler, checks.result);
    site.scalar_value(
        assembler,
        model,
        current,
        value,
        ScalarPremises {
            evaluated,
            operands,
            result,
            before,
        },
    )
    .unwrap()
}

fn assemble(
    module: &Module,
    claim: Claim,
    fault: Fault,
    terminal_override: Option<Expr>,
) -> Vec<u8> {
    let reflected = reflect_core_module_v1(module, &[(FUNCTION, 4096)]).unwrap();
    let model = MachineModel::new(c("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(checker().environment(), &reflected, limits()).unwrap();
    let entry = catalog.entry(FUNCTION).unwrap();
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let arguments = list("IRScalar", &[scalar(claim.input)]);
    let memory_guard = truth(&mut assembler, EntryTarget::memory_admission(memory(173)));
    let entry_guard = truth(
        &mut assembler,
        entry.admission(&model, arguments.clone()).unwrap(),
    );
    let initialized = entry
        .initialize(
            &mut assembler,
            &model,
            arguments,
            memory(173),
            nat(37),
            memory_guard,
            entry_guard,
        )
        .unwrap();
    let mut current = initialized.current().clone();
    let original = current.clone();
    let mut valid = initialized.valid().clone();
    let mut prefix = assembler.zero(&model, current.running(&model)).unwrap();
    for pc in 0..3 {
        let mut site = catalog
            .fetch(Coordinate {
                function: FUNCTION,
                block: ENTRY,
                instruction: if pc == 2 && fault == Fault::Pc { 1 } else { pc },
            })
            .unwrap();
        let value = if pc < 2 {
            scalar(MAX - pc as u64)
        } else if fault == Fault::Carrier {
            scalar(u64::from(claim.result))
        } else {
            boolean(if fault == Fault::Result {
                !claim.result
            } else {
                claim.result
            })
        };
        let proof = if pc == 2 {
            if fault == Fault::Destination {
                site.results = list("Nat", &[nat(97)]);
            }
            if fault == Fault::Site {
                let mut fields: Vec<Expr> = site.site.get_app_args().into_iter().cloned().collect();
                fields[5] = list("IRTy", &[app("IRTy.usize_", [nat(64)])]);
                site.site = app("IRByteSiteV1.mk", fields);
            }
            if fault == Fault::Legacy {
                let fields = site
                    .scalar_checks(&model, &current, value.clone())
                    .unwrap()
                    .evaluation
                    .get_app_args()
                    .into_iter()
                    .cloned()
                    .collect::<Vec<_>>();
                Some(refl(c("IRStepResult"), app("ir_icmp_eval", fields)))
            } else if matches!(
                module.functions[0].blocks[0].body[2].inst,
                Inst::ICmp { ty: Ty::Usize, .. }
            ) {
                Some(ordered_evaluation(claim.input))
            } else {
                None
            }
        } else {
            None
        };
        let next = transfer(&mut assembler, &model, &current, valid, &site, value, proof);
        assert_eq!(next.current().world, original.world);
        assert_eq!(next.current().tail, original.tail);
        assert_eq!(next.current().legacy_memory, original.legacy_memory);
        assert_eq!(next.current().legacy_cursor, original.legacy_cursor);
        prefix = assembler.concatenate(prefix, next.run().clone()).unwrap();
        current = next.current().clone();
        valid = next.valid().clone();
    }
    let taken = if fault == Fault::Branch {
        !claim.result
    } else {
        claim.result
    };
    let block = BlockId::new(if taken { 1 } else { 2 });
    let destination = catalog.branch_target(FUNCTION, block).unwrap();
    let site = catalog
        .fetch(Coordinate {
            function: FUNCTION,
            block: ENTRY,
            instruction: 3,
        })
        .unwrap();
    let checks = site
        .branch_checks(&model, &current, &destination, Some(taken))
        .unwrap();
    let condition = assembler
        .conversion(c("IRScalar"), checks.condition.unwrap(), boolean(taken))
        .unwrap();
    let resolved = assembler
        .conversion(
            app("IRList", [c("IRScalar")]),
            app("ir_resolve", [current.machine(), checks.arguments]),
            list("IRScalar", &[]),
        )
        .unwrap();
    let arity = truth(&mut assembler, checks.arity);
    let branched = site
        .branch_to(
            &mut assembler,
            &model,
            &current,
            &destination,
            Some(taken),
            BranchPremises {
                condition: Some(condition),
                resolved,
                arity,
                before: valid,
            },
        )
        .unwrap();
    assert_eq!(branched.current().world, original.world);
    prefix = assembler
        .concatenate(prefix, branched.run().clone())
        .unwrap();
    let constant = catalog
        .fetch(Coordinate {
            function: FUNCTION,
            block,
            instruction: 0,
        })
        .unwrap();
    let returned = transfer(
        &mut assembler,
        &model,
        branched.current(),
        branched.valid().clone(),
        &constant,
        scalar(u64::from(taken)),
        None,
    );
    prefix = assembler
        .concatenate(prefix, returned.run().clone())
        .unwrap();
    let returning = catalog
        .fetch(Coordinate {
            function: FUNCTION,
            block,
            instruction: 1,
        })
        .unwrap();
    let dispatch = returning
        .step(
            &mut assembler,
            &model,
            returned.current(),
            returned.valid().clone(),
        )
        .unwrap();
    let terminal = terminal_override.unwrap_or_else(|| expected_terminal(u64::from(claim.result)));
    let finish = assembler
        .conversion(model.config_type(), dispatch.right().clone(), terminal)
        .unwrap();
    let step = assembler.compose(dispatch, finish).unwrap();
    let returned_run = assembler
        .one_step(&model, returned.current().running(&model), step)
        .unwrap();
    let execution = assembler.concatenate(prefix, returned_run).unwrap();
    let mapped = assembler
        .congruence(
            initialized.equality().clone(),
            model.config_type(),
            |state| model.run(execution.fuel(), state),
        )
        .unwrap();
    let start = assembler
        .conversion(
            model.config_type(),
            model.run(&NatTerm::literal(6), initial(&model, claim.input)),
            mapped.left().clone(),
        )
        .unwrap();
    let end = assembler
        .conversion(
            model.config_type(),
            mapped.right().clone(),
            execution.equality().left().clone(),
        )
        .unwrap();
    let complete = assembler.compose(start, mapped).unwrap();
    let complete = assembler.compose(complete, end).unwrap();
    let complete = assembler
        .compose(complete, execution.equality().clone())
        .unwrap();
    let closed = scope.close(complete.term()).unwrap();
    assert!(
        !closed.has_fvar_quick(),
        "no evaluation/post-state assumptions"
    );
    trust_ir::proof::encode_clean_expr_dag_v2(&closed).unwrap()
}

fn rejects(claim: &Claim, module: &Module, proof: &[u8]) {
    let error = checker().recheck_dag_v2(claim, module, proof).unwrap_err();
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
            "{error}"
        );
    }
}

#[test]
fn usize_threshold_comparison_and_actual_condbr_replay_whole_world() {
    let module = fixture(Ty::Usize);
    let original = module.clone();
    for input in [MAX - 1, MAX, MAX + 1] {
        let claim = Claim {
            input,
            result: input > MAX,
        };
        let proof = assemble(&module, claim, Fault::None, None);
        let checked = checker().recheck_dag_v2(&claim, &module, &proof).unwrap();
        assert!(std::ptr::eq(checked.target(), &module));
        assert!(std::ptr::eq(checked.source(), &claim));
    }
    assert_eq!(
        module, original,
        "no annotation or module rewrite may confer authority"
    );
    for name in [
        "ir_byte_icmp_usize64_ugt_canonical_v1",
        "ir_byte_icmp_usize64_ugt_le_v1",
        "ir_byte_icmp_usize64_ugt_lt_v1",
    ] {
        let name = Name::from_string(name);
        assert!(
            checker()
                .environment()
                .axiom_deps(&name)
                .unwrap()
                .is_empty()
        );
        assert!(
            checker()
                .environment()
                .trust_marker_deps(&name)
                .unwrap()
                .is_empty()
        );
    }
}

#[test]
fn u64_comparison_and_both_branches_remain_kernel_replayable() {
    let module = fixture(Ty::U64);
    for input in [MAX - 1, MAX, MAX + 1] {
        let claim = Claim {
            input,
            result: input > MAX,
        };
        let proof = assemble(&module, claim, Fault::None, None);
        checker().recheck_dag_v2(&claim, &module, &proof).unwrap();
    }
}

#[test]
fn usize_comparison_candidate_operand_result_site_pc_and_branch_controls() {
    let module = fixture(Ty::Usize);
    let claim = Claim {
        input: MAX + 1,
        result: true,
    };
    for fault in [
        Fault::Result,
        Fault::Carrier,
        Fault::Destination,
        Fault::Site,
        Fault::Pc,
        Fault::Legacy,
        Fault::Branch,
    ] {
        let proof = assemble(&module, claim, fault, None);
        rejects(&claim, &module, &proof);
    }
}

#[test]
fn actual_module_live_operands_opcode_branch_and_source_are_bound() {
    let module = fixture(Ty::Usize);
    let claim = Claim {
        input: MAX,
        result: false,
    };
    let proof = assemble(&module, claim, Fault::None, None);
    for mode in 0..4 {
        let mut changed = module.clone();
        let Inst::ICmp { lhs, rhs, op, .. } = &mut changed.functions[0].blocks[0].body[2].inst
        else {
            unreachable!()
        };
        match mode {
            0 => *rhs = ValueId::new(2), // live MAX-1, not a wrong-typed placeholder
            1 => *lhs = ValueId::new(2),
            2 => *op = ICmpOp::Uge,
            _ => {
                let Inst::CondBr {
                    then_target,
                    else_target,
                    ..
                } = &mut changed.functions[0].blocks[0].body[3].inst
                else {
                    unreachable!()
                };
                std::mem::swap(then_target, else_target);
            }
        }
        assert!(trust_ir_build::validate_module(&changed).is_empty());
        if mode == 1 {
            // This input makes the valid live lhs substitution change true to
            // false. Replaying execution is not a syntactic-module hash test:
            // a consistently renamed SSA result may preserve the same claim.
            let above = Claim {
                input: MAX + 1,
                result: true,
            };
            let above_proof = assemble(&module, above, Fault::None, None);
            rejects(&above, &changed, &above_proof);
        } else {
            rejects(&claim, &changed, &proof);
        }
    }
    rejects(
        &Claim {
            result: true,
            ..claim
        },
        &module,
        &proof,
    );
    rejects(
        &Claim {
            input: MAX + 1,
            ..claim
        },
        &module,
        &proof,
    );
}

#[test]
fn comparison_preserves_complete_world_not_only_return_value() {
    let module = fixture(Ty::Usize);
    let claim = Claim {
        input: MAX + 1,
        result: true,
    };
    for wrong in [
        world(174, 37, &[], 9),
        world(173, 38, &[], 9),
        world(173, 37, &[nat(8)], 9),
        world(173, 37, &[], 8),
    ] {
        let proof = assemble(&module, claim, Fault::None, Some(halted(1, wrong)));
        rejects(&claim, &module, &proof);
    }
}

#[test]
fn comparison_legacy_wrong_kind_width_and_opcode_refusals_are_preserved() {
    let not_int = app(
        "IRStepResult.fault",
        [app("IROutcome.type_error", [c("IRFault.not_int")])],
    );
    let bounded = app(
        "IRStepResult.fault",
        [app("IROutcome.unmodelled", [c("IRFault.width_bounded")])],
    );
    let usize64 = app("IRTy.usize_", [nat(64)]);
    let mut cases = vec![(
        app(
            "ir_icmp_eval",
            [c("IRICmpOp.ugt"), usize64.clone(), scalar(8), scalar(7)],
        ),
        not_int.clone(),
    )];
    for bits in [0, 8, 32, 128] {
        cases.push((
            app(
                "ir_byte_icmp_eval_v1",
                [
                    c("IRICmpOp.ugt"),
                    app("IRTy.usize_", [nat(bits)]),
                    scalar(8),
                    scalar(7),
                ],
            ),
            bounded.clone(),
        ));
    }
    for (op, expected) in [
        ("eq_", false),
        ("ne_", true),
        ("ult", false),
        ("ule", false),
        ("uge", true),
        ("slt", false),
        ("sle", false),
        ("sgt", true),
        ("sge", true),
    ] {
        cases.push((
            app(
                "ir_byte_icmp_eval_v1",
                [
                    c(&format!("IRICmpOp.{op}")),
                    usize64.clone(),
                    scalar(8),
                    scalar(7),
                ],
            ),
            app("IRStepResult.value", [boolean(expected)]),
        ));
    }
    for wrong in [
        boolean(true),
        app("IRScalar.ptr_", [nat(16)]),
        c("IRScalar.undef_"),
    ] {
        cases.push((
            app(
                "ir_byte_icmp_eval_v1",
                [c("IRICmpOp.ugt"), usize64.clone(), wrong, scalar(7)],
            ),
            not_int.clone(),
        ));
    }
    for (actual, expected) in cases {
        let goal = eq(c("IRStepResult"), actual, expected.clone());
        let audit = checker()
            .environment()
            .audit_certification(&goal, &refl(c("IRStepResult"), expected));
        assert!(audit.issues.is_empty(), "{:?}", audit.issues);
    }
    for pointer_size in [4, 16] {
        let mut module = fixture(Ty::Usize);
        module.target_info.as_mut().unwrap().pointer_size = pointer_size;
        assert!(reflect_core_module_v1(&module, &[(FUNCTION, 4096)]).is_err());
    }
}
