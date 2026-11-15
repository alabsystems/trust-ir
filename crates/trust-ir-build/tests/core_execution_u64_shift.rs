// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Opt-in full64 shift candidates, replayed against independently authored
//! operation and whole-world claims. No evaluation answer is an input premise.
//! These bounded model tests establish neither native nor frontend authority.

#[path = "core_execution_u64_shift/support.rs"]
mod support;

use clean_kernel::{Environment, Expr, Level, Name};
use std::sync::OnceLock;
use support::*;
use trust_ir::{
    BinOp, BlockId, Constant, Endianness, FuncId, Inst, Module, StructPassingPolicy, TargetInfo,
    Ty, ValueId,
};
use trust_ir_build::{
    ModuleBuilder,
    core_execution::{Assembler, MachineModel, NatTerm, PendingEquality, PendingProof},
    core_reflection::reflect_core_module_v1,
    scoped_local::LocalScope,
    translation::{SourceTranslationModel, TranslationRechecker},
};

const FUNCTION: FuncId = FuncId::new(0);
const BLOCK: BlockId = BlockId::new(0);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Shift {
    Logical,
    Arithmetic,
}

impl Shift {
    fn ty(self) -> Ty {
        match self {
            Self::Logical => Ty::U64,
            Self::Arithmetic => Ty::I64,
        }
    }
    fn ir_ty(self) -> Expr {
        app(
            match self {
                Self::Logical => "IRTy.uint_",
                Self::Arithmetic => "IRTy.int_",
            },
            [nat(64)],
        )
    }
    fn op(self) -> BinOp {
        match self {
            Self::Logical => BinOp::LShr,
            Self::Arithmetic => BinOp::AShr,
        }
    }
    fn opcode(self) -> &'static str {
        match self {
            Self::Logical => "IRBinOp.lshr",
            Self::Arithmetic => "IRBinOp.ashr",
        }
    }
    fn law(self) -> &'static str {
        match self {
            Self::Logical => "ir_byte_lshr_u64_by_three_v1",
            Self::Arithmetic => "ir_byte_ashr_i64_by_three_v1",
        }
    }
    fn derive(
        self,
        assembler: &mut Assembler<'_>,
        word: Expr,
        bound: PendingProof,
    ) -> (Expr, PendingEquality) {
        match self {
            Self::Logical => assembler.byte_lshr_u64_by_three(word, bound),
            Self::Arithmetic => assembler.byte_ashr_i64_by_three(word, bound),
        }
        .expect("construct only a pending canonical-word operation")
    }
    fn operation(self, word: Expr, amount: u64) -> Expr {
        app(
            "ir_binop_eval",
            [
                c(self.opcode()),
                self.ir_ty(),
                scalar(word),
                scalar(nat(amount)),
            ],
        )
    }
    fn result(self, word: Expr) -> Expr {
        // Independent reconstruction: the result is not copied from derive().
        let q = quotient(word.clone());
        let value = match self {
            Self::Logical => q,
            Self::Arithmetic => Expr::apps(
                Expr::const_(
                    Name::from_string("Bool.rec"),
                    vec![Level::succ(Level::zero())],
                ),
                [
                    lam(c("Bool"), c("Nat")),
                    q.clone(),
                    app(
                        "Nat.add",
                        [
                            q,
                            app(
                                "Nat.sub",
                                [
                                    app("ir_nat_pow2", [nat(64)]),
                                    quotient(app("ir_nat_pow2", [nat(64)])),
                                ],
                            ),
                        ],
                    ),
                    app("ir_sign_bit", [nat(64), word]),
                ],
            ),
        };
        scalar(value)
    }
}

#[derive(Clone, Copy)]
struct Claim {
    shift: Shift,
    word: u64,
    answer: u64,
}

impl Claim {
    fn values(self) -> Expr {
        list("IRScalar", &[scalar(nat(self.answer))])
    }
    fn initial(self, model: &MachineModel) -> Expr {
        app(
            "ir_byte_init_v1",
            [
                c("Nat"),
                model.context().clone(),
                nat(0),
                list("IRScalar", &[scalar(nat(self.word))]),
                memory(173),
                nat(37),
            ],
        )
    }
    fn terminal(self, world: Expr) -> Expr {
        app(
            "IRByteConfigV1.halted",
            [c("Nat"), app("IROutcome.ret", [self.values()]), world],
        )
    }
}

struct ShiftModel;

impl SourceTranslationModel for ShiftModel {
    type Source = Claim;
    fn build_environment() -> Result<Environment, String> {
        // Owned transfer: no default Byte vocabulary change or per-program spec.
        clean_verify::eval_ir::build_u64_shift_by_three_byte_prelude_spec_v1_with_stack()
            .map(|spec| spec.into_environment())
            .map_err(|error| error.to_string())
    }
    fn reconstruct(source: &Claim, target: &Module) -> Result<Expr, String> {
        if !trust_ir_build::validate_module(target).is_empty() {
            return Err("shift replay requires an actually valid target module".into());
        }
        let reflected = reflect_core_module_v1(target, &[(FUNCTION, 4096)])
            .map_err(|error| error.to_string())?;
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        // Both endpoints come from retained source and actual target, not a
        // candidate's equality or a normalization of the target execution.
        Ok(eq(
            model.config_type(),
            model.run(&NatTerm::literal(3), source.initial(&model)),
            source.terminal(world(173, 37, &[], 9)),
        ))
    }
}

fn checker() -> &'static TranslationRechecker<ShiftModel> {
    static CHECKER: OnceLock<TranslationRechecker<ShiftModel>> = OnceLock::new();
    CHECKER.get_or_init(|| TranslationRechecker::new(Default::default()).unwrap())
}

fn fixture(shift: Shift) -> Module {
    let mut builder = ModuleBuilder::new_with_target_info(
        "full64_shift_consumer",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let ty = shift.ty();
    let signature = builder.add_func_type(vec![ty.clone()], vec![ty.clone()]);
    let id = builder.declare_function("shift_by_three", signature);
    assert_eq!(id, FUNCTION);
    let mut body = builder.define_function(id).unwrap();
    let block = body.create_block();
    assert_eq!(block, BLOCK);
    let word = body.add_block_param(block, ty.clone());
    body.switch_to_block(block);
    let amount = body.uconst(ty.clone(), 3);
    let result = body.binop(shift.op(), ty, word, amount);
    assert_eq!(
        (word, amount, result),
        (ValueId::new(0), ValueId::new(1), ValueId::new(2))
    );
    body.ret(vec![result]);
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}

#[test]
fn canonical_symbolic_shift_candidates_replay_original_operations_and_lossless_dags() {
    for shift in [Shift::Logical, Shift::Arithmetic] {
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let word = assembler.local(c("Nat")).unwrap();
        let bounded = assembler.local(bound(word.term().clone())).unwrap();
        let (value, proof) = shift.derive(
            &mut assembler,
            word.term().clone(),
            PendingProof::candidate(bound(word.term().clone()), bounded.term().clone()),
        );
        let expected_value = shift.result(word.term().clone());
        assert_eq!(value, expected_value);
        let claim = eq(
            c("IRStepResult"),
            shift.operation(word.term().clone(), 3),
            result(expected_value),
        );
        replay(
            &scope,
            &[word, bounded],
            proof.term(),
            &claim,
            Some(shift.law()),
        );
    }
}

#[test]
fn fullwidth_boundary_candidates_compute_only_the_restoring_side() {
    for (word, logical, arithmetic) in [
        (0, 0, 0),
        (7, 0, 0),
        (8, 1, 1),
        (
            9_223_372_036_854_775_807,
            1_152_921_504_606_846_975,
            1_152_921_504_606_846_975,
        ),
        (
            9_223_372_036_854_775_808,
            1_152_921_504_606_846_976,
            17_293_822_569_102_704_640,
        ),
        (
            18_446_744_073_709_551_608,
            2_305_843_009_213_693_951,
            u64::MAX,
        ),
        (u64::MAX, 2_305_843_009_213_693_951, u64::MAX),
    ] {
        for (shift, answer) in [(Shift::Logical, logical), (Shift::Arithmetic, arithmetic)] {
            let mut scope = LocalScope::new();
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let (_, evaluated) = shift.derive(&mut assembler, nat(word), bounded(word));
            let computed = assembler
                .conversion(
                    c("IRStepResult"),
                    evaluated.right().clone(),
                    result(scalar(nat(answer))),
                )
                .unwrap();
            let complete = assembler.compose(evaluated, computed).unwrap();
            let claim = eq(
                c("IRStepResult"),
                shift.operation(nat(word), 3),
                result(scalar(nat(answer))),
            );
            replay(&scope, &[], complete.term(), &claim, Some(shift.law()));
        }
    }
}

#[path = "core_execution_u64_shift/small_false_mutants.rs"]
mod small_false_mutants;

#[test]
fn small_actual_shift_mutants_refuse_changed_operands_amount_opcode_and_desired_answer() {
    small_false_mutants::run();
}

#[test]
fn changed_in_range_amount_has_small_actual_positive_controls() {
    for shift in [Shift::Logical, Shift::Arithmetic] {
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let operation = shift.operation(nat(8), 4);
        let value = result(scalar(nat(0)));
        let proof = assembler
            .conversion(c("IRStepResult"), operation.clone(), value.clone())
            .unwrap();
        replay(
            &scope,
            &[],
            proof.term(),
            &eq(c("IRStepResult"), operation, value),
            None,
        );
    }
}

#[test]
fn matching_foreign_carrier_bounds_remain_untrusted_until_strict_replay() {
    for shift in [Shift::Logical, Shift::Arithmetic] {
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let foreign = scalar(nat(8));
        // Exact matching endpoints deliberately pass the structural API. The
        // ill-typed Nat operand and forged bound must fail the kernel, not be
        // mislabeled as a type-inference service provided by the assembler.
        let (_, proof) = shift.derive(
            &mut assembler,
            foreign.clone(),
            PendingProof::candidate(bound(foreign), c("True.intro")),
        );
        refuses(
            &scope,
            &[],
            proof.term(),
            &eq(
                c("IRStepResult"),
                shift.operation(nat(8), 3),
                result(scalar(nat(1))),
            ),
        );
    }
}

#[test]
fn fetched_const_shift_and_root_return_replay_full_world_at_fullwidth_boundaries() {
    for claim in [
        Claim {
            shift: Shift::Logical,
            word: 8,
            answer: 1,
        },
        Claim {
            shift: Shift::Logical,
            word: u64::MAX,
            answer: 2_305_843_009_213_693_951,
        },
        Claim {
            shift: Shift::Arithmetic,
            word: 9_223_372_036_854_775_808,
            answer: 17_293_822_569_102_704_640,
        },
        Claim {
            shift: Shift::Arithmetic,
            word: u64::MAX,
            answer: u64::MAX,
        },
    ] {
        let module = fixture(claim.shift);
        let original = module.clone();
        let bytes = assemble(&module, claim, None);
        // Budgeted first: a replay that evaluates the shift's reference
        // semantics fails here in seconds, not in the hours the default
        // budget below would take to notice.
        budgeted_replay(&module, claim, &bytes).unwrap();
        let checked = checker().recheck_dag_v2(&claim, &module, &bytes).unwrap();
        assert_eq!(checked.proof_term(), bytes);
        assert_eq!(module, original, "assembly never rewrites its target");
        let term = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
        let proposition = ShiftModel::reconstruct(&claim, &module).unwrap();
        certify(&term, &proposition, Some(claim.shift.law()));
    }
}

/// Kernel work to strictly replay one assembled whole-world claim under
/// [`REPLAY_HEARTBEATS`]. It decodes the actual bytes and reconstructs the
/// claim independently, as the rechecker does.
fn budgeted_replay(module: &Module, claim: Claim, bytes: &[u8]) -> Result<u64, String> {
    let term = trust_ir::proof::decode_clean_expr_dag_v2(bytes).map_err(|e| e.to_string())?;
    let proposition = ShiftModel::reconstruct(&claim, module)?;
    replay_work(&term, &proposition, REPLAY_HEARTBEATS)
}

/// The kernel budget a whole-world shift replay must fit at EVERY word.
///
/// Measured 2026-10-14 (debug, Clean 023d17b65): 991 heartbeats at word 1,
/// 2,267 at `u64::MAX` (logical), 4,902 at `u64::MAX` (arithmetic, whose sign
/// fill divides 2^64 too). The budget is about four times the largest. A
/// replay that evaluates the shift's reference semantics instead, the
/// repeated-subtraction `ir_nat_div word 8`, needs 2^61 iterations at
/// `u64::MAX`; it spends this budget within seconds and is refused.
const REPLAY_HEARTBEATS: u32 = 20_000;

/// Heartbeats one more bit of the word may add. The derived shift is a
/// restoring division whose loop runs once per bit: measured about 20 per bit
/// for the logical ladder, and 61 per bit from word 1 to the arithmetic
/// `u64::MAX`, whose negative sign adds the fill term.
const REPLAY_HEARTBEATS_PER_BIT: u64 = 96;

/// The complexity guard for the whole-world replay: the kernel's work grows
/// with the word's BIT LENGTH, never its MAGNITUDE.
///
/// History: run-one presentation by kernel conversion (trust-ir 2ce4067d,
/// reverted) made replay evaluate the actual step's reference semantics. The
/// replay then grew from 0.2 s at a 4-bit word to 21-46 s at 20 bits and did not
/// finish at 64 bits; gate 9 sat on
/// `fetched_const_shift_and_root_return_replay_full_world_at_fullwidth_boundaries`
/// for 3.5 hours. Against that tree this guard fails in seconds.
#[test]
fn fetched_replay_work_tracks_word_bit_length_not_magnitude() {
    for shift in [Shift::Logical, Shift::Arithmetic] {
        let mut base = None;
        for bits in [1u32, 4, 8, 16, 24, 32, 48, 63, 64] {
            let word = if bits == 64 {
                u64::MAX
            } else {
                (1u64 << bits) - 1
            };
            // Rust's own shifts are the independent oracle for the answer.
            let answer = match shift {
                Shift::Logical => word >> 3,
                Shift::Arithmetic => ((word as i64) >> 3) as u64,
            };
            let claim = Claim {
                shift,
                word,
                answer,
            };
            let module = fixture(shift);
            let bytes = assemble(&module, claim, None);
            let work = budgeted_replay(&module, claim, &bytes)
                .unwrap_or_else(|error| panic!("{shift:?} {bits}-bit word {word}: {error}"));
            let base = *base.get_or_insert(work);
            assert!(
                work <= base + REPLAY_HEARTBEATS_PER_BIT * u64::from(bits),
                "{shift:?} {bits}-bit word {word}: {work} heartbeats, over {base} + \
                 {REPLAY_HEARTBEATS_PER_BIT} per bit: replay work is tracking the word's magnitude"
            );
        }
    }
}

#[test]
fn whole_claim_replay_refuses_actual_target_and_source_mutations() {
    let claim = Claim {
        shift: Shift::Logical,
        word: 8,
        answer: 1,
    };
    let module = fixture(claim.shift);
    let bytes = assemble(&module, claim, None);
    for changed_source in [Claim { word: 16, ..claim }, Claim { answer: 0, ..claim }] {
        rejects(&changed_source, &module, &bytes);
    }
    for mode in 0..4 {
        let mut changed = module.clone();
        match mode {
            0 => {
                let Inst::Const { value, .. } = &mut changed.functions[0].blocks[0].body[0].inst
                else {
                    panic!("actual amount constant")
                };
                *value = Constant::Int(4);
            }
            1 | 2 => {
                let Inst::BinOp { lhs, op, .. } = &mut changed.functions[0].blocks[0].body[1].inst
                else {
                    panic!("actual shift")
                };
                if mode == 1 {
                    *lhs = ValueId::new(1);
                } else {
                    *op = BinOp::Shl;
                }
            }
            3 => {
                let Inst::Return { values } = &mut changed.functions[0].blocks[0].body[2].inst
                else {
                    panic!("actual Return")
                };
                values[0] = ValueId::new(1);
            }
            _ => panic!("fixed mutation inventory"),
        }
        assert!(trust_ir_build::validate_module(&changed).is_empty());
        rejects(&claim, &changed, &bytes);
    }
}

#[test]
fn whole_claim_keeps_bytes_host_owner_retirement_and_next_epoch() {
    let claim = Claim {
        shift: Shift::Logical,
        word: 8,
        answer: 1,
    };
    let module = fixture(claim.shift);
    for changed_world in [
        world(174, 37, &[], 9),
        world(173, 38, &[], 9),
        world(173, 37, &[nat(8)], 9),
        world(173, 37, &[], 10),
    ] {
        rejects(
            &claim,
            &module,
            &assemble(&module, claim, Some(changed_world)),
        );
    }
}
