// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Bounded AUTHORED Core countdown consumer, not extracted Rust/TLA/native
//! evidence. Inputs 0/1/3 have independent mathematical phase witnesses;
//! every actual fetched transition, repeated backedge binding and root return
//! must replay. Nat induction proves arbitrary fuel, not a fuel-test matrix.
//! No declaration, axiom, evaluator replacement or assumed loop closure is
//! installed. The relation retains the COMPLETE configuration and byte world.

use clean_kernel::{BinderInfo, Environment, Expr, Level, Name, TypeChecker};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use std::sync::OnceLock;
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::{
    BinOp, BlockId, Endianness, FuncId, ICmpOp, Inst, Module, StructPassingPolicy, TargetInfo, Ty,
    ValueId,
};
use trust_ir_build::{
    ModuleBuilder,
    core_execution::{
        Assembler, Catalog, Coordinate, Current, EntryTarget, Limits, MachineModel, NatTerm,
        PendingEquality, PendingProof, PrefixSimulation,
    },
    core_reflection::reflect_core_module_v1,
    scoped_local::LocalScope,
    translation::{SourceTranslationModel, TranslationRechecker},
};

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn nat(n: u64) -> Expr {
    Expr::nat_lit(n)
}
fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}
fn eq(ty: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, a, b],
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
fn symmetry(ty: Expr, left: Expr, right: Expr, proof: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, left, right, proof],
    )
}
fn list(ty: &str, values: &[Expr]) -> Expr {
    values
        .iter()
        .rev()
        .fold(app("IRList.nil", [c(ty)]), |tail, value| {
            app("IRList.cons", [c(ty), value.clone(), tail])
        })
}
fn scalar(n: u64) -> Expr {
    app("IRScalar.int_", [nat(n)])
}
fn boolean(b: bool) -> Expr {
    c(if b { "Bool.true" } else { "Bool.false" })
}
fn config_type() -> Expr {
    app("IRByteConfigV1", [c("Nat")])
}
fn limits() -> Limits {
    Limits {
        max_operations: 1_000,
        max_locals: 100,
        max_list_items: 100,
        max_lookup_candidates: 32,
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}
fn memory(byte: u64) -> Expr {
    app(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                &[
                    app(
                        "IRByteAllocationV1.mk",
                        [nat(16), nat(16), nat(0), boolean(true)],
                    ),
                    app(
                        "IRByteAllocationV1.mk",
                        [nat(80), nat(8), nat(7), boolean(false)],
                    ),
                ],
            ),
            lam(c("Nat"), app("IROption.some", [c("Nat"), nat(byte)])),
            nat(128),
        ],
    )
}
fn world(retired: bool, byte: u64, host: u64) -> Expr {
    let owners = if retired { vec![] } else { vec![nat(8)] };
    app(
        "IRByteWorldV1.mk",
        [
            c("Nat"),
            memory(byte),
            nat(host),
            list("Nat", &owners),
            nat(9),
        ],
    )
}
fn terminal(byte: u64, host: u64) -> Expr {
    app(
        "IRByteConfigV1.halted",
        [
            c("Nat"),
            app("IROutcome.ret", [list("IRScalar", &[scalar(0)])]),
            world(true, byte, host),
        ],
    )
}
fn providers() -> Expr {
    lam(
        c("Nat"),
        lam(
            app("IRList", [c("IRScalar")]),
            lam(
                c("IRByteMemoryV1"),
                lam(
                    c("Nat"),
                    app(
                        "IRByteImportResultV1.mk",
                        [
                            c("Nat"),
                            app("IROutcome.stuck", [c("IRFault.no_func")]),
                            Expr::bvar(1),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        ),
    )
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

fn module() -> Module {
    let mut b = ModuleBuilder::new_with_target_info(
        "authored_countdown",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = b.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let id = b.declare_function("countdown", signature);
    let mut f = b.define_function(id).unwrap();
    let header = f.create_block();
    let body = f.create_block();
    let exit = f.create_block();
    let k = f.add_block_param(header, Ty::U64);
    f.switch_to_block(header);
    let zero = f.uconst(Ty::U64, 0);
    let one = f.uconst(Ty::U64, 1);
    let done = f.icmp(ICmpOp::Eq, Ty::U64, k, zero);
    f.condbr(done, exit, vec![], body, vec![]);
    f.switch_to_block(body);
    let decremented = f.sub(Ty::U64, k, one);
    f.br(header, vec![decremented]);
    f.switch_to_block(exit);
    f.ret(vec![k]);
    f.build();
    assert_eq!(
        (id, header, body, exit),
        (
            FuncId::new(0),
            BlockId::new(0),
            BlockId::new(1),
            BlockId::new(2)
        )
    );
    assert_eq!(
        (k, zero, one, done, decremented),
        (
            ValueId::new(0),
            ValueId::new(1),
            ValueId::new(2),
            ValueId::new(3),
            ValueId::new(4)
        )
    );
    let m = b.build().unwrap();
    assert!(trust_ir_build::validate_module(&m).is_empty());
    m
}

#[derive(Clone)]
struct Phase {
    block: u64,
    pc: u64,
    bindings: Vec<(u64, Expr)>,
}
impl Phase {
    fn current(&self) -> Current {
        Current {
            frame: app(
                "IRFrame.mk",
                [
                    nat(0),
                    nat(self.block),
                    nat(self.pc),
                    list(
                        "IRBinding",
                        &self
                            .bindings
                            .iter()
                            .map(|(id, value)| app("IRBinding.mk", [nat(*id), value.clone()]))
                            .collect::<Vec<_>>(),
                    ),
                    list("Nat", &[]),
                ],
            ),
            tail: list("IRFrame", &[]),
            legacy_memory: list("IRMemSlot", &[]),
            legacy_cursor: nat(0),
            world: world(false, 173, 37),
        }
    }
}

// Independent source arithmetic/phase specification. Never calls Core step,
// run, an interpreter, or a normalizer to obtain its expected configurations.
fn phases(input: u64) -> Vec<Phase> {
    assert!([0, 1, 3].contains(&input));
    let mut p = Phase {
        block: 0,
        pc: 0,
        bindings: vec![(0, scalar(input))],
    };
    let mut states = vec![p.clone()];
    let mut k = input;
    loop {
        p.bindings.insert(0, (1, scalar(0)));
        p.pc = 1;
        states.push(p.clone());
        p.bindings.insert(0, (2, scalar(1)));
        p.pc = 2;
        states.push(p.clone());
        p.bindings
            .insert(0, (3, app("IRScalar.bool_", [boolean(k == 0)])));
        p.pc = 3;
        states.push(p.clone());
        p.block = if k == 0 { 2 } else { 1 };
        p.pc = 0;
        states.push(p.clone());
        if k == 0 {
            break;
        }
        k -= 1;
        p.bindings.insert(0, (4, scalar(k)));
        p.pc = 1;
        states.push(p.clone());
        p.bindings.insert(0, (0, scalar(k)));
        p.block = 0;
        p.pc = 0;
        states.push(p.clone());
    }
    states
}

// A finite table has a genuinely constant tail, rather than a neutral
// constant-result Nat.rec which would still require a separate induction.
fn table(ty: Expr, values: &[Expr], default: Expr, index: Expr) -> Expr {
    let Some((head, rest)) = values.split_first() else {
        return default;
    };
    let successor = lam(
        c("Nat"),
        lam(ty.clone(), table(ty.clone(), rest, default, Expr::bvar(1))),
    );
    Expr::apps(
        Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [lam(c("Nat"), ty), head.clone(), successor, index],
    )
}

#[derive(Clone)]
struct Source {
    values: Vec<Expr>,
    halted: Expr,
    step: Expr,
    relation: Expr,
}
impl Source {
    fn new(input: u64, model: &MachineModel, final_state: Expr) -> Self {
        let mut values: Vec<_> = phases(input)
            .iter()
            .map(|p| p.current().running(model))
            .collect();
        values.push(final_state.clone());
        let last = values.len() - 1;
        let halted = lam(
            c("Nat"),
            table(
                c("Bool"),
                &vec![boolean(false); last],
                boolean(true),
                Expr::bvar(0),
            ),
        );
        // Poison the terminal source step: if incorrectly executed it returns
        // phase0, discarding the terminal outcome and activation retirement.
        let step = lam(
            c("Nat"),
            table(
                c("Nat"),
                &(1..=last).map(|i| nat(i as u64)).collect::<Vec<_>>(),
                nat(0),
                Expr::bvar(0),
            ),
        );
        let relation = lam(
            c("Nat"),
            lam(
                config_type(),
                eq(
                    config_type(),
                    Expr::bvar(0),
                    table(config_type(), &values[..last], final_state, Expr::bvar(1)),
                ),
            ),
        );
        Self {
            values,
            halted,
            step,
            relation,
        }
    }
    fn related(&self, index: Expr, cfg: Expr) -> Expr {
        Expr::apps(self.relation.clone(), [index, cfg])
    }
    fn simulation(&self) -> PrefixSimulation {
        PrefixSimulation {
            source_type: c("Nat"),
            source_halted: self.halted.clone(),
            source_step: self.step.clone(),
            relation: self.relation.clone(),
            halt_agrees: PendingProof::candidate(c("False"), c("True.intro")),
            step_preserves: PendingProof::candidate(c("False"), c("True.intro")),
        }
    }
}

struct CountdownModel;
impl SourceTranslationModel for CountdownModel {
    type Source = u64;
    fn build_environment() -> Result<Environment, String> {
        Ok(shared_specification_with_stack(EvalIrVocabulary::ByteV1)
            .map_err(|e| e.to_string())?
            .env()
            .clone())
    }
    fn reconstruct(input: &u64, target: &Module) -> Result<Expr, String> {
        if ![0, 1, 3].contains(input) {
            return Err("bounded authored consumer admits inputs 0/1/3 only".into());
        }
        let reflected =
            reflect_core_module_v1(target, &[(FuncId::new(0), 4096)]).map_err(|e| e.to_string())?;
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        let source = Source::new(*input, &model, terminal(173, 37));
        Ok(Expr::pi(
            BinderInfo::Default,
            c("Nat"),
            source.related(
                app(
                    "ir_drive_v1",
                    [
                        c("Nat"),
                        source.halted.clone(),
                        source.step.clone(),
                        Expr::bvar(0),
                        nat(0),
                    ],
                ),
                app(
                    "ir_byte_run_v1",
                    [
                        c("Nat"),
                        model.context().clone(),
                        model.providers().clone(),
                        Expr::bvar(0),
                        initial(&model, *input),
                    ],
                ),
            ),
        ))
    }
}
fn checker() -> &'static TranslationRechecker<CountdownModel> {
    static CHECKER: OnceLock<TranslationRechecker<CountdownModel>> = OnceLock::new();
    CHECKER.get_or_init(|| TranslationRechecker::new(Default::default()).unwrap())
}

// Test-only closed binder construction for finite CASES, not fuel unrolling.
// Each leaf uses a fetched step proof derived above. The generic production
// theorem, not this finite case analysis, performs arbitrary-fuel induction.
struct Cases<'a, 'scope> {
    depth: u32,
    assembler: &'a mut Assembler<'scope>,
    model: &'a MachineModel,
    source: &'a Source,
    transitions: &'a [PendingEquality],
    step: bool,
}
impl Cases<'_, '_> {
    fn v(&self, slot: u32) -> Expr {
        Expr::bvar(self.depth - slot - 1)
    }
    fn bind(&mut self, ty: Expr, pi: bool, f: impl FnOnce(&mut Self) -> Expr) -> Expr {
        self.depth += 1;
        let body = f(self);
        self.depth -= 1;
        if pi {
            Expr::pi(BinderInfo::Default, ty, body)
        } else {
            lam(ty, body)
        }
    }
    fn index(&self, slot: u32, offset: usize) -> Expr {
        (0..offset).fold(self.v(slot), |n, _| app("Nat.succ", [n]))
    }
    fn proposition(&mut self, slot: u32, offset: usize) -> Expr {
        let cfg = self.depth;
        self.bind(config_type(), true, |b| {
            b.bind(
                b.source.related(b.index(slot, offset), b.v(cfg)),
                true,
                |b| {
                    if b.step {
                        b.bind(
                            eq(
                                c("Bool"),
                                Expr::app(b.source.halted.clone(), b.index(slot, offset)),
                                boolean(false),
                            ),
                            true,
                            |b| {
                                b.source.related(
                                    Expr::app(b.source.step.clone(), b.index(slot, offset)),
                                    b.model.step(b.v(cfg)),
                                )
                            },
                        )
                    } else {
                        eq(
                            c("Bool"),
                            Expr::app(b.source.halted.clone(), b.index(slot, offset)),
                            app("ir_byte_halted_v1", [c("Nat"), b.v(cfg)]),
                        )
                    }
                },
            )
        })
    }
    fn leaf(&mut self, index: Expr, ordinal: usize) -> Expr {
        let cfg = self.depth;
        let h = cfg + 1;
        let expected = self.source.values[ordinal.min(self.source.values.len() - 1)].clone();
        self.bind(config_type(), false, |b| {
            // All caller inputs here are closed, except this leaf's explicit
            // index. Recompute it below when binders change its depth.
            let index = shift_index(index.clone(), 1);
            b.bind(b.source.related(index.clone(), b.v(cfg)), false, |b| {
                let index = shift_index(index.clone(), 1);
                let premise =
                    PendingEquality::candidate(config_type(), b.v(cfg), expected.clone(), b.v(h));
                if !b.step {
                    let mapped = b
                        .assembler
                        .congruence_function(
                            premise,
                            c("Bool"),
                            app("ir_byte_halted_v1", [c("Nat")]),
                        )
                        .unwrap();
                    let reverse = symmetry(
                        c("Bool"),
                        mapped.left().clone(),
                        mapped.right().clone(),
                        mapped.term().clone(),
                    );
                    let flag = Expr::app(b.source.halted.clone(), index);
                    let conversion = b
                        .assembler
                        .conversion(c("Bool"), flag, mapped.right().clone())
                        .unwrap();
                    let symmetric = PendingEquality::candidate(
                        c("Bool"),
                        mapped.right().clone(),
                        mapped.left().clone(),
                        reverse,
                    );
                    b.assembler
                        .compose(conversion, symmetric)
                        .unwrap()
                        .term()
                        .clone()
                } else {
                    let bad = b.depth;
                    b.bind(
                        eq(
                            c("Bool"),
                            Expr::app(b.source.halted.clone(), index.clone()),
                            boolean(false),
                        ),
                        false,
                        |b| {
                            let index = shift_index(index, 1);
                            if ordinal == b.source.values.len() - 1 {
                                let contradiction =
                                    symmetry(c("Bool"), boolean(true), boolean(false), b.v(bad));
                                return Expr::apps(
                                    Expr::const_(
                                        Name::from_string("False.elim"),
                                        vec![Level::zero()],
                                    ),
                                    [
                                        b.source.related(
                                            Expr::app(b.source.step.clone(), index),
                                            b.model.step(b.v(cfg)),
                                        ),
                                        app("ir_byte_world_false_true_v1", [contradiction]),
                                    ],
                                );
                            }
                            let premise = PendingEquality::candidate(
                                config_type(),
                                b.v(cfg),
                                expected.clone(),
                                b.v(h),
                            );
                            let mapped = b
                                .assembler
                                .congruence_function(
                                    premise,
                                    config_type(),
                                    app(
                                        "ir_byte_step_v1",
                                        [
                                            c("Nat"),
                                            b.model.context().clone(),
                                            b.model.providers().clone(),
                                        ],
                                    ),
                                )
                                .unwrap();
                            b.assembler
                                .compose(mapped, b.transitions[ordinal].clone())
                                .unwrap()
                                .term()
                                .clone()
                        },
                    )
                }
            })
        })
    }
    fn split(&mut self, slot: u32, offset: usize) -> Expr {
        if offset == self.source.values.len() - 1 {
            return self.leaf(self.index(slot, offset), offset);
        }
        let n = self.depth;
        let motive = self.bind(c("Nat"), false, |b| b.proposition(n, offset));
        let zero = self.leaf(nat(offset as u64), offset);
        let successor = self.bind(c("Nat"), false, |b| {
            let ih = b.proposition(n, offset);
            b.bind(ih, false, |b| b.split(n, offset + 1))
        });
        Expr::apps(
            Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            [motive, zero, successor, self.v(slot)],
        )
    }
    fn proof(&mut self) -> Expr {
        self.bind(c("Nat"), false, |b| b.split(0, 0))
    }
}

// Leaf indices are only Nat literals/successor chains over one explicit BVar.
// Do not install a general expression-substitution engine in this consumer.
fn shift_index(index: Expr, amount: u32) -> Expr {
    match index.kind() {
        clean_kernel::ExprKind::BVar(n) => Expr::bvar(*n + amount),
        clean_kernel::ExprKind::App(f, x) => {
            Expr::app(f.as_ref().clone(), shift_index(x.as_ref().clone(), amount))
        }
        _ => index,
    }
}

fn assemble(target: &Module, input: u64, final_override: Option<Expr>, forged_step: bool) -> Expr {
    let reflected = reflect_core_module_v1(target, &[(FuncId::new(0), 4096)]).unwrap();
    let model = MachineModel::new(c("Nat"), &reflected, providers());
    let source = Source::new(
        input,
        &model,
        final_override.unwrap_or_else(|| terminal(173, 37)),
    );
    let mut catalog = Catalog::new(checker().environment(), &reflected, limits()).unwrap();
    let mut scope = LocalScope::new();
    let mut a = Assembler::new(&mut scope, limits()).unwrap();
    let entry = catalog.entry(FuncId::new(0)).unwrap();
    let args = list("IRScalar", &[scalar(input)]);
    let memory_guard = a
        .conversion(
            c("Bool"),
            EntryTarget::memory_admission(memory(173)),
            boolean(true),
        )
        .unwrap();
    let guard = a
        .conversion(
            c("Bool"),
            entry.admission(&model, args.clone()).unwrap(),
            boolean(true),
        )
        .unwrap();
    let initialized = entry
        .initialize(
            &mut a,
            &model,
            args,
            memory(173),
            nat(37),
            memory_guard,
            guard,
        )
        .unwrap();
    let conversion = a
        .conversion(
            config_type(),
            initialized.equality().right().clone(),
            source.values[0].clone(),
        )
        .unwrap();
    let initialization = a
        .compose(initialized.equality().clone(), conversion)
        .unwrap();
    let mut transitions = Vec::new();
    for (ordinal, phase) in phases(input).iter().enumerate() {
        let current = phase.current();
        let site = catalog
            .fetch(Coordinate {
                function: FuncId::new(0),
                block: BlockId::new(phase.block as u32),
                instruction: phase.pc as usize,
            })
            .unwrap();
        let valid = a
            .conversion(c("Bool"), current.valid(&model), boolean(true))
            .unwrap();
        let fetched = site.step(&mut a, &model, &current, valid).unwrap();
        let reduced = a
            .conversion(
                config_type(),
                fetched.right().clone(),
                source.values[ordinal + 1].clone(),
            )
            .unwrap();
        transitions.push(a.compose(fetched, reduced).unwrap());
    }
    let mut simulation = source.simulation();
    let halt_term = Cases {
        depth: 0,
        assembler: &mut a,
        model: &model,
        source: &source,
        transitions: &transitions,
        step: false,
    }
    .proof();
    let step_term = if forged_step {
        c("True.intro")
    } else {
        Cases {
            depth: 0,
            assembler: &mut a,
            model: &model,
            source: &source,
            transitions: &transitions,
            step: true,
        }
        .proof()
    };
    simulation.halt_agrees =
        PendingProof::candidate(simulation.halt_agreement_proposition(&model), halt_term);
    simulation.step_preserves =
        PendingProof::candidate(simulation.step_preservation_proposition(&model), step_term);
    let fuel = a.local(c("Nat")).unwrap();
    let prefix = a
        .simulate_prefix(
            &model,
            &simulation,
            &NatTerm::local(&fuel).unwrap(),
            nat(0),
            initial(&model, input),
            PendingProof::candidate(
                source.related(nat(0), initial(&model, input)),
                initialization.term().clone(),
            ),
        )
        .unwrap();
    assert!(a.operations() < limits().max_operations);
    assert_eq!(
        a.local_scope().allocated(),
        1,
        "the prefix helper allocates no caller locals"
    );
    scope.close(&fuel.lam(prefix.term().clone())).unwrap()
}

fn replay(target: &Module, input: u64, term: &Expr, accepted: bool) {
    assert!(!term.has_fvar_quick() && !term.has_loose_bvars());
    let claim = CountdownModel::reconstruct(&input, target).unwrap();
    let mut kernel = TypeChecker::new(checker().environment());
    kernel.set_allow_unsafe(false);
    kernel.set_allow_partial(false);
    kernel.set_heartbeat_limit(5_000_000);
    kernel.set_max_cache_entries(100_000);
    kernel
        .check_type(&claim, &Expr::sort(Level::zero()))
        .unwrap();
    let checked = kernel.check_type(term, &claim);
    assert!(
        !kernel.heartbeat_spent(),
        "resource refusal is not a semantic refutation"
    );
    assert_eq!(checked.is_ok(), accepted, "{checked:?}");
    let bytes = trust_ir::proof::encode_clean_expr_dag_v2(term).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
    assert_eq!(&decoded, term);
    let result = checker().recheck_dag_v2(&input, target, &bytes);
    assert_eq!(
        result.is_ok(),
        accepted,
        "{}",
        result.err().map_or_else(String::new, |e| e.to_string())
    );
}

#[test]
fn countdown_arbitrary_fuel_replays_zero_one_three_with_real_backedges() {
    let target = module();
    for input in [0, 1, 3] {
        let phases = phases(input);
        assert_eq!(phases.len() as u64, 6 * input + 5);
        let reentries: Vec<_> = phases
            .iter()
            .filter(|p| p.block == 0 && p.pc == 0)
            .collect();
        assert_eq!(reentries.len() as u64, input + 1);
        for (ordinal, phase) in reentries.iter().enumerate() {
            assert_eq!(
                phase.bindings[0],
                (0, scalar(input - ordinal as u64)),
                "actual repeated header binding, not stale original input"
            );
        }
        let actual = Interpreter::with_module(&target)
            .execute_func(
                FuncId::new(0),
                [InterpretValue::int(Ty::U64, i128::from(input)).unwrap()],
            )
            .unwrap();
        assert_eq!(actual.returns[0].as_int().unwrap().as_unsigned(), 0);
        assert_eq!(actual.steps, phases.len() as u64);
        assert_eq!(actual.host_calls, 0);
        replay(&target, input, &assemble(&target, input, None, false), true);
    }
}

#[test]
fn partial_zero_surplus_prefixes_and_poisoned_terminal_keep_complete_world() {
    let target = module();
    let reflected = reflect_core_module_v1(&target, &[(FuncId::new(0), 4096)]).unwrap();
    let model = MachineModel::new(c("Nat"), &reflected, providers());
    for input in [0, 1, 3] {
        let source = Source::new(input, &model, terminal(173, 37));
        let proof = assemble(&target, input, None, false);
        for fuel in [0, 1, 4, 6 * input + 5, 6 * input + 9] {
            let index = fuel.min(6 * input + 5);
            let goal = eq(
                config_type(),
                model.run(&NatTerm::literal(fuel), initial(&model, input)),
                source.values[index as usize].clone(),
            );
            let term = Expr::app(proof.clone(), nat(fuel));
            let mut kernel = TypeChecker::new(checker().environment());
            kernel.set_heartbeat_limit(5_000_000);
            kernel.set_max_cache_entries(100_000);
            kernel.check_type(&term, &goal).unwrap();
            assert!(!kernel.heartbeat_spent());
        }
        let last = source.values.len() - 1;
        let poison = eq(
            c("Nat"),
            Expr::app(source.step.clone(), nat(last as u64)),
            nat(0),
        );
        TypeChecker::new(checker().environment())
            .check_type(&refl(c("Nat"), nat(0)), &poison)
            .unwrap();
        assert_ne!(source.values[0], terminal(173, 37));
    }
}

#[test]
fn forged_step_proof_does_not_gain_authority_from_matching_premise_metadata() {
    let target = module();
    replay(&target, 1, &assemble(&target, 1, None, true), false);
}

#[test]
fn changed_actual_arithmetic_branch_and_backedge_are_refuted() {
    for mutant in 0..3 {
        let mut target = module();
        let function = &mut target.functions[0];
        match mutant {
            0 => {
                let Inst::BinOp { op, .. } = &mut function.blocks[1].body[0].inst else {
                    panic!("real sub")
                };
                *op = BinOp::Add;
            }
            1 => {
                let Inst::CondBr {
                    then_target,
                    else_target,
                    ..
                } = &mut function.blocks[0].body[3].inst
                else {
                    panic!("real condbr")
                };
                std::mem::swap(then_target, else_target);
            }
            _ => {
                let Inst::Br { args, .. } = &mut function.blocks[1].body[1].inst else {
                    panic!("real backedge")
                };
                args[0] = ValueId::new(2);
            }
        }
        assert!(trust_ir_build::validate_module(&target).is_empty());
        replay(&target, 3, &assemble(&target, 3, None, false), false);
    }
}

#[test]
fn lost_final_memory_host_owner_or_wrong_outcome_is_refuted() {
    let target = module();
    let bad_owner = app(
        "IRByteConfigV1.halted",
        [
            c("Nat"),
            app("IROutcome.ret", [list("IRScalar", &[scalar(0)])]),
            world(false, 173, 37),
        ],
    );
    let bad_outcome = app(
        "IRByteConfigV1.halted",
        [
            c("Nat"),
            app("IROutcome.fuel_out", []),
            world(true, 173, 37),
        ],
    );
    for final_state in [terminal(174, 37), terminal(173, 38), bad_owner, bad_outcome] {
        replay(
            &target,
            1,
            &assemble(&target, 1, Some(final_state), false),
            false,
        );
    }
}

#[test]
fn changed_context_rejects_previously_built_proof() {
    let target = module();
    let proof = assemble(&target, 1, None, false);
    let mut changed = target.clone();
    let Inst::Const { value, .. } = &mut changed.functions[0].blocks[0].body[1].inst else {
        panic!("real one")
    };
    *value = trust_ir::Constant::Int(2);
    replay(&changed, 1, &proof, false);
}

#[test]
fn premise_shapes_and_exhausted_work_fail_without_refunds_or_caller_locals() {
    let target = module();
    let reflected = reflect_core_module_v1(&target, &[(FuncId::new(0), 4096)]).unwrap();
    let model = MachineModel::new(c("Nat"), &reflected, providers());
    let source = Source::new(0, &model, terminal(173, 37));
    let mut simulation = source.simulation();
    simulation.halt_agrees = PendingProof::candidate(
        simulation.halt_agreement_proposition(&model),
        c("True.intro"),
    );
    simulation.step_preserves = PendingProof::candidate(
        simulation.step_preservation_proposition(&model),
        c("True.intro"),
    );
    for cap in [1, 2, 10] {
        let mut scope = LocalScope::new();
        let mut bound = limits();
        bound.max_operations = cap;
        let mut a = Assembler::new(&mut scope, bound).unwrap();
        let attempt =
            || PendingProof::candidate(source.related(nat(0), initial(&model, 0)), c("True.intro"));
        assert!(
            a.simulate_prefix(
                &model,
                &simulation,
                &NatTerm::literal(0),
                nat(0),
                initial(&model, 0),
                attempt()
            )
            .err()
            .unwrap()
            .contains("operation budget")
        );
        assert_eq!(a.operations(), cap);
        assert_eq!(a.local_scope().allocated(), 0);
        assert!(
            a.simulate_prefix(
                &model,
                &simulation,
                &NatTerm::literal(0),
                nat(0),
                initial(&model, 0),
                attempt()
            )
            .is_err()
        );
        assert_eq!(a.operations(), cap);
    }
    for mismatch in 0..3 {
        let mut scope = LocalScope::new();
        let mut a = Assembler::new(&mut scope, limits()).unwrap();
        let mut wrong = simulation.clone();
        let mut initial_relation =
            PendingProof::candidate(source.related(nat(0), initial(&model, 0)), c("True.intro"));
        match mismatch {
            0 => wrong.halt_agrees = PendingProof::candidate(c("False"), c("True.intro")),
            1 => wrong.step_preserves = PendingProof::candidate(c("False"), c("True.intro")),
            _ => initial_relation = PendingProof::candidate(c("False"), c("True.intro")),
        }
        let error = a
            .simulate_prefix(
                &model,
                &wrong,
                &NatTerm::literal(0),
                nat(0),
                initial(&model, 0),
                initial_relation,
            )
            .err()
            .unwrap();
        assert!(
            error.contains(["halt agreement", "step preservation", "initial relation"][mismatch])
        );
        assert_eq!(a.operations(), 1);
        assert_eq!(a.local_scope().allocated(), 0);
    }
    // Even a definitionally identical provider expression is a different
    // candidate model identity. Old premises cannot be silently retargeted.
    // This is a shape/custody control, not an import-execution claim: this
    // countdown has no imports and its result is provider-independent.
    let retargeted = MachineModel::new(
        c("Nat"),
        &reflected,
        Expr::app(
            lam(app("IRByteProvidersV1", [c("Nat")]), Expr::bvar(0)),
            providers(),
        ),
    );
    let mut scope = LocalScope::new();
    let mut a = Assembler::new(&mut scope, limits()).unwrap();
    let error = a
        .simulate_prefix(
            &retargeted,
            &simulation,
            &NatTerm::literal(0),
            nat(0),
            initial(&retargeted, 0),
            PendingProof::candidate(
                source.related(nat(0), initial(&retargeted, 0)),
                c("True.intro"),
            ),
        )
        .err()
        .unwrap();
    assert!(error.contains("halt agreement"));
    assert_eq!(a.operations(), 1);
    assert_eq!(a.local_scope().allocated(), 0);
}
