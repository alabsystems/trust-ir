// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Validator <-> reference-interpreter differential property test.
//
// `crates/trust-ir/src/interpret.rs` is a 5000+ line reference interpreter
// for the bounded core subset, but it had only inline unit tests and no
// integration coverage. This file is the W5a "differential oracle" payoff
// that does not need a second reference implementation: a seeded generator
// (`common::exec_gen`, shared with the W5b Lean-execution oracle
// `lean_exec_differential.rs`, roadmap WS2.19, which runs the SAME corpus
// through the Lean executable semantics) emits a wide space of VALID
// scalar/control-flow modules and asserts three properties that tie the
// interpreter to the validator:
//
//   1. DETERMINISM. Executing the same function with the same arguments
//      twice yields byte-identical results (Ok outcome or Err code). The
//      interpreter is `Copy` and rebuilds fresh state per call, so any
//      observable nondeterminism (e.g. a HashMap creeping into value or
//      memory state, or address randomization) is a regression this catches.
//
//   2. NO STRUCTURAL ERROR ON VALIDATED IR. A module the validator accepts
//      must never make the interpreter report a structural-integrity code
//      (`MalformedInstruction` / `MissingValue` / `MissingBlock`). If it
//      does, the validator and interpreter disagree about well-formedness —
//      exactly the cross-checking a differential oracle exists to surface.
//      Runtime/capability codes (`UndefinedBehavior` from div-by-zero,
//      `Unsupported*`, `OutOfFuel`, `Panic`) are legitimate outcomes.
//
//   3. RETURN SHAPE. When a function returns `Ok`, the produced value count
//      matches the declared return arity and the value's type matches the
//      declared return type.
//
// A second corpus (WS2.12, `gen_module_host`) makes the functions CALL
// bodyless declarations and checks all three properties twice: without a host
// model (every such call is `UnsupportedCall`, the named fail-closed refusal —
// before the host-call hook it was `MissingBlock`, a property-2 violation) and
// with a zero-returning test host (host-assisted `Ok` runs, counted in
// `InterpretOutcome::host_calls`).
//
// The generator is intentionally focused on the interpreter's robust core
// (integer/bool arithmetic, comparisons, select, copy, and diamond control
// flow), plus BINDING FRAMES (roadmap WS2.8): `OpenFrame` / functional
// `BindSlot` chains and siblings / `LoadSlot` / `CloseFrame`, including a frame
// handle carried across the diamond through a `Ptr` block parameter, so
// property 2 covers the frame quartet the builder emits, plus ENUM LANE
// PROJECTIONS (roadmap WS2.2): every module carries
// `enum GenE { a(i32, bool), b(u64), c }`, and the generator constructs
// variants with `Const` and projects them with `extract_field` /
// `insert_field` at every lane/type pair the validator admits — mostly lanes
// of the ACTIVE variant, sometimes a lane only ANOTHER variant carries. The
// latter is undefined behaviour the validator cannot see statically, and
// property 2 then pins that the interpreter answers it with
// `UndefinedBehavior`, never a structural code. Memory, atomics, casts, and
// the other aggregates are exercised against the codec by
// `module_roundtrip_fuzz.rs`; here they would mostly surface as
// `Unsupported*` and dilute the execution signal. Floats are excluded (the
// generator never mints them) so results stay structurally comparable.

use trust_ir::constant::Constant;
use trust_ir::inst::{BinOp, BindingFrameDef, BindingSlot, ICmpOp};
use trust_ir::interpret::{
    HostCalls, HostState, InterpretError, InterpretErrorCode, InterpretOutcome, InterpretResult,
    InterpretValue, Interpreter,
};
use trust_ir::ty::{EnumDef, EnumVariant, FuncTy, Ty};
use trust_ir::value::{BindingFrameId, EnumId, FuncId, ValueId};
use trust_ir::{BodyGate, Endianness, Function, Inst, Module, StructPassingPolicy, TargetInfo};
use trust_ir_build::{ModuleBuilder, ValidationError};

mod common;
use common::Rng;
use common::exec_gen::{
    FnSpec, build_args, gen_enum_def, gen_inst, gen_module_exec, gen_signature, get_or_mint,
};

/// Structural-integrity codes that a validator-accepted module must never
/// trigger: the ones the scalar/CFG core can reach if (and only if) the
/// interpreter and validator disagree about IR well-formedness. The scalar
/// generator emits no calls; the bodyless-callee generator (WS2.12) does, and
/// holds a call to a declaration to the same rule — it is `UnsupportedCall`
/// (or host-served), never `MissingBlock`.
fn is_structural(code: InterpretErrorCode) -> bool {
    matches!(
        code,
        InterpretErrorCode::MalformedInstruction
            | InterpretErrorCode::MissingValue
            | InterpretErrorCode::MissingBlock
    )
}

/// Execution coverage of one seed, so the caller can assert the suite
/// exercises real execution and has not silently degraded into all-error
/// paths — for the scalar core, the binding frames and the enum projections.
#[derive(Default)]
struct ExecStats {
    /// Functions that executed to `Ok`.
    ok: u32,
    /// Functions containing a binding frame that executed to `Ok` (WS2.8).
    ok_with_frames: u32,
    /// Functions containing an enum lane projection that executed to `Ok`.
    ok_with_enum_projection: u32,
    /// Functions refused at run time for projecting a lane of a variant
    /// other than the active one (the dynamic half the validator admits).
    wrong_variant_ub: u32,
}

/// How many `extract_field` / `insert_field` a function carries (in this
/// generator, only enum projections emit them).
fn enum_projections(module: &Module, id: FuncId) -> usize {
    module.functions.iter().find(|f| f.id == id).map_or(0, |f| {
        f.blocks
            .iter()
            .flat_map(|b| &b.body)
            .filter(|n| matches!(n.inst, Inst::ExtractField { .. } | Inst::InsertField { .. }))
            .count()
    })
}

fn check_exec(seed: u64) -> ExecStats {
    let mut stats = ExecStats::default();
    let (module, specs) = gen_module_exec(seed);

    // Tie the differential to validation: the generator must only emit IR the
    // validator accepts, otherwise property 2 is vacuous.
    let errs = trust_ir_build::validate_module(&module);
    assert!(
        errs.is_empty(),
        "seed {seed}: generated module failed validation: {errs:?}"
    );

    let interp = Interpreter::with_module(&module);
    // A dedicated, fixed-seed RNG for argument values so the two executions
    // of a given function receive identical inputs.
    let mut arg_rng = Rng::new(seed ^ 0xA5A5_A5A5_A5A5_A5A5);

    for spec in &specs {
        let args = build_args(&spec.params, &mut arg_rng);

        let r1 = interp.execute_func(spec.id, args.clone());
        let r2 = interp.execute_func(spec.id, args.clone());
        assert_eq!(
            r1, r2,
            "seed {seed} fn {:?}: interpreter is nondeterministic across two identical calls",
            spec.id
        );

        match &r1 {
            Ok(outcome) => {
                stats.ok += 1;
                stats.ok_with_frames += u32::from(spec.frames);
                if enum_projections(&module, spec.id) > 0 {
                    stats.ok_with_enum_projection += 1;
                }
                let expected_arity = usize::from(spec.ret.is_some());
                assert_eq!(
                    outcome.returns.len(),
                    expected_arity,
                    "seed {seed} fn {:?}: return arity {} != declared {expected_arity}",
                    spec.id,
                    outcome.returns.len()
                );
                if let Some(ret_ty) = &spec.ret {
                    assert_eq!(
                        &outcome.returns[0].ty, ret_ty,
                        "seed {seed} fn {:?}: returned value type {} != declared {ret_ty}",
                        spec.id, outcome.returns[0].ty
                    );
                }
            }
            Err(e) => {
                if e.code == InterpretErrorCode::UndefinedBehavior
                    && e.message.contains("belongs to no field of active variant")
                {
                    stats.wrong_variant_ub += 1;
                }
                assert!(
                    !is_structural(e.code),
                    "seed {seed} fn {:?}: validator accepted the module but the \
                     interpreter reported a structural error {:?}: {}",
                    spec.id,
                    e.code,
                    e.message
                );
            }
        }
    }
    stats
}

// ---------------------------------------------------------------------------
// WS2.12 — bodyless callees. A module whose functions CALL bodyless
// declarations validates, and before the host-call hook the interpreter
// entered the declaration and reported `MissingBlock` — a structural code on
// validated IR, violating property 2. Such a call is now `UnsupportedCall`
// without a host model, and executes when a host serves it. Both runs are
// held to all three properties.
// ---------------------------------------------------------------------------

/// Bodyless External declarations need a pinned target (`TargetInfoRequired`);
/// this one selects the interpreter's canonical 64-bit little-endian model.
fn host_target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

/// A module of 1..=3 bodyless `ext{k}` declarations (palette signatures) and
/// 1..=3 straight-line callers, each making 1..=2 calls whose results feed the
/// pool. Drawn from its own RNG stream, so the scalar corpus above is unchanged.
fn gen_module_host(seed: u64) -> (Module, Vec<FnSpec>) {
    let mut rng = Rng::new(seed ^ 0x5753_3231_3200_0000);
    let mut mb = ModuleBuilder::new_with_target_info(format!("host_mod_{seed}"), host_target());
    let decls: Vec<(FuncId, Vec<Ty>, Option<Ty>)> = (0..1 + rng.bounded(3))
        .map(|k| {
            let (params, ret) = gen_signature(&mut rng);
            let ft = mb.add_func_type(params.clone(), ret.iter().cloned().collect());
            (mb.declare_function(format!("ext{k}"), ft), params, ret)
        })
        .collect();
    let mut specs = Vec::new();
    for idx in 0..1 + rng.bounded(3) {
        let (params, ret) = gen_signature(&mut rng);
        let returns = ret.iter().cloned().collect::<Vec<_>>();
        let ft = mb.add_func_type(params.clone(), returns);
        let mut fb = mb.function(format!("caller{idx}"), ft);
        let entry = fb.create_block();
        let mut pool: Vec<(ValueId, Ty)> = Vec::new();
        for p in &params {
            let v = fb.add_block_param(entry, p.clone());
            pool.push((v, p.clone()));
        }
        fb.switch_to_block(entry);
        for _ in 0..1 + rng.bounded(2) {
            for _ in 0..rng.bounded(4) {
                gen_inst(&mut fb, &mut rng, &mut pool);
            }
            let (callee, callee_params, callee_ret) =
                &decls[rng.bounded(decls.len() as u32) as usize];
            let args: Vec<ValueId> = callee_params
                .iter()
                .map(|t| get_or_mint(&mut fb, &mut rng, &mut pool, t))
                .collect();
            match callee_ret {
                Some(t) => {
                    let v = fb.call(*callee, args);
                    pool.push((v, t.clone()));
                }
                None => fb.call_void(*callee, args),
            }
        }
        for _ in 0..rng.bounded(4) {
            gen_inst(&mut fb, &mut rng, &mut pool);
        }
        match &ret {
            None => fb.ret(vec![]),
            Some(t) => {
                let v = get_or_mint(&mut fb, &mut rng, &mut pool, t);
                fb.ret(vec![v]);
            }
        }
        specs.push(FnSpec {
            id: fb.build(),
            params,
            ret,
            frames: false,
        });
    }
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.add_enum(gen_enum_def());
    (module, specs)
}

/// A host that serves every declaration with the zero of each declared return
/// type (`0` / `false`), reading the signature from the module. A TEST model.
struct ZeroHost<'m>(&'m Module);

impl HostCalls for ZeroHost<'_> {
    fn call(
        &self,
        callee: &Function,
        sig: &FuncTy,
        _args: &[InterpretValue],
        _host: &mut HostState,
    ) -> Option<InterpretResult<Vec<InterpretValue>>> {
        // The interpreter hands over the declared signature; it must be the
        // one the module records for the callee.
        assert_eq!(Some(sig), self.0.func_type(callee.ty));
        Some(
            sig.returns
                .iter()
                .map(|t| match t {
                    Ty::Bool => Ok(InterpretValue::bool(false)),
                    other => InterpretValue::int(other.clone(), 0),
                })
                .collect(),
        )
    }
}

/// Coverage of the bodyless-callee corpus.
#[derive(Default)]
struct HostStats {
    /// Runs without a host refused at a declaration with `UnsupportedCall`.
    unsupported_call: u32,
    /// Runs with the zero host that executed to `Ok` host-assisted.
    ok_host_assisted: u32,
}

/// Properties 1-3 for one run configuration; returns the result for tallying.
fn check_run(
    seed: u64,
    interp: Interpreter<'_>,
    spec: &FnSpec,
    args: &[InterpretValue],
) -> Result<InterpretOutcome, InterpretError> {
    let r1 = interp.execute_func(spec.id, args.to_vec());
    let r2 = interp.execute_func(spec.id, args.to_vec());
    assert_eq!(r1, r2, "seed {seed} fn {:?}: nondeterministic", spec.id);
    match &r1 {
        Ok(outcome) => {
            assert_eq!(
                outcome.returns.len(),
                usize::from(spec.ret.is_some()),
                "seed {seed} fn {:?}: return arity",
                spec.id
            );
            if let Some(ret_ty) = &spec.ret {
                assert_eq!(
                    &outcome.returns[0].ty, ret_ty,
                    "seed {seed} fn {:?}",
                    spec.id
                );
            }
        }
        Err(e) => assert!(
            !is_structural(e.code),
            "seed {seed} fn {:?}: validator accepted the module but the interpreter \
             reported a structural error {:?}: {}",
            spec.id,
            e.code,
            e.message
        ),
    }
    r1
}

fn check_host_exec(seed: u64) -> HostStats {
    let mut stats = HostStats::default();
    let (module, specs) = gen_module_host(seed);
    let errs = trust_ir_build::validate_module(&module);
    assert!(
        errs.is_empty(),
        "seed {seed}: host module failed validation: {errs:?}"
    );
    let zero = ZeroHost(&module);
    let mut arg_rng = Rng::new(seed ^ 0x5A5A_5A5A_5A5A_5A5A);
    for spec in &specs {
        let args = build_args(&spec.params, &mut arg_rng);
        match check_run(seed, Interpreter::with_module(&module), spec, &args) {
            Ok(outcome) => panic!(
                "seed {seed} fn {:?}: every caller reaches a declaration, but it ran to Ok \
                 without a host ({outcome:?})",
                spec.id
            ),
            Err(e) if e.code == InterpretErrorCode::UnsupportedCall => {
                assert!(e.message.contains("no host model"), "{e}");
                stats.unsupported_call += 1;
            }
            Err(_) => {}
        }
        let served = Interpreter::with_module(&module).with_host(&zero);
        if let Ok(outcome) = check_run(seed, served, spec, &args) {
            assert!(
                outcome.host_calls >= 1,
                "seed {seed} fn {:?}: a host-assisted run reports no host call",
                spec.id
            );
            stats.ok_host_assisted += 1;
        }
    }
    stats
}

#[test]
fn interpret_differential_bodyless_callees() {
    let mut totals = HostStats::default();
    for seed in 1..=512u64 {
        let stats = check_host_exec(seed);
        totals.unsupported_call += stats.unsupported_call;
        totals.ok_host_assisted += stats.ok_host_assisted;
    }
    // Both halves must actually be exercised, not routed onto other errors.
    assert!(
        totals.unsupported_call > 400,
        "only {} callers reached a declaration's UnsupportedCall",
        totals.unsupported_call
    );
    assert!(
        totals.ok_host_assisted > 400,
        "only {} callers executed host-assisted to Ok",
        totals.ok_host_assisted
    );
}

/// Build `fn() -> i32 { binop(op, i32, a, b) }`, execute it, and return the
/// i32 bit-pattern of the result (the interpreter's computed value).
fn run_i32_binop(op: BinOp, a: i32, b: i32) -> u32 {
    let mut mb = ModuleBuilder::new("oracle");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let va = fb.iconst(Ty::I32, a as i128);
    let vb = fb.iconst(Ty::I32, b as i128);
    let r = fb.binop(op, Ty::I32, va, vb);
    fb.ret(vec![r]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let out = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .expect("oracle binop executes");
    out.returns[0].as_int().expect("int result").as_unsigned() as u32
}

/// SEMANTIC ORACLE (closes #83): the prior differential checked determinism,
/// no-structural-error, and return-shape but NEVER a single arithmetic VALUE,
/// and excluded shifts. Here plain Rust i32/u32 arithmetic is an INDEPENDENT
/// second reference implementation; every case (incl. shifts and negative
/// operands) cross-checks the interpreter's computed value against it.
#[test]
fn interpreter_arithmetic_matches_independent_rust_oracle() {
    // (op, a, b, expected-as-i32). Expected computed by hand/Rust as the oracle.
    let cases: &[(BinOp, i32, i32, i32)] = &[
        (BinOp::Add, 2147483647, 1, i32::MIN), // wraps
        (BinOp::Add, -5, 8, 3),
        (BinOp::Sub, i32::MIN, 1, i32::MAX), // wraps
        (BinOp::Mul, 65536, 65536, 0),       // overflow wraps to 0
        (BinOp::Mul, -3, 7, -21),
        (BinOp::SDiv, -7, 2, -3), // truncates toward zero
        (BinOp::SDiv, 7, -2, -3),
        (BinOp::SRem, -7, 3, -1), // sign of dividend
        (BinOp::SRem, 7, -3, 1),
        (BinOp::UDiv, -1, 2, (u32::MAX / 2) as i32), // -1 == u32::MAX
        (BinOp::URem, -1, 3, (u32::MAX % 3) as i32),
        (BinOp::And, -1, 0x0F0F0F0F, 0x0F0F0F0F),
        (BinOp::Or, 0x00FF00FF, 0xFF00FF00u32 as i32, -1),
        (BinOp::Xor, -1, -1, 0),
        (BinOp::Shl, 1, 31, i32::MIN),  // 1<<31
        (BinOp::LShr, -1, 1, i32::MAX), // logical: 0x7FFFFFFF
        (BinOp::AShr, -8, 1, -4),       // arithmetic: floor
        (BinOp::AShr, -1, 31, -1),      // sign-extends
    ];
    for &(op, a, b, expected) in cases {
        let got = run_i32_binop(op, a, b);
        assert_eq!(
            got, expected as u32,
            "interpreter {op:?}({a}, {b}) = {} (i32 {}), oracle expected {expected}",
            got, got as i32
        );
    }
}

#[test]
fn interpret_differential() {
    // Fixed seed range -> deterministic, never flakes.
    let mut total_ok = 0u32;
    let mut frame_ok = 0u32;
    let mut ok_with_enum = 0u32;
    let mut wrong_variant_ub = 0u32;
    for seed in 1..=1024u64 {
        let stats = check_exec(seed);
        total_ok += stats.ok;
        frame_ok += stats.ok_with_frames;
        ok_with_enum += stats.ok_with_enum_projection;
        wrong_variant_ub += stats.wrong_variant_ub;
    }
    // The enum projections are exercised on BOTH sides of the static/dynamic
    // split (WS2.2): honest lanes execute to Ok, and wrong-variant lanes the
    // validator admitted reach the interpreter's named UB.
    assert!(
        ok_with_enum > 500,
        "only {ok_with_enum} functions with an enum projection executed to Ok"
    );
    assert!(
        wrong_variant_ub > 100,
        "only {wrong_variant_ub} wrong-variant projections reached the interpreter's UB"
    );
    // WS2.8: the binding-frame share of the corpus must actually EXECUTE.
    // Before the functional `BindSlot` every builder-emitted bind failed
    // property 2 (`MalformedInstruction`), so this floor also guards against
    // the generator quietly routing frames onto an error path.
    assert!(
        frame_ok > 400,
        "only {frame_ok} binding-frame functions executed to Ok; the generator \
         is no longer exercising binding frames"
    );
    // Guard the test's own value: if a future generator change degraded into
    // all-error paths, the Ok-branch assertions (return arity/type) would
    // never run and the differential would be vacuous. The vast majority of
    // generated functions execute cleanly, so this floor is very loose.
    assert!(
        total_ok > 500,
        "only {total_ok} functions executed to Ok; the generator is no longer \
         exercising real interpreter execution"
    );
}

// ---------------------------------------------------------------------------
// WS2.8 — `BindSlot` is the FUNCTIONAL frame update (closes F-038).
//
// Every other party already specified it: `inst.rs` ("the result is a new
// frame handle ... previous frame handles remain valid; loading from them
// returns their prior slot values"), Lean `semBindSlot` (`bindFresh` of the
// updated frame), `FunctionBuilder::bind_slot` (one result), and the
// validator's result table (one `Ptr` result, `InstrResultArityMismatch`
// otherwise). The reference interpreter wrote in place and bound ZERO
// results, so every builder-emitted `bind_slot` failed property 2 above with
// `MalformedInstruction` ("node declares 1, interpreter produced 0") —
// completeness-critic probe `c2_format_probes.rs::binding_frames`, ratchet
// row `crit.unex08`. Frame handles now carry their own slot snapshot and the
// `OpenFrame` lineage they descend from; `CloseFrame` through any handle
// closes the lineage.
// ---------------------------------------------------------------------------

/// Which frame handle the probe's `LoadSlot` reads through.
#[derive(Clone, Copy)]
enum ReadVia {
    /// The handle `bind_slot` RETURNED (the documented shape).
    BoundHandle,
    /// The handle passed INTO `bind_slot` (the critic probe's literal shape).
    PreBindHandle,
}

/// The critic probe: `program() -> u64` opens a one-slot `U64` frame, binds
/// 41 into slot 0, reads the slot back through `via`, adds 1, closes, returns.
fn critic_frames_probe(via: ReadVia) -> Module {
    let mut mb = ModuleBuilder::new("critic_frames");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let opened = fb.open_frame(BindingFrameDef::new(
        BindingFrameId::new(0),
        "exists_i",
        vec![BindingSlot::new("i", Ty::U64)],
    ));
    let forty_one = fb.uconst(Ty::U64, 41);
    let bound = fb.bind_slot(opened, 0, forty_one);
    let read_from = match via {
        ReadVia::BoundHandle => bound,
        ReadVia::PreBindHandle => opened,
    };
    let loaded = fb.load_slot(read_from, 0, Ty::U64);
    let one = fb.uconst(Ty::U64, 1);
    let sum = fb.add(Ty::U64, loaded, one);
    fb.close_frame(read_from);
    fb.ret(vec![sum]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Every return of `program` as a `u64`.
fn run_u64s(module: &Module) -> Result<Vec<u64>, InterpretError> {
    let outcome = Interpreter::with_module(module).execute_func(FuncId::new(0), [])?;
    Ok(outcome
        .returns
        .iter()
        .map(|value| value.as_int().expect("integer result").as_unsigned() as u64)
        .collect())
}

/// The consumer pipeline: validate, and execute ONLY a module that validates.
fn validate_then_run(module: &Module) -> Result<Vec<u64>, Vec<ValidationError>> {
    let errors = trust_ir_build::validate_module(module);
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(run_u64s(module).expect("a validated frame module executes"))
}

fn bind_slot_index(module: &Module) -> usize {
    module.functions[0].blocks[0]
        .body
        .iter()
        .position(|node| matches!(node.inst, Inst::BindSlot { .. }))
        .expect("the builder emitted a bind_slot")
}

fn assert_ub(error: &InterpretError, reason: &str) {
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{error}");
    assert!(
        error.to_string().contains(reason),
        "expected UB naming {reason:?}, got: {error}"
    );
}

/// Positive: the critic probe, read through the handle `bind_slot` returned
/// (the shape every documented lowering uses), carries ONE `Ptr` result,
/// validates, is inside the proven subset, passes the codegen validator, and
/// executes to the bound value + 1.
#[test]
fn ws2_8_critic_binding_frames_probe_executes() {
    let mut module = critic_frames_probe(ReadVia::BoundHandle);
    let bind = &module.functions[0].blocks[0].body[bind_slot_index(&module)];
    assert_eq!(bind.results.len(), 1, "bind_slot declares one result");
    assert_eq!(bind.result_tys(&module), vec![Ty::Ptr]);
    assert_eq!(validate_then_run(&module), Ok(vec![42]));
    assert!(
        module.check_conformance_subset().is_ok(),
        "binding frames are inside the proven subset"
    );
    // The codegen validator additionally demands the v41 codegen license,
    // orthogonal to binding frames (the probe carried none and reported
    // exactly that one row); grant it so the assertion is about frame ops.
    // The grant names an authority outside `EVIDENCE_BOUND_GATE_AUTHORITIES`:
    // since WS1.5 `clean-kernel-tv` must be backed by a kernel-rechecked TV
    // certificate, which a binding-frame probe has no reason to carry.
    module.functions[0].body_gate = Some(BodyGate::Gated {
        authority: "trust-direct-lane-structural".to_string(),
        evidence: None,
    });
    assert_eq!(trust_ir_build::validate_module_for_codegen(&module), []);
}

/// Negative twin (one mutation: the load reads the PRE-bind handle — the
/// probe's literal shape): legal IR, so it validates, but that handle's own
/// slot was never bound, so the interpreter does NOT serve the bind made
/// through the other handle (the in-place model this increment retires). An
/// unbound slot reads as scalar POISON (roadmap WS2.10, Lean's `undef`), so
/// the read itself succeeds and the `add` that inspects it is the UB — never
/// 41 + 1.
#[test]
fn ws2_8_pre_bind_handle_reads_its_own_unbound_slot() {
    let module = critic_frames_probe(ReadVia::PreBindHandle);
    assert_eq!(trust_ir_build::validate_module(&module), []);
    let error = run_u64s(&module).expect_err("the pre-bind handle's slot is unbound");
    assert_ub(&error, "use of an uninitialized value");
}

/// The probe with `bind_slot`'s result stripped: the zero-result node the
/// retired in-place interpreter executed. The downstream uses are routed back
/// to the opened handle so the ONLY defect left is the missing result (else a
/// dangling-value error would mask the arity rule).
fn void_bind_slot_probe() -> Module {
    let mut void_bind = critic_frames_probe(ReadVia::BoundHandle);
    let idx = bind_slot_index(&void_bind);
    let body = &mut void_bind.functions[0].blocks[0].body;
    let opened = body[0].results[0];
    let stale = body[idx].results[0];
    body[idx].results.clear();
    for node in body.iter_mut() {
        match &mut node.inst {
            Inst::LoadSlot { frame, .. } | Inst::CloseFrame { frame } if *frame == stale => {
                *frame = opened;
            }
            _ => {}
        }
    }
    void_bind
}

/// Mutation control: a hand-mutated `bind_slot` declaring 0 (or 2) results is
/// refused by the validator by name and therefore never executed — the
/// validator and interpreter now agree on ONE. The interpreter, driven
/// directly, refuses the same node as malformed rather than tolerating it.
#[test]
fn ws2_8_result_arity_mismatched_bind_slot_is_refused_not_executed() {
    let void_bind = void_bind_slot_probe();
    let refused = validate_then_run(&void_bind).expect_err("a void bind_slot must not validate");
    assert!(
        refused.contains(&ValidationError::InstrResultArityMismatch {
            block: 0,
            op: "bind_slot".to_string(),
            expected: 1,
            actual: 0,
        }),
        "expected InstrResultArityMismatch(bind_slot, 1, 0), got {refused:?}"
    );
    let error = run_u64s(&void_bind).expect_err("a void bind_slot is malformed");
    assert_eq!(error.code, InterpretErrorCode::MalformedInstruction);
    assert!(
        error
            .to_string()
            .contains("node declares 0, interpreter produced 1"),
        "unexpected interpreter error: {error}"
    );

    // 2 results: the arity rule is exact, not a lower bound.
    let mut two_results = critic_frames_probe(ReadVia::BoundHandle);
    let idx = bind_slot_index(&two_results);
    two_results.functions[0].blocks[0].body[idx]
        .results
        .push(ValueId::new(900));
    let refused =
        validate_then_run(&two_results).expect_err("a two-result bind_slot must not validate");
    assert!(
        refused.contains(&ValidationError::InstrResultArityMismatch {
            block: 0,
            op: "bind_slot".to_string(),
            expected: 1,
            actual: 2,
        }),
        "expected InstrResultArityMismatch(bind_slot, 1, 2), got {refused:?}"
    );
    let error = run_u64s(&two_results).expect_err("a two-result bind_slot is malformed");
    assert_eq!(error.code, InterpretErrorCode::MalformedInstruction);

    // And the control does not over-refuse: the unmutated module runs.
    assert_eq!(
        validate_then_run(&critic_frames_probe(ReadVia::BoundHandle)),
        Ok(vec![42])
    );
}

/// Two binds from the SAME handle are two independent versions of the frame:
/// `%a` holds 7 and `%b` holds 9. An in-place model that merely grew a result
/// would make them one mutated frame and read `(9, 9)`.
#[test]
fn ws2_8_sibling_binds_from_one_handle_do_not_alias() {
    let mut mb = ModuleBuilder::new("binding_frame_siblings");
    let sig = mb.add_func_type(vec![], vec![Ty::U64, Ty::U64]);
    let mut fb = mb.function("program", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let opened = fb.open_frame(BindingFrameDef::new(
        BindingFrameId::new(0),
        "exists_i",
        vec![BindingSlot::new("i", Ty::U64)],
    ));
    let seven = fb.uconst(Ty::U64, 7);
    let nine = fb.uconst(Ty::U64, 9);
    let a = fb.bind_slot(opened, 0, seven);
    let b = fb.bind_slot(opened, 0, nine);
    let from_a = fb.load_slot(a, 0, Ty::U64);
    let from_b = fb.load_slot(b, 0, Ty::U64);
    fb.close_frame(a);
    fb.ret(vec![from_a, from_b]);
    fb.build();
    assert_eq!(
        validate_then_run(&mb.build().expect("ModuleBuilder::build: test fixture")),
        Ok(vec![7, 9])
    );
}

/// `CloseFrame` closes the LINEAGE, whichever handle names it. After closing
/// through the bound handle `%f1`, the pre-bind handle `%f0` is dead too: a
/// `LoadSlot` through it is UB ("frame is not open"), and a second close
/// through a sibling is the double close. The unmutated twin (load BEFORE
/// the close) runs.
///
/// Both same-block mutants are rejected by lineage-aware validation. The
/// reference interpreter independently refuses their closed-lineage accesses.
/// This does not claim CFG-wide lifetime validation or a Lean equivalence proof:
/// Lean's CloseFrame remains a no-op outside the well-formed input contract.
#[test]
fn ws2_8_close_through_any_handle_closes_the_lineage() {
    /// `load_after_close`: read `%f0` after closing via `%f1`.
    /// `close_twice`: also close via `%f0` (same lineage).
    fn module(load_after_close: bool, close_twice: bool) -> Module {
        let mut mb = ModuleBuilder::new("binding_frame_lineage");
        let sig = mb.add_func_type(vec![], vec![Ty::U64]);
        let mut fb = mb.function("program", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let f0 = fb.open_frame(BindingFrameDef::new(
            BindingFrameId::new(0),
            "q",
            vec![
                BindingSlot::new("i", Ty::U64),
                BindingSlot::new("k", Ty::U64),
            ],
        ));
        let five = fb.uconst(Ty::U64, 5);
        let f0k = fb.bind_slot(f0, 1, five);
        let six = fb.uconst(Ty::U64, 6);
        let f1 = fb.bind_slot(f0k, 0, six);
        let early = (!load_after_close).then(|| fb.load_slot(f0k, 1, Ty::U64));
        fb.close_frame(f1);
        let loaded = early.unwrap_or_else(|| fb.load_slot(f0k, 1, Ty::U64));
        if close_twice {
            fb.close_frame(f0k);
        }
        fb.ret(vec![loaded]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    assert_eq!(validate_then_run(&module(false, false)), Ok(vec![5]));

    let after_close = module(true, false);
    assert!(
        trust_ir_build::validate_module(&after_close)
            .iter()
            .any(|error| matches!(error, ValidationError::BindingUseAfterClose { .. }))
    );
    assert_ub(
        &run_u64s(&after_close).expect_err("the lineage is closed"),
        "LoadSlot: frame is not open",
    );

    let twice = module(false, true);
    assert!(
        trust_ir_build::validate_module(&twice)
            .iter()
            .any(|error| matches!(error, ValidationError::BindingUseAfterClose { .. }))
    );
    assert_ub(
        &run_u64s(&twice).expect_err("second close of one lineage"),
        "CloseFrame: frame is not open (double close)",
    );
}

/// A loop that carries the frame handle through `Ptr` block parameters, the
/// documented `\E i \in S` shape: a two-slot frame `{i, k}` binds `k = 7`
/// once before the loop, then rebinds `i` each iteration for `i in 0..3`.
/// `carry_new_handle = false` is the mutation: the back edge passes the
/// handle the body bound INTO, not the one it got back.
fn loop_frame_module(carry_new_handle: bool) -> Module {
    let mut mb = ModuleBuilder::new("binding_frame_loop");
    let sig = mb.add_func_type(vec![], vec![Ty::U64, Ty::U64]);
    let mut fb = mb.function("program", sig);
    let entry = fb.create_block();
    let header = fb.create_block();
    let header_frame = fb.add_block_param(header, Ty::Ptr);
    let header_i = fb.add_block_param(header, Ty::U64);
    let body = fb.create_block();
    let body_frame = fb.add_block_param(body, Ty::Ptr);
    let body_i = fb.add_block_param(body, Ty::U64);
    let exit = fb.create_block();
    let exit_frame = fb.add_block_param(exit, Ty::Ptr);

    fb.switch_to_block(entry);
    let opened = fb.open_frame(BindingFrameDef::new(
        BindingFrameId::new(0),
        "exists_i",
        vec![
            BindingSlot::new("i", Ty::U64),
            BindingSlot::new("k", Ty::U64),
        ],
    ));
    let seven = fb.uconst(Ty::U64, 7);
    let with_k = fb.bind_slot(opened, 1, seven);
    let zero = fb.uconst(Ty::U64, 0);
    fb.br(header, vec![with_k, zero]);

    fb.switch_to_block(header);
    let three = fb.uconst(Ty::U64, 3);
    let more = fb.icmp(ICmpOp::Ult, Ty::U64, header_i, three);
    fb.condbr(
        more,
        body,
        vec![header_frame, header_i],
        exit,
        vec![header_frame],
    );

    fb.switch_to_block(body);
    let rebound = fb.bind_slot(body_frame, 0, body_i);
    let one = fb.uconst(Ty::U64, 1);
    let next_i = fb.add(Ty::U64, body_i, one);
    let carried = if carry_new_handle {
        rebound
    } else {
        body_frame
    };
    fb.br(header, vec![carried, next_i]);

    fb.switch_to_block(exit);
    let last_i = fb.load_slot(exit_frame, 0, Ty::U64);
    let k = fb.load_slot(exit_frame, 1, Ty::U64);
    fb.close_frame(exit_frame);
    fb.ret(vec![last_i, k]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A loop-carried handle: the copy a bind makes keeps the OTHER slots (`k`
/// survives three rebinds of `i`), and the last bound `i` is the one the exit
/// reads. Handles are typed `Ptr` (the validator's typing), so they cross the
/// `Ptr` block parameters; typed `Unit` they failed the first edge with
/// `TypeError`. The mutation (back edge carries the pre-bind handle) is legal
/// SSA and validates, but no bind reaches the exit's handle, so slot `i` is
/// unbound there: it reads as poison (WS2.10), and returning it is the
/// inspection that faults.
#[test]
fn ws2_8_loop_carried_frame_handle_keeps_other_slots() {
    assert_eq!(validate_then_run(&loop_frame_module(true)), Ok(vec![2, 7]));

    let mutated = loop_frame_module(false);
    assert_eq!(trust_ir_build::validate_module(&mutated), []);
    assert_ub(
        &run_u64s(&mutated).expect_err("slot i never bound on the carried handle"),
        "Call returns: use of an uninitialized value",
    );
}

// ---------------------------------------------------------------------------
// Ratchet row `crit.unex08` (F-038), ported. Source: the completeness critic's
// `c2_format_probes.rs::binding_frames` (archived under
// `reports/2026-09-17-two-language-proof-program/critic/crate/tests/`), which
// printed one measurement vector for a builder-emitted binding frame: the
// validator's verdict, an interpreter run, the binary / text / JSON
// round-trips, proven-subset membership, and the codegen validator's verdict.
//
// GAP, as measured 2026-09-17: the module validated, round-tripped and sat
// INSIDE the proven subset, yet the interpreter refused it as malformed
// ("instruction result arity mismatch: node declares 1, interpreter produced
// 0"). Builder, validator and interpreter disagreed on `BindSlot`'s result
// arity. The row is PASS now. All three agree on ONE `Ptr` result, the
// agreement survives every transport (MessagePack is added to the critic's
// three), and the critic's LITERAL shape is answered by the functional
// semantics Lean specifies, never by the arity refusal. That shape reads the
// slot through the handle passed INTO `bind_slot` and discards the one it
// returned. Lean's `initFrame` seeds every slot `.undef`, so that handle's
// slot is unbound: WS2.10 poison, and inspecting it is UB.
// ---------------------------------------------------------------------------

/// `module` as built, then decoded back through each of the four transports.
/// Binary, JSON and MessagePack must be lossless. Text is decoded in BOTH of
/// its spellings: the canonical one must rebuild the canonical module, and
/// the exact transport one (`text_checked`, what `trust-ir convert --to
/// text` writes) must rebuild the module itself, sparse value ids included.
/// A transport that dropped or invented a `bind_slot` result would fail
/// here, before any image is judged.
fn crit_unex08_images(module: &Module) -> Vec<(&'static str, Module)> {
    let binary = trust_ir::binary::deserialize_module(
        &trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture"),
    )
    .expect("binary decodes");
    assert_eq!(&binary, module, "binary round-trip is lossless");
    let text =
        trust_ir::format::canonical_checked(module).expect("binding frames are text-lossless");
    let parsed = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|e| panic!("text parses: {e}\n{text}"));
    assert_eq!(
        parsed,
        trust_ir::format::canonicalize(module),
        "text rebuilds the canonical module"
    );
    let exact_text =
        trust_ir::format::text_checked(module).expect("binding frames are text-lossless");
    let exact = trust_ir::parser::parse_module(&exact_text)
        .unwrap_or_else(|e| panic!("exact text parses: {e}\n{exact_text}"));
    assert_eq!(&exact, module, "exact text round-trip is lossless");
    let json: Module = serde_json::from_str(&serde_json::to_string(module).expect("JSON encodes"))
        .expect("JSON decodes");
    assert_eq!(&json, module, "JSON round-trip is lossless");
    let msgpack: Module =
        rmp_serde::from_slice(&rmp_serde::to_vec(module).expect("MessagePack encodes"))
            .expect("MessagePack decodes");
    assert_eq!(&msgpack, module, "MessagePack round-trip is lossless");
    vec![
        ("built", module.clone()),
        ("binary", binary),
        ("text", parsed),
        ("text-exact", exact),
        ("json", json),
        ("msgpack", msgpack),
    ]
}

/// The static half of the agreement, for one image: `bind_slot` declares ONE
/// `Ptr` result, the image validates and sits inside the proven subset, and
/// the codegen validator's only refusal is the codegen license the probe
/// never carried (no arity row). Once licensed, it has none.
fn crit_unex08_assert_static_agreement(format: &str, image: &Module) {
    let bind = &image.functions[0].blocks[0].body[bind_slot_index(image)];
    // Two separate facts. `result_tys` reads the op's result TABLE (the
    // instruction kind alone decides it), so it cannot see the node; the
    // node's own declared arity is `results`.
    assert_eq!(
        bind.results.len(),
        1,
        "{format}: the bind_slot node declares one result"
    );
    assert_eq!(
        bind.result_tys(image),
        vec![Ty::Ptr],
        "{format}: bind_slot's result table is one Ptr"
    );
    assert_eq!(trust_ir_build::validate_module(image), [], "{format}");
    assert!(
        image.check_conformance_subset().is_ok(),
        "{format}: binding frames are inside the proven subset"
    );
    assert_eq!(
        trust_ir_build::validate_module_for_codegen(image),
        [ValidationError::UnlicensedBodyForCodegen {
            function: 0,
            name: "program".to_string(),
        }],
        "{format}: unlicensed, the license row is the only codegen refusal"
    );
    // An authority outside `EVIDENCE_BOUND_GATE_AUTHORITIES`, as in
    // `ws2_8_critic_binding_frames_probe_executes`: the grant is orthogonal
    // to binding frames and needs no kernel-rechecked TV certificate.
    let mut licensed = image.clone();
    licensed.functions[0].body_gate = Some(BodyGate::Gated {
        authority: "trust-direct-lane-structural".to_string(),
        evidence: None,
    });
    assert_eq!(
        trust_ir_build::validate_module_for_codegen(&licensed),
        [],
        "{format}: licensed, binding frames pass the codegen validator"
    );
}

/// `crit.unex08` positive (PASS). The documented shape reads the slot
/// through the handle `bind_slot` RETURNED. In the built module and in every
/// decoded image it holds the static agreement and executes to 41 + 1.
#[test]
fn crit_unex08_builder_binding_frames_agree_in_every_format() {
    for (format, image) in crit_unex08_images(&critic_frames_probe(ReadVia::BoundHandle)) {
        crit_unex08_assert_static_agreement(format, &image);
        assert_eq!(validate_then_run(&image), Ok(vec![42]), "{format}");
    }
}

/// `crit.unex08` negative twin. One mutation: the critic's LITERAL shape,
/// where the load reads the PRE-bind handle. That is legal IR, so it holds
/// the same static agreement as the positive. At execution the built module
/// and every decoded image are refused by the named poison-inspection UB:
/// the pre-bind handle's own slot is unbound, the load transports the
/// poison, and the `add` inspects it. The answer is never the GAP's
/// structural `MalformedInstruction` arity refusal, and never 41 + 1.
#[test]
fn crit_unex08_literal_probe_is_refused_by_poison_inspection_not_arity() {
    for (format, image) in crit_unex08_images(&critic_frames_probe(ReadVia::PreBindHandle)) {
        crit_unex08_assert_static_agreement(format, &image);
        let error = run_u64s(&image).expect_err("the pre-bind handle's slot is unbound");
        assert_ne!(
            error.code,
            InterpretErrorCode::MalformedInstruction,
            "{format}: {error}"
        );
        // The `add`'s integer read is the inspection. The `LoadSlot` only
        // transported the poison, so the refusal never names it.
        assert_ub(&error, "integer use: use of an uninitialized value");
        assert!(!error.to_string().contains("LoadSlot"), "{format}: {error}");
    }
}

/// `crit.unex08` mutation control: the zero-result `bind_slot`, the node
/// shape the retired in-place interpreter executed. It is refused by name in
/// the built module and in every decoded image, so no transport repairs or
/// launders the arity. The validator reports `InstrResultArityMismatch`, so a
/// consumer never runs the node. The interpreter, driven directly, refuses it
/// as malformed instead of tolerating it. This is the sensor for the GAP
/// reopening from either side.
#[test]
fn crit_unex08_zero_result_bind_slot_is_refused_in_every_format() {
    for (format, image) in crit_unex08_images(&void_bind_slot_probe()) {
        crit_unex08_assert_arity_refused(format, &image, 0);
    }
}

/// One image whose `bind_slot` node declares `declared` results, not one:
/// the declaration survived the transport, the validator refuses it by name,
/// and the interpreter, driven directly, refuses it as malformed.
fn crit_unex08_assert_arity_refused(format: &str, image: &Module, declared: usize) {
    let bind = &image.functions[0].blocks[0].body[bind_slot_index(image)];
    assert_eq!(
        bind.results.len(),
        declared,
        "{format}: the mutation survives"
    );
    let refused = validate_then_run(image).expect_err("a mis-arity bind_slot must not validate");
    assert!(
        refused.contains(&ValidationError::InstrResultArityMismatch {
            block: 0,
            op: "bind_slot".to_string(),
            expected: 1,
            actual: declared,
        }),
        "{format}: expected InstrResultArityMismatch(bind_slot, 1, {declared}), got {refused:?}"
    );
    let error = run_u64s(image).expect_err("a mis-arity bind_slot is malformed");
    assert_eq!(
        error.code,
        InterpretErrorCode::MalformedInstruction,
        "{format}: {error}"
    );
    assert!(
        error
            .to_string()
            .contains(&format!("node declares {declared}, interpreter produced 1")),
        "{format}: unexpected interpreter error: {error}"
    );
}

/// Review twin of the mutation control: the rule is EXACT, not a lower
/// bound, and that holds after every transport too. The WS2.8 test refuses
/// a two-result `bind_slot` only as built; here the surplus result (a fresh
/// id no instruction uses) must survive binary, both text spellings, JSON
/// and MessagePack and still be refused by both engines. A transport that
/// kept only the first result would hand a consumer the valid probe.
#[test]
fn crit_unex08_review_two_result_bind_slot_is_refused_in_every_format() {
    let mut two_results = critic_frames_probe(ReadVia::BoundHandle);
    let idx = bind_slot_index(&two_results);
    two_results.functions[0].blocks[0].body[idx]
        .results
        .push(ValueId::new(900));
    for (format, image) in crit_unex08_images(&two_results) {
        crit_unex08_assert_arity_refused(format, &image, 2);
    }
}

/// Review twin of the negative: the critic's literal shape with its ONE
/// inspection removed. The `add` reads the bound constant instead of the
/// loaded value, so the pre-bind handle's unbound slot is still read by
/// `LoadSlot` and the frame is still closed through that handle, but nothing
/// inspects the poison. Every image validates and executes to 41 + 1. That
/// locates the negative twin's refusal at the inspection by behaviour, where
/// its `!contains("LoadSlot")` check could only look at message text.
#[test]
fn crit_unex08_review_uninspected_pre_bind_read_executes_in_every_format() {
    /// The `open_frame` result: the handle passed INTO the one `bind_slot`.
    fn pre_bind_handle(module: &Module) -> ValueId {
        let body = &module.functions[0].blocks[0].body;
        let Inst::BindSlot { frame, .. } = body[bind_slot_index(module)].inst else {
            unreachable!("bind_slot_index names a bind_slot")
        };
        assert!(
            body.iter()
                .any(|node| matches!(node.inst, Inst::OpenFrame { .. }) && node.results == [frame]),
            "the bind's input handle is the opened one"
        );
        frame
    }

    let mut module = critic_frames_probe(ReadVia::PreBindHandle);
    let body = &module.functions[0].blocks[0].body;
    let Inst::BindSlot {
        value: bound_value, ..
    } = body[bind_slot_index(&module)].inst
    else {
        unreachable!("bind_slot_index names a bind_slot")
    };
    let loaded = body
        .iter()
        .find(|node| matches!(node.inst, Inst::LoadSlot { .. }))
        .expect("the probe loads a slot")
        .results[0];
    let mut rerouted = 0;
    for node in module.functions[0].blocks[0].body.iter_mut() {
        if let Inst::BinOp { lhs, .. } = &mut node.inst
            && *lhs == loaded
        {
            *lhs = bound_value;
            rerouted += 1;
        }
    }
    assert_eq!(rerouted, 1, "exactly the add read the loaded value");
    for (format, image) in crit_unex08_images(&module) {
        crit_unex08_assert_static_agreement(format, &image);
        let pre_bind = pre_bind_handle(&image);
        let through_pre_bind = image.functions[0].blocks[0]
            .body
            .iter()
            .filter(|node| {
                matches!(node.inst, Inst::LoadSlot { frame, .. } if frame == pre_bind)
                    || matches!(node.inst, Inst::CloseFrame { frame } if frame == pre_bind)
            })
            .count();
        assert_eq!(
            through_pre_bind, 2,
            "{format}: LoadSlot and CloseFrame still go through the pre-bind handle"
        );
        assert_eq!(validate_then_run(&image), Ok(vec![42]), "{format}");
    }
}

/// The critic probe with the bound handle carried across ONE block edge into
/// a parameter of type `param`, where the load, the `add` and the close run.
fn crit_unex08_edge_probe(param: Ty) -> Module {
    let mut mb = ModuleBuilder::new("critic_frames_edge");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let entry = fb.create_block();
    let tail = fb.create_block();
    let carried = fb.add_block_param(tail, param);
    fb.switch_to_block(entry);
    let opened = fb.open_frame(BindingFrameDef::new(
        BindingFrameId::new(0),
        "exists_i",
        vec![BindingSlot::new("i", Ty::U64)],
    ));
    let forty_one = fb.uconst(Ty::U64, 41);
    let bound = fb.bind_slot(opened, 0, forty_one);
    fb.br(tail, vec![bound]);
    fb.switch_to_block(tail);
    let loaded = fb.load_slot(carried, 0, Ty::U64);
    let one = fb.uconst(Ty::U64, 1);
    let sum = fb.add(Ty::U64, loaded, one);
    fb.close_frame(carried);
    fb.ret(vec![sum]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Review twin for the `Ptr` half of "one `Ptr` result". `result_tys` is a
/// table lookup, so the static helper cannot tell whether either ENGINE
/// types the handle `Ptr`; an edge can. Across a `Ptr` parameter the handle
/// executes to 41 + 1 in every image. Across a `Unit` parameter (the type
/// the interpreter once gave frame handles) every image is refused by both
/// engines: the validator names the edge `BranchArgTypeMismatch` with the
/// actual type `ptr`, and the interpreter raises `TypeError` at the edge,
/// never reaching the load.
#[test]
fn crit_unex08_review_bound_handle_is_ptr_typed_across_an_edge() {
    for (format, image) in crit_unex08_images(&crit_unex08_edge_probe(Ty::Ptr)) {
        assert_eq!(validate_then_run(&image), Ok(vec![42]), "{format}");
    }
    for (format, image) in crit_unex08_images(&crit_unex08_edge_probe(Ty::Unit)) {
        let refused = trust_ir_build::validate_module(&image);
        assert!(
            refused.iter().any(|error| matches!(
                error,
                ValidationError::BranchArgTypeMismatch {
                    arg_index: 0,
                    expected,
                    actual,
                    ..
                } if expected == &Ty::Unit.to_string() && actual == &Ty::Ptr.to_string()
            )),
            "{format}: expected BranchArgTypeMismatch(unit <- ptr), got {refused:?}"
        );
        let error = run_u64s(&image).expect_err("a frame handle is not a unit value");
        assert_eq!(
            error.code,
            InterpretErrorCode::TypeError,
            "{format}: {error}"
        );
        assert!(
            error.to_string().contains(&format!(
                "expected value of type {}, got {}",
                Ty::Unit,
                Ty::Ptr
            )),
            "{format}: unexpected interpreter error: {error}"
        );
    }
}

// ---------------------------------------------------------------------------
// WS2.5 — the unwind surface under panic=abort (ub-numerics-policy §4,
// "Unwinding": the `PanicStrategy::Abort` default). Gate 8 runs these.
// ---------------------------------------------------------------------------

/// `fn() -> i32 { bb0: br bb1; bb1: landingpad cleanup; ret 0 }` when `pad`,
/// else the same function with the landingpad deleted (the mutation control).
fn branch_into_block(pad: bool) -> Module {
    let mut mb = ModuleBuilder::new("pad_by_branch");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let target = fb.create_block();
    fb.switch_to_block(entry);
    fb.br(target, vec![]);
    fb.switch_to_block(target);
    if pad {
        let _ = fb.landingpad(true, vec![]);
    }
    let zero = fb.iconst(Ty::I32, 0);
    fb.ret(vec![zero]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A pad entered by a plain `Br` is refused by the validator AND by the
/// interpreter: before WS2.5 the interpreter bound a fabricated `(null, 0)`
/// and returned `Ok(0)`.
#[test]
fn landingpad_entered_by_a_branch_is_unsupported_not_ok() {
    let module = branch_into_block(true);
    let err = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .expect_err("a directly-entered landing pad must not execute");
    assert_eq!(
        err.code,
        InterpretErrorCode::UnsupportedInstruction,
        "{err:?}"
    );
    assert!(
        err.message
            .contains("landingpad entered without an unwind edge"),
        "{err:?}"
    );
    let validation = trust_ir_build::validate_module(&module);
    assert!(
        validation.iter().any(|e| matches!(
            e,
            trust_ir_build::ValidationError::MisplacedLandingPad { block: 1, .. }
        )),
        "{validation:?}"
    );

    // Mutation control: delete the pad and the same CFG runs to Ok(0), so the
    // refusal above is the pad arm's, not the branch's.
    let control = branch_into_block(false);
    assert_eq!(trust_ir_build::validate_module(&control), []);
    let out = Interpreter::with_module(&control)
        .execute_func(FuncId::new(0), [])
        .expect("pad-free control executes");
    assert_eq!(out.returns[0].as_int().expect("int").as_signed(), 0);
}

/// `callee` returns 7 or traps; `caller` invokes it with a well-placed cleanup
/// pad that resumes.
fn invoke_module(callee_traps: bool) -> Module {
    let mut mb = ModuleBuilder::new("invoke_panic_abort");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let callee = {
        let mut fb = mb.function("callee", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        if callee_traps {
            fb.unreachable();
        } else {
            let seven = fb.iconst(Ty::I32, 7);
            fb.ret(vec![seven]);
        }
        fb.build()
    };
    let mut fb = mb.function("caller", ft);
    let entry = fb.create_block();
    let normal = fb.create_block();
    let unwind = fb.create_block();
    fb.switch_to_block(entry);
    let result = fb.invoke(callee, vec![], normal, vec![], unwind);
    fb.switch_to_block(normal);
    fb.ret(vec![result]);
    fb.switch_to_block(unwind);
    let (exn, _) = fb.landingpad(true, vec![]);
    fb.resume(exn);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The panic=abort projection: a returning callee continues on the NORMAL
/// edge, and a trapping callee's trap propagates as the abort — the unwind
/// edge is never taken (taking it would surface the pad's
/// `UnsupportedInstruction`, not the callee's `UndefinedBehavior`).
#[test]
fn invoke_is_the_panic_abort_projection() {
    let module = invoke_module(false);
    let report = trust_ir_build::validate_module_report(&module);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.unwind_surface(), [FuncId::new(1)]);
    let out = Interpreter::with_module(&module)
        .execute_func(FuncId::new(1), [])
        .expect("normal edge executes");
    assert_eq!(out.returns[0].as_int().expect("int").as_signed(), 7);

    let trapping = invoke_module(true);
    assert_eq!(trust_ir_build::validate_module(&trapping), []);
    let err = Interpreter::with_module(&trapping)
        .execute_func(FuncId::new(1), [])
        .expect_err("a trapping callee aborts the caller");
    assert_eq!(err.code, InterpretErrorCode::UndefinedBehavior, "{err:?}");
    assert!(err.message.contains("executed unreachable"), "{err:?}");
}

/// `enum E { a(u64), b(u64) }` and `fn program() -> u64 { %e = const E a(7);
/// %t = u8 <tag>; %r = insert_field E %e, <lane>, <value>; extract_field u64
/// %r, 1 }`. `lane == 0` writes `%t` over the tag.
fn tag_rewrite_module(lane: u32) -> Module {
    let e_ty = Ty::Enum(EnumId::new(0));
    let mut mb = ModuleBuilder::new("tag_rewrite");
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let e = fb.const_value(
        e_ty.clone(),
        Constant::Aggregate(vec![Constant::Int(0), Constant::Int(7)]),
    );
    let value = if lane == 0 {
        fb.iconst(Ty::U8, 1)
    } else {
        fb.iconst(Ty::U64, 9)
    };
    let r = fb.insert_field(e_ty, e, lane, value);
    let out = fb.extract_field(Ty::U64, r, 1);
    fb.ret(vec![out]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.add_enum(EnumDef::new(
        EnumId::new(0),
        "E",
        vec![
            EnumVariant {
                name: "a".into(),
                fields: vec![Ty::U64],
                field_names: vec![],
            },
            EnumVariant {
                name: "b".into(),
                fields: vec![Ty::U64],
                field_names: vec![],
            },
        ],
    ));
    module
}

/// CONFORMANCE (roadmap WS2.2 item 2, partb c06 `p1_insert_tag_overwrite`):
/// rewriting an enum's discriminant with `insert_field` lane 0 is refused by
/// BOTH engines. The validator names it (`FieldAccessInvalid`); the reference
/// interpreter, run on the unvalidated module, answers `UndefinedBehavior`
/// instead of the silent re-tag that used to return `Ok 7` (Lean's
/// `semInsertField` throws on the same write). The twin — the same module
/// writing payload lane 1 — validates and runs to the written value.
#[test]
fn enum_tag_rewrite_is_refused_by_validator_and_interpreter() {
    let retag = tag_rewrite_module(0);
    let errors = trust_ir_build::validate_module(&retag);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        matches!(
            &errors[0],
            ValidationError::FieldAccessInvalid { op, reason, .. }
                if op == "insert_field"
                    && reason.contains(
                        "insert_field cannot rewrite an enum discriminant; construct the \
                         variant with Const"
                    )
        ),
        "{errors:?}"
    );
    let run = Interpreter::with_module(&retag).execute_func(FuncId::new(0), []);
    let error = run.expect_err("the re-tag must not run to Ok");
    assert_eq!(
        error.code,
        InterpretErrorCode::UndefinedBehavior,
        "{error:?}"
    );
    assert!(
        error
            .message
            .contains("insert_field cannot rewrite an enum discriminant"),
        "{error:?}"
    );

    let payload = tag_rewrite_module(1);
    assert!(trust_ir_build::validate_module(&payload).is_empty());
    let out = Interpreter::with_module(&payload)
        .execute_func(FuncId::new(0), [])
        .expect("payload write runs");
    assert_eq!(out.returns[0].as_int().map(|i| i.as_unsigned()), Some(9));
}

// ══════════════════════════════════════════════════════════════════════════
// Roadmap WS2.4 (F-045, row `exec-log-and-tcb/by-value-struct-cycle-robustness`)
// — the interpreter half of the by-value aggregate cycle rule.
//
// Modules reach the reference interpreter without validation (binary decode
// and the text parser run no validator). A type that contains itself BY VALUE
// used to send `byte_size -> struct_layout -> aggregate_layout ->
// byte_size(field)` into unbounded recursion — a host stack overflow, not an
// error. The interpreter now threads a visiting stack through its layout
// functions and answers re-entry with a fail-closed `TypeError` "type {ty}
// contains itself by value (no finite layout)". Every case runs on a thread
// with a deliberately SMALL stack, so a regression to unbounded recursion
// fails the test by aborting instead of passing by luck on a large stack.
// The validator half (`InlineAggregateCycle`) is gate 9's
// `trust-ir-build/tests/by_value_struct_cycle_robustness.rs`.
// ══════════════════════════════════════════════════════════════════════════

/// Stack for the WS2.4 cases: ample for the interpreter's bounded work, and
/// far too small for the unbounded recursion the guard replaced.
const WS2_4_SMALL_STACK: usize = 1024 * 1024;

fn on_small_stack<T: Send + 'static>(work: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .name("ws2_4_small_stack".to_string())
        .stack_size(WS2_4_SMALL_STACK)
        .spawn(work)
        .expect("spawn the small-stack thread")
        .join()
        .expect("the small-stack thread completed without crashing")
}

fn ws2_4_field(name: &str, ty: Ty) -> trust_ir::ty::FieldDef {
    trust_ir::ty::FieldDef {
        name: name.to_string(),
        ty,
        offset: None,
    }
}

/// `program() -> u64`: allocate struct #0, write a null `next` at byte 0 and
/// 42 at byte 8, load the WHOLE struct back and return field 1.
fn ws2_4_node_program(next: Ty) -> Module {
    let node = trust_ir::value::StructId::new(0);
    let mut mb = ModuleBuilder::new("ws2_4_node");
    mb.add_struct(trust_ir::ty::StructDef {
        id: node,
        name: "Node".to_string(),
        fields: vec![ws2_4_field("next", next), ws2_4_field("v", Ty::U64)],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let slot = fb.alloca(Ty::Struct(node));
    let null = fb.null_ptr();
    fb.store(Ty::Ptr, slot, null);
    let v_slot = fb.gep_byte_offset(slot, 8);
    let v = fb.uconst(Ty::U64, 42);
    fb.store(Ty::U64, v_slot, v);
    let loaded = fb.load(Ty::Struct(node), slot);
    let out = fb.extract_field(Ty::U64, loaded, 1);
    fb.ret(vec![out]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `program() -> u64 { alloca <ty>; 0 }` over `module`'s tables — the smallest
/// program that asks the interpreter for `ty`'s layout.
fn ws2_4_alloca_program(tables: Module, ty: Ty) -> Module {
    let mut mb = ModuleBuilder::new("ws2_4_alloca");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.alloca(ty);
    let zero = fb.uconst(Ty::U64, 0);
    fb.ret(vec![zero]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.structs = tables.structs;
    module.enums = tables.enums;
    module.types = tables.types;
    module
}

/// Run `program` on the small stack WITHOUT validating, and require the
/// fail-closed layout-cycle `TypeError`.
fn ws2_4_assert_layout_cycle(module: Module, label: &'static str) {
    let error = on_small_stack(move || {
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect_err("a by-value cycle has no finite layout")
    });
    assert_eq!(
        error.code,
        InterpretErrorCode::TypeError,
        "{label}: {error}"
    );
    assert!(
        error
            .message
            .contains("contains itself by value (no finite layout)"),
        "{label}: {error}"
    );
}

fn ws2_4_has_cycle_error(module: &Module) -> bool {
    trust_ir_build::validate_module(module)
        .iter()
        .any(|e| matches!(e, ValidationError::InlineAggregateCycle { .. }))
}

/// Positive: `struct Node { next: *mut Node, v: u64 }` validates and executes
/// (on the small stack) to 42 — the pointer breaks the cycle.
#[test]
fn ws2_4_pointer_broken_self_reference_executes() {
    let node = trust_ir::value::StructId::new(0);
    let module = ws2_4_node_program(Ty::PtrMut(Box::new(Ty::Struct(node))));
    assert_eq!(trust_ir_build::validate_module(&module), []);
    let out = on_small_stack(move || {
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .map(|outcome| outcome.returns[0].as_int().expect("u64").as_unsigned())
    });
    assert_eq!(out.expect("a finite layout executes"), 42);
}

/// Negative twin (one mutation: `next` holds the Node by value): refused by
/// the validator by name, and — run UNVALIDATED — a `TypeError`, not a crash.
#[test]
fn ws2_4_by_value_self_reference_is_a_type_error_not_a_crash() {
    let module = ws2_4_node_program(Ty::Struct(trust_ir::value::StructId::new(0)));
    assert!(ws2_4_has_cycle_error(&module));
    ws2_4_assert_layout_cycle(module, "struct Node { next: Node }");
}

/// Mutation controls: the cycle through an enum variant, a self-resolving
/// `Array(TyId)` row, a tuple, a DECLARED-size struct, and two structs are all
/// refused by both engines.
#[test]
fn ws2_4_layout_cycle_mutations_fail_closed() {
    use trust_ir::ty::StructDef;
    use trust_ir::value::{StructId, TyId};
    let named = |id: u32, name: &str, fields: Vec<trust_ir::ty::FieldDef>| StructDef {
        id: StructId::new(id),
        name: name.to_string(),
        fields,
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    };

    // enum E { A(u8), B(E) }
    let mut tables = Module::new("ws2_4_enum");
    tables.add_enum(EnumDef {
        id: EnumId::new(0),
        name: "E".to_string(),
        variants: vec![
            EnumVariant {
                name: "A".to_string(),
                fields: vec![Ty::U8],
                field_names: vec![],
            },
            EnumVariant {
                name: "B".to_string(),
                fields: vec![Ty::Enum(EnumId::new(0))],
                field_names: vec![],
            },
        ],
        discriminants: vec![],
        repr: None,
        layout: None,
        origin: None,
    });
    let module = ws2_4_alloca_program(tables, Ty::Enum(EnumId::new(0)));
    assert!(ws2_4_has_cycle_error(&module));
    ws2_4_assert_layout_cycle(module, "enum variant");

    // Row 0 = [row0; 1]: no nominal type at all.
    let mut tables = Module::new("ws2_4_row");
    tables.types.push(Ty::Array(TyId::new(0), 1));
    let module = ws2_4_alloca_program(tables, Ty::Array(TyId::new(0), 1));
    assert!(ws2_4_has_cycle_error(&module));
    ws2_4_assert_layout_cycle(module, "Array(TyId) row");

    // struct Node { pair: (u64, Node) }: through an inline tuple.
    let mut tables = Module::new("ws2_4_tuple");
    tables.add_struct(named(
        0,
        "Node",
        vec![ws2_4_field(
            "pair",
            Ty::Tuple(vec![Ty::U64, Ty::Struct(StructId::new(0))]),
        )],
    ));
    let module = ws2_4_alloca_program(tables, Ty::Struct(StructId::new(0)));
    assert!(ws2_4_has_cycle_error(&module));
    ws2_4_assert_layout_cycle(module, "tuple");

    // A declared layout sizes its fields too.
    let mut declared = named(
        0,
        "Node",
        vec![ws2_4_field("next", Ty::Struct(StructId::new(0)))],
    );
    declared.size = Some(8);
    declared.align = Some(8);
    declared.fields[0].offset = Some(0);
    let mut tables = Module::new("ws2_4_declared");
    tables.add_struct(declared);
    let module = ws2_4_alloca_program(tables, Ty::Struct(StructId::new(0)));
    assert!(ws2_4_has_cycle_error(&module));
    ws2_4_assert_layout_cycle(module, "declared-size struct");

    // struct A { b: B }  struct B { a: A }
    let mut tables = Module::new("ws2_4_mutual");
    tables.add_struct(named(
        0,
        "A",
        vec![ws2_4_field("b", Ty::Struct(StructId::new(1)))],
    ));
    tables.add_struct(named(
        1,
        "B",
        vec![ws2_4_field("a", Ty::Struct(StructId::new(0)))],
    ));
    let module = ws2_4_alloca_program(tables, Ty::Struct(StructId::new(0)));
    assert!(ws2_4_has_cycle_error(&module));
    ws2_4_assert_layout_cycle(module, "two-struct cycle");
}

/// WS2.4 review adversaries: layout paths the implementer's fixtures did not
/// reach — an enum whose DESCRIPTOR (direct, then niche) sizes a variant field
/// that is the enum itself, and a cyclic struct reached only through a GLOBAL
/// (global storage is sized on first address, not by an `Alloca`). Each is
/// refused by the validator by name and, run unvalidated on the small stack,
/// is the fail-closed layout-cycle `TypeError`.
#[test]
fn ws2_4_review_descriptor_and_global_cycles_fail_closed() {
    use trust_ir::ty::{EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, StructDef};
    use trust_ir::value::StructId;

    let self_enum = |layout: EnumLayoutDescriptor| {
        let mut tables = Module::new("ws2_4_descriptor");
        tables.add_enum(EnumDef {
            id: EnumId::new(0),
            name: "E".to_string(),
            variants: vec![
                EnumVariant {
                    name: "Some".to_string(),
                    fields: vec![Ty::U64, Ty::Enum(EnumId::new(0))],
                    field_names: vec![],
                },
                EnumVariant {
                    name: "None".to_string(),
                    fields: vec![],
                    field_names: vec![],
                },
            ],
            discriminants: vec![],
            repr: None,
            layout: Some(layout),
            origin: None,
        });
        ws2_4_alloca_program(tables, Ty::Enum(EnumId::new(0)))
    };

    let module = self_enum(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 0 },
        size: 24,
        align: 8,
        variant_field_offsets: vec![vec![8, 16], vec![]],
    });
    assert!(ws2_4_has_cycle_error(&module));
    ws2_4_assert_layout_cycle(module, "direct descriptor");

    let module = self_enum(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: 0,
            niche_variants_start: 1,
            niche_variants_end: 1,
            niche_start: 0,
            niche_offset: 0,
            niche_ty: EnumTagRepr::U64,
        },
        size: 16,
        align: 8,
        variant_field_offsets: vec![vec![0, 8], vec![]],
    });
    assert!(ws2_4_has_cycle_error(&module));
    ws2_4_assert_layout_cycle(module, "niche descriptor");

    // A cyclic struct reached only through a global's storage.
    let node = StructId::new(0);
    let mut mb = ModuleBuilder::new("ws2_4_global");
    mb.add_struct(StructDef {
        id: node,
        name: "Node".to_string(),
        fields: vec![ws2_4_field("next", Ty::Struct(node))],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    mb.add_global(trust_ir::Global {
        name: "storage".into(),
        ty: Ty::Struct(node),
        mutable: true,
        initializer: None,
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let addr = fb.global_addr(trust_ir::value::GlobalId::new(0));
    let loaded = fb.load(Ty::U64, addr);
    fb.ret(vec![loaded]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(ws2_4_has_cycle_error(&module));
    ws2_4_assert_layout_cycle(module, "global storage");
}

/// WS3.8 (F-049): the differential properties over VALIDATED non-null pointer
/// constants. A module the validator accepts carrying a `&'static str`, a
/// `&'static u64`, a `*mut u64` and a `&[u32]` constant — in body `Const`s
/// and in global initializers — executes every function (1) deterministically, (2)
/// without a structural code, (3) with its declared return shape, and (4) to
/// the value the globals denote.
#[test]
fn ws3_8_validated_pointer_constants_execute_deterministically() {
    use trust_ir::ty::FatPtrKind;
    use trust_ir::value::GlobalId;
    use trust_ir::{Global, Linkage, Visibility};

    let global = |name: &str, ty: Ty, mutable: bool, init: Constant| Global {
        name: name.into(),
        ty,
        mutable,
        initializer: Some(init),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    };
    let fat = |symbol: &str, addend: i64, len: i128| {
        Constant::Aggregate(vec![
            Constant::symbol_addr_with_addend(symbol, addend),
            Constant::Int(len),
        ])
    };
    let str_ty = Ty::FatPtr(FatPtrKind::Str);
    let mut mb = ModuleBuilder::new("ws3_8_differential");
    let u8_id = mb.add_type(Ty::U8);
    let u32_id = mb.add_type(Ty::U32);
    let slice_ty = Ty::FatPtr(FatPtrKind::Slice(u32_id));
    mb.add_global(global(
        "HELLO",
        Ty::Array(u8_id, 5),
        false,
        Constant::str_bytes("hello"),
    ));
    mb.add_global(global(
        "TABLE",
        Ty::Array(u32_id, 3),
        false,
        Constant::Array(vec![Constant::Int(7), Constant::Int(8), Constant::Int(9)]),
    ));
    mb.add_global(global("ANSWER", Ty::U64, false, Constant::Int(42)));
    mb.add_global(global("COUNTER", Ty::U64, true, Constant::Int(0)));
    mb.add_global(global(
        "GREETING",
        str_ty.clone(),
        false,
        fat("HELLO", 1, 4),
    ));

    let u8_ret = mb.add_func_type(vec![], vec![Ty::U8]);
    let u32_ret = mb.add_func_type(vec![], vec![Ty::U32]);
    let u64_ret = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut expected = Vec::new();
    {
        let mut f = mb.function("greeting_first", u8_ret);
        let e = f.create_block();
        f.switch_to_block(e);
        let slot = f.global_addr(GlobalId::new(4));
        let s = f.load(str_ty.clone(), slot);
        let data = f.ptr_data(str_ty.clone(), s);
        let b = f.load(Ty::U8, data);
        f.ret(vec![b]);
        expected.push((f.build(), u128::from(b'e')));
    }
    {
        let mut f = mb.function("table_last", u32_ret);
        let e = f.create_block();
        f.switch_to_block(e);
        let view = f.const_value(slice_ty.clone(), fat("TABLE", 4, 2));
        let data = f.ptr_data(slice_ty, view);
        let last = f.gep_byte_offset(data, 4);
        let v = f.load(Ty::U32, last);
        f.ret(vec![v]);
        expected.push((f.build(), 9));
    }
    {
        let mut f = mb.function("answer_plus_counter", u64_ret);
        let e = f.create_block();
        f.switch_to_block(e);
        let answer = f.const_value(Ty::Ref(Box::new(Ty::U64)), Constant::symbol_addr("ANSWER"));
        let counter = f.const_value(
            Ty::PtrMut(Box::new(Ty::U64)),
            Constant::symbol_addr("COUNTER"),
        );
        let one = f.const_value(Ty::U64, Constant::Int(1));
        f.store(Ty::U64, counter, one);
        let a = f.load(Ty::U64, answer);
        let c = f.load(Ty::U64, counter);
        let sum = f.binop(BinOp::Add, Ty::U64, a, c);
        f.ret(vec![sum]);
        expected.push((f.build(), 43));
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");

    for (id, want) in expected {
        let first = Interpreter::with_module(&module).execute_func(id, []);
        let second = Interpreter::with_module(&module).execute_func(id, []);
        assert_eq!(
            format!("{first:?}"),
            format!("{second:?}"),
            "nondeterministic"
        );
        let out = match first {
            Ok(out) => out,
            Err(error) => {
                assert!(!is_structural(error.code), "{error:?}");
                panic!("validated pointer constant failed to execute: {error:?}");
            }
        };
        let sig = module.functions[id.as_usize()].ty;
        let declared = &module.func_types[sig.as_usize()].returns;
        assert_eq!(out.returns.len(), declared.len());
        assert_eq!(&out.returns[0].ty, &declared[0]);
        assert_eq!(out.returns[0].as_int().map(|i| i.as_unsigned()), Some(want));
    }
}

// ───────────────────── WS3.22 (F-060): pinned releases are dead-marking steps ─────────────────────

/// A seeded release corpus for the reference host model (roadmap WS3.22,
/// F-060 — `Inst::Dealloc` cannot state a free, so a free is a CALL to a
/// pinned release entry point, and the interpreter can only see it because
/// `trust_ir_build::pinned_release_entry_points()` names those symbols in one
/// place and `PinnedHandleHost` keys its dead-marking on it).
///
/// Each seed builds `f() -> u8` over 1..=3 `Nat` handles (`from_u64`) and
/// 0..=2 `HeapAlloc(CleanHeap)` cells, then a random sequence of 2..=7 steps,
/// each a RELEASE (`trust_bignum_nat_drop(h)` / `clean_dec(c)`) or a USE
/// (`is_zero(h)` / `load c`) of a random resource. An INDEPENDENT liveness
/// oracle — a per-resource released flag, updated from the program text alone
/// — predicts the outcome: `Ok` when no step touches a released resource,
/// otherwise `UndefinedBehavior` at the first step that does. Three
/// properties per seed:
///
///   1. under the reference model the interpreter agrees with the oracle
///      exactly (Ok vs UB, and the UB names the release — "used after
///      release" for a handle, "freed allocation" / "use after dealloc" for a
///      cell, the latter being the SAME fault a load after `Inst::Dealloc`
///      raises: the pinned release IS the dealloc step);
///   2. under the no-op mutant (a host that serves the release symbols as
///      no-ops and everything else through the reference model) EVERY program
///      runs to `Ok` — the faults come from the table-keyed dead-marking and
///      nothing else, so a reference model that lost the keying is caught;
///   3. determinism and no structural code, as for the other corpora.
mod ws3_22_release_corpus {
    use super::*;
    use trust_ir::inst::AllocOrigin;
    use trust_ir::interpret::HostRcOp;
    use trust_ir_build::{
        HandleRuntimePin, PinnedHandleHost, TRUSTED_HANDLE_RUNTIMES,
        pinned_release_entry_for_symbol,
    };

    fn nat_pin() -> &'static HandleRuntimePin {
        TRUSTED_HANDLE_RUNTIMES
            .iter()
            .find(|pin| pin.name == "Nat" && pin.runtime == "trust_bignum::Nat")
            .expect("v1 pins (Nat, trust_bignum::Nat)")
    }

    /// One step of a generated program.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Step {
        DropHandle(usize),
        UseHandle(usize),
        DecCell(usize),
        LoadCell(usize),
    }

    /// The oracle's prediction for one program.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Expected {
        Ok,
        /// The index of the first step that touches a released resource, and
        /// whether that resource is a handle (else a cell).
        FaultAt {
            step: usize,
            handle: bool,
        },
    }

    /// The independent liveness oracle: released-flags over the program text.
    fn oracle(handles: usize, cells: usize, steps: &[Step]) -> Expected {
        let mut handle_dead = vec![false; handles];
        let mut cell_dead = vec![false; cells];
        for (index, step) in steps.iter().enumerate() {
            match *step {
                Step::DropHandle(h) | Step::UseHandle(h) => {
                    if handle_dead[h] {
                        return Expected::FaultAt {
                            step: index,
                            handle: true,
                        };
                    }
                    if *step == Step::DropHandle(h) {
                        handle_dead[h] = true;
                    }
                }
                Step::DecCell(c) | Step::LoadCell(c) => {
                    if cell_dead[c] {
                        return Expected::FaultAt {
                            step: index,
                            handle: false,
                        };
                    }
                    if *step == Step::DecCell(c) {
                        cell_dead[c] = true;
                    }
                }
            }
        }
        Expected::Ok
    }

    fn gen_program(seed: u64) -> (Module, usize, usize, Vec<Step>) {
        let mut rng = Rng::new(seed ^ 0x5753_3332_3200_0000);
        let handles = 1 + rng.bounded(3) as usize;
        let cells = rng.bounded(3) as usize;
        let mut steps = Vec::new();
        for _ in 0..2 + rng.bounded(6) {
            let pick = rng.bounded(if cells == 0 { 2 } else { 4 });
            steps.push(match pick {
                0 => Step::DropHandle(rng.bounded(handles as u32) as usize),
                1 => Step::UseHandle(rng.bounded(handles as u32) as usize),
                2 => Step::DecCell(rng.bounded(cells as u32) as usize),
                _ => Step::LoadCell(rng.bounded(cells as u32) as usize),
            });
        }
        let mut mb =
            ModuleBuilder::new_with_target_info(format!("release_corpus_{seed}"), host_target());
        let decls = mb
            .declare_handle_runtime_roles(nat_pin(), &["from_u64", "is_zero", "drop"])
            .expect("pinned declarations");
        let dec_entry = pinned_release_entry_for_symbol("clean_dec").expect("pinned");
        let dec_ty = mb.add_func_type(
            dec_entry.func_ty.params.clone(),
            dec_entry.func_ty.returns.clone(),
        );
        let dec = mb.declare_function(dec_entry.symbol, dec_ty);
        let sig = mb.add_func_type(vec![], vec![Ty::U8]);
        let mut fb = mb.function("f", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let handle_values: Vec<ValueId> = (0..handles)
            .map(|index| {
                let seed_value = fb.uconst(Ty::U64, index as u128);
                fb.call(decls.entry("from_u64").unwrap(), vec![seed_value])
            })
            .collect();
        let cell_values: Vec<ValueId> = (0..cells)
            .map(|index| {
                let cell = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::CleanHeap);
                let value = fb.uconst(Ty::U64, index as u128);
                fb.store(Ty::U64, cell, value);
                cell
            })
            .collect();
        for step in &steps {
            match *step {
                Step::DropHandle(h) => {
                    fb.call_void(decls.entry("drop").unwrap(), vec![handle_values[h]]);
                }
                Step::UseHandle(h) => {
                    fb.call(decls.entry("is_zero").unwrap(), vec![handle_values[h]]);
                }
                Step::DecCell(c) => fb.call_void(dec, vec![cell_values[c]]),
                Step::LoadCell(c) => {
                    fb.load(Ty::U64, cell_values[c]);
                }
            }
        }
        let out = fb.uconst(Ty::U8, 1);
        fb.ret(vec![out]);
        fb.build();
        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
        for function in &mut module.functions {
            if !function.is_declaration() {
                function.body_gate = Some(BodyGate::Gated {
                    authority: "interpret-differential".into(),
                    evidence: None,
                });
            }
        }
        (module, handles, cells, steps)
    }

    /// The mutant: the release symbols the one-place table names are served
    /// as NO-OPS; everything else goes through the reference model.
    struct NoOpRelease;

    impl HostCalls for NoOpRelease {
        fn call(
            &self,
            callee: &Function,
            sig: &FuncTy,
            args: &[InterpretValue],
            host: &mut HostState,
        ) -> Option<InterpretResult<Vec<InterpretValue>>> {
            if pinned_release_entry_for_symbol(&callee.name).is_some() {
                return Some(Ok(Vec::new()));
            }
            PinnedHandleHost::new().call(callee, sig, args, host)
        }

        fn rc_op(&self, callee: &Function, sig: &FuncTy) -> Option<HostRcOp> {
            if pinned_release_entry_for_symbol(&callee.name).is_some() {
                return None;
            }
            PinnedHandleHost::new().rc_op(callee, sig)
        }
    }

    fn run(module: &Module, host: &dyn HostCalls) -> Result<InterpretOutcome, InterpretError> {
        let f = module.function_by_name("f").expect("@f").id;
        let interp = Interpreter::with_module(module).with_host(host);
        let first = interp.execute_func(f, Vec::new());
        let second = interp.execute_func(f, Vec::new());
        assert_eq!(first, second, "{}: nondeterministic", module.name);
        if let Err(error) = &first {
            assert!(
                !is_structural(error.code),
                "{}: structural error on validated IR: {error}",
                module.name
            );
        }
        first
    }

    #[derive(Default)]
    struct Tally {
        ok: u32,
        handle_faults: u32,
        cell_faults: u32,
    }

    #[test]
    fn ws3_22_pinned_release_differential() {
        let reference = PinnedHandleHost::new();
        let mut tally = Tally::default();
        for seed in 1..=512u64 {
            let (module, handles, cells, steps) = gen_program(seed);
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "seed {seed}: {errors:?}");
            let expected = oracle(handles, cells, &steps);

            // 1. The reference model agrees with the oracle.
            let observed = run(&module, &reference);
            match (expected, &observed) {
                (Expected::Ok, Ok(outcome)) => {
                    assert_eq!(
                        outcome.returns,
                        vec![InterpretValue::int(Ty::U8, 1).unwrap()]
                    );
                    assert!(outcome.host_calls >= handles as u64, "seed {seed}");
                    tally.ok += 1;
                }
                (Expected::FaultAt { handle, .. }, Err(error)) => {
                    assert_eq!(
                        error.code,
                        InterpretErrorCode::UndefinedBehavior,
                        "seed {seed} steps {steps:?}: {error}"
                    );
                    if handle {
                        assert!(
                            error.message.contains("used after release"),
                            "seed {seed} steps {steps:?}: {error}"
                        );
                        tally.handle_faults += 1;
                    } else {
                        assert!(
                            error.message.contains("freed allocation")
                                || error.message.contains("use after dealloc"),
                            "seed {seed} steps {steps:?}: {error}"
                        );
                        tally.cell_faults += 1;
                    }
                }
                (expected, observed) => panic!(
                    "seed {seed} steps {steps:?}: oracle says {expected:?}, reference model \
                     says {observed:?}"
                ),
            }

            // 2. The mutant sees nothing: every program is Ok.
            let mutant = run(&module, &NoOpRelease).unwrap_or_else(|error| {
                panic!("seed {seed} steps {steps:?}: the no-op mutant faulted: {error}")
            });
            assert_eq!(
                mutant.returns,
                vec![InterpretValue::int(Ty::U8, 1).unwrap()]
            );
        }
        // Every arm is exercised, not routed onto the others.
        assert!(tally.ok > 100, "only {} clean programs", tally.ok);
        assert!(
            tally.handle_faults > 100,
            "only {} handle faults",
            tally.handle_faults
        );
        assert!(
            tally.cell_faults > 30,
            "only {} cell faults",
            tally.cell_faults
        );
    }
}

#[path = "interpret_differential/frame_cfg.rs"]
mod frame_cfg;
