// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// W5b: the Lean-EXECUTION differential oracle (roadmap WS2.19, closes the
// F-044 "no W5b oracle" row; proof-program row
// `arch-0804-and-spine/32-w5b-lean-execution-oracle`).
//
// The W5a differential (`interpret_differential.rs`) ties the reference
// interpreter to the VALIDATOR. It has no second reference implementation, so
// a producer validated only against the interpreter inherits every
// interpreter<->Lean divergence unseen. This file adds the second
// implementation: the Lean executable semantics (`evalFunctionInContext`,
// `lean/trust_ir-semantics/TrustIr/Semantics/Eval.lean`) compiled into the
// `trustir_eval` executable (`lean/trust_ir-semantics/TrustIrEval/`), which
// reads a serde-JSON module and runs it. Both engines execute ONE corpus:
//
//   * every conformance fixture in the lowering-target subset (v3,
//     `trust_ir_conformance::subset`) that validates, function by function,
//     for every function whose parameters are all integers / `Bool`;
//   * `SEEDS` generator-seeded modules of the shared W5a corpus
//     (`common::exec_gen`, now with shifts, the checked `Overflow` trio and
//     range-edge arguments: `MIN / -1`, `MIN - 1`, shift-by-width).
//
// The verdicts are compared through ONE rule (`compare`):
//
//   * `Ok` / `Ok` with different values, two panics with different messages
//     (plan item P: the message names the failed assert's kind), or `Ok`
//     against a UB / panic /
//     out-of-fuel / type-error verdict, or any two different refusal classes,
//     is a MISMATCH and fails the test — every one is a semantic
//     disagreement between the two engines the format's proofs rest on;
//   * a `TypeError` on EITHER side is a mismatch too: the module validated,
//     so an engine that calls it ill-formed disagrees with the validator
//     (the interpreter's structural codes are W5a's property 2; the Lean
//     model's `type_error` is the same class — the WS2.19 audit reclassified
//     the unmodelled constructs that used to surface this way, every "type
//     has no byte size" memory site, as `unsupported.layout`, each pinned by
//     an `ExecutableFixtures` case beside its still-UB twin);
//   * `unsupported` on EITHER side is COVERAGE, not agreement: it is counted
//     by feature and RATCHETED — `UNSUPPORTED_LEDGER` is the exact number of
//     runs one side refused by name, and it may only go DOWN;
//   * the interpreter's `AssumeViolated` (a false `Assume`, WS2.11) is a
//     VACUITY filter over the entry parameters, not a program verdict — the
//     Lean model runs `Assume` as a no-op (the ratified split,
//     `docs/ub-numerics-policy.md` §4) — so such a run is not compared; it is
//     counted, and each test pins that count exactly;
//   * an oracle that could not answer (`error`) is a mismatch whatever the
//     interpreter said: a broken harness is never laundered into coverage.
//
// W5b successes use validated whole-result observation graphs: an integer is its
// width and two's-complement bit pattern (the interpreter's `raw`, the Lean
// value modulo 2^w); a float is its binary64 bit pattern, bit-exact, except
// that NaNs compare NaN-ness only while the WS2.23 payload residue stands
// (Lean 4.8.0 cannot observe a NaN's bits); a pointer compares nullness only
// (addresses are engine-private); aggregates compare structurally.
//
// Running the oracle needs `lake` (elan). The locator tries `TRUST_IR_LAKE`,
// then `$HOME/.elan/bin/lake`, then `lake` on `PATH`. Without one, the
// oracle tests report SKIPPED (the harness self-tests still run) unless
// `TRUST_IR_REQUIRE_LEAN=1`, which makes a missing `lake` a hard failure —
// the standing gate `lean-exec-differential` (`scripts/ci_gates.sh`) sets it
// whenever `$HOME/.elan/bin/lake` exists, so on a Lean-equipped machine the
// oracle is REQUIRED, never silently skipped. There is no `#[ignore]` and no
// other opt-out (the no-hidden-test-paths rule).

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Arc, Mutex, OnceLock, Weak};

use serde_json::{Value as Json, json};
use trust_ir::Module;
use trust_ir::inst::AllocOrigin;
use trust_ir::interpret::{
    InterpretError, InterpretErrorCode, InterpretOptions, InterpretValue, InterpretValueKind,
    Interpreter, PanicStrategy,
};
use trust_ir::ty::Ty;
use trust_ir::value::FuncId;
use trust_ir_build::ModuleBuilder;
use trust_ir_conformance::subset::module_subset_violations;

#[path = "common/aggregate_inactive_variants.rs"]
mod aggregate_inactive_variant_cases;
#[path = "common/aggregate_memory.rs"]
mod aggregate_memory_cases;
#[path = "common/allocation_operands.rs"]
mod allocation_operand_cases;
#[path = "common/bool_vector_comparisons.rs"]
mod bool_vector_comparison_cases;
#[path = "common/closure_unwritten_transport.rs"]
mod closure_unwritten_transport;
mod common;
#[path = "common/compact_array_execution.rs"]
mod compact_array_execution;
#[path = "common/compact_bulk_memory.rs"]
mod compact_bulk_memory;
#[path = "common/compact_graph_collect.rs"]
mod compact_graph_collect;
#[path = "common/compact_graph_compare.rs"]
mod compact_graph_compare;
#[path = "common/compact_value_graph.rs"]
mod compact_value_graph;
#[path = "common/constant_typing.rs"]
mod constant_typing_cases;
#[path = "common/entry_integer_arguments.rs"]
mod entry_integer_argument_cases;
#[path = "common/enum_id_admission.rs"]
mod enum_id_admission_cases;
#[path = "common/exact_field_types.rs"]
mod exact_field_type_cases;
#[path = "common/float_minmax.rs"]
mod float_minmax_cases;
#[path = "common/function_memory.rs"]
mod function_memory_cases;
#[path = "common/function_namespace.rs"]
mod function_namespace_cases;
#[path = "common/generic_coro_all_blocks.rs"]
mod generic_coro_all_blocks_cases;
#[path = "common/generic_coro_expansion.rs"]
mod generic_coro_expansion_cases;
#[path = "common/generic_coro_prefix.rs"]
mod generic_coro_prefix_cases;
#[path = "common/generic_coro_prefix_seqmap.rs"]
mod generic_coro_prefix_seqmap_cases;
#[path = "common/graph_oracle.rs"]
mod graph_oracle;
#[path = "common/host_pointer_arguments.rs"]
mod host_pointer_argument_cases;
#[cfg(unix)]
#[path = "common/lake_build_concurrency.rs"]
mod lake_build_concurrency;
#[path = "common/null_constants.rs"]
mod null_constant_cases;
#[path = "common/null_constant_refusals.rs"]
mod null_constant_refusals;
#[path = "common/pointer_comparisons.rs"]
mod pointer_comparison_cases;
#[path = "common/pointer_observations.rs"]
mod pointer_observation_cases;
#[path = "common/scalar_bool_binops.rs"]
mod scalar_bool_binop_cases;
#[path = "common/scalar_memory.rs"]
mod scalar_memory_cases;
#[path = "common/ssa_char_validity.rs"]
mod ssa_char_validity_cases;

#[path = "common/typed_array_splat.rs"]
mod typed_array_splat_cases;
#[path = "common/vector_memory.rs"]
mod vector_memory_cases;
#[path = "common/vector_operations.rs"]
mod vector_operation_cases;
use common::Rng;
use common::exec_gen::{FnSpec, build_args, gen_module_exec, int_arg};

/// Generator seeds run through both engines. Each seed is a module of one to
/// three functions; the ledger below counts runs over exactly this range.
const SEEDS: std::ops::RangeInclusive<u64> = 1..=384;

/// The unsupported-coverage RATCHET: the exact number of corpus runs one
/// engine refused BY NAME (`unsupported.*` / `Unsupported*`). It may only go
/// down. Raising it means a construct the subset covers stopped executing in
/// one engine — a regression, not a ledger update. Lowering it (a depth-ledger
/// item landing) is the intended direction; edit the constant in the same
/// commit and say which feature moved. The per-feature breakdown is printed
/// with every run so the number is attributable.
const UNSUPPORTED_LEDGER: usize = 0;

/// The same ratchet over the SUBSET FIXTURES, pinned per `side:feature`: the
/// exact number of fixture runs one engine refused by name. Measured
/// 2026-09-23 (every refused run is printed, with its fixture, by `tally`):
///
/// The former four `lean:layout` refusals (`declared_tuple_v42` fn 0)
/// now execute and agree through the actual source-layout image service.
///
/// * `rust:unsupported_call` (4) — `abi_function_symbol` fn 1, a call to a
///   bodyless declaration: BOTH engines refuse it by name (`UnsupportedCall`
///   / `interprocedural_call`); `compare` attributes a two-sided refusal to
///   the interpreter, which it checks first.
///
/// A fixture added by another increment that hits an unmodelled construct
/// RAISES a count and must say so in its own commit; a depth-ledger item
/// landing lowers one. Either way the table is edited in the same commit.
const FIXTURE_UNSUPPORTED_LEDGER: &[(&str, usize)] = &[("rust:unsupported_call", 4)];

/// The exact number of fixture runs the interpreter filtered out as outside
/// the assumed domain (`AssumeViolated`, `Verdict::Vacuous`). Pinned, so a
/// vacuity filter can never grow into a silent skip. The generator corpus
/// mints no `Assume`, so its count is pinned at zero in its own test.
const FIXTURE_VACUOUS_LEDGER: usize = 0;

/// Fuel and call depth handed to BOTH engines. The corpus is loop-free and
/// shallow, so neither budget is reached; they are equal so an `out_of_fuel`
/// on one side can only mean a real divergence.
const FUEL: u64 = 10_000;
const CALL_DEPTH: u64 = 64;

// ---------------------------------------------------------------------------
// The canonical value and verdict grammar (shared with TrustIrEval/Run.lean)
// ---------------------------------------------------------------------------

/// A finite expected value or an independent SemR wire value.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Val {
    Int {
        width: u32,
        raw: u128,
    },
    Bool(bool),
    /// binary64 bits of a non-NaN float.
    Float(u64),
    /// NaN-ness only (payload residue, WS2.23).
    Nan,
    Ptr {
        null: bool,
    },
    /// A pointer with provenance, by its allocation and byte offset: the SemR
    /// differential's spelling (`semr_rust_val`, SemR's `renderVal`), so two
    /// pointers into different slots, or at different offsets, differ.
    PtrAt {
        alloc: u64,
        offset: u64,
    },
    FatPtr(Box<Val>, Box<Val>),
    Aggregate(Vec<Val>),
    /// Finite expected array contents; runtime arrays use compact graphs.
    Array(Vec<Val>),
    Vector(Vec<Val>),
    Sequence(Vec<Val>),
    Set(Vec<Val>),
    Record(Vec<(String, Val)>),
    Closure {
        func: u32,
        captures: Vec<Val>,
    },
    Function {
        signature: u32,
        func: u32,
    },
    Unit,
    /// An UNWRITTEN aggregate lane (crystal lane, E3b): the interpreter's
    /// `InterpretValueKind::Uninit`, the Lean model's `Value.uninit`.
    Uninit,
    /// A tensor value (v67, PKG-U13a): its element type by SemR's `IntTy`
    /// code (`semr_int_code`: exact, so `i32` and `u32` differ), its extents
    /// and its row-major element residues. Its own kind, so a tensor never
    /// compares equal to an aggregate of the same residues.
    Tensor {
        elem: u32,
        dims: Vec<u64>,
        elems: Vec<u128>,
    },
    /// Anything one engine spelled that the grammar does not carry; the
    /// rendering is kept so a mismatch names it.
    Other(String),
}

/// An engine's verdict on one run.
#[derive(Debug, Clone)]
enum Verdict {
    /// Finite expected values and the independent SemR wire protocol.
    Ok(Vec<Val>),
    /// Actual W5b successes, collected without logical expansion.
    Graph(compact_value_graph::Graph),
    Ub(String),
    /// A panic: its message and, for a sited check (amendment P, wire v54),
    /// its resolved site rendered `entry:E@global:G+O` / `entry:E@other`.
    Panic(String, Option<String>),
    Unsupported(String),
    OutOfFuel,
    /// The address space is exhausted (the interpreter's `OutOfMemory`).
    /// Only the SemR differential tells it from [`Verdict::OutOfFuel`]
    /// (`semr_rust_verdict`, `semr_verdicts`); the W5b rule keeps the two one
    /// class.
    OutOfMemory,
    TypeError(String),
    /// The oracle could not answer at all (not the schema, no reply): a broken
    /// harness, never an agreement.
    Error(String),
    /// The interpreter's `AssumeViolated` (WS2.11): an `Assume` condition was
    /// `false`, so this INPUT is outside the function's assumed domain — a
    /// vacuity filter over the entry parameters, not a program verdict. The
    /// Lean model runs `Assume` as a no-op (the ratified model split,
    /// `docs/ub-numerics-policy.md` §4), so there is nothing to compare; the
    /// run is counted and each test pins that count exactly.
    Vacuous(String),
}

// Runtime W5b results never pass through Val. This bridge encodes only finite
// handwritten expectations, keeping exact array/container tags. SemR-to-SemR
// equality retains allocation/offset observations rather than erasing them.
impl PartialEq for Verdict {
    fn eq(&self, other: &Self) -> bool {
        use Verdict::*;
        match (self, other) {
            (Graph(a), Graph(b)) => {
                compact_graph_compare::equivalent(a, b).is_ok_and(|comparison| comparison.equal)
            }
            (Graph(graph), Ok(values)) | (Ok(values), Graph(graph)) => expected_graph(values)
                .is_ok_and(|expected| {
                    compact_graph_compare::equivalent(graph, &expected)
                        .is_ok_and(|comparison| comparison.equal)
                }),
            (Ok(a), Ok(b)) => {
                a == b
                    || expected_graph(a).is_ok_and(|left| {
                        expected_graph(b).is_ok_and(|right| {
                            compact_graph_compare::equivalent(&left, &right)
                                .is_ok_and(|comparison| comparison.equal)
                        })
                    })
            }
            (Panic(a, sa), Panic(b, sb)) => a == b && sa == sb,
            (Ub(a), Ub(b))
            | (Unsupported(a), Unsupported(b))
            | (TypeError(a), TypeError(b))
            | (Error(a), Error(b))
            | (Vacuous(a), Vacuous(b)) => a == b,
            (OutOfFuel, OutOfFuel) | (OutOfMemory, OutOfMemory) => true,
            _ => false,
        }
    }
}
impl Eq for Verdict {}

#[path = "common/expected_graph.rs"]
mod expected_graph_encoding;
use expected_graph_encoding::expected_graph;

impl Verdict {
    fn class(&self) -> &'static str {
        match self {
            Verdict::Ok(_) | Verdict::Graph(_) => "ok",
            Verdict::Ub(_) => "ub",
            Verdict::Panic(..) => "panic",
            Verdict::Unsupported(_) => "unsupported",
            Verdict::OutOfFuel => "out_of_fuel",
            Verdict::OutOfMemory => "out_of_memory",
            Verdict::TypeError(_) => "type_error",
            Verdict::Error(_) => "error",
            Verdict::Vacuous(_) => "vacuous",
        }
    }
}

/// The one comparison rule.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Comparison {
    Agree,
    /// One side refused by name; `(side, feature)`.
    Unsupported(&'static str, String),
    /// The interpreter filtered the input out (`Verdict::Vacuous`).
    Vacuous,
    Mismatch(String),
}

fn compare(rust: &Verdict, lean: &Verdict) -> Comparison {
    match (rust, lean) {
        // A broken oracle is never coverage, whatever the interpreter said.
        (_, Verdict::Error(e)) => Comparison::Mismatch(format!("the oracle could not answer: {e}")),
        (Verdict::Error(e), _) => {
            Comparison::Mismatch(format!("Rust observation could not answer: {e}"))
        }
        (Verdict::Vacuous(_), _) => Comparison::Vacuous,
        (Verdict::Unsupported(f), _) => Comparison::Unsupported("rust", f.clone()),
        (_, Verdict::Unsupported(f)) => Comparison::Unsupported("lean", f.clone()),
        (Verdict::Ok(_) | Verdict::Graph(_), Verdict::Ok(_) | Verdict::Graph(_)) => {
            if rust == lean {
                Comparison::Agree
            } else {
                Comparison::Mismatch(format!("values differ: rust {rust:?} vs lean {lean:?}"))
            }
        }
        // Plan item P (wire v52): a panic names WHICH panic — both engines
        // derive the message from the failed assert's kind (`core`'s text),
        // so two panics agree only when the messages are equal. Amendment P
        // (wire v54): and only when their sites — the entry and the resolved
        // location — are equal too.
        (Verdict::Panic(a, site_a), Verdict::Panic(b, site_b)) => {
            if a != b {
                Comparison::Mismatch(format!("panic messages differ: rust {a:?} vs lean {b:?}"))
            } else if site_a != site_b {
                Comparison::Mismatch(format!(
                    "panic sites differ: rust {site_a:?} vs lean {site_b:?}"
                ))
            } else {
                Comparison::Agree
            }
        }
        (Verdict::Ub(_), Verdict::Ub(_))
        | (Verdict::OutOfFuel, Verdict::OutOfFuel)
        | (Verdict::OutOfMemory, Verdict::OutOfMemory) => Comparison::Agree,
        (r, l) => Comparison::Mismatch(format!(
            "verdict classes differ: rust {} ({r:?}) vs lean {} ({l:?})",
            r.class(),
            l.class()
        )),
    }
}

// --- the interpreter side ---------------------------------------------------

fn rust_val(v: &InterpretValue) -> Val {
    match &v.kind {
        InterpretValueKind::Int(i) => Val::Int {
            width: i.bits,
            raw: i.raw,
        },
        InterpretValueKind::Bool(b) => Val::Bool(*b),
        InterpretValueKind::FloatBits(bits) => {
            let f = match v.ty {
                Ty::F16 => trust_ir::interpret::f16_bits_to_f64(*bits as u16),
                Ty::F32 => f64::from(f32::from_bits(*bits as u32)),
                _ => f64::from_bits(*bits),
            };
            if f.is_nan() {
                Val::Nan
            } else {
                Val::Float(f.to_bits())
            }
        }
        InterpretValueKind::Ptr(_) | InterpretValueKind::DanglingPtr(_) => Val::Ptr { null: false },
        InterpretValueKind::NullPtr => Val::Ptr { null: true },
        InterpretValueKind::FatPtr { data, metadata } => {
            Val::FatPtr(Box::new(rust_val(data)), Box::new(rust_val(metadata)))
        }
        InterpretValueKind::Vector(vs) => Val::Vector(vs.iter().map(rust_val).collect()),
        InterpretValueKind::Aggregate(vs) => Val::Aggregate(vs.iter().map(rust_val).collect()),
        // Only the independent SemR/finite-fixture helper uses this recursive
        // value grammar. Ordinary W5b execution calls the graph collector.
        InterpretValueKind::Array(vs) => Val::Aggregate(vs.iter().map(rust_val).collect()),
        InterpretValueKind::Sequence(vs) => Val::Sequence(vs.iter().map(rust_val).collect()),
        InterpretValueKind::Set(vs) => Val::Set(vs.iter().map(rust_val).collect()),
        InterpretValueKind::Record(fs) => {
            Val::Record(fs.iter().map(|(n, v)| (n.clone(), rust_val(v))).collect())
        }
        InterpretValueKind::Closure { func, captures } => Val::Closure {
            func: func.0,
            captures: captures.iter().map(rust_val).collect(),
        },
        InterpretValueKind::FnDef(func) => match &v.ty {
            Ty::Func(signature) => Val::Function {
                signature: signature.0,
                func: func.0,
            },
            other => Val::Other(format!("FnDef at non-function type {other:?}")),
        },
        InterpretValueKind::Unit => Val::Unit,
        // The zero-size unit value is what the Lean model spells `PhantomData`
        // as (`Value.ofConstant .phantomData = .aggregate []`).
        InterpretValueKind::PhantomData => Val::Aggregate(Vec::new()),
        InterpretValueKind::Uninit => Val::Uninit,
        InterpretValueKind::Tensor { dims, elems } => {
            let residues: Option<Vec<u128>> = elems
                .iter()
                .map(|e| match &e.kind {
                    InterpretValueKind::Int(i) => Some(i.raw),
                    _ => None,
                })
                .collect();
            match (&v.ty, residues) {
                (Ty::Tensor(elem, _), Some(elems)) if elem.is_integer() => Val::Tensor {
                    elem: semr_int_code(elem),
                    dims: dims.clone(),
                    elems,
                },
                _ => Val::Other(format!("{:?}", v.kind)),
            }
        }
        other => Val::Other(format!("{other:?}")),
    }
}

fn rust_verdict(result: &Result<trust_ir::interpret::InterpretOutcome, InterpretError>) -> Verdict {
    match result {
        Ok(outcome) => {
            assert_eq!(
                outcome.host_calls, 0,
                "no host is installed, so no run can be host-assisted"
            );
            match compact_graph_collect::observe(&outcome.returns) {
                Ok(graph) => Verdict::Graph(graph),
                Err(error) => Verdict::Error(format!("Rust observation failed: {error}")),
            }
        }
        Err(e) => match e.code {
            InterpretErrorCode::UndefinedBehavior => Verdict::Ub(e.message.clone()),
            InterpretErrorCode::AssumeViolated => Verdict::Vacuous(e.message.clone()),
            InterpretErrorCode::Panic => Verdict::Panic(
                e.panic()
                    .map_or_else(|| e.message.clone(), |panic| panic.message()),
                e.panic().and_then(|panic| panic.site).map(|site| {
                    let location = match site.location {
                        trust_ir::interpret::PanicLocationValue::Global { global, offset } => {
                            format!("global:{}+{offset}", global.index())
                        }
                        trust_ir::interpret::PanicLocationValue::Other => "other".to_string(),
                    };
                    format!("entry:{}@{location}", site.entry.index())
                }),
            ),
            InterpretErrorCode::UnsupportedDialectOp
            | InterpretErrorCode::UnsupportedCall
            | InterpretErrorCode::UnsupportedMemory
            | InterpretErrorCode::UnsupportedVectorShape
            | InterpretErrorCode::UnsupportedInstruction
            | InterpretErrorCode::UnsupportedCast
            | InterpretErrorCode::UnsupportedFloat => Verdict::Unsupported(e.code.as_str().into()),
            InterpretErrorCode::OutOfFuel => Verdict::OutOfFuel,
            InterpretErrorCode::OutOfMemory => Verdict::OutOfMemory,
            InterpretErrorCode::TypeError
            | InterpretErrorCode::MissingFunction
            | InterpretErrorCode::InvalidFunctionPointer
            | InterpretErrorCode::SignatureMismatch
            | InterpretErrorCode::MissingBlock
            | InterpretErrorCode::MissingValue
            | InterpretErrorCode::MalformedInstruction => {
                Verdict::TypeError(format!("{}: {}", e.code, e.message))
            }
        },
    }
}

/// Run the interpreter on one function with the harness's budgets.
fn run_rust(module: &Module, func: FuncId, args: &[InterpretValue]) -> Verdict {
    run_rust_under(module, func, args, PanicStrategy::Abort)
}

/// [`run_rust`] under an explicit panic strategy (amendment D, Part 2).
fn run_rust_under(
    module: &Module,
    func: FuncId,
    args: &[InterpretValue],
    strategy: PanicStrategy,
) -> Verdict {
    let interp = Interpreter::with_module(module).with_options(InterpretOptions {
        fuel: FUEL,
        max_call_depth: CALL_DEPTH,
        panic_strategy: strategy,
    });
    rust_verdict(&interp.execute_func(func, args.to_vec()))
}

/// A witness of the format-permitted min/max zero choices actually returned
/// by this execution. Recording cannot select a result or alter a budget.
fn run_rust_with_float_choices(
    module: &Module,
    func: FuncId,
    args: &[InterpretValue],
) -> (Verdict, Vec<bool>) {
    let choices = std::sync::Mutex::new(Vec::new());
    let record = |choice| choices.lock().expect("choice recorder").push(choice);
    let interpreter = Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: FUEL,
            max_call_depth: CALL_DEPTH,
            panic_strategy: PanicStrategy::Abort,
        })
        .with_float_zero_choice_observer(&record);
    let verdict = rust_verdict(&interpreter.execute_func(func, args.to_vec()));
    (verdict, choices.into_inner().expect("choice recorder"))
}

// --- the Lean side ----------------------------------------------------------

/// A scalar or thin-pointer argument in the oracle's request grammar.
fn arg_json(v: &InterpretValue) -> Json {
    match &v.kind {
        InterpretValueKind::Int(i) => json!({"int": {"width": i.bits, "raw": i.raw.to_string()}}),
        InterpretValueKind::Bool(b) => json!({"bool": b}),
        InterpretValueKind::NullPtr => json!({"null_ptr": true}),
        InterpretValueKind::DanglingPtr(address) => json!({"dangling_ptr": address.to_string()}),
        other => panic!("unsupported oracle entry argument: {other:?}"),
    }
}

fn lean_val(j: &Json) -> Val {
    let obj = match j.as_object() {
        Some(o) if o.len() == 1 => o,
        _ => return Val::Other(j.to_string()),
    };
    let (tag, p) = obj.iter().next().expect("one key");
    let list = |p: &Json| -> Vec<Val> {
        p.as_array()
            .map(|a| a.iter().map(lean_val).collect())
            .unwrap_or_default()
    };
    match tag.as_str() {
        "int" => match (
            p["width"].as_u64(),
            p["raw"].as_str().and_then(|s| s.parse::<u128>().ok()),
        ) {
            (Some(width), Some(raw)) => Val::Int {
                width: width as u32,
                raw,
            },
            _ => Val::Other(j.to_string()),
        },
        "bool" => p
            .as_bool()
            .map(Val::Bool)
            .unwrap_or_else(|| Val::Other(j.to_string())),
        "float" => {
            if p.as_str() == Some("nan") {
                Val::Nan
            } else {
                match p["bits"].as_str().and_then(|s| s.parse::<u64>().ok()) {
                    Some(bits) => Val::Float(bits),
                    None => Val::Other(j.to_string()),
                }
            }
        }
        "ptr" => match (p["alloc"].as_u64(), p["offset"].as_u64()) {
            (Some(alloc), Some(offset)) => Val::PtrAt { alloc, offset },
            _ => Val::Ptr {
                null: p.as_str() == Some("null"),
            },
        },
        "fatptr" => Val::FatPtr(
            Box::new(lean_val(&p["data"])),
            Box::new(lean_val(&p["metadata"])),
        ),
        // The Lean unit value is the empty aggregate (`unitValue`), so a
        // `Ty::Unit` return renders as `{"aggregate": []}`; the interpreter's
        // `Unit` kind is mapped to the same spelling below.
        "aggregate" => Val::Aggregate(list(p)),
        "vector" => Val::Vector(list(p)),
        "sequence" => Val::Sequence(list(p)),
        "set" => Val::Set(list(p)),
        "record" => Val::Record(
            p.as_array()
                .map(|fs| {
                    fs.iter()
                        .map(|f| {
                            (
                                f[0].as_str().unwrap_or_default().to_string(),
                                lean_val(&f[1]),
                            )
                        })
                        .collect()
                })
                .unwrap_or_default(),
        ),
        "closure" => Val::Closure {
            func: p["func"].as_u64().unwrap_or(u64::MAX) as u32,
            captures: list(&p["captures"]),
        },
        "function" => Val::Function {
            signature: p["signature"].as_u64().unwrap_or(u64::MAX) as u32,
            func: p["func"].as_u64().unwrap_or(u64::MAX) as u32,
        },
        "uninit" if p.as_bool() == Some(true) => Val::Uninit,
        "tensor" => {
            let dims = p["dims"]
                .as_array()
                .and_then(|ds| ds.iter().map(Json::as_u64).collect::<Option<Vec<u64>>>());
            let elems = p["elems"].as_array().and_then(|xs| {
                xs.iter()
                    .map(|x| x.as_str().and_then(|s| s.parse::<u128>().ok()))
                    .collect::<Option<Vec<u128>>>()
            });
            match (p["elem"].as_u64(), dims, elems) {
                (Some(elem), Some(dims), Some(elems)) => Val::Tensor {
                    elem: elem as u32,
                    dims,
                    elems,
                },
                _ => Val::Other(j.to_string()),
            }
        }
        _ => Val::Other(j.to_string()),
    }
}

/// W5b successes require the whole-result graph protocol. Legacy successful
/// arrays are refused rather than accepted as an alternate execution format.
fn lean_verdict(j: &Json) -> Verdict {
    if let Some(values) = j.get("ok") {
        if j.as_object().is_none_or(|object| object.len() != 1) {
            return Verdict::Error(
                "successful verdict must contain only its graph observation".into(),
            );
        }
        return match compact_value_graph::Graph::decode(values) {
            Ok(graph) => Verdict::Graph(graph),
            Err(error) => Verdict::Error(format!("Lean observation failed: {error}")),
        };
    }
    status_or_semr_verdict(j)
}

/// SemR has its own scalar/provenance observation protocol.
fn status_or_semr_verdict(j: &Json) -> Verdict {
    let obj = match j.as_object() {
        Some(o) => o,
        None => return Verdict::Error(format!("verdict is not an object: {j}")),
    };
    if let Some(vals) = obj.get("ok").and_then(Json::as_array) {
        return Verdict::Ok(vals.iter().map(lean_val).collect());
    }
    let text = |k: &str| obj.get(k).and_then(Json::as_str).map(str::to_string);
    if let Some(m) = text("ub") {
        return Verdict::Ub(m);
    }
    if let Some(m) = text("panic") {
        // Amendment P: `site` is `{"entry": E, "location": {"global": G,
        // "offset": O} | "other"}`, absent for an unsited panic.
        let site = obj.get("site").map(|site| {
            let entry = site["entry"].as_u64().map_or("?".into(), |e| e.to_string());
            let location = match &site["location"] {
                Json::String(other) if other == "other" => "other".to_string(),
                location => format!(
                    "global:{}+{}",
                    location["global"]
                        .as_u64()
                        .map_or("?".into(), |g| g.to_string()),
                    location["offset"]
                        .as_u64()
                        .map_or("?".into(), |o| o.to_string())
                ),
            };
            format!("entry:{entry}@{location}")
        });
        return Verdict::Panic(m, site);
    }
    if let Some(f) = text("unsupported") {
        return Verdict::Unsupported(f);
    }
    if obj.get("out_of_fuel").is_some() {
        return Verdict::OutOfFuel;
    }
    if obj.get("out_of_memory").is_some() {
        return Verdict::OutOfMemory;
    }
    if let Some(m) = text("type_error") {
        return Verdict::TypeError(m);
    }
    Verdict::Error(text("error").unwrap_or_else(|| format!("unrecognised verdict: {j}")))
}

/// Normalise the interpreter's `Unit` to the Lean spelling (see `lean_val`).
fn canonical(v: Val) -> Val {
    match v {
        Val::Unit => Val::Aggregate(Vec::new()),
        Val::FatPtr(a, b) => Val::FatPtr(Box::new(canonical(*a)), Box::new(canonical(*b))),
        Val::Aggregate(vs) => Val::Aggregate(vs.into_iter().map(canonical).collect()),
        Val::Array(vs) => Val::Array(vs.into_iter().map(canonical).collect()),
        Val::Vector(vs) => Val::Vector(vs.into_iter().map(canonical).collect()),
        Val::Sequence(vs) => Val::Sequence(vs.into_iter().map(canonical).collect()),
        Val::Set(vs) => Val::Set(vs.into_iter().map(canonical).collect()),
        Val::Record(fs) => Val::Record(fs.into_iter().map(|(n, v)| (n, canonical(v))).collect()),
        Val::Closure { func, captures } => Val::Closure {
            func,
            captures: captures.into_iter().map(canonical).collect(),
        },
        other => other,
    }
}

fn canonical_verdict(v: Verdict) -> Verdict {
    match v {
        Verdict::Ok(vs) => Verdict::Ok(vs.into_iter().map(canonical).collect()),
        other => other,
    }
}

// ---------------------------------------------------------------------------
// Locating and building the oracle
// ---------------------------------------------------------------------------

fn lean_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean/trust_ir-semantics")
}

/// `lake`, if this machine has one: `TRUST_IR_LAKE`, `$HOME/.elan/bin/lake`,
/// or `lake` on `PATH`.
fn find_lake() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("TRUST_IR_LAKE") {
        return Some(PathBuf::from(p));
    }
    if let Some(home) = std::env::var_os("HOME") {
        let elan = Path::new(&home).join(".elan/bin/lake");
        if elan.is_file() {
            return Some(elan);
        }
    }
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|d| d.join("lake"))
        .find(|p| p.is_file())
}

/// SemR pins a different Lean version from the TrustIR semantics package.
/// A direct Lake executable cannot dispatch like an elan shim, so allow an
/// explicit package-specific executable. Build failure remains mandatory when
/// the oracle is required; this does not substitute or rewrite a toolchain pin.
fn find_semr_lake() -> Option<PathBuf> {
    std::env::var_os("TRUST_IR_SEMR_LAKE")
        .map(PathBuf::from)
        .or_else(find_lake)
}

/// Prevent an ambient xcrun-injected SDKROOT from changing Lake's source-defined
/// C toolchain policy. Builds and context-aware direct runs share the same policy;
/// the actual Lean/compiler/linker/SDK inputs remain part of each native receipt.
const LAKE_SCRUBBED_ENV: &[&str] = &["SDKROOT"];

/// A Lake build holds its package's lock until the subprocess finishes.
/// Separate targets share imported outputs, so target names cannot identify
/// independent builds. Canonical paths also join callers using symlink aliases.
struct LakePackageCommand {
    command: Command,
    package: PathBuf,
}

impl LakePackageCommand {
    fn arg(&mut self, arg: impl AsRef<std::ffi::OsStr>) -> &mut Self {
        self.command.arg(arg);
        self
    }

    fn output(&mut self) -> std::io::Result<std::process::Output> {
        static LOCKS: OnceLock<Mutex<BTreeMap<PathBuf, Weak<Mutex<()>>>>> = OnceLock::new();
        let package = self.package.canonicalize()?;
        let lock = {
            let mut locks = LOCKS
                .get_or_init(Mutex::default)
                .lock()
                .expect("Lake build lock registry");
            locks.retain(|_, lock| lock.strong_count() != 0);
            if let Some(lock) = locks.get(&package).and_then(Weak::upgrade) {
                lock
            } else {
                let lock = Arc::new(Mutex::new(()));
                locks.insert(package, Arc::downgrade(&lock));
                lock
            }
        };
        let _build = lock.lock().expect("Lake package build lock");
        self.command.output()
    }
}

// Preserve command inspection (including the SDKROOT control) without exposing
// mutable Command methods that could execute a build without its package lock.
impl std::ops::Deref for LakePackageCommand {
    type Target = Command;

    fn deref(&self) -> &Self::Target {
        &self.command
    }
}

/// Shared environment and canonical package lock for every build-capable Lake command.
fn lake_package_command(lake: &Path, dir: &Path) -> LakePackageCommand {
    // `lake` needs `lean` beside it on PATH.
    let mut path = std::env::var_os("PATH").unwrap_or_default();
    if let Some(bin) = lake.parent() {
        let mut joined = std::ffi::OsString::from(bin);
        joined.push(":");
        joined.push(&path);
        path = joined;
    }
    let mut cmd = Command::new(lake);
    cmd.current_dir(dir).env("PATH", path);
    for name in LAKE_SCRUBBED_ENV {
        cmd.env_remove(name);
    }
    LakePackageCommand {
        command: cmd,
        package: dir.to_owned(),
    }
}

fn lake_build_command(lake: &Path, dir: &Path, target: &str) -> LakePackageCommand {
    let mut command = lake_package_command(lake, dir);
    command.arg("build").arg(target);
    command
}

/// Lake builds/loads precompiled provider imports before executing the file.
/// This command can write the package cache, so it holds the same lock as builds.
fn lake_run_command(lake: &Path, dir: &Path, file: &str) -> LakePackageCommand {
    let mut command = lake_package_command(lake, dir);
    // Lean 4.8 still parses dashed program arguments unless option parsing ends.
    command
        .arg("lean")
        .arg(file)
        .arg("--")
        .arg("--run")
        .arg("--");
    command
}

#[derive(Debug)]
enum Oracle {
    Ready(PathBuf),
    /// No `lake` on this machine (and `TRUST_IR_REQUIRE_LEAN` unset).
    Absent,
}

/// Retain build failures too: panicking inside `get_or_init` leaves the cell
/// empty and makes the next differential repeat the same failed build.
fn cached_oracle(
    cache: &OnceLock<Result<Oracle, String>>,
    build: impl FnOnce() -> Result<Oracle, String>,
) -> &Oracle {
    match cache.get_or_init(build) {
        Ok(oracle) => oracle,
        Err(diagnostic) => panic!("{diagnostic}"),
    }
}

/// Build `trustir_eval` once per test process and return its path.
fn oracle() -> &'static Oracle {
    static ORACLE: OnceLock<Result<Oracle, String>> = OnceLock::new();
    cached_oracle(&ORACLE, || {
        let require = std::env::var("TRUST_IR_REQUIRE_LEAN")
            .map(|v| v == "1")
            .unwrap_or(false);
        let Some(lake) = find_lake() else {
            if require {
                return Err(
                    "TRUST_IR_REQUIRE_LEAN=1 but no `lake` was found (TRUST_IR_LAKE, \
                     $HOME/.elan/bin/lake, PATH)"
                        .to_owned(),
                );
            }
            eprintln!(
                "SKIPPED: the Lean-execution oracle needs `lake` (elan); none found. \
                 Set TRUST_IR_REQUIRE_LEAN=1 to make this a failure."
            );
            return Ok(Oracle::Absent);
        };
        let dir = lean_dir();
        let out = lake_build_command(&lake, &dir, "trustir_eval")
            .output()
            .map_err(|e| format!("cannot run {}: {e}", lake.display()))?;
        if !out.status.success() {
            return Err(format!(
                "`lake build trustir_eval` failed in {}:\n{}\n{}",
                dir.display(),
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            ));
        }
        let exe = dir.join(".lake/build/bin/trustir_eval");
        if !exe.is_file() {
            return Err(format!(
                "lake reported success but {} is missing",
                exe.display()
            ));
        }
        Ok(Oracle::Ready(exe))
    })
}

/// One module's runs: `(function, args)` per run.
struct Batch<'m> {
    label: String,
    module: &'m Module,
    runs: Vec<(FuncId, Vec<InterpretValue>)>,
}

/// A module that owns its runs: one SemR differential's corpus, which its
/// own test and the parity gate on SemR (`semr_gate_runs`) both run.
struct SemrCase {
    label: String,
    module: Module,
    runs: Vec<(FuncId, Vec<InterpretValue>)>,
}

impl SemrCase {
    fn batch(&self) -> Batch<'_> {
        Batch {
            label: self.label.clone(),
            module: &self.module,
            runs: self.runs.clone(),
        }
    }
}

/// Send every batch to the oracle in ONE process and return one verdict per
/// run, per batch. The request is written straight to bytes, module by
/// module: `serde_json::to_value` cannot hold a 128-bit integer outside the
/// i64/u64 range ("number out of range"), and a module's unwrapped 128-bit
/// fields (an `EnumDef`'s explicit discriminants, for one) are exactly what
/// the writer-based serializer, and the Lean JSON reader, carry natively.
fn run_lean(exe: &Path, batches: &[Batch<'_>]) -> Vec<Vec<Verdict>> {
    run_lean_under(exe, batches, None)
}

/// [`run_lean`] with the request's optional `panic_strategy` field (amendment
/// D, Part 2): `None` omits it (the oracle's default, `abort`).
fn run_lean_under(
    exe: &Path,
    batches: &[Batch<'_>],
    strategy: Option<PanicStrategy>,
) -> Vec<Vec<Verdict>> {
    run_lean_under_with_float_choices(exe, batches, strategy, None)
}

fn run_lean_under_with_float_choices(
    exe: &Path,
    batches: &[Batch<'_>],
    strategy: Option<PanicStrategy>,
    choices: Option<&[Vec<Vec<bool>>]>,
) -> Vec<Vec<Verdict>> {
    if let Some(choices) = choices {
        assert_eq!(choices.len(), batches.len(), "choice batch census");
        for (choices, batch) in choices.iter().zip(batches) {
            assert_eq!(choices.len(), batch.runs.len(), "choice run census");
        }
    }
    let strategy_field = match strategy {
        None => String::new(),
        Some(PanicStrategy::Abort) => "\"panic_strategy\":\"abort\",".to_string(),
        Some(PanicStrategy::Unwind) => "\"panic_strategy\":\"unwind\",".to_string(),
    };
    let mut request =
        format!("{{{strategy_field}\"fuel\":{FUEL},\"call_depth\":{CALL_DEPTH},\"batches\":[");
    for (i, b) in batches.iter().enumerate() {
        if i > 0 {
            request.push(',');
        }
        let runs: Vec<Json> = b
            .runs
            .iter()
            .enumerate()
            .map(|(run_index, (f, args))| {
                let mut request = json!({
                    "function": f.0,
                    "args": args.iter().map(arg_json).collect::<Vec<_>>(),
                });
                if let Some(choices) = choices {
                    request["float_zero_choices"] = json!(choices[i][run_index]);
                }
                request
            })
            .collect();
        request.push_str("{\"module\":");
        request.push_str(&serde_json::to_string(b.module).expect("module serializes"));
        request.push_str(",\"runs\":");
        request.push_str(&serde_json::to_string(&runs).expect("runs serialize"));
        request.push('}');
    }
    request.push_str("]}");
    let tmp = std::env::temp_dir().join(format!(
        "trustir-w5b-{}-{}.json",
        std::process::id(),
        std::thread::current()
            .name()
            .unwrap_or("t")
            .replace("::", "_")
    ));
    fs::write(&tmp, request.as_bytes()).expect("write oracle request");
    let out = Command::new(exe)
        .arg(&tmp)
        .output()
        .unwrap_or_else(|e| panic!("cannot run {}: {e}", exe.display()));
    // Optional evidence records the exact request/response bytes before the
    // ordinary parser and comparator run. Each test thread has its own name.
    if let Some(directory) = std::env::var_os("TRUST_IR_ORACLE_EVIDENCE_DIR") {
        let directory = PathBuf::from(directory);
        fs::create_dir_all(&directory).expect("create oracle evidence directory");
        let stem = tmp.file_stem().unwrap().to_string_lossy();
        fs::write(
            directory.join(format!("{stem}.request.json")),
            request.as_bytes(),
        )
        .expect("record oracle request");
        fs::write(directory.join(format!("{stem}.response.json")), &out.stdout)
            .expect("record oracle response");
        fs::write(directory.join(format!("{stem}.stderr.txt")), &out.stderr)
            .expect("record oracle diagnostics");
    }
    let _ = fs::remove_file(&tmp);
    assert!(
        out.status.success(),
        "trustir_eval exited with {}:\n{}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    let reply: Json = serde_json::from_slice(&out.stdout).unwrap_or_else(|e| {
        panic!(
            "oracle reply is not JSON ({e}): {}",
            String::from_utf8_lossy(&out.stdout)
        )
    });
    let lists = reply
        .as_array()
        .unwrap_or_else(|| panic!("oracle refused the whole request: {reply}"));
    assert_eq!(lists.len(), batches.len(), "one verdict list per batch");
    lists
        .iter()
        .zip(batches)
        .map(|(list, batch)| {
            let verdicts = list.as_array().unwrap_or_else(|| {
                panic!("batch {}: oracle reply is not a list: {list}", batch.label)
            });
            assert_eq!(
                verdicts.len(),
                batch.runs.len(),
                "batch {}: one verdict per run",
                batch.label
            );
            verdicts.iter().map(lean_verdict).collect()
        })
        .collect()
}

// ---------------------------------------------------------------------------
// The corpus
// ---------------------------------------------------------------------------

/// A parameter the harness can build a scalar argument for: `Bool` and the
/// fixed-width integers (the generator's palette). `Isize` / `Usize` (whose
/// width the interpreter resolves against the module's target, while the
/// model pins 64) and `Char` (whose argument must be a Unicode scalar value)
/// have no engine-neutral argument spelling here, so a function taking one
/// is not run — narrower coverage, never a silent agreement.
fn scalar_param(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Bool
            | Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
    )
}

/// The runnable functions of a module: definitions whose parameters are all
/// scalar. `n` argument vectors per function, from a fixed-seed RNG.
fn module_runs(module: &Module, n: u32, seed: u64) -> Vec<(FuncId, Vec<InterpretValue>)> {
    let mut rng = Rng::new(seed);
    let mut runs = Vec::new();
    for f in &module.functions {
        if f.is_declaration() {
            continue;
        }
        let Some(sig) = module.func_type(f.ty) else {
            continue;
        };
        if !sig.params.iter().all(scalar_param) {
            continue;
        }
        for _ in 0..n {
            let args = sig
                .params
                .iter()
                .map(|p| match p {
                    Ty::Bool => InterpretValue::bool(rng.bool()),
                    other => int_arg(other, &mut rng),
                })
                .collect();
            runs.push((f.id, args));
        }
    }
    runs
}

fn fixtures_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

/// Every JSON fixture that is a module, validates, and is inside the
/// lowering-target subset — the "subset fixtures". Sorted by name.
fn subset_fixtures() -> Vec<(String, Module)> {
    let mut out = Vec::new();
    let mut names: Vec<PathBuf> = fs::read_dir(fixtures_dir())
        .expect("fixtures dir")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|e| e == "json"))
        .collect();
    names.sort();
    for path in names {
        let text = fs::read_to_string(&path).expect("read fixture");
        let Ok(module) = serde_json::from_str::<Module>(&text) else {
            continue; // not a module (bundles, oracles, lineage manifests)
        };
        if !trust_ir_build::validate_module(&module).is_empty() {
            continue;
        }
        if !module_subset_violations(&module).is_empty() {
            continue;
        }
        let name = path.file_stem().unwrap().to_string_lossy().into_owned();
        out.push((name, module));
    }
    out
}

/// One run's comparison, with the coordinates a failure message needs.
#[derive(Debug)]
struct RunReport {
    label: String,
    func: FuncId,
    args: Vec<InterpretValue>,
    rust: Verdict,
    lean: Verdict,
    comparison: Comparison,
}

/// Run every batch through both engines and compare run by run.
fn differential(exe: &Path, batches: &[Batch<'_>]) -> Vec<RunReport> {
    let rust: Vec<Vec<_>> = batches
        .iter()
        .map(|batch| {
            batch
                .runs
                .iter()
                .map(|(func, args)| run_rust_with_float_choices(batch.module, *func, args))
                .collect()
        })
        .collect();
    let choices: Vec<Vec<_>> = rust
        .iter()
        .map(|batch| batch.iter().map(|(_, choices)| choices.clone()).collect())
        .collect();
    let lean = run_lean_under_with_float_choices(exe, batches, None, Some(&choices));
    let mut reports = Vec::new();
    for ((batch, rust_verdicts), lean_verdicts) in batches.iter().zip(rust).zip(lean) {
        for (((func, args), (rust, _)), lean) in
            batch.runs.iter().zip(rust_verdicts).zip(lean_verdicts)
        {
            let rust = canonical_verdict(rust);
            let lean = canonical_verdict(lean);
            let comparison = compare(&rust, &lean);
            reports.push(RunReport {
                label: batch.label.clone(),
                func: *func,
                args: args.clone(),
                rust,
                lean,
                comparison,
            });
        }
    }
    reports
}

/// Ordinary code-plus-environment spelling: two ternary implementations, one
/// shared dispatcher, a forwarding call, a returned function value, and a
/// state update between applications. No TLA-specific opcode or host model.
fn typed_function_environment_module(expired: bool) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new_with_target_info(
        "typed_function_environments",
        trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        },
    );
    let op = mb.add_func_type(vec![Ty::Ptr, Ty::I64, Ty::I64, Ty::I64], vec![Ty::I64]);
    let dispatch_sig = mb.add_func_type(
        vec![Ty::Func(op), Ty::Ptr, Ty::I64, Ty::I64, Ty::I64],
        vec![Ty::I64],
    );
    let provider_sig = mb.add_func_type(vec![], vec![Ty::Func(op)]);
    let ignore_sig = mb.add_func_type(vec![Ty::Func(op)], vec![Ty::I64]);
    let root_sig = mb.add_func_type(
        vec![],
        vec![Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::Func(op)],
    );
    let mut implementations = Vec::new();
    for multiply in [false, true] {
        let mut fb = mb.function(if multiply { "product" } else { "sum" }, op);
        let entry = fb.create_block();
        let env = fb.add_block_param(entry, Ty::Ptr);
        let x = fb.add_block_param(entry, Ty::I64);
        let y = fb.add_block_param(entry, Ty::I64);
        let z = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let bias = fb.load(Ty::I64, env);
        let xy = if multiply {
            fb.mul(Ty::I64, x, y)
        } else {
            fb.add(Ty::I64, x, y)
        };
        let xyz = fb.add(Ty::I64, xy, z);
        let result = fb.add(Ty::I64, bias, xyz);
        fb.ret(vec![result]);
        implementations.push(fb.build());
    }
    let dispatch = {
        let mut fb = mb.function("dispatch", dispatch_sig);
        let entry = fb.create_block();
        let callback = fb.add_block_param(entry, Ty::Func(op));
        let env = fb.add_block_param(entry, Ty::Ptr);
        let x = fb.add_block_param(entry, Ty::I64);
        let y = fb.add_block_param(entry, Ty::I64);
        let z = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let result = fb.call_indirect(callback, op, vec![env, x, y, z]);
        fb.ret(vec![result]);
        fb.build()
    };
    let forward = {
        let mut fb = mb.function("forward", dispatch_sig);
        let entry = fb.create_block();
        let args = [Ty::Func(op), Ty::Ptr, Ty::I64, Ty::I64, Ty::I64]
            .into_iter()
            .map(|ty| fb.add_block_param(entry, ty))
            .collect();
        fb.switch_to_block(entry);
        let result = fb.call(dispatch, args);
        fb.ret(vec![result]);
        fb.build()
    };
    let provider = {
        let mut fb = mb.function("provider", provider_sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let callback = fb.fn_addr(op, implementations[1]);
        fb.ret(vec![callback]);
        fb.build()
    };
    let ignored = mb.declare_function("unavailable_but_unused", op);
    let ignore = {
        let mut fb = mb.function("ignore", ignore_sig);
        let entry = fb.create_block();
        fb.add_block_param(entry, Ty::Func(op));
        fb.switch_to_block(entry);
        let result = fb.iconst(Ty::I64, 77);
        fb.ret(vec![result]);
        fb.build()
    };
    let root = {
        let mut fb = mb.function("program", root_sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let env1 = fb.alloca(Ty::I64);
        let env2 = fb.alloca(Ty::I64);
        let ten = fb.iconst(Ty::I64, 10);
        let hundred = fb.iconst(Ty::I64, 100);
        fb.store(Ty::I64, env1, ten);
        fb.store(Ty::I64, env2, hundred);
        let cb1 = fb.fn_addr(op, implementations[0]);
        let cb2 = fb.call(provider, vec![]);
        let unused = fb.fn_addr(op, ignored);
        let lazy = fb.call(ignore, vec![unused]);
        let x = fb.iconst(Ty::I64, 1);
        let y = fb.iconst(Ty::I64, 2);
        let z = fb.iconst(Ty::I64, 3);
        let a = fb.call(forward, vec![cb1, env1, x, y, z]);
        let b = fb.call(forward, vec![cb2, env2, x, y, z]);
        let twenty = fb.iconst(Ty::I64, 20);
        fb.store(Ty::I64, env1, twenty);
        if expired {
            fb.dealloc(env1);
        }
        let c = fb.call(forward, vec![cb1, env1, x, y, z]);
        fb.ret(vec![a, b, c, lazy, cb2]);
        fb.build()
    };
    (
        mb.build().expect("typed function environment fixture"),
        root,
    )
}

#[test]
fn typed_function_values_cross_calls_and_environments() {
    let mut modules = Vec::new();
    for expired in [false, true] {
        let (module, root) = typed_function_environment_module(expired);
        let binary = trust_ir::binary::serialize_module(&module).expect("callable binary");
        let text = trust_ir::format::text_checked(&module).expect("callable text");
        let json = serde_json::to_vec(&module).expect("callable JSON");
        let msgpack = rmp_serde::to_vec(&module).expect("callable MessagePack");
        for (format, decoded) in [
            ("original", module),
            (
                "binary",
                trust_ir::binary::deserialize_module(&binary).expect("callable binary decode"),
            ),
            (
                "text",
                trust_ir::parser::parse_module(&text).expect("callable text decode"),
            ),
            (
                "JSON",
                serde_json::from_slice(&json).expect("callable JSON decode"),
            ),
            (
                "MessagePack",
                rmp_serde::from_slice(&msgpack).expect("callable MessagePack decode"),
            ),
        ] {
            modules.push((format, decoded, root, expired));
        }
    }
    let mut batches = Vec::new();
    for (format, module, root, expired) in &modules {
        let errors = trust_ir_build::validate_module(module);
        assert!(errors.is_empty(), "{format}/expired={expired}: {errors:#?}");
        let result = run_rust(module, *root, &[]);
        if !expired {
            assert_eq!(
                result,
                Verdict::Ok(vec![
                    Val::Int { width: 64, raw: 16 },
                    Val::Int {
                        width: 64,
                        raw: 105
                    },
                    Val::Int { width: 64, raw: 26 },
                    Val::Int { width: 64, raw: 77 },
                    Val::Function {
                        signature: 0,
                        func: 1
                    },
                ])
            );
        } else {
            assert!(matches!(result, Verdict::Ub(_)), "{result:?}");
        }
        batches.push(Batch {
            label: format!("typed-functions-{format}-expired-{expired}"),
            module,
            runs: vec![(*root, vec![])],
        });
    }
    let Oracle::Ready(exe) = oracle() else {
        return;
    };
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 10);
    for report in reports {
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
}

/// Min/max is callable through the original function table. An unknown future
/// operator in one encoded body remains lazy data until that target is called.
#[test]
fn typed_function_target_decode_failure_is_lazy_and_fail_closed() {
    let mut mb = ModuleBuilder::new("lazy_function_target");
    let op = mb.add_func_type(vec![], vec![Ty::F64]);
    let ignore_sig = mb.add_func_type(vec![Ty::Func(op)], vec![Ty::I64]);
    let unused_sig = mb.add_func_type(vec![], vec![Ty::I64]);
    let target = {
        let mut fb = mb.function("out_of_fragment", op);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let a = fb.fconst(Ty::F64, 1.5);
        let b = fb.fconst(Ty::F64, 2.5);
        let result = fb.binop(trust_ir::inst::BinOp::FMin, Ty::F64, a, b);
        fb.ret(vec![result]);
        fb.build()
    };
    let ignore = {
        let mut fb = mb.function("ignore", ignore_sig);
        let entry = fb.create_block();
        fb.add_block_param(entry, Ty::Func(op));
        fb.switch_to_block(entry);
        let result = fb.iconst(Ty::I64, 42);
        fb.ret(vec![result]);
        fb.build()
    };
    let unused = {
        let mut fb = mb.function("unused", unused_sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let callback = fb.fn_addr(op, target);
        let result = fb.call(ignore, vec![callback]);
        fb.ret(vec![result]);
        fb.build()
    };
    let used = {
        let mut fb = mb.function("used", op);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let callback = fb.fn_addr(op, target);
        let result = fb.call_indirect(callback, op, vec![]);
        fb.ret(vec![result]);
        fb.build()
    };
    let module = mb.build().expect("lazy function target fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let expected = Verdict::Ok(vec![Val::Int { width: 64, raw: 42 }]);
    assert_eq!(run_rust(&module, unused, &[]), expected);
    assert_eq!(
        run_rust(&module, used, &[]),
        Verdict::Ok(vec![Val::Float(1.5f64.to_bits())])
    );
    let Oracle::Ready(exe) = oracle() else {
        return;
    };
    let reports = differential(
        exe,
        &[Batch {
            label: "lazy decoded target".into(),
            module: &module,
            runs: vec![(unused, vec![]), (used, vec![])],
        }],
    );
    assert_eq!(reports.len(), 2);
    assert_eq!(reports[0].lean, expected);
    assert_eq!(reports[0].comparison, Comparison::Agree);
    assert_eq!(
        reports[1].lean,
        Verdict::Ok(vec![Val::Float(1.5f64.to_bits())])
    );
    assert_eq!(reports[1].comparison, Comparison::Agree);

    // This is a decoder-boundary mutation, not an admitted Rust Module.
    let mut future = serde_json::to_value(&module).expect("lazy target JSON");
    let operator = &mut future["functions"][0]["blocks"][0]["body"][2]["inst"]["BinOp"]["op"];
    assert_eq!(*operator, json!("FMin"));
    *operator = json!("FutureMinMax");
    let request = json!({"fuel": FUEL, "call_depth": CALL_DEPTH, "batches": [{
        "module": future,
        "runs": [
            {"function": unused.0, "args": []},
            {"function": used.0, "args": []},
            {"function": target.0, "args": []}
        ],
    }]});
    let path =
        std::env::temp_dir().join(format!("trustir-lazy-future-{}.json", std::process::id()));
    fs::write(&path, serde_json::to_vec(&request).unwrap())
        .expect("write future operator mutation");
    let output = Command::new(exe)
        .arg(&path)
        .output()
        .expect("run future operator mutation");
    fs::remove_file(path).expect("remove future operator mutation");
    assert!(output.status.success(), "{output:?}");
    let reply: Json = serde_json::from_slice(&output.stdout).expect("future operator reply");
    let values = reply[0].as_array().expect("one batch of three verdicts");
    assert_eq!(values.len(), 3);
    assert_eq!(lean_verdict(&values[0]), expected);
    assert_eq!(
        lean_verdict(&values[1]),
        Verdict::Unsupported("interprocedural_call".into())
    );
    assert_eq!(
        lean_verdict(&values[2]),
        Verdict::Unsupported("binop.FutureMinMax".into())
    );
}

#[test]
fn float_absolute_value_agrees_at_both_widths() {
    float_unary_cases(&[trust_ir::UnOp::FAbs]);
}

#[test]
fn float_integral_rounding_agrees_at_both_widths() {
    float_unary_cases(&[
        trust_ir::UnOp::FFloor,
        trust_ir::UnOp::FCeil,
        trust_ir::UnOp::FTrunc,
    ]);
}

#[test]
fn float_square_root_agrees_at_both_widths() {
    float_unary_cases(&[trust_ir::UnOp::FSqrt]);
}

#[test]
fn float_binary16_images_and_extensions_agree_exhaustively() {
    use trust_ir::inst::CastOp;
    let mut mb = ModuleBuilder::new("binary16_images");
    let view_sig = mb.add_func_type(
        vec![Ty::U16],
        vec![Ty::F16, Ty::F32, Ty::F64, Ty::F16, Ty::F16],
    );
    let bits_sig = mb.add_func_type(vec![Ty::U16], vec![Ty::U16, Ty::U16]);
    let view = {
        let mut fb = mb.function("view", view_sig);
        let entry = fb.create_block();
        let raw = fb.add_block_param(entry, Ty::U16);
        fb.switch_to_block(entry);
        let half = fb.cast(CastOp::Bitcast, Ty::U16, Ty::F16, raw);
        let single = fb.cast(CastOp::FPExt, Ty::F16, Ty::F32, half);
        let double = fb.cast(CastOp::FPExt, Ty::F16, Ty::F64, half);
        let neg = fb.unop(trust_ir::UnOp::FNeg, Ty::F16, half);
        let slot = fb.alloca(Ty::U16);
        fb.store(Ty::U16, slot, raw);
        let loaded = fb.load(Ty::F16, slot);
        fb.ret(vec![half, single, double, neg, loaded]);
        fb.build()
    };
    let bytes = {
        let mut fb = mb.function("bytes", bits_sig);
        let entry = fb.create_block();
        let raw = fb.add_block_param(entry, Ty::U16);
        fb.switch_to_block(entry);
        let half = fb.cast(CastOp::Bitcast, Ty::U16, Ty::F16, raw);
        let bits = fb.cast(CastOp::Bitcast, Ty::F16, Ty::U16, half);
        let slot = fb.alloca(Ty::F16);
        fb.store(Ty::F16, slot, half);
        let loaded = fb.load(Ty::F16, slot);
        let loaded_bits = fb.cast(CastOp::Bitcast, Ty::F16, Ty::U16, loaded);
        fb.ret(vec![bits, loaded_bits]);
        fb.build()
    };
    let module = mb.build().expect("binary16 image module");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let mut runs = Vec::new();
    let mut expected = Vec::new();
    let val = |f: f64| {
        if f.is_nan() {
            Val::Nan
        } else {
            Val::Float(f.to_bits())
        }
    };
    for raw in 0..=u16::MAX {
        let f = trust_ir::interpret::f16_bits_to_f64(raw);
        let args = vec![InterpretValue::int(Ty::U16, i128::from(raw)).unwrap()];
        runs.push((view, args.clone()));
        expected.push(Verdict::Ok(vec![val(f), val(f), val(f), val(-f), val(f)]));
        // NaN payloads are unobservable in pinned Lean; exposing their bits
        // remains an explicit refusal, covered by separate negative controls.
        if !f.is_nan() {
            runs.push((bytes, args));
            let raw = Val::Int {
                width: 16,
                raw: u128::from(raw),
            };
            expected.push(Verdict::Ok(vec![raw.clone(), raw]));
        }
    }
    assert_eq!(runs.len(), 129_026);
    let Oracle::Ready(exe) = oracle() else { return };
    let reports = differential(
        exe,
        &[Batch {
            label: "all binary16 images, extensions, negation and non-NaN byte round trips".into(),
            module: &module,
            runs,
        }],
    );
    assert_eq!(reports.len(), expected.len());
    for (report, expected) in reports.iter().zip(&expected) {
        assert_eq!(&report.rust, expected, "{report:?}");
        assert_eq!(&report.lean, expected, "{report:?}");
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
}

#[test]
fn float_binary16_arithmetic_agrees() {
    use trust_ir::inst::{BinOp, CastOp};
    let ops = [
        BinOp::FAdd,
        BinOp::FSub,
        BinOp::FMul,
        BinOp::FDiv,
        BinOp::FRem,
    ];
    let mut mb = ModuleBuilder::new("binary16_arithmetic");
    let sig = mb.add_func_type(vec![Ty::U16, Ty::U16], vec![Ty::F16; 5]);
    let mut fb = mb.function("arithmetic", sig);
    let entry = fb.create_block();
    let lhs = fb.add_block_param(entry, Ty::U16);
    let rhs = fb.add_block_param(entry, Ty::U16);
    fb.switch_to_block(entry);
    let lhs = fb.cast(CastOp::Bitcast, Ty::U16, Ty::F16, lhs);
    let rhs = fb.cast(CastOp::Bitcast, Ty::U16, Ty::F16, rhs);
    let results = ops.map(|op| fb.binop(op, Ty::F16, lhs, rhs));
    fb.ret(results.to_vec());
    let function = fb.build();
    let module = mb.build().expect("binary16 arithmetic module");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let edges = [
        0, 1, 0x3ff, 0x400, 0x3bff, 0x3c00, 0x3c01, 0x7bff, 0x7c00, 0x7e01, 0x8000, 0x8001, 0xbc00,
        0xfbff, 0xfc00, 0xfe01,
    ];
    let mut pairs: Vec<_> = edges
        .iter()
        .flat_map(|&a| edges.iter().map(move |&b| (a, b)))
        .collect();
    let mut seed = 0x519d_e822_405a_7c01u64;
    for _ in 0..4096 {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        pairs.push((seed as u16, (seed >> 32) as u16));
    }
    let mut runs = Vec::new();
    let mut expected = Vec::new();
    for (a, b) in pairs {
        let a_value = trust_ir::interpret::f16_bits_to_f64(a) as f32;
        let b_value = trust_ir::interpret::f16_bits_to_f64(b) as f32;
        let values = [
            a_value + b_value,
            a_value - b_value,
            a_value * b_value,
            a_value / b_value,
            a_value % b_value,
        ];
        expected.push(Verdict::Ok(
            values
                .into_iter()
                .map(|value| {
                    let rounded = trust_ir::interpret::f16_bits_to_f64(
                        trust_ir::interpret::f64_to_f16_bits(f64::from(value)),
                    );
                    if rounded.is_nan() {
                        Val::Nan
                    } else {
                        Val::Float(rounded.to_bits())
                    }
                })
                .collect(),
        ));
        runs.push((
            function,
            vec![
                InterpretValue::int(Ty::U16, i128::from(a)).unwrap(),
                InterpretValue::int(Ty::U16, i128::from(b)).unwrap(),
            ],
        ));
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let reports = differential(
        exe,
        &[Batch {
            label: "binary16 arithmetic".into(),
            module: &module,
            runs,
        }],
    );
    assert_eq!(reports.len(), 4352);
    for (report, expected) in reports.iter().zip(&expected) {
        assert_eq!(&report.rust, expected, "{report:?}");
        assert_eq!(&report.lean, expected, "{report:?}");
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
}

#[test]
fn float_binary16_cast_rounding_agrees() {
    use trust_ir::inst::CastOp;
    let mut mb = ModuleBuilder::new("binary16_casts");
    let sig = mb.add_func_type(vec![Ty::U64, Ty::I64], vec![Ty::F16; 3]);
    let mut fb = mb.function("casts", sig);
    let entry = fb.create_block();
    let raw = fb.add_block_param(entry, Ty::U64);
    let signed = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let wide = fb.cast(CastOp::Bitcast, Ty::U64, Ty::F64, raw);
    let narrowed = fb.cast(CastOp::FPTrunc, Ty::F64, Ty::F16, wide);
    let unsigned = fb.cast(CastOp::UIToFP, Ty::U64, Ty::F16, raw);
    let signed_float = fb.cast(CastOp::SIToFP, Ty::I64, Ty::F16, signed);
    fb.ret(vec![narrowed, unsigned, signed_float]);
    let function = fb.build();
    let module = mb.build().expect("binary16 cast module");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let mut raw = vec![
        0,
        1,
        u64::MAX,
        2049,
        2051,
        65504,
        65519,
        65520,
        i64::MAX as u64,
        i64::MIN as u64,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0x7ff8_0000_0000_0001,
    ];
    for value in [
        0.0f64,
        0.1,
        1.0 + 1.0 / 2048.0,
        1.0 + 3.0 / 2048.0,
        65504.0,
        65520.0,
        2.0f64.powi(-25),
        2.0f64.powi(-24),
        2.0f64.powi(-14),
    ] {
        for signed in [value, -value] {
            for offset in [-1i64, 0, 1] {
                raw.push(signed.to_bits().wrapping_add_signed(offset));
            }
        }
    }
    let mut seed = 0x317f_9155_2ce9_7a10u64;
    for _ in 0..1024 {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        raw.push(seed);
    }
    let mut runs = Vec::new();
    let mut expected = Vec::new();
    for bits in raw {
        let signed = bits as i64;
        let values = [f64::from_bits(bits), bits as f64, signed as f64];
        expected.push(Verdict::Ok(
            values
                .into_iter()
                .map(|value| {
                    let rounded = trust_ir::interpret::f16_bits_to_f64(
                        trust_ir::interpret::f64_to_f16_bits(value),
                    );
                    if rounded.is_nan() {
                        Val::Nan
                    } else {
                        Val::Float(rounded.to_bits())
                    }
                })
                .collect(),
        ));
        runs.push((
            function,
            vec![
                InterpretValue::int(Ty::U64, i128::from(bits)).unwrap(),
                InterpretValue::int(Ty::I64, i128::from(signed)).unwrap(),
            ],
        ));
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let reports = differential(
        exe,
        &[Batch {
            label: "binary16 narrowing and integer casts".into(),
            module: &module,
            runs,
        }],
    );
    assert_eq!(reports.len(), 1091);
    for (report, expected) in reports.iter().zip(&expected) {
        assert_eq!(&report.rust, expected, "{report:?}");
        assert_eq!(&report.lean, expected, "{report:?}");
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
}

/// Table-resolved constants must keep element widths through splats, legacy
/// array spelling, and nested tuple/struct fields. Float leaves deliberately
/// need rounding (or are F64 values not exactly representable at F32).
#[test]
fn typed_array_constants_agree_across_engines() {
    use trust_ir::constant::Constant;
    use trust_ir::ty::{FieldDef, StructDef};
    use trust_ir::value::StructId;

    let mut mb = ModuleBuilder::new("typed_array_constants");
    let mut runs = Vec::new();
    let mut expected = Vec::new();
    for (struct_index, elem_ty) in [Ty::I8, Ty::U16, Ty::F16, Ty::F32, Ty::F64]
        .into_iter()
        .enumerate()
    {
        let elem_id = mb.add_type(elem_ty.clone());
        let array_ty = Ty::Array(elem_id, 3);
        let struct_id = mb.add_struct(StructDef {
            id: StructId::new(struct_index as u32),
            name: format!("Array_{elem_ty}"),
            fields: vec![FieldDef {
                name: "values".into(),
                ty: array_ty.clone(),
                offset: None,
            }],
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        });
        let sig = mb.add_func_type(vec![], vec![elem_ty.clone()]);
        for spelling in ["array", "legacy", "splat"] {
            for wrapper in ["direct", "tuple", "struct"] {
                let scalar = if elem_ty == Ty::I8 {
                    Constant::Int(-7)
                } else if elem_ty == Ty::U16 {
                    Constant::Int(259)
                } else {
                    Constant::Float(1.0006)
                };
                // Nonuniform lists preserve the canonical array spelling rule.
                let zero = if matches!(scalar, Constant::Float(_)) {
                    Constant::Float(0.0)
                } else {
                    Constant::Int(0)
                };
                let constant = match spelling {
                    "splat" => Constant::Splat {
                        elem: Box::new(scalar.clone()),
                        len: 3,
                    },
                    "legacy" => Constant::Aggregate(vec![scalar.clone(), zero, scalar.clone()]),
                    _ => Constant::Array(vec![scalar.clone(), zero, scalar.clone()]),
                };
                let mut fb = mb.function(format!("{elem_ty}_{spelling}_{wrapper}"), sig);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                let array = match wrapper {
                    "tuple" => {
                        let value = fb.const_value(
                            Ty::Tuple(vec![array_ty.clone()]),
                            Constant::Aggregate(vec![constant]),
                        );
                        fb.extract_field(array_ty.clone(), value, 0)
                    }
                    "struct" => {
                        let value = fb.const_value(
                            Ty::Struct(struct_id),
                            Constant::Aggregate(vec![constant]),
                        );
                        fb.extract_field(array_ty.clone(), value, 0)
                    }
                    _ => fb.const_value(array_ty.clone(), constant),
                };
                let index = fb.iconst(Ty::U32, 2);
                let result = fb.extract_element(elem_ty.clone(), array, index);
                fb.ret(vec![result]);
                runs.push((fb.build(), vec![]));
                let value = match elem_ty {
                    Ty::I8 => Val::Int { width: 8, raw: 249 },
                    Ty::U16 => Val::Int {
                        width: 16,
                        raw: 259,
                    },
                    Ty::F16 => Val::Float(
                        trust_ir::interpret::f16_bits_to_f64(trust_ir::interpret::f64_to_f16_bits(
                            1.0006,
                        ))
                        .to_bits(),
                    ),
                    Ty::F32 => Val::Float((1.0006f64 as f32 as f64).to_bits()),
                    Ty::F64 => Val::Float(1.0006f64.to_bits()),
                    _ => unreachable!(),
                };
                expected.push(Verdict::Ok(vec![value]));
            }
        }
    }
    let module = mb.build().expect("typed constant module");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    let Oracle::Ready(exe) = oracle() else { return };
    let reports = differential(
        exe,
        &[Batch {
            label: module.name.clone(),
            module: &module,
            runs,
        }],
    );
    assert_eq!(reports.len(), 45);
    for (report, expected) in reports.iter().zip(&expected) {
        assert_eq!(&report.rust, expected, "{report:?}");
        assert_eq!(&report.lean, expected, "{report:?}");
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
}

/// Invalid array lengths must still refuse after typed constant recursion.
/// These modules intentionally fail validation; compare the two type-error
/// classes directly rather than treating ill-formed programs as valid corpus.
#[test]
fn typed_array_constant_length_refusals_agree() {
    use trust_ir::constant::Constant;
    let mut mb = ModuleBuilder::new("typed_array_constant_length_refusals");
    let elem = mb.add_type(Ty::I8);
    let array_ty = Ty::Array(elem, 3);
    let sig = mb.add_func_type(vec![], vec![]);
    let mut runs = Vec::new();
    for (spelling, constant) in [
        (
            "array",
            Constant::Array(vec![Constant::Int(1), Constant::Int(2)]),
        ),
        (
            "legacy",
            Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]),
        ),
        (
            "splat",
            Constant::Splat {
                elem: Box::new(Constant::Int(1)),
                len: 2,
            },
        ),
    ] {
        for nested in [false, true] {
            let mut fb = mb.function(format!("{spelling}_{nested}"), sig);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            if nested {
                fb.const_value(
                    Ty::Tuple(vec![array_ty.clone()]),
                    Constant::Aggregate(vec![constant.clone()]),
                );
            } else {
                fb.const_value(array_ty.clone(), constant.clone());
            }
            fb.ret(vec![]);
            runs.push((fb.build(), vec![]));
        }
    }
    let module = mb.build().expect("invalid array constant module");
    assert!(!trust_ir_build::validate_module(&module).is_empty());
    let Oracle::Ready(exe) = oracle() else { return };
    let reports = differential(
        exe,
        &[Batch {
            label: module.name.clone(),
            module: &module,
            runs,
        }],
    );
    assert_eq!(reports.len(), 6);
    for report in reports {
        assert!(matches!(report.rust, Verdict::TypeError(_)), "{report:?}");
        assert!(matches!(report.lean, Verdict::TypeError(_)), "{report:?}");
    }
}

#[test]
fn typed_array_splat_reader_refuses_noncanonical_lengths() {
    use trust_ir::constant::Constant;
    let mut modules = Vec::new();
    for len in [0, 1] {
        let mut mb = ModuleBuilder::new(format!("noncanonical_splat_{len}"));
        let elem = mb.add_type(Ty::I8);
        let sig = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("program", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.const_value(
            Ty::Array(elem, len),
            Constant::Splat {
                elem: Box::new(Constant::Int(1)),
                len,
            },
        );
        fb.ret(vec![]);
        let root = fb.build();
        let module = mb.build().expect("noncanonical splat module");
        let bytes = serde_json::to_vec(&module).expect("serialize mutation");
        assert!(serde_json::from_slice::<Module>(&bytes).is_err());
        modules.push((module, root));
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(module, root)| Batch {
            label: module.name.clone(),
            module,
            runs: vec![(*root, vec![])],
        })
        .collect();
    for replies in run_lean(exe, &batches) {
        assert_eq!(replies.len(), 1);
        match &replies[0] {
            Verdict::Error(message) => assert!(
                message.contains("Splat: length must be at least two"),
                "{message}"
            ),
            other => panic!("unexpected noncanonical splat decoder verdict: {other:?}"),
        }
    }
}

/// The register-value twin must also survive the oracle's JSON handoff.
#[test]
fn typed_array_splat_instruction_agrees() {
    let mut mb = ModuleBuilder::new("typed_array_splat_instruction");
    let mut runs = Vec::new();
    for elem_ty in [Ty::I8, Ty::U16, Ty::F16, Ty::F32, Ty::F64] {
        let elem = mb.add_type(elem_ty.clone());
        let array_ty = Ty::Array(elem, 3);
        let sig = mb.add_func_type(vec![], vec![array_ty.clone(), elem_ty.clone()]);
        let mut fb = mb.function(format!("splat_{elem_ty}"), sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let value = match elem_ty {
            Ty::I8 => fb.iconst(Ty::I8, -7),
            Ty::U16 => fb.iconst(Ty::U16, 259),
            _ => fb.fconst(elem_ty.clone(), 1.0006),
        };
        let array = fb.array_splat(array_ty, value);
        let index = fb.iconst(Ty::U32, 2);
        let last = fb.extract_element(elem_ty, array, index);
        fb.ret(vec![array, last]);
        runs.push((fb.build(), vec![]));
    }
    let module = mb.build().expect("register splat module");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    let Oracle::Ready(exe) = oracle() else { return };
    let reports = differential(
        exe,
        &[Batch {
            label: module.name.clone(),
            module: &module,
            runs,
        }],
    );
    assert_eq!(reports.len(), 5);
    for report in reports {
        assert!(matches!(report.rust, Verdict::Graph(_)), "{report:?}");
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
}

/// Table-backed containers retain their element types through nesting and
/// target-width changes, including the validator's two record spellings.
#[test]
fn typed_container_constants_agree_across_engines() {
    use trust_ir::constant::Constant;
    use trust_ir::ty::{FieldDef, RecordDef, SetRepr};
    use trust_ir::value::RecordId;

    fn add_case(mb: &mut ModuleBuilder, name: String, ty: Ty, value: Constant) -> FuncId {
        let callee_sig = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
        let mut callee = mb.function(format!("{name}_identity"), callee_sig);
        let entry = callee.create_block();
        let callee_value = callee.add_block_param(entry, ty.clone());
        callee.switch_to_block(entry);
        callee.ret(vec![callee_value]);
        let callee = callee.build();
        let sig = mb.add_func_type(vec![], vec![ty.clone()]);
        let mut fb = mb.function(name, sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let result = fb.const_value(ty, value);
        let returned = fb.call(callee, vec![result]);
        fb.ret(vec![returned]);
        fb.build()
    }

    let mut modules = Vec::new();
    for bits in [32, 64] {
        let mut mb = ModuleBuilder::new_with_target_info(
            format!("typed_containers_{bits}"),
            semr_target(bits),
        );
        let mut runs = Vec::new();
        let mut expected = Vec::new();
        for (index, ty) in [Ty::I8, Ty::U16, Ty::Usize, Ty::F16, Ty::F32, Ty::F64]
            .into_iter()
            .enumerate()
        {
            let (scalar, value, zero) = match ty {
                Ty::I8 => (
                    Constant::Int(-7),
                    Val::Int { width: 8, raw: 249 },
                    Constant::Int(0),
                ),
                Ty::U16 => (
                    Constant::Int(259),
                    Val::Int {
                        width: 16,
                        raw: 259,
                    },
                    Constant::Int(0),
                ),
                Ty::Usize => (
                    Constant::Int(0x8000_0005),
                    Val::Int {
                        width: bits,
                        raw: 0x8000_0005,
                    },
                    Constant::Int(0),
                ),
                _ => {
                    let rounded = match ty {
                        Ty::F16 => trust_ir::interpret::f16_bits_to_f64(
                            trust_ir::interpret::f64_to_f16_bits(1.0006),
                        ),
                        Ty::F32 => 1.0006f64 as f32 as f64,
                        _ => 1.0006,
                    };
                    (
                        Constant::Float(1.0006),
                        Val::Float(rounded.to_bits()),
                        Constant::Float(0.0),
                    )
                }
            };
            let zero_value = match &value {
                Val::Int { width, .. } => Val::Int {
                    width: *width,
                    raw: 0,
                },
                _ => Val::Float(0.0f64.to_bits()),
            };
            let tid = mb.add_type(ty.clone());
            let seq_ty = Ty::Sequence(tid);
            let set_ty = Ty::Set(tid, SetRepr::Boxed);
            // Sparse nominal ids ensure the reader uses declaration identity.
            let rid = mb.add_record(RecordDef {
                id: RecordId::new(10 + index as u32 * 10),
                name: format!("Scalar_{ty}"),
                fields: vec![
                    FieldDef {
                        name: "a".into(),
                        ty: ty.clone(),
                        offset: None,
                    },
                    FieldDef {
                        name: "z".into(),
                        ty: Ty::Bool,
                        offset: None,
                    },
                ],
            });
            let outer = mb.add_record(RecordDef {
                id: RecordId::new(11 + index as u32 * 10),
                name: format!("Nested_{ty}"),
                fields: vec![
                    FieldDef {
                        name: "a".into(),
                        ty: seq_ty.clone(),
                        offset: None,
                    },
                    FieldDef {
                        name: "z".into(),
                        ty: set_ty.clone(),
                        offset: None,
                    },
                ],
            });
            let record_ty = Ty::Record(rid);
            let record_tid = mb.add_type(record_ty.clone());
            let seq_tid = mb.add_type(seq_ty.clone());
            let lanes = vec![scalar.clone(), zero];
            let values = vec![value.clone(), zero_value];
            let named = Constant::Record(vec![
                ("a".into(), scalar.clone()),
                ("z".into(), Constant::Bool(true)),
            ]);
            let record_value =
                Val::Record(vec![("a".into(), value), ("z".into(), Val::Bool(true))]);
            let cases = vec![
                (
                    "sequence",
                    seq_ty.clone(),
                    Constant::Sequence(lanes.clone()),
                    Val::Sequence(values.clone()),
                ),
                (
                    "set_boxed",
                    set_ty.clone(),
                    Constant::Set(lanes.clone()),
                    Val::Set(values.clone()),
                ),
                (
                    "set_bitset",
                    Ty::Set(tid, SetRepr::Bitset),
                    Constant::Set(lanes.clone()),
                    Val::Set(values.clone()),
                ),
                (
                    "record_named",
                    record_ty.clone(),
                    named.clone(),
                    record_value.clone(),
                ),
                (
                    "record_legacy",
                    record_ty,
                    Constant::Aggregate(vec![scalar, Constant::Bool(true)]),
                    record_value.clone(),
                ),
                (
                    "nested_record",
                    Ty::Record(outer),
                    Constant::Record(vec![
                        ("a".into(), Constant::Sequence(lanes.clone())),
                        ("z".into(), Constant::Set(lanes)),
                    ]),
                    Val::Record(vec![
                        ("a".into(), Val::Sequence(values.clone())),
                        ("z".into(), Val::Set(values)),
                    ]),
                ),
                (
                    "sequence_record",
                    Ty::Sequence(record_tid),
                    Constant::Sequence(vec![named]),
                    Val::Sequence(vec![record_value]),
                ),
                (
                    "set_sequence",
                    Ty::Set(seq_tid, SetRepr::Boxed),
                    Constant::Set(vec![Constant::Sequence(vec![])]),
                    Val::Set(vec![Val::Sequence(vec![])]),
                ),
                (
                    "empty_sequence",
                    seq_ty,
                    Constant::Sequence(vec![]),
                    Val::Sequence(vec![]),
                ),
                ("empty_set", set_ty, Constant::Set(vec![]), Val::Set(vec![])),
            ];
            for (name, ty, constant, expected_value) in cases {
                runs.push((
                    add_case(&mut mb, format!("{name}_{index}"), ty, constant),
                    vec![],
                ));
                expected.push(Verdict::Ok(vec![expected_value]));
            }
        }
        let empty = mb.add_record(RecordDef {
            id: RecordId::new(1000),
            name: "Empty".into(),
            fields: vec![],
        });
        runs.push((
            add_case(
                &mut mb,
                "empty_record".into(),
                Ty::Record(empty),
                Constant::Record(vec![]),
            ),
            vec![],
        ));
        expected.push(Verdict::Ok(vec![Val::Record(vec![])]));
        let module = mb.build().expect("typed container module");
        let errors = trust_ir_build::validate_module(&module);
        assert!(errors.is_empty(), "{bits}: {errors:?}");
        modules.push((module, runs, expected));
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(module, runs, _)| Batch {
            label: module.name.clone(),
            module,
            runs: runs.clone(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 122);
    for (report, expected) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, expected)| expected))
    {
        assert_eq!(&report.rust, expected, "{report:?}");
        assert_eq!(&report.lean, expected, "{report:?}");
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
}

#[test]
fn typed_container_constant_refusals_agree() {
    use trust_ir::constant::Constant;
    use trust_ir::ty::{FieldDef, RecordDef, SetRepr};
    use trust_ir::value::RecordId;
    let mut mb = ModuleBuilder::new("container_constant_refusals");
    let elem = mb.add_type(Ty::I8);
    let rid = mb.add_record(RecordDef {
        id: RecordId::new(7),
        name: "Pair".into(),
        fields: vec![
            FieldDef {
                name: "a".into(),
                ty: Ty::I8,
                offset: None,
            },
            FieldDef {
                name: "z".into(),
                ty: Ty::Bool,
                offset: None,
            },
        ],
    });
    let record_tid = mb.add_type(Ty::Record(rid));
    let unknown = Constant::Record(vec![
        ("a".into(), Constant::Int(1)),
        ("unknown".into(), Constant::Bool(true)),
    ]);
    let cases = vec![
        (
            Ty::Record(rid),
            Constant::Record(vec![("a".into(), Constant::Int(1))]),
        ),
        (Ty::Record(rid), unknown.clone()),
        (Ty::Record(rid), Constant::Aggregate(vec![Constant::Int(1)])),
        (Ty::Sequence(record_tid), Constant::Sequence(vec![unknown])),
        (Ty::Sequence(elem), Constant::Set(vec![])),
        (Ty::Set(elem, SetRepr::Boxed), Constant::Sequence(vec![])),
        (Ty::Tuple(vec![]), Constant::Record(vec![])),
    ];
    let sig = mb.add_func_type(vec![], vec![]);
    let mut runs = Vec::new();
    for (index, (ty, constant)) in cases.into_iter().enumerate() {
        let mut fb = mb.function(format!("bad_{index}"), sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.const_value(ty, constant);
        fb.ret(vec![]);
        runs.push((fb.build(), vec![]));
    }
    let module = mb.build().expect("invalid container constants");
    assert!(!trust_ir_build::validate_module(&module).is_empty());
    let Oracle::Ready(exe) = oracle() else { return };
    let reports = differential(
        exe,
        &[Batch {
            label: module.name.clone(),
            module: &module,
            runs,
        }],
    );
    assert_eq!(reports.len(), 7);
    for report in reports {
        assert!(matches!(report.rust, Verdict::TypeError(_)), "{report:?}");
        assert!(matches!(report.lean, Verdict::TypeError(_)), "{report:?}");
    }
}

/// An unsupported record field type is local to users of its declaration;
/// malformed record data still refuses instead of becoming an empty table.
#[test]
fn typed_container_record_reader_preserves_definition_refusals() {
    use trust_ir::constant::Constant;
    use trust_ir::ty::{FieldDef, RecordDef};
    use trust_ir::value::RecordId;
    let mut mb = ModuleBuilder::new("record_reader_refusals");
    let rid = mb.add_record(RecordDef {
        id: RecordId::new(17),
        name: "Record".into(),
        fields: vec![FieldDef {
            name: "a".into(),
            ty: Ty::I8,
            offset: None,
        }],
    });
    let sig = mb.add_func_type(vec![], vec![Ty::I32]);
    let unused = {
        let mut fb = mb.function("unused", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let answer = fb.iconst(Ty::I32, 42);
        fb.ret(vec![answer]);
        fb.build()
    };
    let used = {
        let mut fb = mb.function("used", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.const_value(
            Ty::Record(rid),
            Constant::Record(vec![("a".into(), Constant::Int(1))]),
        );
        let answer = fb.iconst(Ty::I32, 42);
        fb.ret(vec![answer]);
        fb.build()
    };
    let module = mb.build().expect("record reader module");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let Oracle::Ready(exe) = oracle() else { return };
    let original = serde_json::to_value(&module).expect("reader module JSON");
    let mut replies = Vec::new();
    for field_ty in [json!("FutureContainerLane"), json!({"Tuple": null})] {
        let mut mutated = original.clone();
        mutated["records"][0]["fields"][0]["ty"] = field_ty;
        let request = json!({"fuel": FUEL, "call_depth": CALL_DEPTH, "batches": [{
            "module": mutated,
            "runs": [{"function": unused.0, "args": []}, {"function": used.0, "args": []}],
        }]});
        let path =
            std::env::temp_dir().join(format!("trustir-record-reader-{}.json", std::process::id()));
        fs::write(&path, serde_json::to_vec(&request).unwrap())
            .expect("write record-reader mutation");
        let output = Command::new(exe)
            .arg(&path)
            .output()
            .expect("run record-reader mutation");
        fs::remove_file(path).expect("remove record-reader mutation");
        assert!(output.status.success(), "{output:?}");
        replies.push(serde_json::from_slice::<Json>(&output.stdout).expect("mutation reply JSON"));
    }
    let values = replies[0][0].as_array().expect("one batch of two verdicts");
    assert_eq!(values.len(), 2);
    assert_eq!(
        lean_verdict(&values[0]),
        Verdict::Ok(vec![Val::Int { width: 32, raw: 42 }])
    );
    assert_eq!(
        lean_verdict(&values[1]),
        Verdict::Unsupported("enum_def_table".into())
    );
    assert!(
        replies[1]["error"].as_str().is_some(),
        "malformed record was hidden: {}",
        replies[1]
    );
}

/// Actual closure construction, capture projection/update and application must
/// retain every supported value shape through cold module codecs and calls.
#[test]
fn closure_capture_shapes_agree_across_engines_and_codecs() {
    use trust_ir::constant::Constant as C;
    use trust_ir::ty::{
        ClosureTy, EnumDef, EnumTagRepr, EnumVariant, FieldDef, RecordDef, SetRepr,
    };
    use trust_ir::value::{EnumId, RecordId};

    fn add_case(mb: &mut ModuleBuilder, name: &str, ty: Ty, first: C, second: C) -> FuncId {
        let apparent = mb.add_func_type(vec![Ty::Bool], vec![ty.clone()]);
        let physical = mb.add_func_type(vec![ty.clone(), Ty::Bool], vec![ty.clone()]);
        let cid = mb.add_closure_type(ClosureTy {
            func: apparent,
            captures: vec![ty.clone()],
        });
        let target = {
            let mut fb = mb.function(format!("{name}_target"), physical);
            let entry = fb.create_block();
            let capture = fb.add_block_param(entry, ty.clone());
            fb.add_block_param(entry, Ty::Bool);
            fb.switch_to_block(entry);
            fb.ret(vec![capture]);
            fb.build()
        };
        let main_sig = mb.add_func_type(vec![], vec![ty.clone(); 4]);
        let mut fb = mb.function(name, main_sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let first = fb.const_value(ty.clone(), first);
        let closure = fb.make_closure(cid, target, vec![first]);
        let first_read = fb.extract_field(ty.clone(), closure, 0);
        let yes = fb.bool_const(true);
        let first_call = fb.call_indirect(closure, apparent, vec![yes]);
        let second = fb.const_value(ty.clone(), second);
        let updated = fb.insert_field(Ty::Closure(cid), closure, 0, second);
        let second_read = fb.extract_field(ty, updated, 0);
        let no = fb.bool_const(false);
        let second_call = fb.call_indirect(updated, apparent, vec![no]);
        fb.ret(vec![first_read, first_call, second_read, second_call]);
        fb.build()
    }
    let f16 = |value| {
        Val::Float(
            trust_ir::interpret::f16_bits_to_f64(trust_ir::interpret::f64_to_f16_bits(value))
                .to_bits(),
        )
    };
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let mut mb = ModuleBuilder::new_with_target_info(
            format!("closure_shapes_{bits}"),
            semr_target(bits),
        );
        let half = mb.add_type(Ty::F16);
        let word = mb.add_type(Ty::Usize);
        let seq_ty = Ty::Sequence(word);
        let seq_a = C::Sequence(vec![C::Int(0x8000_0005), C::Int(1)]);
        let seq_b = C::Sequence(vec![C::Int(7)]);
        let seq_va = Val::Sequence(vec![
            Val::Int {
                width: bits,
                raw: 0x8000_0005,
            },
            Val::Int {
                width: bits,
                raw: 1,
            },
        ]);
        let seq_vb = Val::Sequence(vec![Val::Int {
            width: bits,
            raw: 7,
        }]);
        let rid = mb.add_record(RecordDef {
            id: RecordId::new(21),
            name: "Environment".into(),
            fields: vec![
                FieldDef {
                    name: "a".into(),
                    ty: Ty::F16,
                    offset: None,
                },
                FieldDef {
                    name: "z".into(),
                    ty: seq_ty.clone(),
                    offset: None,
                },
            ],
        });
        let record_a = C::Record(vec![
            ("a".into(), C::Float(1.0006)),
            ("z".into(), seq_a.clone()),
        ]);
        let record_b = C::Record(vec![
            ("a".into(), C::Float(-0.0)),
            ("z".into(), seq_b.clone()),
        ]);
        let record_va = Val::Record(vec![
            ("a".into(), f16(1.0006)),
            ("z".into(), seq_va.clone()),
        ]);
        let record_vb = Val::Record(vec![("a".into(), f16(-0.0)), ("z".into(), seq_vb.clone())]);
        let eid = mb.add_enum(
            EnumDef::new(
                EnumId::new(13),
                "Choice",
                vec![
                    EnumVariant {
                        name: "Half".into(),
                        fields: vec![Ty::F16],
                        field_names: vec![],
                    },
                    EnumVariant {
                        name: "Words".into(),
                        fields: vec![seq_ty.clone()],
                        field_names: vec![],
                    },
                    EnumVariant {
                        name: "Empty".into(),
                        fields: vec![],
                        field_names: vec![],
                    },
                ],
            )
            .with_discriminants(vec![Some(-1), Some(3), Some(42)])
            .with_repr(EnumTagRepr::I8),
        );
        let mut cases = vec![
            (
                "half",
                Ty::F16,
                C::Float(1.0006),
                C::Float(-0.0),
                f16(1.0006),
                f16(-0.0),
            ),
            (
                "half_nan",
                Ty::F16,
                C::Float(f64::NAN),
                C::Float(2.0),
                Val::Nan,
                f16(2.0),
            ),
            (
                "single",
                Ty::F32,
                C::Float(1.0006),
                C::Float(-0.0),
                Val::Float((1.0006f64 as f32 as f64).to_bits()),
                Val::Float((-0.0f64).to_bits()),
            ),
            (
                "double",
                Ty::F64,
                C::Float(1.0006),
                C::Float(-0.0),
                Val::Float(1.0006f64.to_bits()),
                Val::Float((-0.0f64).to_bits()),
            ),
            (
                "vector",
                Ty::Vector(Box::new(Ty::F16), 2),
                C::Vector(vec![C::Float(1.0006), C::Float(-0.0)]),
                C::Vector(vec![C::Float(2.0), C::Float(0.0)]),
                Val::Vector(vec![f16(1.0006), f16(-0.0)]),
                Val::Vector(vec![f16(2.0), f16(0.0)]),
            ),
            (
                "sequence",
                seq_ty.clone(),
                seq_a.clone(),
                seq_b.clone(),
                seq_va.clone(),
                seq_vb.clone(),
            ),
            (
                "set",
                Ty::Set(word, SetRepr::Boxed),
                C::Set(vec![C::Int(1), C::Int(0x8000_0005)]),
                C::Set(vec![C::Int(7)]),
                Val::Set(vec![
                    Val::Int {
                        width: bits,
                        raw: 1,
                    },
                    Val::Int {
                        width: bits,
                        raw: 0x8000_0005,
                    },
                ]),
                Val::Set(vec![Val::Int {
                    width: bits,
                    raw: 7,
                }]),
            ),
            (
                "record",
                Ty::Record(rid),
                record_a.clone(),
                record_b.clone(),
                record_va.clone(),
                record_vb.clone(),
            ),
            (
                "array",
                Ty::Array(half, 3),
                C::Splat {
                    elem: Box::new(C::Float(1.0006)),
                    len: 3,
                },
                C::Splat {
                    elem: Box::new(C::Float(-0.0)),
                    len: 3,
                },
                Val::Array(vec![f16(1.0006); 3]),
                Val::Array(vec![f16(-0.0); 3]),
            ),
            (
                "enum",
                Ty::Enum(eid),
                C::Aggregate(vec![C::Int(-1), C::Float(1.0006)]),
                C::Aggregate(vec![C::Int(3), seq_a]),
                Val::Aggregate(vec![Val::Int { width: 8, raw: 255 }, f16(1.0006)]),
                Val::Aggregate(vec![Val::Int { width: 8, raw: 3 }, seq_va]),
            ),
            (
                "enum_empty",
                Ty::Enum(eid),
                C::Aggregate(vec![C::Int(42)]),
                C::Aggregate(vec![C::Int(3), seq_b]),
                Val::Aggregate(vec![Val::Int { width: 8, raw: 42 }]),
                Val::Aggregate(vec![Val::Int { width: 8, raw: 3 }, seq_vb]),
            ),
        ];
        cases.push((
            "nested",
            Ty::Tuple(vec![Ty::Record(rid), Ty::Vector(Box::new(Ty::F16), 2)]),
            C::Aggregate(vec![
                record_a,
                C::Vector(vec![C::Float(1.0006), C::Float(-0.0)]),
            ]),
            C::Aggregate(vec![
                record_b,
                C::Vector(vec![C::Float(2.0), C::Float(0.0)]),
            ]),
            Val::Aggregate(vec![record_va, Val::Vector(vec![f16(1.0006), f16(-0.0)])]),
            Val::Aggregate(vec![record_vb, Val::Vector(vec![f16(2.0), f16(0.0)])]),
        ));
        let mut runs = Vec::new();
        let mut expected = Vec::new();
        for (name, ty, first, second, va, vb) in cases {
            let id = add_case(&mut mb, name, ty, first, second);
            runs.push((id, vec![]));
            expected.push(Verdict::Ok(vec![va.clone(), va, vb.clone(), vb]));
        }
        let module = mb.build().expect("closure capture module");
        let errors = trust_ir_build::validate_module(&module);
        assert!(errors.is_empty(), "{bits}: {errors:?}");
        let binary = trust_ir::binary::serialize_module(&module).expect("closure binary");
        let text = trust_ir::format::text_checked(&module).expect("closure text");
        let json = serde_json::to_vec(&module).expect("closure JSON");
        let msgpack = rmp_serde::to_vec(&module).expect("closure MessagePack");
        for (format, decoded) in [
            ("original", module),
            (
                "binary",
                trust_ir::binary::deserialize_module(&binary).expect("binary decode"),
            ),
            (
                "text",
                trust_ir::parser::parse_module(&text).expect("text decode"),
            ),
            ("JSON", serde_json::from_slice(&json).expect("JSON decode")),
            (
                "MessagePack",
                rmp_serde::from_slice(&msgpack).expect("MessagePack decode"),
            ),
        ] {
            assert!(
                trust_ir_build::validate_module(&decoded).is_empty(),
                "{format}"
            );
            modules.push((format, decoded, runs.clone(), expected.clone()));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(format, module, runs, _)| Batch {
            label: format!("{}-{format}", module.name),
            module,
            runs: runs.clone(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 120);
    for (report, expected) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, _, expected)| expected))
    {
        assert_eq!(&report.rust, expected, "{report:?}");
        assert_eq!(&report.lean, expected, "{report:?}");
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
}

#[test]
fn closure_capture_shape_and_call_refusals_agree() {
    use trust_ir::ty::ClosureTy;
    let mut mb = ModuleBuilder::new("closure_capture_refusals");
    let elem = mb.add_type(Ty::Usize);
    let mut runs = Vec::new();
    for case in 0..9 {
        let capture_ty = match case {
            1 => Ty::Vector(Box::new(Ty::F16), 2),
            2 => Ty::Sequence(elem),
            _ => Ty::F16,
        };
        let apparent = mb.add_func_type(vec![], vec![capture_ty.clone()]);
        let physical = mb.add_func_type(vec![capture_ty.clone()], vec![capture_ty.clone()]);
        let wrong_sig = mb.add_func_type(vec![], vec![Ty::I16]);
        let cid = mb.add_closure_type(ClosureTy {
            func: apparent,
            captures: vec![capture_ty.clone()],
        });
        let target = {
            let mut fb = mb.function(format!("target_{case}"), physical);
            let entry = fb.create_block();
            let capture = fb.add_block_param(entry, capture_ty);
            fb.switch_to_block(entry);
            fb.ret(vec![capture]);
            fb.build()
        };
        let sig = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function(format!("bad_{case}"), sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let capture = match case {
            0..=2 => fb.iconst(Ty::I16, 7),
            3 => fb.fconst(Ty::F32, 1.0006),
            5 => fb.undef(Ty::F16),
            _ => fb.fconst(Ty::F16, 1.5),
        };
        let fn_id = if case == 6 {
            FuncId::new(1_000_000)
        } else {
            target
        };
        let captures = if case == 7 { vec![] } else { vec![capture] };
        let closure = fb.make_closure(cid, fn_id, captures);
        if case == 4 {
            let wrong = fb.iconst(Ty::I16, 7);
            fb.insert_field(Ty::Closure(cid), closure, 0, wrong);
        }
        if case == 8 {
            fb.call_indirect(closure, wrong_sig, vec![]);
        }
        fb.ret(vec![]);
        runs.push((fb.build(), vec![]));
    }
    let module = mb.build().expect("closure refusal module");
    assert!(!trust_ir_build::validate_module(&module).is_empty());
    let Oracle::Ready(exe) = oracle() else { return };
    let reports = differential(
        exe,
        &[Batch {
            label: module.name.clone(),
            module: &module,
            runs,
        }],
    );
    assert_eq!(reports.len(), 9);
    for (case, report) in reports.iter().enumerate() {
        if case == 5 {
            assert!(matches!(report.rust, Verdict::Ub(_)), "{report:?}");
            assert!(matches!(report.lean, Verdict::Ub(_)), "{report:?}");
        } else {
            assert!(
                matches!(report.rust, Verdict::TypeError(_)),
                "case {case}: {report:?}"
            );
            assert!(
                matches!(report.lean, Verdict::TypeError(_)),
                "case {case}: {report:?}"
            );
        }
    }
}

/// Register construction and field access need declarations, not byte layouts.
/// The sequence inside the record has no byte image in either model.
#[test]
fn closure_capture_register_aggregates_agree() {
    use trust_ir::constant::Constant as C;
    use trust_ir::ty::{EnumDef, EnumTagRepr, EnumVariant, FieldDef, RecordDef};
    use trust_ir::value::{EnumId, RecordId};
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let mut mb = ModuleBuilder::new_with_target_info(
            format!("register_aggregates_{bits}"),
            semr_target(bits),
        );
        let word = mb.add_type(Ty::Usize);
        let sequence_ty = Ty::Sequence(word);
        let record_ty = Ty::Record(mb.add_record(RecordDef {
            id: RecordId::new(8),
            name: "R".into(),
            fields: vec![
                FieldDef {
                    name: "a".into(),
                    ty: Ty::F16,
                    offset: None,
                },
                FieldDef {
                    name: "z".into(),
                    ty: sequence_ty.clone(),
                    offset: None,
                },
            ],
        }));
        let enum_ty = Ty::Enum(
            mb.add_enum(
                EnumDef::new(
                    EnumId::new(9),
                    "E",
                    vec![
                        EnumVariant {
                            name: "Half".into(),
                            fields: vec![Ty::F16],
                            field_names: vec![],
                        },
                        EnumVariant {
                            name: "Record".into(),
                            fields: vec![record_ty.clone()],
                            field_names: vec![],
                        },
                    ],
                )
                .with_discriminants(vec![Some(-1), Some(3)])
                .with_repr(EnumTagRepr::I8),
            ),
        );
        let sig = mb.add_func_type(
            vec![],
            vec![
                record_ty.clone(),
                enum_ty.clone(),
                record_ty.clone(),
                sequence_ty.clone(),
                record_ty.clone(),
                Ty::F16,
            ],
        );
        let mut fb = mb.function("construct_and_access", sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let half = fb.fconst(Ty::F16, 1.0006);
        let words = fb.const_value(
            sequence_ty.clone(),
            C::Sequence(vec![C::Int(0x8000_0005), C::Int(1)]),
        );
        let record = fb.make_aggregate(record_ty.clone(), vec![half, words]);
        let enumeration = fb.make_enum_variant(enum_ty, 1, vec![record]);
        let extracted = fb.extract_field(record_ty.clone(), enumeration, 1);
        let sequence = fb.extract_field(sequence_ty, extracted, 1);
        let minus_zero = fb.fconst(Ty::F16, -0.0);
        let updated = fb.insert_field(record_ty, extracted, 0, minus_zero);
        let field = fb.extract_field(Ty::F16, updated, 0);
        fb.ret(vec![
            record,
            enumeration,
            extracted,
            sequence,
            updated,
            field,
        ]);
        let root = fb.build();
        let module = mb.build().expect("register aggregate module");
        let errors = trust_ir_build::validate_module(&module);
        assert!(errors.is_empty(), "{errors:?}");
        let sequence_value = Val::Sequence(vec![
            Val::Int {
                width: bits,
                raw: 0x8000_0005,
            },
            Val::Int {
                width: bits,
                raw: 1,
            },
        ]);
        let half_value = Val::Float(
            trust_ir::interpret::f16_bits_to_f64(trust_ir::interpret::f64_to_f16_bits(1.0006))
                .to_bits(),
        );
        let record_value = Val::Record(vec![
            ("a".into(), half_value),
            ("z".into(), sequence_value.clone()),
        ]);
        let minus_zero_value = Val::Float((-0.0f64).to_bits());
        let updated_value = Val::Record(vec![
            ("a".into(), minus_zero_value.clone()),
            ("z".into(), sequence_value.clone()),
        ]);
        let expected = Verdict::Ok(vec![
            record_value.clone(),
            Val::Aggregate(vec![Val::Int { width: 8, raw: 3 }, record_value.clone()]),
            record_value,
            sequence_value,
            updated_value,
            minus_zero_value,
        ]);
        let binary = trust_ir::binary::serialize_module(&module).expect("aggregate binary");
        let text = trust_ir::format::text_checked(&module).expect("aggregate text");
        let json = serde_json::to_vec(&module).expect("aggregate JSON");
        let msgpack = rmp_serde::to_vec(&module).expect("aggregate MessagePack");
        for (format, decoded) in [
            ("original", module),
            (
                "binary",
                trust_ir::binary::deserialize_module(&binary).expect("binary decode"),
            ),
            (
                "text",
                trust_ir::parser::parse_module(&text).expect("text decode"),
            ),
            ("JSON", serde_json::from_slice(&json).expect("JSON decode")),
            (
                "MessagePack",
                rmp_serde::from_slice(&msgpack).expect("MessagePack decode"),
            ),
        ] {
            assert!(trust_ir_build::validate_module(&decoded).is_empty());
            modules.push((format, decoded, root, expected.clone()));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(format, module, root, _)| Batch {
            label: format!("{}-{format}", module.name),
            module,
            runs: vec![(*root, vec![])],
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 10);
    for (report, (_, _, _, expected)) in reports.iter().zip(&modules) {
        assert_eq!(&report.rust, expected, "{report:?}");
        assert_eq!(&report.lean, expected, "{report:?}");
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
}

#[test]
fn closure_capture_register_aggregate_refusals_agree() {
    use trust_ir::ty::{EnumDef, EnumVariant, FieldDef, RecordDef};
    use trust_ir::value::{EnumId, RecordId};
    let mut mb = ModuleBuilder::new("register_aggregate_refusals");
    let record = Ty::Record(mb.add_record(RecordDef {
        id: RecordId::new(0),
        name: "R".into(),
        fields: vec![FieldDef {
            name: "a".into(),
            ty: Ty::F16,
            offset: None,
        }],
    }));
    let enumeration = Ty::Enum(mb.add_enum(EnumDef::new(
        EnumId::new(0),
        "E",
        vec![EnumVariant {
            name: "A".into(),
            fields: vec![Ty::F16],
            field_names: vec![],
        }],
    )));
    let sig = mb.add_func_type(vec![], vec![]);
    let mut runs = Vec::new();
    for case in 0..6 {
        let mut fb = mb.function(format!("refuse_{case}"), sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        match case {
            0 => {
                fb.make_aggregate(record.clone(), vec![]);
            }
            1 => {
                let v = fb.fconst(Ty::F16, 1.5);
                fb.make_enum_variant(record.clone(), 0, vec![v]);
            }
            2 => {
                let v = fb.fconst(Ty::F16, 1.5);
                fb.make_aggregate(enumeration.clone(), vec![v]);
            }
            3 => {
                let v = fb.fconst(Ty::F16, 1.5);
                fb.make_enum_variant(enumeration.clone(), 99, vec![v]);
            }
            4 => {
                let v = fb.iconst(Ty::I16, 7);
                fb.make_enum_variant(enumeration.clone(), 0, vec![v]);
            }
            _ => {
                let v = fb.undef(Ty::F16);
                fb.make_enum_variant(enumeration.clone(), 99, vec![v]);
            }
        }
        fb.ret(vec![]);
        runs.push((fb.build(), vec![]));
    }
    let module = mb.build().expect("aggregate refusal module");
    assert!(!trust_ir_build::validate_module(&module).is_empty());
    let Oracle::Ready(exe) = oracle() else { return };
    let reports = differential(
        exe,
        &[Batch {
            label: module.name.clone(),
            module: &module,
            runs,
        }],
    );
    assert_eq!(reports.len(), 6);
    for (case, report) in reports.iter().enumerate() {
        if case == 5 {
            assert!(matches!(report.rust, Verdict::Ub(_)), "{report:?}");
            assert!(matches!(report.lean, Verdict::Ub(_)), "{report:?}");
        } else {
            assert!(matches!(report.rust, Verdict::TypeError(_)), "{report:?}");
            assert!(matches!(report.lean, Verdict::TypeError(_)), "{report:?}");
        }
    }
}

fn float_unary_cases(ops: &[trust_ir::UnOp]) {
    let mut bits = vec![
        0x7c00,
        0xfc00,
        0x7e01,
        0xfe01,
        0x7bff,
        0xfbff,
        0x0400,
        0x03ff,
        0x8001,
        0xbc00,
        0x3c00,
        0x8000,
        0,
        1,
        u64::MAX,
        0x8000_0000_0000_0000,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0x7ff8_0000_0000_0001,
        0xfff8_0000_0000_0001,
        0x0010_0000_0000_0000,
        0x8010_0000_0000_0000,
        0x000f_ffff_ffff_ffff,
        0x7f80_0000,
        0xff80_0000,
        0x7fc0_0001,
        0xffc0_0001,
        0x8000_0000,
        0x0080_0000,
        0x8080_0000,
        0x007f_ffff,
        0x8000_0001,
        0x8000_0000_0000_0001,
        0x7f7f_ffff,
        0xff7f_ffff,
        0x7fef_ffff_ffff_ffff,
        0xffef_ffff_ffff_ffff,
        0x3fc0_0000,
        0xbfc0_0000,
        0x3ff8_0000_0000_0000,
        0xbff8_0000_0000_0000,
    ];
    let mut seed = 0x73b9_5ec4_d01a_826fu64;
    for _ in 0..512 {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        bits.push(seed);
    }
    // Neighbors of integral and half-integral boundaries, including both signs.
    for value in [0.5f64, 1.0, 1.5, 2.0, 8_388_608.0, 4_503_599_627_370_496.0] {
        for signed in [value, -value] {
            for offset in [-1i64, 0, 1] {
                bits.push(signed.to_bits().wrapping_add_signed(offset));
                bits.push(u64::from(
                    (signed as f32).to_bits().wrapping_add_signed(offset as i32),
                ));
            }
        }
    }
    if ops.contains(&trust_ir::UnOp::FSqrt) {
        // Squared F32 midpoints are exactly representable in F64. Probe their
        // neighbors at each input width as well as ordinary perfect squares.
        for root in [0.5f64, 1.0, 1.5, 2.0, 3.0, 127.0, 4096.0, 8_388_608.0] {
            let midpoint = root + f64::from(f32::from_bits((root as f32).to_bits() + 1));
            for square in [root * root, (midpoint * 0.5).powi(2)] {
                for offset in [-1i64, 0, 1] {
                    bits.push(square.to_bits().wrapping_add_signed(offset));
                    bits.push(u64::from(
                        (square as f32).to_bits().wrapping_add_signed(offset as i32),
                    ));
                }
            }
        }
    }
    let mut mb = ModuleBuilder::new("float_unary");
    let mut runs = Vec::new();
    let mut expected = Vec::new();
    for ty in [Ty::F16, Ty::F32, Ty::F64] {
        let signature = mb.add_func_type(vec![], vec![ty.clone()]);
        for &op in ops {
            for (i, &raw) in bits.iter().enumerate() {
                let (input, magnitude) = if ty == Ty::F16 {
                    (
                        trust_ir::interpret::f16_bits_to_f64(raw as u16),
                        trust_ir::interpret::f16_bits_to_f64((raw as u16) & 0x7fff),
                    )
                } else if ty == Ty::F32 {
                    (
                        f64::from(f32::from_bits(raw as u32)),
                        f64::from(f32::from_bits((raw as u32) & 0x7fff_ffff)),
                    )
                } else {
                    (
                        f64::from_bits(raw),
                        f64::from_bits(raw & 0x7fff_ffff_ffff_ffff),
                    )
                };
                let rounded = match op {
                    trust_ir::UnOp::FAbs => magnitude,
                    trust_ir::UnOp::FSqrt if ty == Ty::F16 || ty == Ty::F32 => {
                        f64::from((input as f32).sqrt())
                    }
                    trust_ir::UnOp::FSqrt => input.sqrt(),
                    trust_ir::UnOp::FFloor => input.floor(),
                    trust_ir::UnOp::FCeil => input.ceil(),
                    trust_ir::UnOp::FTrunc => input.trunc(),
                    _ => unreachable!("test operator"),
                };
                let rounded = if ty == Ty::F16 {
                    trust_ir::interpret::f16_bits_to_f64(trust_ir::interpret::f64_to_f16_bits(
                        rounded,
                    ))
                } else {
                    rounded
                };
                let mut fb = mb.function(format!("{op:?}_{ty:?}_{i}"), signature);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                let value = fb.fconst(ty.clone(), input);
                let result = fb.unop(op, ty.clone(), value);
                fb.ret(vec![result]);
                runs.push((fb.build(), vec![]));
                expected.push(Verdict::Ok(vec![if rounded.is_nan() {
                    Val::Nan
                } else {
                    Val::Float(rounded.to_bits())
                }]));
            }
        }
    }
    let module = mb.build().expect("floating unary module");
    eprintln!("{ops:?}: {} paired cases", runs.len());
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:#?}");
    for ((function, args), expected) in runs.iter().zip(&expected) {
        assert_eq!(&run_rust(&module, *function, args), expected);
    }
    let Oracle::Ready(exe) = oracle() else {
        return;
    };
    let reports = differential(
        exe,
        &[Batch {
            label: format!("{ops:?} at F16/F32/F64"),
            module: &module,
            runs,
        }],
    );
    assert_eq!(reports.len(), expected.len());
    for (report, expected) in reports.iter().zip(&expected) {
        assert_eq!(&report.lean, expected, "{report:?}");
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
}

/// Tally: mismatches (fatal), unsupported by (side, feature), agreements by
/// verdict class. Prints the coverage table.
struct Tally {
    mismatches: Vec<String>,
    unsupported: BTreeMap<String, usize>,
    agreed: BTreeMap<&'static str, usize>,
    /// Runs the interpreter filtered out as outside the assumed domain.
    vacuous: usize,
}

fn tally(reports: &[RunReport]) -> Tally {
    let mut t = Tally {
        mismatches: Vec::new(),
        unsupported: BTreeMap::new(),
        agreed: BTreeMap::new(),
        vacuous: 0,
    };
    for r in reports {
        match &r.comparison {
            Comparison::Agree => *t.agreed.entry(r.rust.class()).or_default() += 1,
            Comparison::Unsupported(side, feature) => {
                eprintln!(
                    "  refused {side}:{feature}: {} fn {:?} (rust {:?}; lean {:?})",
                    r.label, r.func, r.rust, r.lean
                );
                *t.unsupported
                    .entry(format!("{side}:{feature}"))
                    .or_default() += 1;
            }
            Comparison::Vacuous => t.vacuous += 1,
            Comparison::Mismatch(why) => t.mismatches.push(format!(
                "{} fn {:?} args {:?}: {why}\n    rust: {:?}\n    lean: {:?}",
                r.label, r.func, r.args, r.rust, r.lean
            )),
        }
    }
    eprintln!("W5b runs: {}", reports.len());
    eprintln!("  agreed by class: {:?}", t.agreed);
    eprintln!("  unsupported by side:feature: {:?}", t.unsupported);
    eprintln!("  vacuous (interpreter AssumeViolated): {}", t.vacuous);
    eprintln!("  mismatches: {}", t.mismatches.len());
    t
}

fn assert_no_mismatch(t: &Tally, what: &str) {
    assert!(
        t.mismatches.is_empty(),
        "{what}: {} run(s) DISAGREE between the reference interpreter and the Lean \
         executable semantics:\n  {}",
        t.mismatches.len(),
        t.mismatches.join("\n  ")
    );
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// Positive: every subset fixture agrees, function by function.
#[test]
fn subset_fixtures_agree() {
    let Oracle::Ready(exe) = oracle() else { return };
    let fixtures = subset_fixtures();
    assert!(
        fixtures.len() >= 3,
        "expected several subset fixtures, found {:?}",
        fixtures.iter().map(|(n, _)| n).collect::<Vec<_>>()
    );
    let batches: Vec<Batch<'_>> = fixtures
        .iter()
        .enumerate()
        .map(|(i, (name, module))| Batch {
            label: format!("fixture {name}"),
            module,
            runs: module_runs(module, 4, 0x5B5B_0000 + i as u64),
        })
        .collect();
    let runs: usize = batches.iter().map(|b| b.runs.len()).sum();
    assert!(runs >= 10, "only {runs} runnable fixture functions");
    eprintln!(
        "subset fixtures: {:?}",
        batches
            .iter()
            .map(|b| (&b.label, b.runs.len()))
            .collect::<Vec<_>>()
    );
    let t = tally(&differential(exe, &batches));
    assert_no_mismatch(&t, "subset fixtures");
    assert!(
        t.agreed.get("ok").copied().unwrap_or(0) >= 5,
        "too few fixture runs executed to Ok on both sides: {:?}",
        t.agreed
    );
    let expected: BTreeMap<String, usize> = FIXTURE_UNSUPPORTED_LEDGER
        .iter()
        .map(|(k, n)| ((*k).to_string(), *n))
        .collect();
    assert_eq!(
        t.vacuous, FIXTURE_VACUOUS_LEDGER,
        "fixture runs filtered out by a false `Assume` (the interpreter's AssumeViolated): \
         {} measured, the ledger says {FIXTURE_VACUOUS_LEDGER}",
        t.vacuous
    );
    assert_eq!(
        t.unsupported, expected,
        "unsupported-coverage RATCHET (fixtures): the runs refused by name on one side, per \
         side:feature, differ from FIXTURE_UNSUPPORTED_LEDGER. A HIGHER count is a coverage \
         regression; a lower one is progress — edit the ledger in the same commit."
    );
}

/// The generator corpus agrees, and the unsupported count is ratcheted.
#[test]
fn generated_corpus_agrees_and_unsupported_is_ratcheted() {
    let Oracle::Ready(exe) = oracle() else { return };
    let modules: Vec<(u64, Module, Vec<FnSpec>)> = SEEDS
        .map(|seed| {
            let (module, specs) = gen_module_exec(seed);
            let errs = trust_ir_build::validate_module(&module);
            assert!(
                errs.is_empty(),
                "seed {seed}: generated module failed validation: {errs:?}"
            );
            assert!(
                module_subset_violations(&module).is_empty(),
                "seed {seed}: generated module is outside the subset"
            );
            (seed, module, specs)
        })
        .collect();
    let batches: Vec<Batch<'_>> = modules
        .iter()
        .map(|(seed, module, specs)| {
            let mut arg_rng = Rng::new(seed ^ 0xA5A5_A5A5_A5A5_A5A5);
            Batch {
                label: format!("seed {seed}"),
                module,
                runs: specs
                    .iter()
                    .map(|s| (s.id, build_args(&s.params, &mut arg_rng)))
                    .collect(),
            }
        })
        .collect();
    let reports = differential(exe, &batches);
    let t = tally(&reports);
    assert_no_mismatch(&t, "generator corpus");
    let ok = t.agreed.get("ok").copied().unwrap_or(0);
    let ub = t.agreed.get("ub").copied().unwrap_or(0);
    assert!(
        ok > 300,
        "only {ok} runs executed to Ok on both sides — the corpus degraded"
    );
    assert!(
        ub > 20,
        "only {ub} runs reached UB on both sides (div-by-zero, shift-by-width, wrong-variant lanes)"
    );
    let unsupported: usize = t.unsupported.values().sum();
    assert_eq!(
        t.vacuous, 0,
        "the generator mints no `Assume`, yet {} run(s) were AssumeViolated",
        t.vacuous
    );
    assert_eq!(
        unsupported, UNSUPPORTED_LEDGER,
        "unsupported-coverage RATCHET: {unsupported} run(s) were refused by name on one side, \
         the ledger says {UNSUPPORTED_LEDGER} ({:?}). A HIGHER count is a coverage regression; \
         a lower one is progress — edit UNSUPPORTED_LEDGER in the same commit.",
        t.unsupported
    );
}

/// `fn(a: i32, b: i32) -> i32 { a - b }`: the mutation control's subject.
fn sub_module() -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("w5b_sub");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("sub", ft);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    let r = fb.binop(trust_ir::inst::BinOp::Sub, Ty::I32, a, b);
    fb.ret(vec![r]);
    let id = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), id)
}

fn i32_verdict(v: i32) -> Verdict {
    Verdict::Ok(vec![Val::Int {
        width: 32,
        raw: u128::from(v as u32),
    }])
}

/// MUTATION CONTROL (harness self-test, no `lake` needed): the comparator
/// is fed a deliberately WRONG expected table — the verdicts a Lean whose
/// `semIntBinOp .Sub` computed `b - a` would print for `sub(5, 3)` and
/// `sub(3, 5)` — and must report the mismatch; the right table must agree.
/// Also pins that `Ok` against UB, a type error on either side, and any two
/// refusal classes are mismatches, and that `unsupported` is coverage.
#[test]
fn mutation_control_flipped_sub_is_reported() {
    let (module, f) = sub_module();
    let args = |a: i32, b: i32| {
        vec![
            InterpretValue::int(Ty::I32, a.into()).unwrap(),
            InterpretValue::int(Ty::I32, b.into()).unwrap(),
        ]
    };
    let rust_5_3 = canonical_verdict(run_rust(&module, f, &args(5, 3)));
    let rust_3_5 = canonical_verdict(run_rust(&module, f, &args(3, 5)));
    assert_eq!(rust_5_3, i32_verdict(2));
    assert_eq!(rust_3_5, i32_verdict(-2));
    // The right table agrees.
    assert_eq!(compare(&rust_5_3, &i32_verdict(2)), Comparison::Agree);
    assert_eq!(compare(&rust_3_5, &i32_verdict(-2)), Comparison::Agree);
    // The flipped-Sub table (`b - a`) is caught on both argument orders.
    assert!(matches!(
        compare(&rust_5_3, &i32_verdict(-2)),
        Comparison::Mismatch(_)
    ));
    assert!(matches!(
        compare(&rust_3_5, &i32_verdict(2)),
        Comparison::Mismatch(_)
    ));
    // A width disagreement is a value disagreement.
    let wide = Verdict::Ok(vec![Val::Int { width: 64, raw: 2 }]);
    assert!(matches!(compare(&rust_5_3, &wide), Comparison::Mismatch(_)));
    // Ok / UB, type errors and refusal-class drift are mismatches.
    let ub = Verdict::Ub("x".into());
    assert!(matches!(compare(&rust_5_3, &ub), Comparison::Mismatch(_)));
    assert!(matches!(compare(&ub, &rust_5_3), Comparison::Mismatch(_)));
    assert!(matches!(
        compare(&rust_5_3, &Verdict::TypeError("t".into())),
        Comparison::Mismatch(_)
    ));
    assert!(matches!(
        compare(&Verdict::TypeError("t".into()), &ub),
        Comparison::Mismatch(_)
    ));
    assert!(matches!(
        compare(&ub, &Verdict::Panic("p".into(), None)),
        Comparison::Mismatch(_)
    ));
    // Plan item P: two panics agree only on the same message (kind).
    assert_eq!(
        compare(
            &Verdict::Panic("attempt to add with overflow".into(), None),
            &Verdict::Panic("attempt to add with overflow".into(), None)
        ),
        Comparison::Agree
    );
    assert!(matches!(
        compare(
            &Verdict::Panic("attempt to add with overflow".into(), None),
            &Verdict::Panic("assertion failed".into(), None)
        ),
        Comparison::Mismatch(_)
    ));
    // Amendment P: and only on the same site — a dropped or retargeted site,
    // or a different location, is a mismatch with the same message.
    let sited =
        |site: Option<&str>| Verdict::Panic("assertion failed".into(), site.map(Into::into));
    assert_eq!(
        compare(
            &sited(Some("entry:1@global:0+0")),
            &sited(Some("entry:1@global:0+0"))
        ),
        Comparison::Agree
    );
    for other in [
        None,
        Some("entry:2@global:0+0"),
        Some("entry:1@global:0+8"),
        Some("entry:1@other"),
    ] {
        assert!(
            matches!(
                compare(&sited(Some("entry:1@global:0+0")), &sited(other)),
                Comparison::Mismatch(_)
            ),
            "{other:?}"
        );
    }
    assert!(matches!(
        compare(&ub, &Verdict::OutOfFuel),
        Comparison::Mismatch(_)
    ));
    assert!(matches!(
        compare(&rust_5_3, &Verdict::Error("e".into())),
        Comparison::Mismatch(_)
    ));
    // A broken oracle stays a mismatch even beside an interpreter refusal:
    // it must not be laundered into counted coverage.
    assert!(matches!(
        compare(
            &Verdict::Unsupported("unsupported_call".into()),
            &Verdict::Error("e".into())
        ),
        Comparison::Mismatch(_)
    ));
    // An interpreter-side vacuity filter (a false `Assume`) is its own
    // class: neither agreement nor coverage, counted and pinned per test.
    assert_eq!(
        compare(&Verdict::Vacuous("assume".into()), &rust_5_3),
        Comparison::Vacuous
    );
    // Same-class refusals agree; `unsupported` is coverage on either side.
    assert_eq!(compare(&ub, &Verdict::Ub("y".into())), Comparison::Agree);
    assert_eq!(
        compare(&rust_5_3, &Verdict::Unsupported("float".into())),
        Comparison::Unsupported("lean", "float".into())
    );
    assert_eq!(
        compare(&Verdict::Unsupported("unsupported_cast".into()), &ub),
        Comparison::Unsupported("rust", "unsupported_cast".into())
    );
}

/// MUTATION CONTROL against the REAL oracle: the Lean executable's own
/// verdicts for `sub(5, 3)` / `sub(3, 5)` are checked against the flipped
/// table (must mismatch) and the right one (must agree), so the wiring from
/// serde JSON through `trustir_eval` back into `compare` is exercised, not
/// only the comparator.
#[test]
fn mutation_control_against_the_oracle() {
    let Oracle::Ready(exe) = oracle() else { return };
    let (module, f) = sub_module();
    let args = |a: i32, b: i32| {
        vec![
            InterpretValue::int(Ty::I32, a.into()).unwrap(),
            InterpretValue::int(Ty::I32, b.into()).unwrap(),
        ]
    };
    let batches = vec![Batch {
        label: "sub".into(),
        module: &module,
        runs: vec![(f, args(5, 3)), (f, args(3, 5))],
    }];
    let lean = run_lean(exe, &batches).remove(0);
    let lean: Vec<Verdict> = lean.into_iter().map(canonical_verdict).collect();
    assert_eq!(
        lean,
        vec![i32_verdict(2), i32_verdict(-2)],
        "the real oracle computes a - b"
    );
    // The flipped-Sub expected table is reported on both orders.
    assert!(matches!(
        compare(&i32_verdict(-2), &lean[0]),
        Comparison::Mismatch(_)
    ));
    assert!(matches!(
        compare(&i32_verdict(2), &lean[1]),
        Comparison::Mismatch(_)
    ));
    assert_eq!(compare(&i32_verdict(2), &lean[0]), Comparison::Agree);
    assert_eq!(compare(&i32_verdict(-2), &lean[1]), Comparison::Agree);
}

/// A previously refused floating operator now has a strict executable result.
#[test]
fn floating_minimum_is_executable_with_a_strict_verdict() {
    let Oracle::Ready(exe) = oracle() else { return };
    let mut mb = ModuleBuilder::new("w5b_fmin");
    let ft = mb.add_func_type(vec![], vec![Ty::F64]);
    let mut fb = mb.function("fmin", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let a = fb.fconst(Ty::F64, 1.5);
    let b = fb.fconst(Ty::F64, 2.5);
    let r = fb.binop(trust_ir::inst::BinOp::FMin, Ty::F64, a, b);
    fb.ret(vec![r]);
    let f = fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let batches = vec![Batch {
        label: "fmin".into(),
        module: &module,
        runs: vec![(f, vec![])],
    }];
    let reports = differential(exe, &batches);
    assert_eq!(
        reports[0].lean,
        Verdict::Ok(vec![Val::Float(1.5f64.to_bits())])
    );
    assert_eq!(
        reports[0].rust,
        Verdict::Ok(vec![Val::Float(1.5f64.to_bits())])
    );
    assert_eq!(reports[0].comparison, Comparison::Agree);
}

/// A function the module only DECLARES is `UnsupportedCall` in the
/// interpreter and `unsupported interprocedural_call` in the oracle: neither
/// engine fabricates a body, and the harness counts it as coverage.
#[test]
fn bodyless_declaration_is_unsupported_on_both_sides() {
    let Oracle::Ready(exe) = oracle() else { return };
    let mut mb = ModuleBuilder::new_with_target_info(
        "w5b_decl",
        trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        },
    );
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let ext = mb.declare_function("ext", ft);
    let mut fb = mb.function("caller", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    let r = fb.call(ext, vec![x]);
    fb.ret(vec![r]);
    let caller = fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let arg = vec![InterpretValue::int(Ty::I32, 7).unwrap()];
    let batches = vec![Batch {
        label: "decl".into(),
        module: &module,
        runs: vec![(ext, arg.clone()), (caller, arg)],
    }];
    let reports = differential(exe, &batches);
    for r in &reports {
        assert_eq!(
            r.rust,
            Verdict::Unsupported("unsupported_call".into()),
            "{:?}",
            r.func
        );
        assert_eq!(
            r.lean,
            Verdict::Unsupported("interprocedural_call".into()),
            "{:?}",
            r.func
        );
    }
}

/// A `Function` with a scalar signature is runnable; the harness never sends
/// a pointer or aggregate argument (there is no engine-neutral spelling).
#[test]
fn only_scalar_signatures_are_run() {
    let mut mb = ModuleBuilder::new("w5b_sig");
    let scalar = mb.add_func_type(vec![Ty::U8, Ty::Bool], vec![]);
    let pointer = mb.add_func_type(vec![Ty::Ptr], vec![]);
    for (name, ft) in [("s", scalar), ("p", pointer)] {
        let mut fb = mb.function(name, ft);
        let entry = fb.create_block();
        let _ = fb.add_block_param(entry, if name == "s" { Ty::U8 } else { Ty::Ptr });
        if name == "s" {
            let _ = fb.add_block_param(entry, Ty::Bool);
        }
        fb.switch_to_block(entry);
        fb.ret(vec![]);
        fb.build();
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let runs = module_runs(&module, 2, 1);
    let names: Vec<&str> = runs
        .iter()
        .map(|(f, _)| {
            module
                .function_by_id(*f)
                .map(|f| f.name.as_str())
                .unwrap_or("?")
        })
        .collect();
    assert_eq!(names, ["s", "s"]);
}

// The build's result must not depend on the launcher's environment: an
// inherited `SDKROOT` naming the macOS 26 SDK fails the link (see
// `LAKE_SCRUBBED_ENV`), while the same tree built from an interactive shell
// links. Needs no Lean, so it runs on every machine, and it holds with the
// variable set in THIS process too — which is the gate's situation.
#[test]
fn lake_build_does_not_inherit_sdkroot() {
    let cmd = lake_build_command(
        Path::new("/elan/bin/lake"),
        Path::new("/lean"),
        "trustir_eval",
    );
    let removed: Vec<_> = cmd
        .get_envs()
        .filter(|(_, value)| value.is_none())
        .map(|(name, _)| name.to_string_lossy().into_owned())
        .collect();
    for name in LAKE_SCRUBBED_ENV {
        assert!(
            removed.iter().any(|r| r == name),
            "`lake build` inherits {name}; removed: {removed:?}"
        );
    }
    assert!(LAKE_SCRUBBED_ENV.contains(&"SDKROOT"));
    let path = cmd
        .get_envs()
        .find(|(name, _)| *name == "PATH")
        .and_then(|(_, value)| value)
        .expect("PATH is set for lake");
    assert!(
        path.to_string_lossy().starts_with("/elan/bin:"),
        "lean must sit beside lake on PATH, got {path:?}"
    );
}

// Inject a fallible build rather than changing process-wide locator settings:
// these controls need neither Lean nor a subprocess.
#[test]
fn oracle_build_cache_retains_failure_across_repeated_panics() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    let cache = OnceLock::new();
    let calls = AtomicUsize::new(0);
    let diagnostic = "lake failed: stdout\nexact stderr";
    for _ in 0..3 {
        let panic = std::panic::catch_unwind(|| {
            cached_oracle(&cache, || {
                calls.fetch_add(1, Ordering::SeqCst);
                Err(diagnostic.to_owned())
            })
        })
        .expect_err("every dependent test still fails");
        assert_eq!(
            panic.downcast_ref::<String>().map(String::as_str),
            Some(diagnostic)
        );
    }
    assert_eq!(
        calls.load(Ordering::SeqCst),
        1,
        "never repeat a failed build"
    );
}

#[test]
fn oracle_build_cache_initializes_failure_once_under_contention() {
    use std::sync::Barrier;
    use std::sync::atomic::{AtomicUsize, Ordering};

    let cache = OnceLock::new();
    let calls = AtomicUsize::new(0);
    let start = Barrier::new(8);
    std::thread::scope(|scope| {
        let threads: Vec<_> = (0..8)
            .map(|_| {
                scope.spawn(|| {
                    start.wait();
                    let panic = std::panic::catch_unwind(|| {
                        cached_oracle(&cache, || {
                            calls.fetch_add(1, Ordering::SeqCst);
                            Err("one failed build for all waiters".to_owned())
                        })
                    })
                    .expect_err("each waiter sees the failure");
                    assert_eq!(
                        panic.downcast_ref::<String>().map(String::as_str),
                        Some("one failed build for all waiters")
                    );
                })
            })
            .collect();
        for thread in threads {
            thread.join().expect("failure-cache assertion");
        }
    });
    assert_eq!(calls.load(Ordering::SeqCst), 1);
}

#[test]
fn oracle_build_cache_reuses_success_and_optional_absence() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    for available in [false, true] {
        let cache = OnceLock::new();
        let calls = AtomicUsize::new(0);
        let first = cached_oracle(&cache, || {
            calls.fetch_add(1, Ordering::SeqCst);
            Ok(if available {
                Oracle::Ready(PathBuf::from("built-oracle"))
            } else {
                Oracle::Absent
            })
        });
        let second = cached_oracle(&cache, || panic!("successful initialization is reused"));
        assert!(std::ptr::eq(first, second));
        match first {
            Oracle::Ready(path) => assert_eq!(path, Path::new("built-oracle")),
            Oracle::Absent => assert!(!available),
        }
        assert_eq!(matches!(first, Oracle::Ready(_)), available);
        assert_eq!(calls.load(Ordering::SeqCst), 1);
    }
}

// ---------------------------------------------------------------------------
// The release discipline (SPEC "A reference-counted cell is released by
// `Release`, never by `Dealloc`" and "An ARC operation counts only a
// reference-counted cell")
// ---------------------------------------------------------------------------

/// Where a release-matrix cell's allocation comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Region {
    Heap(AllocOrigin),
    /// A stack `Alloca`.
    Stack,
}

/// What a release-matrix function does to its allocation after
/// `store 7; load`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ReleaseOp {
    Dealloc,
    /// Nothing: the allocation is left live.
    Keep,
    Release,
    /// `Retain; Release; Release` — count 1 -> 2 -> 1 -> 0 on an RC cell.
    RetainReleaseRelease,
    /// `Retain` alone — count 1 -> 2 on an RC cell, which stays live.
    Retain,
    /// `u = IsUnique`, and the function returns `select u, v, 0`: the loaded
    /// value iff the answer is "unique" (a fresh RC cell's count is 1).
    IsUnique,
}

/// The DECIDED cells of the release matrix and the verdict class BOTH
/// engines must give. `Dealloc` of a reference-counted cell (`SwiftHeap` /
/// `CleanHeap`) is `ub`. `Retain` / `Release` / `IsUnique` on an allocation
/// that is not reference-counted (a `RustHeap` or `CMalloc` cell, a stack
/// `Alloca`) is `ub` — the six cells that were the shrink-only
/// `LEDGERED_RELEASE_CELLS` until SPEC "An ARC operation counts only a
/// reference-counted cell" decided them, plus `Retain` alone and `IsUnique`
/// on every region. Every other decided cell runs to the loaded value.
const DECIDED_RELEASE_CELLS: &[(Region, ReleaseOp, &str)] = &[
    (
        Region::Heap(AllocOrigin::CleanHeap),
        ReleaseOp::Dealloc,
        "ub",
    ),
    (
        Region::Heap(AllocOrigin::SwiftHeap),
        ReleaseOp::Dealloc,
        "ub",
    ),
    (
        Region::Heap(AllocOrigin::RustHeap),
        ReleaseOp::Dealloc,
        "ok",
    ),
    (Region::Heap(AllocOrigin::CMalloc), ReleaseOp::Dealloc, "ok"),
    (Region::Stack, ReleaseOp::Dealloc, "ok"),
    (Region::Heap(AllocOrigin::CleanHeap), ReleaseOp::Keep, "ok"),
    (Region::Heap(AllocOrigin::SwiftHeap), ReleaseOp::Keep, "ok"),
    (Region::Heap(AllocOrigin::RustHeap), ReleaseOp::Keep, "ok"),
    (Region::Heap(AllocOrigin::CMalloc), ReleaseOp::Keep, "ok"),
    (Region::Stack, ReleaseOp::Keep, "ok"),
    (
        Region::Heap(AllocOrigin::CleanHeap),
        ReleaseOp::Release,
        "ok",
    ),
    (
        Region::Heap(AllocOrigin::SwiftHeap),
        ReleaseOp::Release,
        "ok",
    ),
    (
        Region::Heap(AllocOrigin::CleanHeap),
        ReleaseOp::RetainReleaseRelease,
        "ok",
    ),
    (
        Region::Heap(AllocOrigin::SwiftHeap),
        ReleaseOp::RetainReleaseRelease,
        "ok",
    ),
    (
        Region::Heap(AllocOrigin::CleanHeap),
        ReleaseOp::Retain,
        "ok",
    ),
    (
        Region::Heap(AllocOrigin::SwiftHeap),
        ReleaseOp::Retain,
        "ok",
    ),
    (
        Region::Heap(AllocOrigin::CleanHeap),
        ReleaseOp::IsUnique,
        "ok",
    ),
    (
        Region::Heap(AllocOrigin::SwiftHeap),
        ReleaseOp::IsUnique,
        "ok",
    ),
    // The ARC trio on an allocation that is not reference-counted.
    (
        Region::Heap(AllocOrigin::RustHeap),
        ReleaseOp::Release,
        "ub",
    ),
    (Region::Heap(AllocOrigin::CMalloc), ReleaseOp::Release, "ub"),
    (Region::Stack, ReleaseOp::Release, "ub"),
    (
        Region::Heap(AllocOrigin::RustHeap),
        ReleaseOp::RetainReleaseRelease,
        "ub",
    ),
    (
        Region::Heap(AllocOrigin::CMalloc),
        ReleaseOp::RetainReleaseRelease,
        "ub",
    ),
    (Region::Stack, ReleaseOp::RetainReleaseRelease, "ub"),
    (Region::Heap(AllocOrigin::RustHeap), ReleaseOp::Retain, "ub"),
    (Region::Heap(AllocOrigin::CMalloc), ReleaseOp::Retain, "ub"),
    (Region::Stack, ReleaseOp::Retain, "ub"),
    (
        Region::Heap(AllocOrigin::RustHeap),
        ReleaseOp::IsUnique,
        "ub",
    ),
    (
        Region::Heap(AllocOrigin::CMalloc),
        ReleaseOp::IsUnique,
        "ub",
    ),
    (Region::Stack, ReleaseOp::IsUnique, "ub"),
];

/// Emit `op` on the allocation `p` and return the function's result: the
/// loaded `v`, or for `IsUnique` `select (is_unique p), v, 0`.
fn emit_release_op(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    op: ReleaseOp,
    p: trust_ir::value::ValueId,
    v: trust_ir::value::ValueId,
) -> trust_ir::value::ValueId {
    match op {
        ReleaseOp::Dealloc => fb.dealloc(p),
        ReleaseOp::Keep => {}
        ReleaseOp::Release => fb.release(p),
        ReleaseOp::RetainReleaseRelease => {
            fb.retain(p);
            fb.release(p);
            fb.release(p);
        }
        ReleaseOp::Retain => fb.retain(p),
        ReleaseOp::IsUnique => {
            let unique = fb.is_unique(p);
            let zero = fb.iconst(Ty::I32, 0);
            return fb.select(Ty::I32, unique, v, zero);
        }
    }
    v
}

/// One module holding one `() -> i32` function per cell:
/// `p = alloc i32; store 7 -> p; v = load p; <op> p; ret v`.
fn release_matrix_module(cells: &[(Region, ReleaseOp)]) -> (Module, Vec<FuncId>) {
    let mut mb = ModuleBuilder::new("w5b_release_discipline");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut ids = Vec::new();
    for (i, (region, op)) in cells.iter().enumerate() {
        let mut fb = mb.function(format!("cell{i}_{region:?}_{op:?}"), ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let p = match region {
            Region::Heap(origin) => fb.heap_alloc(Ty::I32, None, None, *origin),
            Region::Stack => fb.alloca(Ty::I32),
        };
        let seven = fb.iconst(Ty::I32, 7);
        fb.store(Ty::I32, p, seven);
        let v = fb.load(Ty::I32, p);
        let r = emit_release_op(&mut fb, *op, p, v);
        fb.ret(vec![r]);
        ids.push(fb.build());
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errs = trust_ir_build::validate_module(&module);
    assert!(
        errs.is_empty(),
        "every release-matrix cell is well-formed (the rule is dynamic): {errs:?}"
    );
    (module, ids)
}

/// Both engines run ONE release matrix, and every cell must AGREE and have
/// its expected verdict class: `Dealloc` of a `SwiftHeap` / `CleanHeap` cell
/// is `ub` in both, `Retain` / `Release` / `IsUnique` on a `RustHeap` /
/// `CMalloc` cell or a stack `Alloca` is `ub` in both, and every other cell is
/// `ok` with the loaded value. No ledger remains here: the six ARC-on-non-RC
/// cells it held are decided. The interpreter half runs without `lake`.
/// Plan item P (wire v52): the `assert_kind` golden, run with arguments that
/// make EVERY kind's check fail (and a passing twin per function), so both
/// engines panic and their messages — the failed assert's kind, its operands
/// printed by `core`'s format — are compared run by run. The random fixture
/// sweep cannot do this: it skips `usize` signatures and rarely fails a
/// check. `usize` arguments are spelled at the 64-bit width both engines use
/// for this module (no target: the interpreter's default, the model's pin).
#[test]
fn assert_kind_panics_agree_message_for_message() {
    let (module, runs) = assert_kind_runs();
    assert!(trust_ir_build::validate_module(&module).is_empty());

    // The interpreter half runs without Lean: each failing run panics with
    // exactly its kind's message, each passing twin returns.
    for (func, args, expected) in &runs {
        let rust = canonical_verdict(run_rust(&module, *func, args));
        match expected {
            Some(message) => {
                assert_eq!(
                    rust,
                    Verdict::Panic((*message).into(), None),
                    "{func:?} {args:?}"
                )
            }
            None => assert_eq!(rust.class(), "ok", "{func:?} {args:?}: {rust:?}"),
        }
    }

    let Oracle::Ready(exe) = oracle() else { return };
    let batches = vec![Batch {
        label: "assert_kind (every kind fails once)".into(),
        module: &module,
        runs: runs.iter().map(|(f, a, _)| (*f, a.clone())).collect(),
    }];
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), runs.len());
    let mut panics = 0;
    for (r, (_, _, expected)) in reports.iter().zip(&runs) {
        assert_eq!(
            r.comparison,
            Comparison::Agree,
            "{:?} {:?}: rust {:?}; lean {:?}",
            r.func,
            r.args,
            r.rust,
            r.lean
        );
        if let Some(message) = expected {
            assert_eq!(r.lean, Verdict::Panic((*message).into(), None));
            panics += 1;
        }
    }
    assert_eq!(panics, 14, "every kind's message was compared");
}

/// The `assert_kind.json` golden and its runs: each kind's failing run with
/// the message it must panic with, and each passing twin (`None`).
#[allow(clippy::type_complexity)]
fn assert_kind_runs() -> (
    Module,
    Vec<(FuncId, Vec<InterpretValue>, Option<&'static str>)>,
) {
    let text = fs::read_to_string(fixtures_dir().join("assert_kind.json")).expect("golden");
    let module: Module = serde_json::from_str(&text).expect("a module");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let int = |ty: Ty, v: i128| InterpretValue::int(ty, v).expect("in range");
    let us = |v: i128| int(Ty::Usize, v);
    let u32v = |v: i128| int(Ty::U32, v);
    let mut runs: Vec<(FuncId, Vec<InterpretValue>, Option<&'static str>)> = vec![
        (
            FuncId::new(0),
            vec![us(5), us(3)],
            Some("index out of bounds: the len is 3 but the index is 5"),
        ),
        (FuncId::new(0), vec![us(2), us(3)], None),
        (
            FuncId::new(1),
            vec![us(4097), us(8)],
            Some("misaligned pointer dereference: address must be a multiple of 0x8 but is 0x1001"),
        ),
        (FuncId::new(1), vec![us(4), us(8)], None),
        (
            FuncId::new(2),
            vec![u32v(7), u32v(0)],
            Some("attempt to divide by zero"),
        ),
        (FuncId::new(2), vec![u32v(7), u32v(2)], None),
        (
            FuncId::new(3),
            vec![u32v(7), u32v(0)],
            Some("attempt to calculate the remainder with a divisor of zero"),
        ),
        (
            FuncId::new(4),
            vec![us(0)],
            Some("null pointer dereference occurred"),
        ),
        (FuncId::new(4), vec![us(16)], None),
        (
            FuncId::new(6),
            vec![InterpretValue::bool(false)],
            Some("assertion failed"),
        ),
        (FuncId::new(6), vec![InterpretValue::bool(true)], None),
        (FuncId::new(5), vec![int(Ty::U8, 8)], None),
    ];
    for (k, message) in [
        "attempt to add with overflow",
        "attempt to subtract with overflow",
        "attempt to multiply with overflow",
        "attempt to divide with overflow",
        "attempt to calculate the remainder with overflow",
        "attempt to shift left with overflow",
        "attempt to shift right with overflow",
        "attempt to negate with overflow",
    ]
    .into_iter()
    .enumerate()
    {
        runs.push((FuncId::new(5), vec![int(Ty::U8, k as i128)], Some(message)));
    }
    (module, runs)
}

/// Amendment P (wire v54): the `assert_panic_site` and `assert_invoke`
/// goldens fail every sited check once against BOTH engines, which must agree
/// on the message, the entry AND the resolved location — the
/// `#[track_caller]` forward through `caller` (a run-time location the Lean
/// model resolves through the global it materialized) included — and return
/// on every passing twin.
#[test]
fn panic_sites_agree_entry_for_entry_and_location_for_location() {
    let load = |name: &str| -> Module {
        let text = fs::read_to_string(fixtures_dir().join(name)).expect("golden");
        serde_json::from_str(&text).expect("a module")
    };
    let sited = load("assert_panic_site.json");
    let invoke = load("assert_invoke.json");
    for module in [&sited, &invoke] {
        assert!(trust_ir_build::validate_module(module).is_empty());
    }
    let by_name = |module: &Module, name: &str| {
        module
            .functions
            .iter()
            .find(|f| f.name == name)
            .map(|f| f.id)
            .expect("function present")
    };
    let us = |v: i128| InterpretValue::int(Ty::Usize, v).expect("in range");
    let u8v = |v: i128| InterpretValue::int(Ty::U8, v).expect("in range");
    let at_loc = |entry: FuncId| Some(format!("entry:{}@global:0+0", entry.index()));
    type Run = (
        FuncId,
        Vec<InterpretValue>,
        Option<(&'static str, Option<String>)>,
    );
    let sited_runs: Vec<Run> = vec![
        (
            by_name(&sited, "bounds"),
            vec![us(5), us(3)],
            Some((
                "index out of bounds: the len is 3 but the index is 5",
                at_loc(by_name(&sited, "panic_bounds_check")),
            )),
        ),
        (by_name(&sited, "bounds"), vec![us(2), us(3)], None),
        (
            by_name(&sited, "add"),
            vec![u8v(255)],
            Some((
                "attempt to add with overflow",
                at_loc(by_name(&sited, "panic_const_add_overflow")),
            )),
        ),
        (by_name(&sited, "add"), vec![u8v(7)], None),
        (
            by_name(&sited, "resumed"),
            vec![InterpretValue::bool(false)],
            Some(("assertion failed", at_loc(by_name(&sited, "panic_resumed")))),
        ),
        (
            by_name(&sited, "resumed"),
            vec![InterpretValue::bool(true)],
            None,
        ),
        (
            by_name(&sited, "caller"),
            vec![us(9), us(2)],
            Some((
                "index out of bounds: the len is 2 but the index is 9",
                at_loc(by_name(&sited, "panic_bounds_check")),
            )),
        ),
        (by_name(&sited, "caller"), vec![us(1), us(2)], None),
    ];
    let invoke_runs: Vec<Run> = vec![
        (
            by_name(&invoke, "guarded"),
            vec![InterpretValue::bool(false), us(42)],
            Some((
                "attempt to divide by zero",
                at_loc(by_name(&invoke, "panic_const_div_by_zero")),
            )),
        ),
        (
            by_name(&invoke, "guarded"),
            vec![InterpretValue::bool(true), us(42)],
            None,
        ),
    ];

    // The interpreter half runs without Lean.
    for (module, runs) in [(&sited, &sited_runs), (&invoke, &invoke_runs)] {
        for (func, args, expected) in runs {
            let rust = canonical_verdict(run_rust(module, *func, args));
            match expected {
                Some((message, site)) => assert_eq!(
                    rust,
                    Verdict::Panic((*message).into(), site.clone()),
                    "{func:?} {args:?}"
                ),
                None => assert_eq!(rust.class(), "ok", "{func:?} {args:?}: {rust:?}"),
            }
        }
    }

    let Oracle::Ready(exe) = oracle() else { return };
    let batches = vec![
        Batch {
            label: "assert_panic_site (every sited check fails once)".into(),
            module: &sited,
            runs: sited_runs.iter().map(|(f, a, _)| (*f, a.clone())).collect(),
        },
        Batch {
            label: "assert_invoke (normal edge and sited failure)".into(),
            module: &invoke,
            runs: invoke_runs
                .iter()
                .map(|(f, a, _)| (*f, a.clone()))
                .collect(),
        },
    ];
    let reports = differential(exe, &batches);
    let expected: Vec<&Run> = sited_runs.iter().chain(&invoke_runs).collect();
    assert_eq!(reports.len(), expected.len());
    let mut panics = 0;
    for (r, (_, _, want)) in reports.iter().zip(expected) {
        assert_eq!(
            r.comparison,
            Comparison::Agree,
            "{:?} {:?}: rust {:?}; lean {:?}",
            r.func,
            r.args,
            r.rust,
            r.lean
        );
        if let Some((message, site)) = want {
            assert_eq!(r.lean, Verdict::Panic((*message).into(), site.clone()));
            panics += 1;
        }
    }
    assert_eq!(panics, 5, "every sited check's panic was compared");
}

#[test]
fn release_discipline_agrees_across_engines() {
    let decided: Vec<(Region, ReleaseOp)> = DECIDED_RELEASE_CELLS
        .iter()
        .map(|(r, o, _)| (*r, *o))
        .collect();
    let (decided_module, decided_ids) = release_matrix_module(&decided);

    // The interpreter half: each decided cell has its expected class, an `ok`
    // cell returns the loaded 7, and a `ub` ARC cell names the rule.
    for ((region, op, class), f) in DECIDED_RELEASE_CELLS.iter().zip(&decided_ids) {
        let rust = canonical_verdict(run_rust(&decided_module, *f, &[]));
        assert_eq!(
            rust.class(),
            *class,
            "interpreter, {region:?} x {op:?}: {rust:?}"
        );
        match &rust {
            Verdict::Graph(_) => assert_eq!(rust, i32_verdict(7), "{region:?} x {op:?}"),
            Verdict::Ub(message) if *op != ReleaseOp::Dealloc => assert!(
                message.contains("not a reference-counted cell"),
                "{region:?} x {op:?}: the ARC refusal must name the rule, got: {message}"
            ),
            _ => {}
        }
    }

    let Oracle::Ready(exe) = oracle() else { return };
    let batches = vec![Batch {
        label: "release matrix (decided)".into(),
        module: &decided_module,
        runs: decided_ids.iter().map(|f| (*f, vec![])).collect(),
    }];
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), DECIDED_RELEASE_CELLS.len());
    for ((region, op, class), r) in DECIDED_RELEASE_CELLS.iter().zip(&reports) {
        assert_eq!(
            r.comparison,
            Comparison::Agree,
            "{region:?} x {op:?}: the engines must agree (rust {:?}; lean {:?})",
            r.rust,
            r.lean
        );
        assert_eq!(
            r.lean.class(),
            *class,
            "{region:?} x {op:?}: expected verdict class {class} (rust {:?}; lean {:?})",
            r.rust,
            r.lean
        );
    }
}

/// The GLOBAL-reservation cells of the ARC rule and the verdict class both
/// engines must give: `g = global_addr G; <op> g; ret 7`. A global's
/// reservation is not a reference-counted cell, so every ARC operation on it
/// is `ub` (interpreter: the reservation has no `HeapAlloc` origin; Lean:
/// `semGlobalAddrWithCtx` gives it the `owned` permission `requireArcRef`
/// refuses). `Keep` is the control. The function touches no byte of the
/// global: the question is the ARC operand alone.
const GLOBAL_ARC_CELLS: &[(ReleaseOp, &str)] = &[
    (ReleaseOp::Keep, "ok"),
    (ReleaseOp::Retain, "ub"),
    (ReleaseOp::Release, "ub"),
    (ReleaseOp::RetainReleaseRelease, "ub"),
    (ReleaseOp::IsUnique, "ub"),
];

/// One module holding one `() -> i32` function per global cell, all over one
/// module global `G: i32`.
fn global_arc_module(cells: &[(ReleaseOp, &str)]) -> (Module, Vec<FuncId>) {
    use trust_ir::value::GlobalId;
    use trust_ir::{Global, Linkage};
    let mut mb = ModuleBuilder::new("w5b_global_arc");
    mb.add_global(Global {
        name: "G".into(),
        ty: Ty::I32,
        mutable: true,
        initializer: None,
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut ids = Vec::new();
    for (i, (op, _)) in cells.iter().enumerate() {
        let mut fb = mb.function(format!("global{i}_{op:?}"), ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let g = fb.global_addr(GlobalId::new(0));
        let seven = fb.iconst(Ty::I32, 7);
        let r = emit_release_op(&mut fb, *op, g, seven);
        fb.ret(vec![r]);
        ids.push(fb.build());
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errs = trust_ir_build::validate_module(&module);
    assert!(
        errs.is_empty(),
        "every global ARC cell is well-formed (the rule is dynamic): {errs:?}"
    );
    (module, ids)
}

/// Both engines run the global-reservation cells: every ARC operation on a
/// global's reservation is `ub` in both, and `Keep` is `ok` 7 in both. Before
/// the interpreter's origin check, `GlobalAddr` + `Retain` ran to `Ok(7)`
/// there while Lean said "ARC operation requires arcRef permission, found
/// owned" (measured, the challenge's `glob_retain`).
#[test]
fn arc_on_a_global_reservation_agrees_across_engines() {
    let (module, ids) = global_arc_module(GLOBAL_ARC_CELLS);
    for ((op, class), f) in GLOBAL_ARC_CELLS.iter().zip(&ids) {
        let rust = canonical_verdict(run_rust(&module, *f, &[]));
        assert_eq!(
            rust.class(),
            *class,
            "interpreter, global x {op:?}: {rust:?}"
        );
        match &rust {
            Verdict::Graph(_) => assert_eq!(rust, i32_verdict(7), "global x {op:?}"),
            Verdict::Ub(message) => assert!(
                message.contains("not a reference-counted cell"),
                "global x {op:?}: the refusal must name the rule, got: {message}"
            ),
            _ => {}
        }
    }

    let Oracle::Ready(exe) = oracle() else { return };
    let batches = vec![Batch {
        label: "global reservation x ARC".into(),
        module: &module,
        runs: ids.iter().map(|f| (*f, vec![])).collect(),
    }];
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), GLOBAL_ARC_CELLS.len());
    for ((op, class), r) in GLOBAL_ARC_CELLS.iter().zip(&reports) {
        assert_eq!(
            r.comparison,
            Comparison::Agree,
            "global x {op:?}: the engines must agree (rust {:?}; lean {:?})",
            r.rust,
            r.lean
        );
        assert_eq!(
            r.lean.class(),
            *class,
            "global x {op:?}: expected verdict class {class} (rust {:?}; lean {:?})",
            r.rust,
            r.lean
        );
    }
}

/// What one engine must say about a ledgered cell, exactly as measured: `ok`
/// with an `i32`, or `ub` with a message containing the given text.
#[derive(Clone, Copy, Debug)]
enum Measured {
    Ok(i32),
    Ub(&'static str),
}

impl Measured {
    fn holds(self, verdict: &Verdict) -> bool {
        match (self, verdict) {
            (Measured::Ok(v), _) => *verdict == i32_verdict(v),
            (Measured::Ub(text), Verdict::Ub(message)) => message.contains(text),
            _ => false,
        }
    }
}

/// The verdict BOTH engines must give a DECIDED cell: `ok` with one integer
/// or `bool` value, or `ub` — the interpreter's message containing the given
/// text, which names the rule.
#[derive(Clone, Copy, Debug)]
enum Expect {
    I32(i32),
    /// An `i64` result, at its bit pattern.
    I64(i64),
    U8(u8),
    U64(u64),
    Bool(bool),
    Ub(&'static str),
}

impl Expect {
    /// The canonical value an `ok` cell returns.
    fn value(self) -> Option<Val> {
        match self {
            Expect::I32(v) => Some(Val::Int {
                width: 32,
                raw: u128::from(v as u32),
            }),
            Expect::I64(v) => Some(Val::Int {
                width: 64,
                raw: u128::from(v as u64),
            }),
            Expect::U8(v) => Some(Val::Int {
                width: 8,
                raw: u128::from(v),
            }),
            Expect::U64(v) => Some(Val::Int {
                width: 64,
                raw: u128::from(v),
            }),
            Expect::Bool(b) => Some(Val::Bool(b)),
            Expect::Ub(_) => None,
        }
    }

    /// Does `verdict` give this expectation? An `ok` value must be equal; a
    /// `ub` message must contain the text (only the interpreter's message is
    /// held to the text: the oracle's `ub` is a class).
    fn holds(self, verdict: &Verdict, check_text: bool) -> bool {
        match (self, verdict) {
            (Expect::Ub(text), Verdict::Ub(message)) => !check_text || message.contains(text),
            (Expect::Ub(_), _) => false,
            (e, Verdict::Ok(_) | Verdict::Graph(_)) => {
                verdict == &Verdict::Ok(vec![e.value().expect("ok cell")])
            }
            _ => false,
        }
    }
}

/// Hold a DECIDED table: without `lake`, every cell's interpreter verdict is
/// the expected one (a `ub` cell's message names the rule); with the oracle,
/// every cell must also AGREE and give the expected verdict in Lean. Every
/// cell is checked before the test fails, and the failure names each cell.
fn check_decided<C: std::fmt::Debug>(
    what: &str,
    module: &Module,
    ids: &[FuncId],
    cells: &[(C, Expect)],
) {
    assert_eq!(ids.len(), cells.len(), "{what}: one function per cell");
    let mut failed = Vec::new();
    for ((cell, expect), f) in cells.iter().zip(ids) {
        let rust = canonical_verdict(run_rust(module, *f, &[]));
        if !expect.holds(&rust, true) {
            failed.push(format!(
                "{what}: interpreter, {cell:?}: expected {expect:?}, got {rust:?}"
            ));
        }
    }
    let Oracle::Ready(exe) = oracle() else {
        assert!(failed.is_empty(), "{}", failed.join("\n"));
        return;
    };
    let batches = vec![Batch {
        label: what.into(),
        module,
        runs: ids.iter().map(|f| (*f, vec![])).collect(),
    }];
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), cells.len());
    for ((cell, expect), r) in cells.iter().zip(&reports) {
        if r.comparison != Comparison::Agree || !expect.holds(&r.lean, false) {
            failed.push(format!(
                "{what}: {cell:?} must agree and give {expect:?} in both engines: {:?} (rust {:?}; \
                 lean {:?})",
                r.comparison, r.rust, r.lean
            ));
        }
    }
    assert!(
        failed.is_empty(),
        "{} of {} decided cells failed:\n{}",
        failed.len(),
        cells.len(),
        failed.join("\n")
    );
}

/// Hold one ledger: every cell's interpreter verdict is as measured without
/// `lake`; with the oracle, a DIVERGENT cell (`rust != lean` as measured)
/// must still be a mismatch and an AGREEING control must still agree. A cell
/// that stops diverging fails here: it leaves the ledger only by a decision
/// both engines implement, which moves it to a decided table in the same
/// commit. Every cell is checked before the test fails, and the failure
/// names each cell that moved.
fn hold_divergence_ledger<C: std::fmt::Debug>(
    what: &str,
    module: &Module,
    ids: &[FuncId],
    cells: &[(C, Measured, Measured)],
) {
    let mut moved = Vec::new();
    for ((cell, rust_expected, _), f) in cells.iter().zip(ids) {
        let rust = canonical_verdict(run_rust(module, *f, &[]));
        if !rust_expected.holds(&rust) {
            moved.push(format!(
                "{what}: interpreter, {cell:?}: expected {rust_expected:?}, got {rust:?}"
            ));
        }
    }
    let Oracle::Ready(exe) = oracle() else {
        assert!(moved.is_empty(), "{}", moved.join("\n"));
        return;
    };
    let batches = vec![Batch {
        label: what.into(),
        module,
        runs: ids.iter().map(|f| (*f, vec![])).collect(),
    }];
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), cells.len());
    for ((cell, rust_expected, lean_expected), r) in cells.iter().zip(&reports) {
        let diverges = matches!(r.comparison, Comparison::Mismatch(_));
        let expected_to_diverge = matches!(
            (rust_expected, lean_expected),
            (Measured::Ok(a), Measured::Ok(b)) if a != b
        ) || !matches!(
            (rust_expected, lean_expected),
            (Measured::Ok(_), Measured::Ok(_)) | (Measured::Ub(_), Measured::Ub(_))
        );
        if !(rust_expected.holds(&r.rust)
            && lean_expected.holds(&r.lean)
            && diverges == expected_to_diverge)
        {
            moved.push(format!(
                "{what}: {cell:?} no longer behaves as measured (rust {rust_expected:?}, lean \
                 {lean_expected:?}, {}): rust {:?}; lean {:?}",
                if expected_to_diverge {
                    "diverging"
                } else {
                    "agreeing"
                },
                r.rust,
                r.lean
            ));
        }
    }
    assert!(
        moved.is_empty(),
        "{} check(s) over {} ledgered cells failed. A ledgered cell leaves the ledger only \
         by a decision both engines implement — move it to a decided table, with its SPEC \
         entry, in the same commit.\n{}",
        moved.len(),
        cells.len(),
        moved.join("\n")
    );
}

/// An ARC-operand shape outside or inside the allocation the pointer was
/// derived from. Unless stated otherwise the pointer is `gep i32 a [1]`: four
/// bytes past `a`'s base.
#[derive(Clone, Copy, Debug)]
enum ProvenanceCell {
    /// (a) `a = CleanHeap i32`; `Retain(a + 4)`; `ret 7`.
    LoneCleanHeap,
    /// (b) `a`, `b` = `CleanHeap i32`; `Retain(a + 4)`;
    /// `ret is_unique(a) + 2 * is_unique(b)`.
    CleanHeapThenCleanHeap,
    /// (c) `a = RustHeap i32`, `b = CleanHeap i32`; `Retain(a + 4)`; `ret 7`.
    /// The one member of the [`ProvenanceCell::NonRcThenRc`] family kept
    /// under its own name: the Lean theorem
    /// `retain_one_past_rustHeap_is_ub_and_spares_neighbour` cites it.
    RustHeapThenCleanHeap,
    /// (d) `a = CleanHeap i32`, `b = RustHeap i32`; `Retain(a + 4)`; `ret 7`.
    CleanHeapThenRustHeap,
    /// `a = CleanHeap i64`; `Retain(a + 4)` (INSIDE `a`, off its base);
    /// `Release(a)`; `ret select(is_unique(a), 7, 0)`. An agreeing control
    /// (ok 7 in both) until clause 3 was decided.
    InteriorOfRcCell,
    /// Probe p18: `a = RustHeap i32`, `b = CleanHeap i32`;
    /// `Retain(gep i32 a [5])`, twenty bytes past `a`'s base: past its slack
    /// tail, at `b`'s base in the reference placement; `ret 7`.
    RetainPastSlackNamesNextRcCell,
    /// Probe p19: `a`, `b` = `CleanHeap i32`; `Retain(gep i32 a [5])`;
    /// `ret is_unique(a) + 2 * is_unique(b)`.
    RetainPastSlackOfRcCell,
    /// The family of (c): `a = <non-RC> i32`, `b = <RC origin> i32`;
    /// `<op>(a + 4)` with the op's [`emit_release_op`] result over 7 (`ret 7`,
    /// or for `IsUnique` `ret select(is_unique(a + 4), 7, 0)`).
    NonRcThenRc(NonRc, AllocOrigin, ReleaseOp),
    /// The interpreter unit test `arc_operand_off_its_cell_base_is_undefined_behavior`'s
    /// matrix, run in both engines: `a`, `b` = `<RC origin> i64`, `align 8`;
    /// `<op>(gep i8 a [offset])` with the op's [`emit_release_op`] result over
    /// 7. Offset 0 is the object base (ok 7); 4 is inside `a`, 8 one past its
    /// end, 20 in its slack tail and 32 inside `b` in the reference placement,
    /// each off `a`'s base. The other off-base cells above all `Retain`; these
    /// put `Release` and `IsUnique`, on both reference-counted origins, under
    /// the gate.
    RcCellAtOffset(AllocOrigin, ReleaseOp, u8),
}

/// The allocation a [`ProvenanceCell::NonRcThenRc`] cell's pointer is
/// derived from: every kind of allocation that is not reference-counted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NonRc {
    /// A stack `Alloca`.
    Stack,
    /// A `RustHeap` or `CMalloc` `HeapAlloc`.
    Heap(AllocOrigin),
    /// The module global `G: i32`'s reservation (`global_addr G`).
    Global,
}

/// Every non-reference-counted allocation a [`ProvenanceCell::NonRcThenRc`]
/// cell's pointer is derived from.
const NON_RC_PREDECESSORS: [NonRc; 4] = [
    NonRc::Stack,
    NonRc::Heap(AllocOrigin::RustHeap),
    NonRc::Heap(AllocOrigin::CMalloc),
    NonRc::Global,
];

/// Every reference-counted origin of the cell that follows it.
const RC_SUCCESSORS: [AllocOrigin; 2] = [AllocOrigin::CleanHeap, AllocOrigin::SwiftHeap];

/// The three ARC operations, applied once to the one-past-end pointer.
const ARC_OPS: [ReleaseOp; 3] = [ReleaseOp::Retain, ReleaseOp::Release, ReleaseOp::IsUnique];

/// The byte offsets of a [`ProvenanceCell::RcCellAtOffset`] operand: the
/// object base, then the four off-base offsets of the interpreter unit test.
const RC_CELL_OFFSETS: [u8; 5] = [0, 4, 8, 20, 32];

/// The DECIDED ARC-operand cells (SPEC "A pointer operand names the
/// allocation it was derived from" with "An ARC operation counts only a
/// reference-counted cell"), in two groups:
/// * every ARC operand whose PROVENANCE is not a reference-counted cell is
///   undefined behaviour at any offset, and never acts on the
///   reference-counted cell placed after it: cell (c) and its whole family —
///   every (non-RC predecessor, RC successor, operation) combination of the
///   one-past-end `i32` shape, 24 cells, each ok 7 in Lean while it resolved
///   the operand by address and acted on the following cell — and probe
///   p18, the same shape past the heap slack tail;
/// * an ARC operand derived from a reference-counted cell is undefined
///   behaviour anywhere but the cell's OBJECT BASE (clause 3, decided
///   2026-09-30): cells (a), (b) and (d), the interior pointer and probe p19.
///   Both engines counted all five before that ruling (the shrink-only
///   ledger `arc_operand_offset_shapes_stay_as_measured`, now deleted). Those
///   five all `Retain`; the [`ProvenanceCell::RcCellAtOffset`] matrix holds
///   every operation on both reference-counted origins off the base, with the
///   base itself as the positive control (ok 7), so that an engine refusing
///   every ARC operand fails here too.
fn decided_arc_operand_cells() -> Vec<(ProvenanceCell, Expect)> {
    let rule = Expect::Ub("not a reference-counted cell");
    let mut cells = vec![(ProvenanceCell::RustHeapThenCleanHeap, rule)];
    for first in NON_RC_PREDECESSORS {
        for second in RC_SUCCESSORS {
            for op in ARC_OPS {
                if (first, second, op)
                    == (
                        NonRc::Heap(AllocOrigin::RustHeap),
                        AllocOrigin::CleanHeap,
                        ReleaseOp::Retain,
                    )
                {
                    continue;
                }
                cells.push((ProvenanceCell::NonRcThenRc(first, second, op), rule));
            }
        }
    }
    cells.push((ProvenanceCell::RetainPastSlackNamesNextRcCell, rule));
    let off_base = Expect::Ub("not at the object base");
    for cell in [
        ProvenanceCell::LoneCleanHeap,
        ProvenanceCell::CleanHeapThenCleanHeap,
        ProvenanceCell::CleanHeapThenRustHeap,
        ProvenanceCell::InteriorOfRcCell,
        ProvenanceCell::RetainPastSlackOfRcCell,
    ] {
        cells.push((cell, off_base));
    }
    for origin in RC_SUCCESSORS {
        for op in ARC_OPS {
            for offset in RC_CELL_OFFSETS {
                let expect = if offset == 0 {
                    Expect::I32(7)
                } else {
                    off_base
                };
                cells.push((ProvenanceCell::RcCellAtOffset(origin, op, offset), expect));
            }
        }
    }
    cells
}

fn provenance_module(cells: &[ProvenanceCell]) -> (Module, Vec<FuncId>) {
    use trust_ir::value::GlobalId;
    use trust_ir::{Global, Linkage};
    let mut mb = ModuleBuilder::new("w5b_arc_operand_provenance");
    mb.add_global(Global {
        name: "G".into(),
        ty: Ty::I32,
        mutable: true,
        initializer: None,
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut ids = Vec::new();
    for (i, cell) in cells.iter().enumerate() {
        let mut fb = mb.function(format!("provenance{i}_{cell:?}"), ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        if let ProvenanceCell::NonRcThenRc(first, second, op) = cell {
            let a = match first {
                NonRc::Stack => fb.alloca(Ty::I32),
                NonRc::Heap(origin) => fb.heap_alloc(Ty::I32, None, None, *origin),
                NonRc::Global => fb.global_addr(GlobalId::new(0)),
            };
            let _b = fb.heap_alloc(Ty::I32, None, None, *second);
            let one = fb.iconst(Ty::U64, 1);
            let past = fb.gep(Ty::I32, a, vec![one]);
            let seven = fb.iconst(Ty::I32, 7);
            let r = emit_release_op(&mut fb, *op, past, seven);
            fb.ret(vec![r]);
            ids.push(fb.build());
            continue;
        }
        if let ProvenanceCell::RcCellAtOffset(origin, op, offset) = cell {
            let a = fb.heap_alloc(Ty::I64, None, Some(8), *origin);
            let _b = fb.heap_alloc(Ty::I64, None, Some(8), *origin);
            let offset = fb.iconst(Ty::U64, i128::from(*offset));
            let p = fb.gep(Ty::I8, a, vec![offset]);
            let seven = fb.iconst(Ty::I32, 7);
            let r = emit_release_op(&mut fb, *op, p, seven);
            fb.ret(vec![r]);
            ids.push(fb.build());
            continue;
        }
        let (first, second, cell_ty, index) = match cell {
            ProvenanceCell::LoneCleanHeap => (AllocOrigin::CleanHeap, None, Ty::I32, 1),
            ProvenanceCell::CleanHeapThenCleanHeap => (
                AllocOrigin::CleanHeap,
                Some(AllocOrigin::CleanHeap),
                Ty::I32,
                1,
            ),
            ProvenanceCell::RustHeapThenCleanHeap => (
                AllocOrigin::RustHeap,
                Some(AllocOrigin::CleanHeap),
                Ty::I32,
                1,
            ),
            ProvenanceCell::CleanHeapThenRustHeap => (
                AllocOrigin::CleanHeap,
                Some(AllocOrigin::RustHeap),
                Ty::I32,
                1,
            ),
            ProvenanceCell::InteriorOfRcCell => (AllocOrigin::CleanHeap, None, Ty::I64, 1),
            ProvenanceCell::RetainPastSlackNamesNextRcCell => (
                AllocOrigin::RustHeap,
                Some(AllocOrigin::CleanHeap),
                Ty::I32,
                5,
            ),
            ProvenanceCell::RetainPastSlackOfRcCell => (
                AllocOrigin::CleanHeap,
                Some(AllocOrigin::CleanHeap),
                Ty::I32,
                5,
            ),
            ProvenanceCell::NonRcThenRc(..) | ProvenanceCell::RcCellAtOffset(..) => {
                unreachable!("built above")
            }
        };
        let a = fb.heap_alloc(cell_ty, None, None, first);
        let b = second.map(|origin| fb.heap_alloc(Ty::I32, None, None, origin));
        let offset = fb.iconst(Ty::U64, index);
        let past = fb.gep(Ty::I32, a, vec![offset]);
        fb.retain(past);
        let seven = fb.iconst(Ty::I32, 7);
        let r = match cell {
            ProvenanceCell::CleanHeapThenCleanHeap | ProvenanceCell::RetainPastSlackOfRcCell => {
                let b = b.expect("two cells");
                let zero = fb.iconst(Ty::I32, 0);
                let one_i32 = fb.iconst(Ty::I32, 1);
                let two = fb.iconst(Ty::I32, 2);
                let ua = fb.is_unique(a);
                let ub_ = fb.is_unique(b);
                let a_bit = fb.select(Ty::I32, ua, one_i32, zero);
                let b_bit = fb.select(Ty::I32, ub_, two, zero);
                fb.add(Ty::I32, a_bit, b_bit)
            }
            ProvenanceCell::InteriorOfRcCell => {
                fb.release(a);
                let zero = fb.iconst(Ty::I32, 0);
                let unique = fb.is_unique(a);
                fb.select(Ty::I32, unique, seven, zero)
            }
            _ => seven,
        };
        fb.ret(vec![r]);
        ids.push(fb.build());
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errs = trust_ir_build::validate_module(&module);
    assert!(
        errs.is_empty(),
        "every provenance cell is well-formed (the rule is dynamic): {errs:?}"
    );
    (module, ids)
}

/// Both engines run the DECIDED ARC-operand cells, and every cell must AGREE
/// and be `ub`: "not a reference-counted cell" where the operand's
/// provenance is not reference-counted, whatever cell sits at its address;
/// "not at the object base" where it is a reference-counted cell reached
/// off its base. Measured against the Lean model of trust-ir `e2154f00`: all
/// 24 one-past-end cells diverged (Lean ok 7, acting on the following
/// cell); p18 agreed there (Lean's address landed in nothing it could
/// count), a pin. The interpreter's mutation recorded by SPEC "An ARC
/// operation counts only a reference-counted cell" (dropping the origin
/// check) fails every provenance cell; dropping the object-base check fails
/// the five off-base `Retain` cells in both halves (measured when clause 3
/// was decided). The [`ProvenanceCell::RcCellAtOffset`] matrix was added
/// because those five reach only `Retain` off a base: with the
/// interpreter's check dropped from `is_unique` alone, the whole gate still
/// passed before the matrix (measured in review, 2026-10-01). With the
/// check dropped from `is_unique` and, for `Release` only, from
/// `arc_allocation_mut`, this test fails on exactly the 16 off-base
/// `Release` / `IsUnique` cells of the matrix, in both halves; with
/// `requireObjectBase` dropped from Lean's `semRelease` and `semIsUnique`
/// it fails on the same 16 cells, agreement half only (measured
/// 2026-10-01).
#[test]
fn arc_operand_provenance_agrees_across_engines() {
    let decided = decided_arc_operand_cells();
    let cells: Vec<ProvenanceCell> = decided.iter().map(|(c, _)| *c).collect();
    let (module, ids) = provenance_module(&cells);
    check_decided("ARC operand provenance", &module, &ids, &decided);
}

/// A borrow-liveness shape at `Dealloc`, DECIDED (SPEC "Freeing an
/// allocation under a live borrow is undefined behaviour"). Every cell stores
/// 7 into its allocation, loads it back, frees the allocation with `Dealloc`
/// and returns the loaded value. Every borrow operand lies inside the bytes
/// its allocation requested, derived without an integer round trip, and each
/// borrow is ended at most once: the conditions under which both engines name
/// the same allocation (clause 2 of that section).
#[derive(Clone, Copy, Debug)]
enum LivenessCell {
    /// `b = Borrow p`; `Dealloc p` with `b` live.
    SharedLive(Region),
    /// `m = BorrowMut p`; `Dealloc p` with `m` live.
    UniqueLive(Region),
    /// `b = Borrow p`; `EndBorrow b`; `Dealloc p`.
    SharedEnded(Region),
    /// `m = BorrowMut p`; `EndBorrow m`; `Dealloc p`.
    UniqueEnded(Region),
    /// `p = Alloca i64`; `b = Borrow (gep i32 p [1])`; `Dealloc p`: an
    /// interior borrow borrows the allocation.
    InteriorLive,
    /// `b = Borrow p`; `c = Borrow p`; `EndBorrow b`; `Dealloc p`.
    OneOfTwoEnded,
    /// `b = Borrow p`; `c = Borrow p`; `EndBorrow c`; `EndBorrow b`; `Dealloc p`.
    BothEnded,
    /// `b = Borrow p`; `EndBorrow b`; `m = BorrowMut p`; `Dealloc p`.
    EndedThenBorrowedAgain,
    /// `b = Borrow p`; `c = Borrow b`; `EndBorrow c`; `EndBorrow b`; `Dealloc p`.
    ReborrowChainEnded,
    /// `p = RustHeap i32`; `call take(p)` where `take` borrows its parameter
    /// and returns; `Dealloc p`: a borrow outlives the function that took it.
    BorrowedInCallee,
    /// `b = Borrow p`; `store b -> slot`; `EndBorrow b`; `Dealloc p`: a stored
    /// copy of a borrow does not keep it live once it is ended.
    EscapedThenEnded,
    /// `g = global_addr G`; `b = Borrow g`; `Dealloc g`.
    GlobalLive,
    /// `g = global_addr G`; `Dealloc g`: the control.
    GlobalNoBorrow,
}

const RUST_HEAP: Region = Region::Heap(AllocOrigin::RustHeap);
const C_MALLOC: Region = Region::Heap(AllocOrigin::CMalloc);

/// The decided borrow-liveness cells and the verdict class both engines must
/// give. Lean's `semDealloc` refuses a `sharedBorrow n` / `uniqueBorrow`
/// permission; the interpreter refuses a nonzero live-borrow count.
const DECIDED_LIVENESS_CELLS: &[(LivenessCell, &str)] = &[
    (LivenessCell::SharedLive(Region::Stack), "ub"),
    (LivenessCell::SharedLive(RUST_HEAP), "ub"),
    (LivenessCell::SharedLive(C_MALLOC), "ub"),
    (LivenessCell::UniqueLive(Region::Stack), "ub"),
    (LivenessCell::UniqueLive(RUST_HEAP), "ub"),
    (LivenessCell::UniqueLive(C_MALLOC), "ub"),
    (LivenessCell::SharedEnded(Region::Stack), "ok"),
    (LivenessCell::SharedEnded(RUST_HEAP), "ok"),
    (LivenessCell::UniqueEnded(Region::Stack), "ok"),
    (LivenessCell::UniqueEnded(RUST_HEAP), "ok"),
    (LivenessCell::InteriorLive, "ub"),
    (LivenessCell::OneOfTwoEnded, "ub"),
    (LivenessCell::BothEnded, "ok"),
    (LivenessCell::EndedThenBorrowedAgain, "ub"),
    (LivenessCell::ReborrowChainEnded, "ok"),
    (LivenessCell::BorrowedInCallee, "ub"),
    (LivenessCell::EscapedThenEnded, "ok"),
    (LivenessCell::GlobalLive, "ub"),
    (LivenessCell::GlobalNoBorrow, "ok"),
];

fn liveness_module(cells: &[(LivenessCell, &str)]) -> (Module, Vec<FuncId>) {
    use trust_ir::value::GlobalId;
    use trust_ir::{Global, Linkage};
    let mut mb = ModuleBuilder::new("w5b_borrow_liveness");
    mb.add_global(Global {
        name: "G".into(),
        ty: Ty::I32,
        mutable: true,
        initializer: None,
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let take_ty = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let take = {
        let mut fb = mb.function("take", take_ty);
        let entry = fb.create_block();
        let p = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        let _ = fb.borrow(p);
        fb.ret(vec![]);
        fb.build()
    };
    let mut ids = Vec::new();
    for (i, (cell, _)) in cells.iter().enumerate() {
        use LivenessCell as C;
        let mut fb = mb.function(format!("live{i}_{cell:?}"), ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let region = match cell {
            C::SharedLive(r) | C::UniqueLive(r) | C::SharedEnded(r) | C::UniqueEnded(r) => *r,
            C::BorrowedInCallee => RUST_HEAP,
            _ => Region::Stack,
        };
        let p = match cell {
            C::GlobalLive | C::GlobalNoBorrow => fb.global_addr(GlobalId::new(0)),
            C::InteriorLive => fb.alloca(Ty::I64),
            _ => match region {
                Region::Heap(origin) => fb.heap_alloc(Ty::I32, None, None, origin),
                Region::Stack => fb.alloca(Ty::I32),
            },
        };
        let seven = fb.iconst(Ty::I32, 7);
        fb.store(Ty::I32, p, seven);
        let v = fb.load(Ty::I32, p);
        match cell {
            C::SharedLive(_) | C::GlobalLive => {
                let _ = fb.borrow(p);
            }
            C::UniqueLive(_) => {
                let _ = fb.borrow_mut(p);
            }
            C::SharedEnded(_) => {
                let b = fb.borrow(p);
                fb.end_borrow(b);
            }
            C::UniqueEnded(_) => {
                let m = fb.borrow_mut(p);
                fb.end_borrow(m);
            }
            C::InteriorLive => {
                let one = fb.iconst(Ty::U64, 1);
                let q = fb.gep(Ty::I32, p, vec![one]);
                let _ = fb.borrow(q);
            }
            C::OneOfTwoEnded => {
                let b = fb.borrow(p);
                let _ = fb.borrow(p);
                fb.end_borrow(b);
            }
            C::BothEnded => {
                let b = fb.borrow(p);
                let c = fb.borrow(p);
                fb.end_borrow(c);
                fb.end_borrow(b);
            }
            C::EndedThenBorrowedAgain => {
                let b = fb.borrow(p);
                fb.end_borrow(b);
                let _ = fb.borrow_mut(p);
            }
            C::ReborrowChainEnded => {
                let b = fb.borrow(p);
                let c = fb.borrow(b);
                fb.end_borrow(c);
                fb.end_borrow(b);
            }
            C::BorrowedInCallee => fb.call_void(take, vec![p]),
            C::EscapedThenEnded => {
                let slot = fb.alloca(Ty::Ptr);
                let b = fb.borrow(p);
                fb.store(Ty::Ptr, slot, b);
                fb.end_borrow(b);
            }
            C::GlobalNoBorrow => {}
        }
        fb.dealloc(p);
        fb.ret(vec![v]);
        ids.push(fb.build());
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errs = trust_ir_build::validate_module(&module);
    assert!(
        errs.is_empty(),
        "every liveness cell is well-formed (the rule is dynamic): {errs:?}"
    );
    (module, ids)
}

/// Both engines run the decided borrow-liveness cells, and every cell must
/// AGREE and have its expected verdict class (SPEC "Freeing an allocation
/// under a live borrow is undefined behaviour"). The interpreter half runs
/// without `lake`, and a `ub` cell must name the rule. Measured when the rule
/// landed: with the interpreter's count check deleted, every `ub` cell runs to
/// `Ok(7)` in the interpreter while Lean refuses it.
#[test]
fn borrow_liveness_at_dealloc_agrees_across_engines() {
    let (module, ids) = liveness_module(DECIDED_LIVENESS_CELLS);
    for ((cell, class), f) in DECIDED_LIVENESS_CELLS.iter().zip(&ids) {
        let rust = canonical_verdict(run_rust(&module, *f, &[]));
        assert_eq!(rust.class(), *class, "interpreter, {cell:?}: {rust:?}");
        match &rust {
            Verdict::Graph(_) => assert_eq!(rust, i32_verdict(7), "{cell:?}"),
            Verdict::Ub(message) => assert!(
                message.contains("under a live borrow"),
                "{cell:?}: the refusal must name the rule, got: {message}"
            ),
            _ => {}
        }
    }

    let Oracle::Ready(exe) = oracle() else { return };
    let batches = vec![Batch {
        label: "borrow liveness at Dealloc (decided)".into(),
        module: &module,
        runs: ids.iter().map(|f| (*f, vec![])).collect(),
    }];
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), DECIDED_LIVENESS_CELLS.len());
    for ((cell, class), r) in DECIDED_LIVENESS_CELLS.iter().zip(&reports) {
        assert_eq!(
            r.comparison,
            Comparison::Agree,
            "{cell:?}: the engines must agree (rust {:?}; lean {:?})",
            r.rust,
            r.lean
        );
        assert_eq!(
            r.lean.class(),
            *class,
            "{cell:?}: expected verdict class {class} (rust {:?}; lean {:?})",
            r.rust,
            r.lean
        );
    }
}

/// A borrow-operand shape. The first six rows are the shapes the liveness
/// rule above leaves UNDECIDED (the ledger [`BORROW_CELLS`]); they store 7
/// into their allocation and return what they load back. The two controls
/// after them do the same. Every row from `OnePastEndLone` on is DECIDED by
/// SPEC "A pointer operand names the allocation it was derived from" with
/// clause 2 of "Freeing an allocation under a live borrow is undefined
/// behaviour" ([`DECIDED_BORROW_OPERAND_CELLS`]); the provenance rows from
/// `PastEndBorrowFreesNeighbour` on touch no byte and return 7.
#[derive(Clone, Copy, Debug)]
enum BorrowCell {
    /// `p = CleanHeap i32`; `b = Borrow p`; `v = load b`; `EndBorrow b`;
    /// `Release p`. Undecided.
    BorrowOfRcCell,
    /// `p = CleanHeap i32`; `m = BorrowMut p`; `v = load m`; `EndBorrow m`;
    /// `Release p`. Undecided.
    BorrowMutOfRcCell,
    /// `b = Borrow p`; `EndBorrow b`; `EndBorrow b`: an `EndBorrow` with no
    /// live borrow. Lean: UB at the second `EndBorrow`; the interpreter's
    /// count stays at 0.
    EndBorrowWithNoLiveBorrow,
    /// `m = BorrowMut p`; `n = BorrowMut p`: two `&mut` of one place, the
    /// first never ended. Lean: UB at the second `BorrowMut`.
    SecondBorrowMut,
    /// `m = BorrowMut p`; `b = Borrow p`: the MIR bridge's spelling of
    /// `s.bump(); s.get()` (it emits no `EndBorrow`). Lean: UB at `Borrow`.
    BorrowAfterUnendedBorrowMut,
    /// `m = BorrowMut p`; `b = Borrow m`: a shared reborrow of a `&mut`.
    /// Lean: UB at `Borrow`.
    SharedReborrowOfBorrowMut,
    /// Control: `p = Alloca i32`; `b = Borrow p`; `v = load b`;
    /// `EndBorrow b`; `Dealloc p`.
    BorrowEndDeallocControl,
    /// Control: `p = RustHeap i32`; `m = BorrowMut p`; `v = load m`;
    /// `EndBorrow m`; `Dealloc p`.
    BorrowMutEndDeallocControl,
    /// `p = Alloca i32`; `Borrow (gep i32 p [1])`; `Dealloc p`: an operand one
    /// past the end moves nothing.
    OnePastEndLone,
    /// As `OnePastEndLone` with a second `Alloca i32` after `p`, placed at
    /// the operand's address.
    OnePastEndNeighbour,
    /// `p = RustHeap i32`; `Borrow (gep i32 p [1])`; `Dealloc p`: an operand
    /// in the heap slack tail moves nothing.
    HeapSlackLone,
    /// As `HeapSlackLone` with an `Alloca i32` after `p`.
    HeapSlackNeighbour,
    /// `p = Alloca ()`; `Borrow p`; `Dealloc p`: a zero-size allocation's
    /// operand moves nothing.
    ZeroSizeBorrow,
    /// Family (a): `a`, `b` = `Alloca i32`; `Borrow (gep i32 a [1])`;
    /// `Dealloc b`. The borrow names `a` (one past its end) and moves
    /// nothing, so `b`'s free runs.
    PastEndBorrowFreesNeighbour,
    /// Family (a) over two `RustHeap i32` cells (the heap slack tail).
    HeapSlackBorrowFreesNeighbour,
    /// Family (b): `a`, `b` = `Alloca i32`; `bb = Borrow b`;
    /// `pp = Borrow (gep i32 a [1])`; `EndBorrow pp` twice; `Dealloc b`.
    /// Neither end names `b`, whose borrow stays live: the free is UB.
    PastEndEndedTwiceNeighbourLive,
    /// Family (b) over two `RustHeap i32` cells (the heap slack tail).
    HeapSlackEndedTwiceNeighbourLive,
    /// Family (b) with `a = Alloca i8`, `b = Alloca i32` and the operand
    /// `gep i8 a [1]`.
    NarrowPastEndEndedTwiceNeighbourLive,
    /// Family (b) through a zero-size slot: `z = Alloca ()`; `b = Alloca i32`;
    /// `bb = Borrow b`; `zz = Borrow z`; `EndBorrow zz` twice; `Dealloc b`.
    ZeroSizeEndedTwiceNeighbourLive,
    /// Family (c), a borrow through an integer: `a = Alloca i8`; `b`, `c` =
    /// `Alloca i32`; `q = IntToPtr(PtrToInt(a) + 5)`; `Borrow q`; `Dealloc b`.
    /// The one reference placement aligns `b` to 4, so `q` lands in `b` and
    /// borrows it: the free is UB.
    IntToPtrAcrossLayouts,
    /// Family (d), `Dealloc` of a zero-size slot: `z = Alloca ()`;
    /// `b = Alloca i32`; `Borrow b`; `Dealloc z`. The free names `z`, which
    /// has no borrow, and runs.
    ZeroSizeFreeNamesBorrowedNeighbour,
    /// `z = Alloca ()`; `b = Alloca i32`; `bb = Borrow b`; `zz = Borrow z`;
    /// `EndBorrow zz`; `EndBorrow bb`; `Dealloc b`.
    ZeroSizeEndedOnce,
    /// `z = Alloca ()`; `b = Alloca i32`; `zz = Borrow z`; `EndBorrow zz`;
    /// `bb = Borrow b`; `Dealloc b`.
    ZeroSizeEndedThenLiveBorrow,
    /// As `IntToPtrAcrossLayouts` with `q = IntToPtr(PtrToInt(b))`.
    IntToPtrSameAllocation,
    /// Probe p08: `a`, `b` = `Alloca i32`; `slot = Alloca ptr`;
    /// `store (gep i32 a [1]) -> slot`; `q = load slot`; `Borrow q`;
    /// `Dealloc b`. A pointer decoded from bytes recovers its provenance by
    /// address — `b`, whose base it is — so the borrow is `b`'s.
    StoredOnePastEndReloadedBorrow,
    /// Probe p14: `a`, `b` = `Alloca i32`; `Dealloc (gep i32 a [1])`: the
    /// operand names `a` at an offset other than its base — UB, never a free
    /// of `b`.
    DeallocOnePastEndNamesNeighbour,
    /// Probe p15: `a`, `b` = `Alloca i32`;
    /// `Dealloc (IntToPtr(PtrToInt(b)))`: the round trip recovers `b`, at its
    /// base, and frees it.
    DeallocIntToPtrOfNeighbourBase,
    /// Probe p17: `p = Alloca i64`; `Dealloc (gep i32 p [1])`: an interior
    /// free is UB.
    DeallocInterior,
    /// Cell c05: `p = Alloca i32`; `f = PtrFromParts fatptr<str> (p, 3)`;
    /// `Borrow f`: a fat pointer passes through a borrow and moves nothing.
    BorrowOfFatPointer,
    /// Cell c10: `p = Alloca i32`; `i = PtrToInt p`; `Dealloc p`;
    /// `Borrow (IntToPtr i)`: the address recovers the FREED slot, and a
    /// borrow of a freed allocation moves nothing.
    BorrowThroughIntToPtrOfFreedSlot,
    /// `p = Alloca i64`; `a = gep i32 p [0]`; `b = gep i32 p [1]`; store 7 at
    /// `a`; `m = BorrowMut a`; `n = BorrowMut b`; `v = load m`; `EndBorrow m`;
    /// `EndBorrow n`: Rust's disjoint field borrows `&mut p.a`, `&mut p.b`,
    /// both ended at their NLL ends. Lean: UB at the second `BorrowMut` (one
    /// allocation, already `uniqueBorrow`). No `EndBorrow` placement helps:
    /// both borrows are live at once in the source (SPEC "A Rust reference
    /// carries no permission instruction").
    DisjointInteriorBorrowMutsEnded,
    /// `p = Alloca i32`; store 7; `m = BorrowMut p`; `v = call get_shared(m)`,
    /// whose body is `b = Borrow param; v = load b; EndBorrow b; ret v`;
    /// `EndBorrow m`: a callee's `&*s` reborrow of the caller's live `&mut`,
    /// every borrow ended. Lean: UB at the callee's `Borrow`. The caller's
    /// `&mut` is live across the call, so no placement helps.
    CalleeReborrowUnderCallersBorrowMut,
}

/// The SHRINK-ONLY ledger of borrow shapes no rule decides, as measured.
/// Lean gates `Borrow` / `BorrowMut` / `EndBorrow` on the allocation's
/// permission; the interpreter never faults at a borrow instruction.
///
/// * `Borrow` / `BorrowMut` of a reference-counted cell is undecided (SPEC "A
///   reference-counted cell is released by `Release`, never by `Dealloc`").
/// * The aliasing and `EndBorrow` rows are `TRUST.md` item 12's producer
///   obligations, which the MIR bridge's output already breaks (it emits no
///   `EndBorrow`): clause 4 of SPEC "Freeing an allocation under a live
///   borrow is undefined behaviour".
///
/// * The last two rows are Rust shapes no `EndBorrow` placement repairs
///   (disjoint field `&mut`s, a callee's reborrow under the caller's `&mut`):
///   their borrows are live at once in the source, which is why a Rust
///   producer emits no permission instruction (SPEC "A Rust reference
///   carries no permission instruction").
///
/// The two controls agree. The address-versus-provenance families of that
/// section's clause 2, which this ledger held until Lean gained pointer
/// provenance, are decided: [`DECIDED_BORROW_OPERAND_CELLS`].
const BORROW_CELLS: &[(BorrowCell, Measured, Measured)] = &[
    (
        BorrowCell::BorrowOfRcCell,
        Measured::Ok(7),
        Measured::Ub("Borrow: invalid permission state"),
    ),
    (
        BorrowCell::BorrowMutOfRcCell,
        Measured::Ok(7),
        Measured::Ub("BorrowMut: expected owned permission"),
    ),
    (
        BorrowCell::EndBorrowWithNoLiveBorrow,
        Measured::Ok(7),
        Measured::Ub("EndBorrow: invalid permission state"),
    ),
    (
        BorrowCell::SecondBorrowMut,
        Measured::Ok(7),
        Measured::Ub("BorrowMut: expected owned permission"),
    ),
    (
        BorrowCell::BorrowAfterUnendedBorrowMut,
        Measured::Ok(7),
        Measured::Ub("Borrow: invalid permission state"),
    ),
    (
        BorrowCell::SharedReborrowOfBorrowMut,
        Measured::Ok(7),
        Measured::Ub("Borrow: invalid permission state"),
    ),
    (
        BorrowCell::BorrowEndDeallocControl,
        Measured::Ok(7),
        Measured::Ok(7),
    ),
    (
        BorrowCell::BorrowMutEndDeallocControl,
        Measured::Ok(7),
        Measured::Ok(7),
    ),
    (
        BorrowCell::DisjointInteriorBorrowMutsEnded,
        Measured::Ok(7),
        Measured::Ub("BorrowMut: expected owned permission"),
    ),
    (
        BorrowCell::CalleeReborrowUnderCallersBorrowMut,
        Measured::Ok(7),
        Measured::Ub("Borrow: invalid permission state"),
    ),
];

/// The DECIDED borrow- and `Dealloc`-operand cells (SPEC "A pointer operand
/// names the allocation it was derived from", with clause 2 of "Freeing an
/// allocation under a live borrow is undefined behaviour") and the verdict
/// BOTH engines must give. A thin borrow operand moves the live-borrow state
/// of the allocation it was derived from, and only inside the bytes that live
/// allocation requested; a `Dealloc` operand frees the allocation it was
/// derived from, and only at its base; an address made from an integer or
/// decoded from bytes recovers the allocation of the one reference
/// placement. These are the sixteen clause-2 rows the ledger held (families
/// (a) to (d) and their controls), probes p08, p14, p15 and p17, and cells
/// c05 and c10 of the challenge of the Lean-provenance design.
const DECIDED_BORROW_OPERAND_CELLS: &[(BorrowCell, Expect)] = &[
    (BorrowCell::OnePastEndLone, Expect::I32(7)),
    (BorrowCell::OnePastEndNeighbour, Expect::I32(7)),
    (BorrowCell::HeapSlackLone, Expect::I32(7)),
    (BorrowCell::HeapSlackNeighbour, Expect::I32(7)),
    (BorrowCell::ZeroSizeBorrow, Expect::I32(7)),
    (BorrowCell::PastEndBorrowFreesNeighbour, Expect::I32(7)),
    (BorrowCell::HeapSlackBorrowFreesNeighbour, Expect::I32(7)),
    (
        BorrowCell::PastEndEndedTwiceNeighbourLive,
        Expect::Ub("under a live borrow"),
    ),
    (
        BorrowCell::HeapSlackEndedTwiceNeighbourLive,
        Expect::Ub("under a live borrow"),
    ),
    (
        BorrowCell::NarrowPastEndEndedTwiceNeighbourLive,
        Expect::Ub("under a live borrow"),
    ),
    (
        BorrowCell::ZeroSizeEndedTwiceNeighbourLive,
        Expect::Ub("under a live borrow"),
    ),
    (
        BorrowCell::IntToPtrAcrossLayouts,
        Expect::Ub("under a live borrow"),
    ),
    (
        BorrowCell::ZeroSizeFreeNamesBorrowedNeighbour,
        Expect::I32(7),
    ),
    (BorrowCell::ZeroSizeEndedOnce, Expect::I32(7)),
    (
        BorrowCell::ZeroSizeEndedThenLiveBorrow,
        Expect::Ub("under a live borrow"),
    ),
    (
        BorrowCell::IntToPtrSameAllocation,
        Expect::Ub("under a live borrow"),
    ),
    (
        BorrowCell::StoredOnePastEndReloadedBorrow,
        Expect::Ub("under a live borrow"),
    ),
    (
        BorrowCell::DeallocOnePastEndNamesNeighbour,
        Expect::Ub("must reference allocation base"),
    ),
    (BorrowCell::DeallocIntToPtrOfNeighbourBase, Expect::I32(7)),
    (
        BorrowCell::DeallocInterior,
        Expect::Ub("must reference allocation base"),
    ),
    (BorrowCell::BorrowOfFatPointer, Expect::I32(7)),
    (BorrowCell::BorrowThroughIntToPtrOfFreedSlot, Expect::I32(7)),
];

/// Emit one provenance cell (`PastEndBorrowFreesNeighbour` on): the
/// allocations, the borrows and the free, and nothing else. Returns `false`
/// for a cell this builder does not own.
fn emit_crossing_cell(fb: &mut trust_ir_build::FunctionBuilder<'_>, cell: BorrowCell) -> bool {
    use BorrowCell as C;
    use trust_ir::inst::CastOp;
    match cell {
        C::PastEndBorrowFreesNeighbour | C::HeapSlackBorrowFreesNeighbour => {
            let (a, b) = if let C::PastEndBorrowFreesNeighbour = cell {
                (fb.alloca(Ty::I32), fb.alloca(Ty::I32))
            } else {
                (
                    fb.heap_alloc(Ty::I32, None, None, AllocOrigin::RustHeap),
                    fb.heap_alloc(Ty::I32, None, None, AllocOrigin::RustHeap),
                )
            };
            let one = fb.iconst(Ty::U64, 1);
            let past = fb.gep(Ty::I32, a, vec![one]);
            let _ = fb.borrow(past);
            fb.dealloc(b);
        }
        C::PastEndEndedTwiceNeighbourLive
        | C::HeapSlackEndedTwiceNeighbourLive
        | C::NarrowPastEndEndedTwiceNeighbourLive => {
            let (a, b, step) = match cell {
                C::HeapSlackEndedTwiceNeighbourLive => (
                    fb.heap_alloc(Ty::I32, None, None, AllocOrigin::RustHeap),
                    fb.heap_alloc(Ty::I32, None, None, AllocOrigin::RustHeap),
                    Ty::I32,
                ),
                C::NarrowPastEndEndedTwiceNeighbourLive => {
                    (fb.alloca(Ty::I8), fb.alloca(Ty::I32), Ty::I8)
                }
                _ => (fb.alloca(Ty::I32), fb.alloca(Ty::I32), Ty::I32),
            };
            let _ = fb.borrow(b);
            let one = fb.iconst(Ty::U64, 1);
            let past = fb.gep(step, a, vec![one]);
            let pp = fb.borrow(past);
            fb.end_borrow(pp);
            fb.end_borrow(pp);
            fb.dealloc(b);
        }
        C::ZeroSizeEndedTwiceNeighbourLive | C::ZeroSizeEndedOnce => {
            let z = fb.alloca(Ty::Unit);
            let b = fb.alloca(Ty::I32);
            let bb = fb.borrow(b);
            let zz = fb.borrow(z);
            fb.end_borrow(zz);
            if let C::ZeroSizeEndedTwiceNeighbourLive = cell {
                fb.end_borrow(zz);
            } else {
                fb.end_borrow(bb);
            }
            fb.dealloc(b);
        }
        C::ZeroSizeEndedThenLiveBorrow => {
            let z = fb.alloca(Ty::Unit);
            let b = fb.alloca(Ty::I32);
            let zz = fb.borrow(z);
            fb.end_borrow(zz);
            let _ = fb.borrow(b);
            fb.dealloc(b);
        }
        C::ZeroSizeFreeNamesBorrowedNeighbour => {
            let z = fb.alloca(Ty::Unit);
            let b = fb.alloca(Ty::I32);
            let _ = fb.borrow(b);
            fb.dealloc(z);
        }
        C::IntToPtrAcrossLayouts | C::IntToPtrSameAllocation => {
            let a = fb.alloca(Ty::I8);
            let b = fb.alloca(Ty::I32);
            let _c = fb.alloca(Ty::I32);
            let address = if let C::IntToPtrAcrossLayouts = cell {
                let a_int = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, a);
                let five = fb.iconst(Ty::U64, 5);
                fb.add(Ty::U64, a_int, five)
            } else {
                fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, b)
            };
            let q = fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, address);
            let _ = fb.borrow(q);
            fb.dealloc(b);
        }
        C::StoredOnePastEndReloadedBorrow => {
            let a = fb.alloca(Ty::I32);
            let b = fb.alloca(Ty::I32);
            let slot = fb.alloca(Ty::Ptr);
            let one = fb.iconst(Ty::U64, 1);
            let past = fb.gep(Ty::I32, a, vec![one]);
            fb.store(Ty::Ptr, slot, past);
            let q = fb.load(Ty::Ptr, slot);
            let _ = fb.borrow(q);
            fb.dealloc(b);
        }
        C::DeallocOnePastEndNamesNeighbour => {
            let a = fb.alloca(Ty::I32);
            let _b = fb.alloca(Ty::I32);
            let one = fb.iconst(Ty::U64, 1);
            let past = fb.gep(Ty::I32, a, vec![one]);
            fb.dealloc(past);
        }
        C::DeallocIntToPtrOfNeighbourBase => {
            let _a = fb.alloca(Ty::I32);
            let b = fb.alloca(Ty::I32);
            let b_int = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, b);
            let q = fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, b_int);
            fb.dealloc(q);
        }
        C::DeallocInterior => {
            let p = fb.alloca(Ty::I64);
            let one = fb.iconst(Ty::U64, 1);
            let interior = fb.gep(Ty::I32, p, vec![one]);
            fb.dealloc(interior);
        }
        C::BorrowOfFatPointer => {
            use trust_ir::ty::FatPtrKind;
            let p = fb.alloca(Ty::I32);
            let three = fb.iconst(Ty::U64, 3);
            let fat = fb.ptr_from_parts(Ty::FatPtr(FatPtrKind::Str), Ty::U64, p, three);
            let _ = fb.borrow(fat);
        }
        C::BorrowThroughIntToPtrOfFreedSlot => {
            let p = fb.alloca(Ty::I32);
            let p_int = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, p);
            fb.dealloc(p);
            let q = fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, p_int);
            let _ = fb.borrow(q);
        }
        _ => return false,
    }
    true
}

fn borrow_module(cells: &[BorrowCell]) -> (Module, Vec<FuncId>) {
    let mut mb = ModuleBuilder::new("w5b_borrow_permission");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    // `CalleeReborrowUnderCallersBorrowMut`'s callee: `&*s`, ended.
    let get_ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);
    let get_shared = {
        let mut fb = mb.function("get_shared", get_ty);
        let entry = fb.create_block();
        let s = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        let b = fb.borrow(s);
        let v = fb.load(Ty::I32, b);
        fb.end_borrow(b);
        fb.ret(vec![v]);
        fb.build()
    };
    let mut ids = Vec::new();
    for (i, cell) in cells.iter().enumerate() {
        use BorrowCell as C;
        let mut fb = mb.function(format!("borrow{i}_{cell:?}"), ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let seven = fb.iconst(Ty::I32, 7);
        if emit_crossing_cell(&mut fb, *cell) {
            fb.ret(vec![seven]);
            ids.push(fb.build());
            continue;
        }
        if let C::ZeroSizeBorrow = cell {
            let p = fb.alloca(Ty::Unit);
            let _ = fb.borrow(p);
            fb.dealloc(p);
            fb.ret(vec![seven]);
            ids.push(fb.build());
            continue;
        }
        if let C::DisjointInteriorBorrowMutsEnded = cell {
            let p = fb.alloca(Ty::I64);
            let zero = fb.iconst(Ty::U64, 0);
            let one = fb.iconst(Ty::U64, 1);
            let a = fb.gep(Ty::I32, p, vec![zero]);
            let b = fb.gep(Ty::I32, p, vec![one]);
            fb.store(Ty::I32, a, seven);
            let m = fb.borrow_mut(a);
            let n = fb.borrow_mut(b);
            let v = fb.load(Ty::I32, m);
            fb.end_borrow(m);
            fb.end_borrow(n);
            fb.ret(vec![v]);
            ids.push(fb.build());
            continue;
        }
        if let C::CalleeReborrowUnderCallersBorrowMut = cell {
            let p = fb.alloca(Ty::I32);
            fb.store(Ty::I32, p, seven);
            let m = fb.borrow_mut(p);
            let v = fb.call(get_shared, vec![m]);
            fb.end_borrow(m);
            fb.ret(vec![v]);
            ids.push(fb.build());
            continue;
        }
        let p = match cell {
            C::BorrowOfRcCell | C::BorrowMutOfRcCell => {
                fb.heap_alloc(Ty::I32, None, None, AllocOrigin::CleanHeap)
            }
            C::BorrowMutEndDeallocControl | C::HeapSlackLone | C::HeapSlackNeighbour => {
                fb.heap_alloc(Ty::I32, None, None, AllocOrigin::RustHeap)
            }
            _ => fb.alloca(Ty::I32),
        };
        if let C::OnePastEndNeighbour | C::HeapSlackNeighbour = cell {
            let _ = fb.alloca(Ty::I32);
        }
        fb.store(Ty::I32, p, seven);
        let v = match cell {
            C::BorrowOfRcCell | C::BorrowMutOfRcCell => {
                let b = if let C::BorrowOfRcCell = cell {
                    fb.borrow(p)
                } else {
                    fb.borrow_mut(p)
                };
                let v = fb.load(Ty::I32, b);
                fb.end_borrow(b);
                fb.release(p);
                v
            }
            C::EndBorrowWithNoLiveBorrow => {
                let b = fb.borrow(p);
                let v = fb.load(Ty::I32, b);
                fb.end_borrow(b);
                fb.end_borrow(b);
                v
            }
            C::SecondBorrowMut => {
                let _ = fb.borrow_mut(p);
                let n = fb.borrow_mut(p);
                fb.load(Ty::I32, n)
            }
            C::BorrowAfterUnendedBorrowMut => {
                let _ = fb.borrow_mut(p);
                let b = fb.borrow(p);
                fb.load(Ty::I32, b)
            }
            C::SharedReborrowOfBorrowMut => {
                let m = fb.borrow_mut(p);
                let b = fb.borrow(m);
                fb.load(Ty::I32, b)
            }
            C::OnePastEndLone
            | C::OnePastEndNeighbour
            | C::HeapSlackLone
            | C::HeapSlackNeighbour => {
                let one = fb.iconst(Ty::U64, 1);
                let q = fb.gep(Ty::I32, p, vec![one]);
                let _ = fb.borrow(q);
                let v = fb.load(Ty::I32, p);
                fb.dealloc(p);
                v
            }
            C::BorrowEndDeallocControl | C::BorrowMutEndDeallocControl => {
                let b = if let C::BorrowEndDeallocControl = cell {
                    fb.borrow(p)
                } else {
                    fb.borrow_mut(p)
                };
                let v = fb.load(Ty::I32, b);
                fb.end_borrow(b);
                fb.dealloc(p);
                v
            }
            C::ZeroSizeBorrow
            | C::PastEndBorrowFreesNeighbour
            | C::HeapSlackBorrowFreesNeighbour
            | C::PastEndEndedTwiceNeighbourLive
            | C::HeapSlackEndedTwiceNeighbourLive
            | C::NarrowPastEndEndedTwiceNeighbourLive
            | C::ZeroSizeEndedTwiceNeighbourLive
            | C::IntToPtrAcrossLayouts
            | C::ZeroSizeFreeNamesBorrowedNeighbour
            | C::ZeroSizeEndedOnce
            | C::ZeroSizeEndedThenLiveBorrow
            | C::IntToPtrSameAllocation
            | C::StoredOnePastEndReloadedBorrow
            | C::DeallocOnePastEndNamesNeighbour
            | C::DeallocIntToPtrOfNeighbourBase
            | C::DeallocInterior
            | C::BorrowOfFatPointer
            | C::BorrowThroughIntToPtrOfFreedSlot
            | C::DisjointInteriorBorrowMutsEnded
            | C::CalleeReborrowUnderCallersBorrowMut => unreachable!("built above"),
        };
        fb.ret(vec![v]);
        ids.push(fb.build());
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errs = trust_ir_build::validate_module(&module);
    assert!(
        errs.is_empty(),
        "every borrow cell is well-formed (the rule is dynamic): {errs:?}"
    );
    (module, ids)
}

/// The borrow shapes no rule decides, pinned rather than asserted: each
/// ledgered cell must still diverge exactly as measured, in either
/// direction, and the two controls must still agree. A cell leaves the
/// ledger only by a decision both engines implement.
#[test]
fn borrow_permission_divergences_stay_as_measured() {
    let cells: Vec<BorrowCell> = BORROW_CELLS.iter().map(|(c, _, _)| *c).collect();
    let (module, ids) = borrow_module(&cells);
    hold_divergence_ledger("borrow permission", &module, &ids, BORROW_CELLS);
}

/// The Rust shapes of SPEC "A Rust reference carries no permission
/// instruction", each reference spelled as the Rust producers spell it (a
/// `Copy` of the address at `Ptr`, no `EndBorrow`): the measured probe shapes
/// `p01` (`s.bump(); s.get()`), `p03` (disjoint field `&mut`s), `p02` (a
/// callee's `&*s` and `&mut *s` under the caller's `&mut`), `p09` (two-phase
/// `v.push(v.len())`) and a heap cell read through a reference and then freed.
/// Spelled with the permission instructions, the first five fault in Lean and
/// the sixth is UB in both (the ledger above holds the two placement-proof
/// rows); spelled as `Copy` they are DECIDED cells, `(name, value)`, which both
/// engines run to the same value.
const RUST_REFERENCE_CELLS: &[(&str, i32)] = &[
    ("p01_copy", 1),
    ("p03_disjoint_copy", 6),
    ("p02_nested_shared_copy", 5),
    ("heap_copy_free", 7),
    ("p02_nested_mut_copy", 6),
    ("p09_two_phase_copy", 4),
];

fn rust_reference_module() -> (Module, Vec<FuncId>) {
    let mut mb = ModuleBuilder::new("rust_reference_spelling");
    let bump_ty = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let get_ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let bump = {
        let mut fb = mb.function("bump", bump_ty);
        let entry = fb.create_block();
        let p = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        let v = fb.load(Ty::I32, p);
        let one = fb.iconst(Ty::I32, 1);
        let w = fb.add(Ty::I32, v, one);
        fb.store(Ty::I32, p, w);
        fb.ret(vec![]);
        fb.build()
    };
    let get = {
        let mut fb = mb.function("get", get_ty);
        let entry = fb.create_block();
        let p = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        let v = fb.load(Ty::I32, p);
        fb.ret(vec![v]);
        fb.build()
    };
    let reborrow_get = {
        let mut fb = mb.function("reborrow_get_copy", get_ty);
        let entry = fb.create_block();
        let s = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        let r = fb.copy(Ty::Ptr, s);
        let v = fb.call(get, vec![r]);
        fb.ret(vec![v]);
        fb.build()
    };
    let reborrow_bump = {
        let mut fb = mb.function("reborrow_bump_copy", get_ty);
        let entry = fb.create_block();
        let s = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        let r = fb.copy(Ty::Ptr, s);
        fb.call_void(bump, vec![r]);
        let zero = fb.iconst(Ty::I32, 0);
        fb.ret(vec![zero]);
        fb.build()
    };
    let mut ids = Vec::new();
    for (name, _) in RUST_REFERENCE_CELLS {
        let mut fb = mb.function(*name, ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let out = match *name {
            "p01_copy" => {
                let x = fb.alloca(Ty::I32);
                let zero = fb.iconst(Ty::I32, 0);
                fb.store(Ty::I32, x, zero);
                let m = fb.copy(Ty::Ptr, x);
                fb.call_void(bump, vec![m]);
                let s = fb.copy(Ty::Ptr, x);
                fb.call(get, vec![s])
            }
            "p03_disjoint_copy" => {
                let p = fb.alloca(Ty::I64);
                let zero = fb.iconst(Ty::U64, 0);
                let one = fb.iconst(Ty::U64, 1);
                let a = fb.gep(Ty::I32, p, vec![zero]);
                let b = fb.gep(Ty::I32, p, vec![one]);
                let c1 = fb.iconst(Ty::I32, 1);
                let c2 = fb.iconst(Ty::I32, 2);
                fb.store(Ty::I32, a, c1);
                fb.store(Ty::I32, b, c2);
                let x = fb.copy(Ty::Ptr, a);
                let y = fb.copy(Ty::Ptr, b);
                let xa = fb.load(Ty::I32, x);
                let yb = fb.load(Ty::I32, y);
                let sum = fb.add(Ty::I32, xa, yb);
                fb.store(Ty::I32, x, sum);
                let yb2 = fb.load(Ty::I32, y);
                let inc = fb.iconst(Ty::I32, 1);
                let y1 = fb.add(Ty::I32, yb2, inc);
                fb.store(Ty::I32, y, y1);
                let pa = fb.load(Ty::I32, a);
                let pb = fb.load(Ty::I32, b);
                fb.add(Ty::I32, pa, pb)
            }
            "p02_nested_shared_copy" => {
                let x = fb.alloca(Ty::I32);
                let five = fb.iconst(Ty::I32, 5);
                fb.store(Ty::I32, x, five);
                let m = fb.copy(Ty::Ptr, x);
                fb.call(reborrow_get, vec![m])
            }
            "heap_copy_free" => {
                let h = fb.heap_alloc(Ty::I32, None, None, AllocOrigin::RustHeap);
                let seven = fb.iconst(Ty::I32, 7);
                fb.store(Ty::I32, h, seven);
                let r = fb.copy(Ty::Ptr, h);
                let v = fb.load(Ty::I32, r);
                fb.dealloc(h);
                v
            }
            "p02_nested_mut_copy" => {
                let x = fb.alloca(Ty::I32);
                let five = fb.iconst(Ty::I32, 5);
                fb.store(Ty::I32, x, five);
                let m = fb.copy(Ty::Ptr, x);
                let _ = fb.call(reborrow_bump, vec![m]);
                fb.load(Ty::I32, x)
            }
            "p09_two_phase_copy" => {
                let v = fb.alloca(Ty::I32);
                let three = fb.iconst(Ty::I32, 3);
                fb.store(Ty::I32, v, three);
                let m = fb.copy(Ty::Ptr, v);
                let s = fb.copy(Ty::Ptr, v);
                let _len = fb.call(get, vec![s]);
                fb.call_void(bump, vec![m]);
                fb.load(Ty::I32, v)
            }
            other => unreachable!("no builder for {other}"),
        };
        fb.ret(vec![out]);
        ids.push(fb.build());
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errs = trust_ir_build::validate_module(&module);
    assert!(
        errs.is_empty(),
        "every Rust-reference cell is well-formed: {errs:?}"
    );
    assert!(
        module
            .functions
            .iter()
            .flat_map(|f| f.blocks.iter().flat_map(|b| b.body.iter()))
            .all(|node| !node.inst.uses_borrow_permissions()),
        "the cells carry no permission instruction"
    );
    (module, ids)
}

/// Both engines run the Copy-spelled Rust shapes to the same value
/// (`RUST_REFERENCE_CELLS`). The interpreter half runs without `lake`. Respell
/// any `copy` as a `borrow`/`borrow_mut` and Lean faults: the cell mismatches.
#[test]
fn rust_reference_spelling_agrees_across_engines() {
    let (module, ids) = rust_reference_module();
    for ((name, value), f) in RUST_REFERENCE_CELLS.iter().zip(&ids) {
        let rust = canonical_verdict(run_rust(&module, *f, &[]));
        assert_eq!(rust, i32_verdict(*value), "interpreter, {name}");
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches = vec![Batch {
        label: "Rust references spelled as Copy (decided)".into(),
        module: &module,
        runs: ids.iter().map(|f| (*f, vec![])).collect(),
    }];
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), RUST_REFERENCE_CELLS.len());
    for ((name, value), r) in RUST_REFERENCE_CELLS.iter().zip(&reports) {
        assert_eq!(
            r.comparison,
            Comparison::Agree,
            "{name}: the engines must agree (rust {:?}; lean {:?})",
            r.rust,
            r.lean
        );
        assert_eq!(r.lean, i32_verdict(*value), "{name}: lean");
    }
}

/// Both engines run the DECIDED borrow- and `Dealloc`-operand cells, and
/// every cell must AGREE and give its expected verdict (SPEC "A pointer
/// operand names the allocation it was derived from"; clause 2 of "Freeing
/// an allocation under a live borrow is undefined behaviour"). Measured
/// against the Lean model of trust-ir `e2154f00`, which resolved an operand
/// by address over a packed allocator: 14 of these 22 cells diverged (11 of
/// the 16 clause-2 rows, p14, c05 and c10); with Lean provenance every one
/// agrees.
#[test]
fn borrow_operand_provenance_agrees_across_engines() {
    let cells: Vec<BorrowCell> = DECIDED_BORROW_OPERAND_CELLS
        .iter()
        .map(|(c, _)| *c)
        .collect();
    let (module, ids) = borrow_module(&cells);
    check_decided(
        "borrow operand provenance",
        &module,
        &ids,
        DECIDED_BORROW_OPERAND_CELLS,
    );
}

// ---------------------------------------------------------------------------
// Access, placement and pointer values (SPEC "A pointer operand names the
// allocation it was derived from")
// ---------------------------------------------------------------------------

/// A cell of the access rule and of the reference placement. An access
/// checks the allocation the pointer was derived from (live, aligned — the
/// declared alignment, else the type's natural one — and in bounds); the
/// placement is the one the two reference models share. Each cell is one
/// function; the probe / cell names are those of the Lean-provenance design.
#[derive(Clone, Debug)]
enum LayoutCell {
    /// p02: `a`, `b` = `Alloca i32`; `store 7 -> b`;
    /// `ret load i32 (gep i32 a [1])`: out of `a`'s bounds, whatever is
    /// placed there.
    LoadOnePastEndIntoNeighbour,
    /// p03: `a`, `b` = `Alloca i32`; `store 7 -> gep i32 a [1]`;
    /// `ret load b`.
    StoreOnePastEndIntoNeighbour,
    /// p04: `Alloca i8`; `p = Alloca i32`; `store 7 -> p, align 4`;
    /// `ret load p, align 4`: the `i32` slot is 4-aligned.
    AlignedAccessAfterByteSlot,
    /// p06: `p = RustHeap i32`; `ret load u8 (gep i8 p [4])`: the first byte
    /// of the heap slack tail reads its defined fill.
    HeapSlackByte,
    /// p07: `z = Alloca ()`; `b = Alloca i32`;
    /// `ret ptrtoint z == ptrtoint b`: a zero-size slot is bumped one byte.
    ZeroSizeSlotSharesNoAddress,
    /// p11: `a`, `b` = `Alloca i32`; `c = Alloca i64`; `memcopy c <- a, 8`:
    /// out of `a`'s bounds.
    MemCopyAcrossBoundary,
    /// p13: `p = Alloca i32`; `store 7 -> p`; `Dealloc p`; `q = Alloca i32`;
    /// `store 7 -> q`; `ret load p`: a use after free, though `q` is live.
    LoadThroughFreedPointer,
    /// The 12 placement gap cells: `x = Alloca i8`, then a second allocation
    /// `y` (an `Alloca` of the type, or the stated shape);
    /// `ret ptrtoint y - ptrtoint x` (p05 is the `I32` gap).
    Gap(GapShape),
    /// c04: `a = Alloca i64`; `store 0`; `ret load i32 (gep i8 a [1])`: no
    /// declared alignment checks the natural one.
    LoadMisalignedNatural,
    /// c09: as c04 with `atomic_load seq_cst`.
    AtomicLoadMisaligned,
    /// c06: `a = Alloca i32`; `store 7`;
    /// `d = inttoptr (ptrtoint a - 4)`; `ret load i32 (gep i8 d [4])`: a GEP
    /// keeps a no-provenance pointer one.
    GepFromDanglingPointer,
    /// c14: `ret ptrtoint (Alloca i32)`: the first base.
    FirstBase,
    /// c15: `x = Alloca i8`; `y = RustHeap i8, align 64`;
    /// `ret ptrtoint y - ptrtoint x`: a declared heap alignment.
    HeapDeclaredAlign,
    /// c16: `x = Alloca i8`; `g = global_addr G64` (`align(64)`);
    /// `ret ptrtoint g - ptrtoint x`: a declared global alignment.
    GlobalDeclaredAlign,
}

/// The second allocation of a [`LayoutCell::Gap`] cell.
#[derive(Clone, Debug)]
enum GapShape {
    Alloca(Ty),
    /// Two `RustHeap i8` cells (the first replaces `x`).
    HeapPair,
    /// `global_addr G` (`G: i32`, no declared alignment).
    GlobalAfterByte,
    /// `Alloca i32, align 32`.
    DeclaredAlign,
}

/// The DECIDED access and placement cells and the verdict BOTH engines must
/// give. The access rule (UB cells) is SPEC "A pointer operand names the
/// allocation it was derived from"; the placement values are a property of
/// the two reference models, held equal here, not a format rule (no
/// consumer reproduces them). Measured against the Lean model of trust-ir
/// `e2154f00`, which placed allocations back to back with no alignment and no
/// heap slack and checked an access against any live allocation: 20 of these
/// 25 cells diverged — p02, p03, p04, p06 and p07, 10 of the 12 gap cells
/// (p05 is the `I32` one) and c04, c06, c09, c15 and c16; p11, p13, c14 and
/// the `Bool` and `Unit` gaps agreed (pins).
const LAYOUT_CELLS: &[(LayoutCell, Expect)] = &[
    (
        LayoutCell::LoadOnePastEndIntoNeighbour,
        Expect::Ub("out of bounds"),
    ),
    (
        LayoutCell::StoreOnePastEndIntoNeighbour,
        Expect::Ub("out of bounds"),
    ),
    (LayoutCell::AlignedAccessAfterByteSlot, Expect::I32(7)),
    (LayoutCell::HeapSlackByte, Expect::U8(255)),
    (LayoutCell::ZeroSizeSlotSharesNoAddress, Expect::Bool(false)),
    (
        LayoutCell::MemCopyAcrossBoundary,
        Expect::Ub("out of bounds"),
    ),
    (
        LayoutCell::LoadThroughFreedPointer,
        Expect::Ub("use after dealloc"),
    ),
    (LayoutCell::Gap(GapShape::Alloca(Ty::Bool)), Expect::I64(1)),
    (LayoutCell::Gap(GapShape::Alloca(Ty::I16)), Expect::I64(2)),
    (LayoutCell::Gap(GapShape::Alloca(Ty::I32)), Expect::I64(4)),
    (LayoutCell::Gap(GapShape::Alloca(Ty::I64)), Expect::I64(8)),
    (LayoutCell::Gap(GapShape::Alloca(Ty::I128)), Expect::I64(16)),
    (LayoutCell::Gap(GapShape::Alloca(Ty::F32)), Expect::I64(4)),
    (LayoutCell::Gap(GapShape::Alloca(Ty::F64)), Expect::I64(8)),
    (LayoutCell::Gap(GapShape::Alloca(Ty::Ptr)), Expect::I64(8)),
    (LayoutCell::Gap(GapShape::Alloca(Ty::Unit)), Expect::I64(1)),
    (LayoutCell::Gap(GapShape::HeapPair), Expect::I64(17)),
    (LayoutCell::Gap(GapShape::GlobalAfterByte), Expect::I64(16)),
    (LayoutCell::Gap(GapShape::DeclaredAlign), Expect::I64(32)),
    (
        LayoutCell::LoadMisalignedNatural,
        Expect::Ub("not aligned to 4"),
    ),
    (
        LayoutCell::AtomicLoadMisaligned,
        Expect::Ub("not aligned to 4"),
    ),
    (
        LayoutCell::GepFromDanglingPointer,
        Expect::Ub("no allocation provenance"),
    ),
    (LayoutCell::FirstBase, Expect::I64(1024)),
    (LayoutCell::HeapDeclaredAlign, Expect::I64(64)),
    (LayoutCell::GlobalDeclaredAlign, Expect::I64(64)),
];

/// `ret ptrtoint later - ptrtoint earlier` as an `i64`.
fn emit_gap(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    earlier: trust_ir::value::ValueId,
    later: trust_ir::value::ValueId,
) -> trust_ir::value::ValueId {
    use trust_ir::inst::CastOp;
    let e = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, earlier);
    let l = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, later);
    fb.sub(Ty::I64, l, e)
}

fn layout_module(cells: &[LayoutCell]) -> (Module, Vec<FuncId>) {
    use trust_ir::inst::{CastOp, ICmpOp, Ordering};
    use trust_ir::value::GlobalId;
    use trust_ir::{Global, Linkage};
    let mut mb = ModuleBuilder::new("w5b_address_layout");
    for (name, align) in [("G", None), ("G64", Some(64))] {
        mb.add_global(Global {
            name: name.into(),
            ty: Ty::I32,
            mutable: true,
            initializer: None,
            linkage: Linkage::Internal,
            tls: None,
            align,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
    }
    let ret_i32 = mb.add_func_type(vec![], vec![Ty::I32]);
    let ret_i64 = mb.add_func_type(vec![], vec![Ty::I64]);
    let ret_u8 = mb.add_func_type(vec![], vec![Ty::U8]);
    let ret_bool = mb.add_func_type(vec![], vec![Ty::Bool]);
    let mut ids = Vec::new();
    for (i, cell) in cells.iter().enumerate() {
        use LayoutCell as C;
        let ft = match cell {
            C::HeapSlackByte => ret_u8,
            C::ZeroSizeSlotSharesNoAddress => ret_bool,
            C::Gap(_) | C::FirstBase | C::HeapDeclaredAlign | C::GlobalDeclaredAlign => ret_i64,
            _ => ret_i32,
        };
        let mut fb = mb.function(format!("layout{i}_{cell:?}"), ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let r = match cell {
            C::LoadOnePastEndIntoNeighbour => {
                let a = fb.alloca(Ty::I32);
                let b = fb.alloca(Ty::I32);
                let seven = fb.iconst(Ty::I32, 7);
                fb.store(Ty::I32, b, seven);
                let one = fb.iconst(Ty::U64, 1);
                let past = fb.gep(Ty::I32, a, vec![one]);
                fb.load(Ty::I32, past)
            }
            C::StoreOnePastEndIntoNeighbour => {
                let a = fb.alloca(Ty::I32);
                let b = fb.alloca(Ty::I32);
                let seven = fb.iconst(Ty::I32, 7);
                let one = fb.iconst(Ty::U64, 1);
                let past = fb.gep(Ty::I32, a, vec![one]);
                fb.store(Ty::I32, past, seven);
                fb.load(Ty::I32, b)
            }
            C::AlignedAccessAfterByteSlot => {
                let _ = fb.alloca(Ty::I8);
                let p = fb.alloca(Ty::I32);
                let seven = fb.iconst(Ty::I32, 7);
                fb.store_aligned(Ty::I32, p, seven, 4);
                fb.load_aligned(Ty::I32, p, 4)
            }
            C::HeapSlackByte => {
                let p = fb.heap_alloc(Ty::I32, None, None, AllocOrigin::RustHeap);
                let four = fb.iconst(Ty::U64, 4);
                let slack = fb.gep(Ty::I8, p, vec![four]);
                fb.load(Ty::U8, slack)
            }
            C::ZeroSizeSlotSharesNoAddress => {
                let z = fb.alloca(Ty::Unit);
                let b = fb.alloca(Ty::I32);
                let zi = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, z);
                let bi = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, b);
                fb.icmp(ICmpOp::Eq, Ty::I64, zi, bi)
            }
            C::MemCopyAcrossBoundary => {
                let a = fb.alloca(Ty::I32);
                let b = fb.alloca(Ty::I32);
                let c = fb.alloca(Ty::I64);
                let seven = fb.iconst(Ty::I32, 7);
                fb.store(Ty::I32, a, seven);
                fb.store(Ty::I32, b, seven);
                let eight = fb.iconst(Ty::U64, 8);
                fb.memcopy(c, a, eight, false);
                fb.load(Ty::I32, c)
            }
            C::LoadThroughFreedPointer => {
                let p = fb.alloca(Ty::I32);
                let seven = fb.iconst(Ty::I32, 7);
                fb.store(Ty::I32, p, seven);
                fb.dealloc(p);
                let q = fb.alloca(Ty::I32);
                fb.store(Ty::I32, q, seven);
                fb.load(Ty::I32, p)
            }
            C::Gap(shape) => match shape {
                GapShape::Alloca(ty) => {
                    let x = fb.alloca(Ty::I8);
                    let y = fb.alloca(ty.clone());
                    emit_gap(&mut fb, x, y)
                }
                GapShape::HeapPair => {
                    let x = fb.heap_alloc(Ty::I8, None, None, AllocOrigin::RustHeap);
                    let y = fb.heap_alloc(Ty::I8, None, None, AllocOrigin::RustHeap);
                    emit_gap(&mut fb, x, y)
                }
                GapShape::GlobalAfterByte => {
                    let x = fb.alloca(Ty::I8);
                    let g = fb.global_addr(GlobalId::new(0));
                    emit_gap(&mut fb, x, g)
                }
                GapShape::DeclaredAlign => {
                    let x = fb.alloca(Ty::I8);
                    let y = fb.alloca_aligned(Ty::I32, 32);
                    emit_gap(&mut fb, x, y)
                }
            },
            C::LoadMisalignedNatural | C::AtomicLoadMisaligned => {
                let a = fb.alloca(Ty::I64);
                let zero = fb.iconst(Ty::I64, 0);
                fb.store(Ty::I64, a, zero);
                let one = fb.iconst(Ty::U64, 1);
                let q = fb.gep(Ty::I8, a, vec![one]);
                if let C::AtomicLoadMisaligned = cell {
                    fb.atomic_load(Ty::I32, q, Ordering::SeqCst)
                } else {
                    fb.load(Ty::I32, q)
                }
            }
            C::GepFromDanglingPointer => {
                let a = fb.alloca(Ty::I32);
                let seven = fb.iconst(Ty::I32, 7);
                fb.store(Ty::I32, a, seven);
                let ai = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, a);
                let four = fb.iconst(Ty::U64, 4);
                let below = fb.sub(Ty::U64, ai, four);
                let d = fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, below);
                let q = fb.gep(Ty::I8, d, vec![four]);
                fb.load(Ty::I32, q)
            }
            C::FirstBase => {
                let p = fb.alloca(Ty::I32);
                fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, p)
            }
            C::HeapDeclaredAlign => {
                let x = fb.alloca(Ty::I8);
                let y = fb.heap_alloc(Ty::I8, None, Some(64), AllocOrigin::RustHeap);
                emit_gap(&mut fb, x, y)
            }
            C::GlobalDeclaredAlign => {
                let x = fb.alloca(Ty::I8);
                let g = fb.global_addr(GlobalId::new(1));
                emit_gap(&mut fb, x, g)
            }
        };
        fb.ret(vec![r]);
        ids.push(fb.build());
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errs = trust_ir_build::validate_module(&module);
    assert!(
        errs.is_empty(),
        "every layout cell is well-formed (the rule is dynamic): {errs:?}"
    );
    (module, ids)
}

/// Both engines run the access and placement cells, and every cell must
/// AGREE and give its expected verdict: an access is checked against the
/// allocation its pointer was derived from, and both reference models place
/// allocations alike (the base 1024, natural and declared alignment, the heap
/// slack tail, a global's section alignment, the one-byte bump of a zero-size
/// slot).
#[test]
fn address_layout_agrees_across_engines() {
    let cells: Vec<LayoutCell> = LAYOUT_CELLS.iter().map(|(c, _)| c.clone()).collect();
    let (module, ids) = layout_module(&cells);
    check_decided("address layout", &module, &ids, LAYOUT_CELLS);
}

/// A cell of the pointer-VALUE rules: the integer-to-address conversion,
/// the null pointer at every pointer cast, and pointer equality.
#[derive(Clone, Copy, Debug)]
enum PointerValueCell {
    /// c01: `ret ptrtoint i64 (inttoptr i64 -8)`: a negative integer is a
    /// large address, never null.
    IntToPtrNegativeI64,
    /// c08: `ret ptrtoint i64 (inttoptr i32 -8)`: the unsigned value at the
    /// SOURCE width.
    IntToPtrNegativeI32,
    /// c11: `ret ptrtoint u64 (inttoptr u128 2^64)`: an address at or above
    /// 2^64 is UB.
    IntToPtrU128TwoPow64,
    /// c02: `slot = Alloca ptr`; `store null -> slot`;
    /// `ret (cmpxchg ptr slot, null, null).success`: null equals null.
    CmpXchgNullNull,
    /// c07: `a`, `b` = `Alloca i32`; `slot = Alloca ptr`; `store b -> slot`;
    /// `ret (cmpxchg ptr slot, a + 4, a + 4).success`: the same address with
    /// another provenance is not equal.
    CmpXchgSameAddressOtherProvenance,
    /// c03: `ret ptrtoint u64 null`.
    PtrToIntNull,
    /// c17: `ret ptrtoint u64 (ptrtoptr null)`.
    PtrToPtrNull,
    /// `ret bitcast ptr null to u64`.
    BitcastNullToU64,
    /// `ret ptrtoint u64 (transmute ptr null to ptr)`.
    TransmuteNullPtrToPtr,
    /// `ret ptrtoint u64 (bitcast ptr null to ptr)`.
    BitcastNullToPtr,
}

/// The DECIDED pointer-value cells and the verdict BOTH engines must give.
/// Measured against the Lean model of trust-ir `e2154f00`: every one
/// diverged — the integer conversion was `Int.toNat` (every negative integer
/// became null; no 2^64 bound), the null pointer was a type error at
/// `PtrToInt` / `PtrToPtr` / `Bitcast` and unsupported at `Transmute`, and
/// pointer equality ignored provenance and called null unequal to null.
/// c01 to c17 are cells of the challenge of the Lean-provenance design; the
/// last three extend its null-cast cells (c03, c17) to `Bitcast` and
/// `Transmute`, which the same rule covers.
const POINTER_VALUE_CELLS: &[(PointerValueCell, Expect)] = &[
    (PointerValueCell::IntToPtrNegativeI64, Expect::I64(-8)),
    (
        PointerValueCell::IntToPtrNegativeI32,
        Expect::I64(4_294_967_288),
    ),
    (
        PointerValueCell::IntToPtrU128TwoPow64,
        Expect::Ub("does not fit u64"),
    ),
    (PointerValueCell::CmpXchgNullNull, Expect::Bool(true)),
    (
        PointerValueCell::CmpXchgSameAddressOtherProvenance,
        Expect::Bool(false),
    ),
    (PointerValueCell::PtrToIntNull, Expect::U64(0)),
    (PointerValueCell::PtrToPtrNull, Expect::U64(0)),
    (PointerValueCell::BitcastNullToU64, Expect::U64(0)),
    (PointerValueCell::TransmuteNullPtrToPtr, Expect::U64(0)),
    (PointerValueCell::BitcastNullToPtr, Expect::U64(0)),
];

fn pointer_value_module(cells: &[PointerValueCell]) -> (Module, Vec<FuncId>) {
    use trust_ir::inst::{CastOp, Ordering};
    let mut mb = ModuleBuilder::new("w5b_pointer_values");
    let ret_i64 = mb.add_func_type(vec![], vec![Ty::I64]);
    let ret_u64 = mb.add_func_type(vec![], vec![Ty::U64]);
    let ret_bool = mb.add_func_type(vec![], vec![Ty::Bool]);
    let mut ids = Vec::new();
    for (i, cell) in cells.iter().enumerate() {
        use PointerValueCell as C;
        let ft = match cell {
            C::IntToPtrNegativeI64 | C::IntToPtrNegativeI32 => ret_i64,
            C::CmpXchgNullNull | C::CmpXchgSameAddressOtherProvenance => ret_bool,
            _ => ret_u64,
        };
        let mut fb = mb.function(format!("pointer{i}_{cell:?}"), ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let r = match cell {
            C::IntToPtrNegativeI64 | C::IntToPtrNegativeI32 => {
                let ty = if let C::IntToPtrNegativeI64 = cell {
                    Ty::I64
                } else {
                    Ty::I32
                };
                let m = fb.iconst(ty.clone(), -8);
                let p = fb.cast(CastOp::IntToPtr, ty, Ty::Ptr, m);
                fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, p)
            }
            C::IntToPtrU128TwoPow64 => {
                let big = fb.uconst(Ty::U128, 1u128 << 64);
                let p = fb.cast(CastOp::IntToPtr, Ty::U128, Ty::Ptr, big);
                fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, p)
            }
            C::CmpXchgNullNull => {
                let slot = fb.alloca(Ty::Ptr);
                let null = fb.null_ptr();
                fb.store(Ty::Ptr, slot, null);
                let (_, ok) = fb.cmpxchg(
                    Ty::Ptr,
                    slot,
                    null,
                    null,
                    Ordering::SeqCst,
                    Ordering::SeqCst,
                );
                ok
            }
            C::CmpXchgSameAddressOtherProvenance => {
                let a = fb.alloca(Ty::I32);
                let b = fb.alloca(Ty::I32);
                let slot = fb.alloca(Ty::Ptr);
                fb.store(Ty::Ptr, slot, b);
                let one = fb.iconst(Ty::U64, 1);
                let past = fb.gep(Ty::I32, a, vec![one]);
                let (_, ok) = fb.cmpxchg(
                    Ty::Ptr,
                    slot,
                    past,
                    past,
                    Ordering::SeqCst,
                    Ordering::SeqCst,
                );
                ok
            }
            C::PtrToIntNull => {
                let null = fb.null_ptr();
                fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, null)
            }
            C::PtrToPtrNull => {
                let null = fb.null_ptr();
                let p = fb.cast(CastOp::PtrToPtr, Ty::Ptr, Ty::Ptr, null);
                fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, p)
            }
            C::BitcastNullToU64 => {
                let null = fb.null_ptr();
                fb.cast(CastOp::Bitcast, Ty::Ptr, Ty::U64, null)
            }
            C::TransmuteNullPtrToPtr | C::BitcastNullToPtr => {
                let op = if let C::TransmuteNullPtrToPtr = cell {
                    CastOp::Transmute
                } else {
                    CastOp::Bitcast
                };
                let null = fb.null_ptr();
                let p = fb.cast(op, Ty::Ptr, Ty::Ptr, null);
                fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, p)
            }
        };
        fb.ret(vec![r]);
        ids.push(fb.build());
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errs = trust_ir_build::validate_module(&module);
    assert!(
        errs.is_empty(),
        "every pointer-value cell is well-formed (the rule is dynamic): {errs:?}"
    );
    (module, ids)
}

/// Both engines run the pointer-value cells, and every cell must AGREE and
/// give its expected verdict: an integer becomes an address as its unsigned
/// value at its width (UB at or above 2^64), the null pointer is address 0 at
/// every pointer cast, and two pointers are equal when address AND
/// provenance are.
#[test]
fn pointer_value_rules_agree_across_engines() {
    let cells: Vec<PointerValueCell> = POINTER_VALUE_CELLS.iter().map(|(c, _)| *c).collect();
    let (module, ids) = pointer_value_module(&cells);
    check_decided("pointer values", &module, &ids, POINTER_VALUE_CELLS);
}

/// The aggregate shape of a reference-counted cell: the struct `Pair { a:
/// u32, b: u32 }` of the `clean_backend_tv` heap fixture (`tv_heap_module`)
/// and the `[u32; 2]` box of `boxed_index_module` — the constructor shapes
/// Fragment-4 exists for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AggregateCell {
    Pair,
    Array2,
}

/// Decided aggregate reference-counted cells. Actual decoded execution uses
/// the source-owned struct/array layout; the bare scalar allocation theorem
/// remains a scalar theorem. Release returns the stored value, Dealloc is UB.
const AGGREGATE_DECIDED_RELEASE_CELLS: &[(AggregateCell, ReleaseOp, &str)] = &[
    (AggregateCell::Pair, ReleaseOp::Release, "ok"),
    (AggregateCell::Pair, ReleaseOp::Dealloc, "ub"),
    (AggregateCell::Array2, ReleaseOp::Release, "ok"),
    (AggregateCell::Array2, ReleaseOp::Dealloc, "ub"),
];

/// One module holding one `() -> u32` function per aggregate cell, the
/// certified Fragment-4 shape with literal arguments: `p = heap_alloc
/// clean_heap <agg>; store 3 -> p; q = gep u32 p [1]; store 9 -> q; v = load
/// q; <op> p; ret v`.
fn aggregate_cell_module(cells: &[(AggregateCell, ReleaseOp, &str)]) -> (Module, Vec<FuncId>) {
    use trust_ir::ty::{FieldDef, StructDef};
    use trust_ir::value::StructId;
    let mut mb = ModuleBuilder::new("w5b_aggregate_release");
    let pair = mb.add_struct(StructDef {
        id: StructId::new(0),
        name: "Pair".to_string(),
        fields: vec![
            FieldDef {
                name: "a".to_string(),
                ty: Ty::U32,
                offset: Some(0),
            },
            FieldDef {
                name: "b".to_string(),
                ty: Ty::U32,
                offset: Some(4),
            },
        ],
        size: Some(8),
        align: Some(4),
        repr: Default::default(),
        origin: None,
    });
    let elem = mb.add_type(Ty::U32);
    let ft = mb.add_func_type(vec![], vec![Ty::U32]);
    let mut ids = Vec::new();
    for (i, (shape, op, _)) in cells.iter().enumerate() {
        let mut fb = mb.function(format!("agg{i}_{shape:?}_{op:?}"), ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let ty = match shape {
            AggregateCell::Pair => Ty::Struct(pair),
            AggregateCell::Array2 => Ty::Array(elem, 2),
        };
        let p = fb.heap_alloc(ty, None, Some(4), AllocOrigin::CleanHeap);
        let x = fb.iconst(Ty::U32, 3);
        fb.store(Ty::U32, p, x);
        let one = fb.iconst(Ty::U64, 1);
        let q = fb.gep(Ty::U32, p, vec![one]);
        let y = fb.iconst(Ty::U32, 9);
        fb.store(Ty::U32, q, y);
        let v = fb.load(Ty::U32, q);
        match op {
            ReleaseOp::Release => fb.release(p),
            ReleaseOp::Dealloc => fb.dealloc(p),
            other => panic!("aggregate ledger holds Release / Dealloc only, not {other:?}"),
        }
        fb.ret(vec![v]);
        ids.push(fb.build());
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errs = trust_ir_build::validate_module(&module);
    assert!(
        errs.is_empty(),
        "every aggregate cell is well-formed (the rule is dynamic): {errs:?}"
    );
    (module, ids)
}

/// Actual source-derived heap layouts extend the release discipline to the
/// two aggregate shapes, with exact returned values and opposite UB controls.
#[test]
fn aggregate_reference_counted_cells_agree_across_engines() {
    let (module, ids) = aggregate_cell_module(AGGREGATE_DECIDED_RELEASE_CELLS);
    let nine = Verdict::Ok(vec![Val::Int { width: 32, raw: 9 }]);
    for ((shape, op, class), function) in AGGREGATE_DECIDED_RELEASE_CELLS.iter().zip(&ids) {
        let rust = canonical_verdict(run_rust(&module, *function, &[]));
        assert_eq!(rust.class(), *class, "{shape:?} x {op:?}: {rust:?}");
        if *class == "ok" {
            assert_eq!(rust, nine, "{shape:?} x {op:?}");
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let reports = differential(
        exe,
        &[Batch {
            label: "decided aggregate reference-counted cells".into(),
            module: &module,
            runs: ids.iter().map(|function| (*function, vec![])).collect(),
        }],
    );
    assert_eq!(reports.len(), AGGREGATE_DECIDED_RELEASE_CELLS.len());
    for ((shape, op, class), report) in AGGREGATE_DECIDED_RELEASE_CELLS.iter().zip(&reports) {
        assert_eq!(
            report.comparison,
            Comparison::Agree,
            "{shape:?} x {op:?}: {report:?}"
        );
        assert_eq!(
            report.lean.class(),
            *class,
            "{shape:?} x {op:?}: {report:?}"
        );
        if *class == "ok" {
            assert_eq!(report.rust, nine, "{shape:?} x {op:?}");
            assert_eq!(report.lean, nine, "{shape:?} x {op:?}");
        }
    }
}

// ---------------------------------------------------------------------------
// One integer representation: every integer constant binds its residue
// ---------------------------------------------------------------------------
//
// The Lean model keeps an integer value as `Value.int w v` with no signedness.
// Parameters (`argValue`) and operation results (`wrap`, `truncateUnsigned`)
// are residues in `[0, 2^w)`; until the residue rule, the SEVEN places where a
// `Constant.int` becomes or meets a model value bound the raw literal, so a
// negative literal had a second spelling (`Value.int 32 (-1)` beside
// `Value.int 32 4294967295`). Every consumer that reads the raw `Int` — the
// unsigned compares and divisions, the shift-amount guard, `ZExt`, `UIToFP`,
// `IntToPtr`, `CmpXchg`'s comparison, the switch case scan — then disagreed
// with the reference interpreter on a negative literal, and the generator
// corpus never mints one (`Rng::small` is non-negative), so the gate never
// saw it. The rows below put negative literals where each consumer reads them,
// in both operand positions, through the bare `Const` step and through the
// module-context lowering (tuple lane, array lane, enum tag, global).

/// The integer `BinOp`s: every one the reference interpreter and the Lean
/// model both define on fixed-width integers.
const RESIDUE_INT_BINOPS: [trust_ir::inst::BinOp; 15] = {
    use trust_ir::inst::BinOp::*;
    [
        Add, Sub, Mul, UDiv, SDiv, URem, SRem, And, Or, Xor, Shl, LShr, AShr, RotL, RotR,
    ]
};

/// Wildcard-free: a new `BinOp` variant fails to compile here until it is
/// classified, so `RESIDUE_INT_BINOPS` cannot silently miss an integer op.
fn residue_is_integer_binop(op: trust_ir::inst::BinOp) -> bool {
    use trust_ir::inst::BinOp::*;
    match op {
        Add | Sub | Mul | UDiv | SDiv | URem | SRem | And | Or | Xor | Shl | LShr | AShr | RotL
        | RotR => true,
        FAdd | FSub | FMul | FDiv | FRem | FMin | FMax | FCopySign | BAnd | BOr | BXor => false,
    }
}

const RESIDUE_ICMP_OPS: [trust_ir::inst::ICmpOp; 10] = {
    use trust_ir::inst::ICmpOp::*;
    [Eq, Ne, Ult, Ule, Ugt, Uge, Slt, Sle, Sgt, Sge]
};

/// Wildcard-free twin of `residue_is_integer_binop` for `ICmpOp`.
fn residue_icmp_listed(op: trust_ir::inst::ICmpOp) -> bool {
    use trust_ir::inst::ICmpOp::*;
    match op {
        Eq | Ne | Ult | Ule | Ugt | Uge | Slt | Sle | Sgt | Sge => RESIDUE_ICMP_OPS.contains(&op),
    }
}

const RESIDUE_RMW_OPS: [trust_ir::inst::AtomicRMWOp; 10] = {
    use trust_ir::inst::AtomicRMWOp::*;
    [Xchg, Add, Sub, And, Or, Xor, Max, Min, UMax, UMin]
};

/// Wildcard-free twin of `residue_is_integer_binop` for `AtomicRMWOp`.
fn residue_rmw_listed(op: trust_ir::inst::AtomicRMWOp) -> bool {
    use trust_ir::inst::AtomicRMWOp::*;
    match op {
        Xchg | Add | Sub | And | Or | Xor | Max | Min | UMax | UMin => {
            RESIDUE_RMW_OPS.contains(&op)
        }
    }
}

/// The signed widths a negative literal is checked at.
fn residue_tys() -> [Ty; 4] {
    [Ty::I8, Ty::I16, Ty::I32, Ty::I64]
}

fn residue_bits(ty: &Ty) -> u32 {
    ty.bit_width().expect("a fixed-width integer")
}

/// `{-1, MIN, MIN + 1}` at `ty`'s width.
fn residue_negative_literals(ty: &Ty) -> [i128; 3] {
    let min = -(1i128 << (residue_bits(ty) - 1));
    [-1, min, min + 1]
}

fn residue_arg(ty: &Ty, v: i128) -> InterpretValue {
    InterpretValue::int(ty.clone(), v).expect("an integer argument")
}

/// One function of a residue module: what it exercises, and its runs.
struct ResidueFn {
    kind: String,
    id: FuncId,
    runs: Vec<Vec<InterpretValue>>,
    /// Every run must be UB on both engines (the negative GEP index / alloca
    /// count rows); otherwise every run must be Ok or UB on the interpreter and
    /// the kind must reach Ok at least once.
    all_ub: bool,
}

/// Binops and compares: for every signed width, every negative literal and
/// every op, the literal on the LEFT and on the RIGHT of `op(x)`.
fn residue_arith_module() -> (Module, Vec<ResidueFn>) {
    assert!(
        RESIDUE_INT_BINOPS
            .iter()
            .all(|op| residue_is_integer_binop(*op))
    );
    assert!(RESIDUE_ICMP_OPS.iter().all(|op| residue_icmp_listed(*op)));
    let mut mb = ModuleBuilder::new("w5b_residue_arith");
    let mut fns = Vec::new();
    for ty in residue_tys() {
        let bits = residue_bits(&ty);
        let max = (1i128 << (bits - 1)) - 1;
        let min = -(1i128 << (bits - 1));
        let xs: Vec<Vec<InterpretValue>> = [1, 5, -1, max, min]
            .iter()
            .map(|x| vec![residue_arg(&ty, *x)])
            .collect();
        let binop_ft = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
        let icmp_ft = mb.add_func_type(vec![ty.clone()], vec![Ty::Bool]);
        for lit in residue_negative_literals(&ty) {
            for op in RESIDUE_INT_BINOPS {
                for lit_on_left in [true, false] {
                    let side = if lit_on_left { "l" } else { "r" };
                    let mut fb = mb.function(format!("{op:?}_{ty}_{lit}_{side}"), binop_ft);
                    let entry = fb.create_block();
                    let x = fb.add_block_param(entry, ty.clone());
                    fb.switch_to_block(entry);
                    let c = fb.iconst(ty.clone(), lit);
                    let (l, r) = if lit_on_left { (c, x) } else { (x, c) };
                    let v = fb.binop(op, ty.clone(), l, r);
                    fb.ret(vec![v]);
                    fns.push(ResidueFn {
                        kind: format!("binop.{op:?}"),
                        id: fb.build(),
                        runs: xs.clone(),
                        all_ub: false,
                    });
                }
            }
            for op in RESIDUE_ICMP_OPS {
                for lit_on_left in [true, false] {
                    let side = if lit_on_left { "l" } else { "r" };
                    let mut fb = mb.function(format!("icmp_{op:?}_{ty}_{lit}_{side}"), icmp_ft);
                    let entry = fb.create_block();
                    let x = fb.add_block_param(entry, ty.clone());
                    fb.switch_to_block(entry);
                    let c = fb.iconst(ty.clone(), lit);
                    let (l, r) = if lit_on_left { (c, x) } else { (x, c) };
                    let v = fb.icmp(op, ty.clone(), l, r);
                    fb.ret(vec![v]);
                    let mut runs = xs.clone();
                    runs.push(vec![residue_arg(&ty, lit)]);
                    fns.push(ResidueFn {
                        kind: format!("icmp.{op:?}"),
                        id: fb.build(),
                        runs,
                        all_ub: false,
                    });
                }
            }
        }
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errs = trust_ir_build::validate_module(&module);
    assert!(
        errs.is_empty(),
        "the residue arithmetic module validates: {errs:?}"
    );
    (module, fns)
}

/// Casts, switches, aggregate lanes, memory and atomics over negative literals.
fn residue_misc_module() -> (Module, Vec<ResidueFn>) {
    use trust_ir::constant::Constant;
    use trust_ir::inst::{CastOp, ICmpOp, Ordering, SwitchCase};
    use trust_ir::ty::{EnumDef, EnumTagRepr, EnumVariant};
    use trust_ir::value::{EnumId, GlobalId};
    use trust_ir::{Global, Linkage};

    let mut mb = ModuleBuilder::new("w5b_residue_misc");
    let mut fns = Vec::new();

    // --- casts of a negative literal (no parameters) ---
    let widen = |ty: &Ty| match ty {
        Ty::I8 => Ty::I16,
        Ty::I16 => Ty::I32,
        Ty::I32 => Ty::I64,
        _ => Ty::I128,
    };
    for ty in residue_tys() {
        for lit in residue_negative_literals(&ty) {
            let mut casts = vec![
                ("zext", CastOp::ZExt, widen(&ty)),
                ("sext", CastOp::SExt, widen(&ty)),
                ("uitofp", CastOp::UIToFP, Ty::F64),
                ("sitofp", CastOp::SIToFP, Ty::F64),
            ];
            if ty != Ty::I8 {
                casts.push(("trunc", CastOp::Trunc, Ty::I8));
            }
            for (name, op, dst) in casts {
                let ft = mb.add_func_type(vec![], vec![dst.clone()]);
                let mut fb = mb.function(format!("cast_{name}_{ty}_{lit}"), ft);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                let c = fb.iconst(ty.clone(), lit);
                let v = fb.cast(op, ty.clone(), dst, c);
                fb.ret(vec![v]);
                fns.push(ResidueFn {
                    kind: format!("cast.{name}"),
                    id: fb.build(),
                    runs: vec![vec![]],
                    all_ub: false,
                });
            }
        }
    }
    // `inttoptr` then `ptrtoint`: the address is what the literal's bits name.
    for lit in residue_negative_literals(&Ty::I64) {
        let ft = mb.add_func_type(vec![], vec![Ty::I64]);
        let mut fb = mb.function(format!("inttoptr_roundtrip_{lit}"), ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let c = fb.iconst(Ty::I64, lit);
        let p = fb.cast(CastOp::IntToPtr, Ty::I64, Ty::Ptr, c);
        let v = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, p);
        fb.ret(vec![v]);
        fns.push(ResidueFn {
            kind: "cast.inttoptr".into(),
            id: fb.build(),
            runs: vec![vec![]],
            all_ub: false,
        });
    }

    // --- switch: in-range negative cases, scrutinee a parameter, a constant
    // and an operation result ---
    let switch_on = |fb: &mut trust_ir_build::FunctionBuilder<'_>,
                     scrutinee: trust_ir::value::ValueId,
                     cases: &[i128]| {
        let arms: Vec<_> = (0..=cases.len()).map(|_| fb.create_block()).collect();
        fb.switch(
            scrutinee,
            cases
                .iter()
                .zip(&arms)
                .map(|(c, target)| SwitchCase {
                    value: Constant::Int(*c),
                    target: *target,
                    args: vec![],
                })
                .collect(),
            arms[cases.len()],
            vec![],
        );
        for (i, arm) in arms.iter().enumerate() {
            fb.switch_to_block(*arm);
            let r = fb.iconst(Ty::I32, 10 * (i as i128 + 1));
            fb.ret(vec![r]);
        }
    };
    for ty in residue_tys() {
        let lits = residue_negative_literals(&ty);
        let cases = [lits[0], lits[1], 1];
        let param_ft = mb.add_func_type(vec![ty.clone()], vec![Ty::I32]);
        let mut fb = mb.function(format!("switch_param_{ty}"), param_ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, ty.clone());
        fb.switch_to_block(entry);
        switch_on(&mut fb, x, &cases);
        fns.push(ResidueFn {
            kind: "switch.param".into(),
            id: fb.build(),
            runs: [lits[0], lits[1], lits[2], 1, 0]
                .iter()
                .map(|v| vec![residue_arg(&ty, *v)])
                .collect(),
            all_ub: false,
        });
        let const_ft = mb.add_func_type(vec![], vec![Ty::I32]);
        for lit in lits {
            let mut fb = mb.function(format!("switch_const_{ty}_{lit}"), const_ft);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let c = fb.iconst(ty.clone(), lit);
            switch_on(&mut fb, c, &cases);
            fns.push(ResidueFn {
                kind: "switch.const".into(),
                id: fb.build(),
                runs: vec![vec![]],
                all_ub: false,
            });
            // The same scrutinee through an operation (`lit - 0`): a residue
            // on every model before and after the rule.
            let mut fb = mb.function(format!("switch_op_{ty}_{lit}"), const_ft);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let c = fb.iconst(ty.clone(), lit);
            let zero = fb.iconst(ty.clone(), 0);
            let d = fb.sub(ty.clone(), c, zero);
            switch_on(&mut fb, d, &cases);
            fns.push(ResidueFn {
                kind: "switch.op_result".into(),
                id: fb.build(),
                runs: vec![vec![]],
                all_ub: false,
            });
        }
    }
    // An unsigned scrutinee: its case at the top of its range.
    {
        let ft = mb.add_func_type(vec![Ty::U8], vec![Ty::I32]);
        let mut fb = mb.function("switch_param_u8", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U8);
        fb.switch_to_block(entry);
        switch_on(&mut fb, x, &[255, 0]);
        fns.push(ResidueFn {
            kind: "switch.param".into(),
            id: fb.build(),
            runs: [255, 0, 1]
                .iter()
                .map(|v| vec![residue_arg(&Ty::U8, *v)])
                .collect(),
            all_ub: false,
        });
    }

    // --- the module-context lowering: enum tag, tuple lane, array lane ---
    let i8_id = mb.add_type(Ty::I8);
    let ord = mb.add_enum(
        EnumDef::new(
            EnumId::new(0),
            "Ord",
            ["Less", "Equal", "Greater"]
                .iter()
                .map(|name| EnumVariant {
                    name: (*name).into(),
                    fields: vec![],
                    field_names: vec![],
                })
                .collect(),
        )
        .with_discriminants(vec![Some(-1), Some(0), Some(1)])
        .with_repr(EnumTagRepr::I8),
    );
    let i8_runs: Vec<Vec<InterpretValue>> = [-1, 0, 1]
        .iter()
        .map(|v| vec![residue_arg(&Ty::I8, *v)])
        .collect();
    let pred_ft = mb.add_func_type(vec![Ty::I8], vec![Ty::Bool]);
    {
        let mut fb = mb.function("enum_tag_negative", pred_ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I8);
        fb.switch_to_block(entry);
        let e = fb.const_value(Ty::Enum(ord), Constant::Aggregate(vec![Constant::Int(-1)]));
        let tag = fb.extract_field(Ty::I8, e, 0);
        let v = fb.icmp(ICmpOp::Eq, Ty::I8, tag, x);
        fb.ret(vec![v]);
        fns.push(ResidueFn {
            kind: "enum.tag".into(),
            id: fb.build(),
            runs: i8_runs.clone(),
            all_ub: false,
        });
    }
    {
        let tuple = Ty::Tuple(vec![Ty::I8, Ty::I32]);
        let mut fb = mb.function("tuple_lane_negative", pred_ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I8);
        fb.switch_to_block(entry);
        let t = fb.const_value(
            tuple,
            Constant::Aggregate(vec![Constant::Int(-1), Constant::Int(-2)]),
        );
        let lane = fb.extract_field(Ty::I8, t, 0);
        let v = fb.icmp(ICmpOp::Ult, Ty::I8, x, lane);
        fb.ret(vec![v]);
        fns.push(ResidueFn {
            kind: "tuple.lane".into(),
            id: fb.build(),
            runs: i8_runs.clone(),
            all_ub: false,
        });
    }
    {
        let ft = mb.add_func_type(vec![Ty::I64, Ty::I8], vec![Ty::Bool]);
        let mut fb = mb.function("array_lane_negative", ft);
        let entry = fb.create_block();
        let i = fb.add_block_param(entry, Ty::I64);
        let x = fb.add_block_param(entry, Ty::I8);
        fb.switch_to_block(entry);
        let a = fb.const_value(
            Ty::Array(i8_id, 2),
            Constant::Array(vec![Constant::Int(-1), Constant::Int(1)]),
        );
        let e = fb.extract_element(Ty::I8, a, i);
        let v = fb.icmp(ICmpOp::Eq, Ty::I8, e, x);
        fb.ret(vec![v]);
        fns.push(ResidueFn {
            kind: "array.lane".into(),
            id: fb.build(),
            runs: [(0, -1), (1, 1), (0, 1)]
                .iter()
                .map(|(i, x)| vec![residue_arg(&Ty::I64, *i), residue_arg(&Ty::I8, *x)])
                .collect(),
            all_ub: false,
        });
    }
    {
        let vty = Ty::Vector(Box::new(Ty::I32), 4);
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::Bool]);
        let mut fb = mb.function("vector_lane_negative", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let v = fb.const_value(
            vty,
            Constant::Vector(
                [-1, i128::from(i32::MIN), i128::from(i32::MAX), 1]
                    .iter()
                    .map(|v| Constant::Int(*v))
                    .collect(),
            ),
        );
        let zero = fb.iconst(Ty::I64, 0);
        let lane0 = fb.extract_element(Ty::I32, v, zero);
        let r = fb.icmp(ICmpOp::Ugt, Ty::I32, lane0, x);
        fb.ret(vec![r]);
        fns.push(ResidueFn {
            kind: "vector.lane".into(),
            id: fb.build(),
            runs: [0, -1, 5]
                .iter()
                .map(|v| vec![residue_arg(&Ty::I32, *v)])
                .collect(),
            all_ub: false,
        });
    }
    // A module global initialized with a negative literal, read back.
    mb.add_global(Global {
        name: "NEG".into(),
        ty: Ty::I32,
        mutable: false,
        initializer: Some(Constant::Int(-1)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    {
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::Bool]);
        let mut fb = mb.function("global_negative", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let g = fb.global_addr(GlobalId::new(0));
        let v = fb.load(Ty::I32, g);
        let r = fb.icmp(ICmpOp::Eq, Ty::I32, v, x);
        fb.ret(vec![r]);
        fns.push(ResidueFn {
            kind: "global".into(),
            id: fb.build(),
            runs: [-1, 0]
                .iter()
                .map(|v| vec![residue_arg(&Ty::I32, *v)])
                .collect(),
            all_ub: false,
        });
    }

    // --- the sign-reading consumers: GEP index and allocation count ---
    let seven_ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let seven_param_ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I32]);
    for (kind, by_param) in [("gep.const", false), ("gep.param", true)] {
        let mut fb = mb.function(
            kind.replace('.', "_"),
            if by_param { seven_param_ft } else { seven_ft },
        );
        let entry = fb.create_block();
        let param = by_param.then(|| fb.add_block_param(entry, Ty::I64));
        fb.switch_to_block(entry);
        let a = fb.alloca(Ty::I32);
        let i = param.unwrap_or_else(|| fb.iconst(Ty::I64, -1));
        let _p = fb.gep(Ty::I32, a, vec![i]);
        let seven = fb.iconst(Ty::I32, 7);
        fb.ret(vec![seven]);
        fns.push(ResidueFn {
            kind: kind.into(),
            id: fb.build(),
            runs: if by_param {
                vec![
                    vec![residue_arg(&Ty::I64, -1)],
                    vec![residue_arg(&Ty::I64, 0)],
                ]
            } else {
                vec![vec![]]
            },
            all_ub: !by_param,
        });
    }
    for (kind, by_param, heap) in [
        ("alloca.const", false, false),
        ("alloca.param", true, false),
        ("heap_alloc.const", false, true),
        ("heap_alloc.param", true, true),
    ] {
        let mut fb = mb.function(
            kind.replace('.', "_"),
            if by_param { seven_param_ft } else { seven_ft },
        );
        let entry = fb.create_block();
        let param = by_param.then(|| fb.add_block_param(entry, Ty::I64));
        fb.switch_to_block(entry);
        let n = param.unwrap_or_else(|| fb.iconst(Ty::I64, -1));
        // The builder's `alloca` takes no count: an `alloca.*` row is emitted
        // as this counted `HeapAlloc` and rewritten to `Alloca` below.
        let _ = heap;
        let _p = fb.heap_alloc(Ty::I32, Some(n), None, AllocOrigin::RustHeap);
        let seven = fb.iconst(Ty::I32, 7);
        fb.ret(vec![seven]);
        fns.push(ResidueFn {
            kind: kind.into(),
            id: fb.build(),
            runs: if by_param {
                vec![
                    vec![residue_arg(&Ty::I64, -1)],
                    vec![residue_arg(&Ty::I64, 1)],
                ]
            } else {
                vec![vec![]]
            },
            all_ub: !by_param,
        });
    }

    // --- CmpXchg: a negative `expected` against the stored value ---
    let cx_ft = mb.add_func_type(vec![Ty::I32], vec![Ty::Bool]);
    for expected_is_const in [true, false] {
        let mut fb = mb.function(
            format!(
                "cmpxchg_{}",
                if expected_is_const { "const" } else { "param" }
            ),
            cx_ft,
        );
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let p = fb.alloca(Ty::I32);
        let m = fb.iconst(Ty::I32, -1);
        // Store the literal and expect the parameter, or the reverse.
        let (stored, expected) = if expected_is_const { (x, m) } else { (m, x) };
        fb.store(Ty::I32, p, stored);
        let desired = fb.iconst(Ty::I32, 5);
        let (_old, ok) = fb.cmpxchg(
            Ty::I32,
            p,
            expected,
            desired,
            Ordering::SeqCst,
            Ordering::SeqCst,
        );
        fb.ret(vec![ok]);
        fns.push(ResidueFn {
            kind: if expected_is_const {
                "cmpxchg.const"
            } else {
                "cmpxchg.param"
            }
            .into(),
            id: fb.build(),
            runs: [-1, 0]
                .iter()
                .map(|v| vec![residue_arg(&Ty::I32, *v)])
                .collect(),
            all_ub: false,
        });
    }
    // --- AtomicRMW: every op, with a negative operand as a constant and as a
    //     parameter, against a stored value of either sign. `Max` / `Min`
    //     order the two values SIGNED (the interpreter's `as_signed`), `UMax`
    //     / `UMin` unsigned; each row returns the value the op wrote. ---
    assert!(RESIDUE_RMW_OPS.iter().all(|op| residue_rmw_listed(*op)));
    for ty in residue_tys() {
        let bits = residue_bits(&ty);
        let max = (1i128 << (bits - 1)) - 1;
        let min = -(1i128 << (bits - 1));
        let stored = [5, -5, -1, 0, max, min];
        let const_ft = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
        let param_ft = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
        for op in RESIDUE_RMW_OPS {
            // `Some(lit)`: the operand is the constant `lit`; `None`: it is
            // the second parameter.
            let operands = residue_negative_literals(&ty)
                .map(Some)
                .into_iter()
                .chain([None]);
            for lit in operands {
                let path = if lit.is_some() { "const" } else { "param" };
                let mut fb = mb.function(
                    format!(
                        "rmw_{op:?}_{ty}_{}",
                        lit.map_or_else(|| "param".to_string(), |l| l.to_string())
                    ),
                    if lit.is_some() { const_ft } else { param_ft },
                );
                let entry = fb.create_block();
                let x = fb.add_block_param(entry, ty.clone());
                let y = lit.is_none().then(|| fb.add_block_param(entry, ty.clone()));
                fb.switch_to_block(entry);
                let p = fb.alloca(ty.clone());
                fb.store(ty.clone(), p, x);
                let operand = match (y, lit) {
                    (Some(y), _) => y,
                    (None, Some(l)) => fb.iconst(ty.clone(), l),
                    (None, None) => unreachable!("a row has an operand"),
                };
                let _old = fb.atomic_rmw(op, ty.clone(), p, operand, Ordering::SeqCst);
                let written = fb.load(ty.clone(), p);
                fb.ret(vec![written]);
                let runs: Vec<Vec<InterpretValue>> = if lit.is_some() {
                    stored.iter().map(|x| vec![residue_arg(&ty, *x)]).collect()
                } else {
                    let operands: Vec<i128> = residue_negative_literals(&ty)
                        .into_iter()
                        .chain([5])
                        .collect();
                    stored
                        .iter()
                        .flat_map(|x| {
                            operands
                                .iter()
                                .map(|y| vec![residue_arg(&ty, *x), residue_arg(&ty, *y)])
                                .collect::<Vec<_>>()
                        })
                        .collect()
                };
                fns.push(ResidueFn {
                    kind: format!("atomic_rmw.{op:?}.{path}"),
                    id: fb.build(),
                    runs,
                    all_ub: false,
                });
            }
        }
    }
    // Store / load of a negative literal: agrees on every model (guard).
    {
        let mut fb = mb.function("store_load_negative", seven_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let p = fb.alloca(Ty::I32);
        let c = fb.iconst(Ty::I32, -2);
        fb.store(Ty::I32, p, c);
        let v = fb.load(Ty::I32, p);
        fb.ret(vec![v]);
        fns.push(ResidueFn {
            kind: "store_load".into(),
            id: fb.build(),
            runs: vec![vec![]],
            all_ub: false,
        });
    }

    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    // The two `alloca.*` rows: turn their `HeapAlloc` into `Alloca` with the
    // same count (the builder has no counted `alloca`).
    for f in fns.iter().filter(|f| f.kind.starts_with("alloca.")) {
        let func = module
            .functions
            .iter_mut()
            .find(|func| func.id == f.id)
            .expect("the row's function");
        for node in &mut func.blocks[0].body {
            if let trust_ir::Inst::HeapAlloc {
                ty, count, align, ..
            } = &node.inst
            {
                node.inst = trust_ir::Inst::Alloca {
                    ty: ty.clone(),
                    count: *count,
                    align: *align,
                };
            }
        }
    }
    let errs = trust_ir_build::validate_module(&module);
    assert!(errs.is_empty(), "the residue module validates: {errs:?}");
    (module, fns)
}

/// Run every residue module through both engines and hold the rules: no run
/// disagrees; every interpreter verdict is `ok` or `ub` (each row executes);
/// every kind reaches `ok` on both engines at least once, except the
/// all-UB rows, which are `ub` on both on every run.
fn hold_residue_rows(modules: &[(Module, Vec<ResidueFn>)]) {
    let mut failures = Vec::new();
    let mut kinds_ok: BTreeMap<String, usize> = BTreeMap::new();
    for (module, fns) in modules {
        for f in fns {
            kinds_ok.entry(f.kind.clone()).or_default();
            for args in &f.runs {
                let rust = canonical_verdict(run_rust(module, f.id, args));
                let class = rust.class();
                if f.all_ub && class != "ub" || !f.all_ub && !matches!(class, "ok" | "ub") {
                    failures.push(format!(
                        "interpreter, {} fn {:?} args {args:?}: unexpected verdict {rust:?}",
                        f.kind, f.id
                    ));
                }
            }
        }
    }
    let Oracle::Ready(exe) = oracle() else {
        assert!(failures.is_empty(), "{}", failures.join("\n"));
        return;
    };
    let batches: Vec<Batch<'_>> = modules
        .iter()
        .map(|(module, fns)| Batch {
            label: module.name.clone(),
            module,
            runs: fns
                .iter()
                .flat_map(|f| f.runs.iter().map(move |args| (f.id, args.clone())))
                .collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    let kinds: Vec<(&str, bool)> = modules
        .iter()
        .flat_map(|(_, fns)| {
            fns.iter()
                .flat_map(|f| f.runs.iter().map(move |_| (f.kind.as_str(), f.all_ub)))
        })
        .collect();
    assert_eq!(kinds.len(), reports.len());
    for ((kind, all_ub), r) in kinds.iter().zip(&reports) {
        match &r.comparison {
            Comparison::Agree => {
                if r.rust.class() == "ok" {
                    *kinds_ok.get_mut(*kind).expect("a listed kind") += 1;
                }
                if *all_ub && r.rust.class() != "ub" {
                    failures.push(format!("{kind}: expected ub on both, got {:?}", r.rust));
                }
            }
            other => failures.push(format!(
                "{kind}: {} fn {:?} args {:?}: {other:?}\n    rust: {:?}\n    lean: {:?}",
                r.label, r.func, r.args, r.rust, r.lean
            )),
        }
    }
    let ub_kinds: Vec<&str> = modules
        .iter()
        .flat_map(|(_, fns)| fns.iter().filter(|f| f.all_ub).map(|f| f.kind.as_str()))
        .collect();
    for (kind, ok) in &kinds_ok {
        if *ok == 0 && !ub_kinds.contains(&kind.as_str()) {
            failures.push(format!(
                "{kind}: no run reached ok on both engines (vacuous row)"
            ));
        }
    }
    eprintln!(
        "residue rows: {} runs, ok-by-kind {kinds_ok:?}",
        reports.len()
    );
    assert!(
        failures.is_empty(),
        "{} residue check(s) failed: a negative integer literal means one thing to the \
         reference interpreter and another to the Lean model.\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Every integer constant binds its RESIDUE in the Lean model, as a parameter
/// and an operation result already do: negative literals in both operand
/// positions of every integer `BinOp` and `ICmpOp`, through every cast that
/// reads the operand's bits, the switch case scan (scrutinee a parameter, a
/// constant and an operation result), the module-context lanes (enum tag,
/// tuple, array, vector, global initializer), the two sign-reading consumers
/// (GEP index, alloca / heap-alloc count) on a signed operand, `CmpXchg`'s
/// comparison, and a store / load guard. Measured red before the rule on the
/// unsigned compares, `udiv` / `urem` / `lshr` / `rotr` with the literal on
/// either side, the shift-amount guard (`shl x, -1` was defined in Lean),
/// `zext` / `uitofp` / `inttoptr`, the switch on a parameter or an operation
/// result, the enum tag, the tuple / array / vector lanes, GEP and the
/// allocation count on a parameter, and `CmpXchg`.
#[test]
fn negative_literal_constants_agree_across_engines() {
    hold_residue_rows(&[residue_arith_module(), residue_misc_module()]);
}

/// Allocation and GEP magnitudes use the original SSA declaration. These
/// formerly divergent cells are decided agreement controls; wide operands,
/// both targets and every cold codec have a separate 9,040-run corpus.
#[derive(Clone, Copy, Debug)]
enum TypedMagnitudeCell {
    /// `a = alloca i8; gep i8, a, const u64 2^63; ret 7`.
    GepU64TopBit,
    /// `alloca i8, count const u32 2^31; ret 7`.
    AllocaU32TopBit,
    /// `heap_alloc RustHeap i8, count const u32 2^31; ret 7`.
    HeapAllocU32TopBit,
    /// Control: `gep i8, a, const i64 -1` — UB on both.
    GepI64NegativeControl,
    /// Control: `alloca i8, count const i32 -1` — UB on both.
    AllocaI32NegativeControl,
    /// Control: `gep i8, a, const u64 1` — ok on both.
    GepU64SmallControl,
}

const TYPED_MAGNITUDE_CELLS: &[(TypedMagnitudeCell, Expect)] = &[
    (TypedMagnitudeCell::GepU64TopBit, Expect::I32(7)),
    (TypedMagnitudeCell::AllocaU32TopBit, Expect::I32(7)),
    (TypedMagnitudeCell::HeapAllocU32TopBit, Expect::I32(7)),
    (
        TypedMagnitudeCell::GepI64NegativeControl,
        Expect::Ub("negative index"),
    ),
    (
        TypedMagnitudeCell::AllocaI32NegativeControl,
        Expect::Ub("count must be positive"),
    ),
    (TypedMagnitudeCell::GepU64SmallControl, Expect::I32(7)),
];

fn typed_magnitude_module(cells: &[(TypedMagnitudeCell, Expect)]) -> (Module, Vec<FuncId>) {
    use TypedMagnitudeCell as C;
    let mut mb = ModuleBuilder::new("w5b_typed_magnitude");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut ids = Vec::new();
    let mut counted_allocas = Vec::new();
    for (i, (cell, _)) in cells.iter().enumerate() {
        let mut fb = mb.function(format!("cell{i}_{cell:?}"), ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        match cell {
            C::GepU64TopBit | C::GepI64NegativeControl | C::GepU64SmallControl => {
                let a = fb.alloca(Ty::I8);
                let i = match cell {
                    C::GepU64TopBit => fb.iconst(Ty::U64, 1i128 << 63),
                    C::GepI64NegativeControl => fb.iconst(Ty::I64, -1),
                    _ => fb.iconst(Ty::U64, 1),
                };
                let _p = fb.gep(Ty::I8, a, vec![i]);
            }
            C::AllocaU32TopBit | C::HeapAllocU32TopBit | C::AllocaI32NegativeControl => {
                let n = match cell {
                    C::AllocaI32NegativeControl => fb.iconst(Ty::I32, -1),
                    _ => fb.iconst(Ty::U32, 1i128 << 31),
                };
                let _p = fb.heap_alloc(Ty::I8, Some(n), None, AllocOrigin::RustHeap);
                if !matches!(cell, C::HeapAllocU32TopBit) {
                    counted_allocas.push(i);
                }
            }
        }
        let seven = fb.iconst(Ty::I32, 7);
        fb.ret(vec![seven]);
        ids.push(fb.build());
    }
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    for i in counted_allocas {
        for node in &mut module.functions[i].blocks[0].body {
            if let trust_ir::Inst::HeapAlloc {
                ty, count, align, ..
            } = &node.inst
            {
                node.inst = trust_ir::Inst::Alloca {
                    ty: ty.clone(),
                    count: *count,
                    align: *align,
                };
            }
        }
    }
    let errs = trust_ir_build::validate_module(&module);
    assert!(
        errs.is_empty(),
        "every typed-magnitude cell is well-formed: {errs:?}"
    );
    (module, ids)
}

#[test]
fn typed_memory_operand_signedness_agrees() {
    let (module, ids) = typed_magnitude_module(TYPED_MAGNITUDE_CELLS);
    check_decided(
        "typed allocation/GEP magnitude",
        &module,
        &ids,
        TYPED_MAGNITUDE_CELLS,
    );
}

/// The measured zero-sized counterexamples plus both representations of the
/// largest valid u64 operand, at both target widths. A zero byte scale cannot
/// erase conversion overflow, and wasm32 cannot cap the operand to 32 bits.
#[test]
fn zero_sized_memory_operands_obey_u64_domain_at_both_targets() {
    for bits in [32, 64] {
        let target = trust_ir::TargetInfo {
            triple: if bits == 32 {
                "wasm32-unknown-unknown"
            } else {
                "aarch64-apple-darwin"
            }
            .into(),
            pointer_size: bits / 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
        };
        let mut mb = ModuleBuilder::new_with_target_info(format!("memory_operand_{bits}"), target);
        let sig = mb.add_func_type(vec![], vec![Ty::I32]);
        let mut ids = Vec::new();
        let mut cells = Vec::new();
        let mut stack = Vec::new();
        for (label, ty, value, expected) in [
            (
                "i128_over_u64",
                Ty::I128,
                1i128 << 64,
                Expect::Ub("does not fit u64"),
            ),
            (
                "u128_over_u64",
                Ty::U128,
                1i128 << 64,
                Expect::Ub("does not fit u64"),
            ),
            ("u64_wide_valid", Ty::U64, 1i128 << 32, Expect::I32(7)),
            ("i8_negative", Ty::I8, -1, Expect::Ub("")),
            ("u8_top_bit", Ty::U8, 255, Expect::I32(7)),
            ("u128_small", Ty::U128, 127, Expect::I32(7)),
            ("u64_max", Ty::U64, u64::MAX as i128, Expect::I32(7)),
            (
                "u128_at_u64_max",
                Ty::U128,
                u64::MAX as i128,
                Expect::I32(7),
            ),
        ] {
            for operation in ["alloca", "heap_alloc", "gep"] {
                let name = format!("{label}_{operation}");
                let mut fb = mb.function(name.clone(), sig);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                let count = fb.iconst(ty.clone(), value);
                if operation == "gep" {
                    let ptr = fb.alloca(Ty::Unit);
                    fb.gep(Ty::Unit, ptr, vec![count]);
                } else {
                    fb.heap_alloc(Ty::Unit, Some(count), None, AllocOrigin::RustHeap);
                }
                let answer = fb.iconst(Ty::I32, 7);
                fb.ret(vec![answer]);
                let fid = fb.build();
                if operation == "alloca" {
                    stack.push(fid);
                }
                ids.push(fid);
                cells.push((name, expected));
            }
        }
        let mut module = mb.build().expect("valid counted allocation source");
        for fid in stack {
            let function = module.functions.iter_mut().find(|f| f.id == fid).unwrap();
            for node in &mut function.blocks[0].body {
                if let trust_ir::Inst::HeapAlloc {
                    ty, count, align, ..
                } = &node.inst
                {
                    node.inst = trust_ir::Inst::Alloca {
                        ty: ty.clone(),
                        count: *count,
                        align: *align,
                    };
                }
            }
        }
        assert!(trust_ir_build::validate_module(&module).is_empty());
        assert_eq!(ids.len(), 24);
        check_decided(
            &format!("zero-size memory operands/{bits}"),
            &module,
            &ids,
            &cells,
        );
    }
}

// ---------------------------------------------------------------------------
// The x86-64 vector-compare cells: both engines and the ONE statement
// ---------------------------------------------------------------------------

/// `{0, 1, 2, -1, -2, MIN, MIN+1, MAX, MAX-1}` at `bits`, as lane PATTERNS.
fn cell_edges(bits: u32) -> [u128; 9] {
    let ones = if bits == 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    };
    let min = 1u128 << (bits - 1);
    [0, 1, 2, ones, ones - 1, min, min + 1, min - 1, min - 2]
}

/// Every x86-64 vector-compare cell (the four `chc_x86` shapes x every
/// `ICmpOp`) runs through BOTH engines at EVERY lane type of its width the
/// validator admits, signed and unsigned (`common::x86_cell_lane_tys`: a cell
/// is keyed by lane width and count alone, so `<4 x u32>` is a lane type of
/// the same cells as `<4 x i32>`): from scalar-lane parameters, and as a twin
/// whose left operand is a `Const` vector of edge patterns (the constant path
/// a negative lane took before the residue rule). The engines must agree with
/// no ledger entry, and the interpreter's lanes must be the ONE statement's
/// (`trust_ir::bv_meaning::vector_icmp` over the lane bits, lane 0 least
/// significant). Red before the residue rule on the constant twin (all four
/// signed shapes); red again with only the vector-lane binding of the bare
/// `Const` step reverted; and red in 1580 of 3160 runs, every unsigned-lane
/// run `unsupported vector_shape` in Lean, while the Lean shape checks listed
/// only the signed lane types (`Ty.executableIntLane?` now states them once).
#[test]
fn vector_icmp_cells_agree_across_engines_and_with_the_statement() {
    use trust_ir::bv_meaning::{BvVector, Concrete, vector_icmp};
    use trust_ir::constant::Constant;
    use trust_ir::inst::ICmpOp;

    const OPS: [ICmpOp; 10] = [
        ICmpOp::Eq,
        ICmpOp::Ne,
        ICmpOp::Ult,
        ICmpOp::Ule,
        ICmpOp::Ugt,
        ICmpOp::Uge,
        ICmpOp::Slt,
        ICmpOp::Sle,
        ICmpOp::Sgt,
        ICmpOp::Sge,
    ];
    // (module, [(op, function, lhs-const lanes, runs)]) per shape.
    type CellRun = (
        ICmpOp,
        FuncId,
        Option<Vec<u128>>,
        Vec<(Vec<u128>, Vec<u128>)>,
    );
    let mut shapes: Vec<(Ty, u32, u32, Module, Vec<CellRun>)> = Vec::new();
    let descriptors = trust_ir::chc_x86_hardware_vector_contract_descriptors();
    assert!(!descriptors.is_empty(), "the chc_x86 descriptors");
    let cell_tys = descriptors.iter().flat_map(|d| {
        common::x86_cell_lane_tys(d.element_bits, d.lane_count)
            .into_iter()
            .map(move |elem| (elem, d.element_bits, d.lane_count))
    });
    for (elem, bits, count) in cell_tys {
        let vty = Ty::Vector(Box::new(elem.clone()), count);
        let mask_ty = Ty::Vector(Box::new(Ty::Bool), count);
        let edges = cell_edges(bits);
        // The edge pairs, each pair at a lane that rotates with the batch.
        let pairs: Vec<(u128, u128)> = edges
            .iter()
            .flat_map(|a| edges.iter().map(move |b| (*a, *b)))
            .collect();
        let n = count as usize;
        let batches: Vec<(Vec<u128>, Vec<u128>)> = pairs
            .chunks(n)
            .enumerate()
            .map(|(k, chunk)| {
                let (mut l, mut r) = (vec![0u128; n], vec![0u128; n]);
                for (slot, (a, b)) in chunk.iter().enumerate() {
                    l[(slot + k) % n] = *a;
                    r[(slot + k) % n] = *b;
                }
                (l, r)
            })
            .collect();
        let const_lhs: Vec<u128> = (0..n).map(|i| edges[i % edges.len()]).collect();
        let mut mb = ModuleBuilder::new(format!("w5b_icmp_cells_v{count}_{elem}"));
        let both_ft = mb.add_func_type(vec![elem.clone(); 2 * n], vec![mask_ty.clone()]);
        let rhs_ft = mb.add_func_type(vec![elem.clone(); n], vec![mask_ty.clone()]);
        let mut cells: Vec<CellRun> = Vec::new();
        for op in OPS {
            for lhs_const in [false, true] {
                let ft = if lhs_const { rhs_ft } else { both_ft };
                let mut fb = mb.function(
                    format!("{}_{op}", if lhs_const { "const" } else { "param" }),
                    ft,
                );
                let entry = fb.create_block();
                let params: Vec<_> = (0..if lhs_const { n } else { 2 * n })
                    .map(|_| fb.add_block_param(entry, elem.clone()))
                    .collect();
                fb.switch_to_block(entry);
                let vector_of =
                    |fb: &mut trust_ir_build::FunctionBuilder<'_>,
                     lanes: &[trust_ir::value::ValueId]| {
                        let mut v = fb.const_value(
                            vty.clone(),
                            Constant::Vector((0..n).map(|_| Constant::Int(0)).collect()),
                        );
                        for (i, lane) in lanes.iter().enumerate() {
                            let idx = fb.iconst(Ty::I64, i as i128);
                            v = fb.insert_element(vty.clone(), v, idx, *lane);
                        }
                        v
                    };
                let (lhs, rhs) = if lhs_const {
                    let l = fb.const_value(
                        vty.clone(),
                        Constant::Vector(
                            const_lhs
                                .iter()
                                .map(|p| {
                                    Constant::Int(common::x86_cell_lane_value(&elem, bits, *p))
                                })
                                .collect(),
                        ),
                    );
                    (l, vector_of(&mut fb, &params))
                } else {
                    let (l, r) = params.split_at(n);
                    (vector_of(&mut fb, l), vector_of(&mut fb, r))
                };
                let m = fb.icmp(op, vty.clone(), lhs, rhs);
                fb.ret(vec![m]);
                cells.push((
                    op,
                    fb.build(),
                    lhs_const.then(|| const_lhs.clone()),
                    batches.clone(),
                ));
            }
        }
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let errs = trust_ir_build::validate_module(&module);
        assert!(errs.is_empty(), "<{count} x {elem}>: {errs:?}");
        shapes.push((elem, bits, count, module, cells));
    }

    // The statement's lanes, from the lane patterns (lane 0 least significant).
    let stated = |bits: u32, count: u32, op: ICmpOp, l: &[u128], r: &[u128]| {
        let pack = |lanes: &[u128]| {
            lanes
                .iter()
                .enumerate()
                .fold(0u128, |acc, (i, p)| acc | (p << (i as u32 * bits)))
        };
        let mut c = Concrete;
        let lb = c.bv_const(pack(l), bits * count);
        let rb = c.bv_const(pack(r), bits * count);
        vector_icmp(&mut c, op, bits, count, &lb, &rb)
    };
    let args_of = |elem: &Ty, bits: u32, lanes: &[u128]| -> Vec<InterpretValue> {
        lanes
            .iter()
            .map(|p| {
                InterpretValue::int(elem.clone(), common::x86_cell_lane_value(elem, bits, *p))
                    .unwrap()
            })
            .collect()
    };
    let mut failures = Vec::new();
    let mut runs_per_shape = Vec::new();
    for (elem, bits, count, module, cells) in &shapes {
        let mut runs = Vec::new();
        for (op, f, const_lhs, batches) in cells {
            for (l, r) in batches {
                let lhs = const_lhs.as_deref().unwrap_or(l);
                let mut args = if const_lhs.is_some() {
                    Vec::new()
                } else {
                    args_of(elem, *bits, l)
                };
                args.extend(args_of(elem, *bits, r));
                let rust = canonical_verdict(run_rust(module, *f, &args));
                let expected = Verdict::Ok(vec![Val::Vector(
                    stated(*bits, *count, *op, lhs, r)
                        .into_iter()
                        .map(Val::Bool)
                        .collect(),
                )]);
                if rust != expected {
                    failures.push(format!(
                        "<{count} x {elem}> icmp {op} {}: interpreter {rust:?}, statement {expected:?}",
                        if const_lhs.is_some() { "(const lhs)" } else { "" }
                    ));
                }
                runs.push((*f, args));
            }
        }
        runs_per_shape.push(runs);
    }
    assert!(
        failures.is_empty(),
        "the interpreter is not the statement:\n{}",
        failures.join("\n")
    );
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<Batch<'_>> = shapes
        .iter()
        .zip(runs_per_shape)
        .map(|((elem, _, count, module, _), runs)| Batch {
            label: format!("<{count} x {elem}> icmp cells"),
            module,
            runs,
        })
        .collect();
    let t = tally(&differential(exe, &batches));
    assert_no_mismatch(&t, "x86-64 vector-compare cells");
    assert!(
        t.unsupported.is_empty(),
        "every cell executes in both engines, none is ledgered: {:?}",
        t.unsupported
    );
}

// ---------------------------------------------------------------------------
// Amendment D (`docs/SPEC_RATIFICATIONS.md` §20): a drop is a call of its
// type's glue, in both engines. A DECIDED matrix, outside the seeded
// `UNSUPPORTED_LEDGER`: every cell has the verdict class both engines must
// give, and every non-`unsupported` cell must AGREE (values compared, panic
// messages compared message for message).
// ---------------------------------------------------------------------------

/// The drop-glue cells: (cell, expected class, expected `i32` result for an
/// `ok` cell).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DropCell {
    /// `drop Counter` over a cell holding 7: the glue adds 1 → 8.
    Resolved,
    /// `drop Outer`, whose glue drops a `Counter` (nested) → 8.
    Nested,
    /// A `Node` whose glue counts its place down and drops a `Node` there
    /// again until it reaches 0 (recursion through the table) → 0.
    Recursive,
    /// `drop First; drop Second` (glues write x*10+1, x*10+2) over 0 → 12.
    Order,
    /// `drop Counter` under a flag (`CondBr`), the flag TRUE → 8.
    FlagTaken,
    /// The same, the flag FALSE → 7.
    FlagNotTaken,
    /// `drop_invoke Counter` to its normal edge → 8.
    DropInvokeNormal,
    /// A glue whose check fails: the panic propagates out of the drop.
    PanickingGlue,
    /// A drop at a type with no row: unsupported in both engines.
    Unresolved,
    /// A drop of a poison (`undef`) pointer: UB at the glue boundary.
    PoisonPointer,
}

const DROP_CELLS: &[(DropCell, &str, i128)] = &[
    (DropCell::Resolved, "ok", 8),
    (DropCell::Nested, "ok", 8),
    (DropCell::Recursive, "ok", 0),
    (DropCell::Order, "ok", 12),
    (DropCell::FlagTaken, "ok", 8),
    (DropCell::FlagNotTaken, "ok", 7),
    (DropCell::DropInvokeNormal, "ok", 8),
    (DropCell::PanickingGlue, "panic", 0),
    (DropCell::Unresolved, "unsupported", 0),
    (DropCell::PoisonPointer, "ub", 0),
];

/// One module: structs `Counter`, `Outer`, `Node`, `First`, `Second`,
/// `Panics`, `Orphan` (no glue); their glues; one `(flag: bool) -> i32`
/// function per cell.
fn drop_glue_matrix_module() -> (Module, Vec<FuncId>) {
    use trust_ir::ty::{FieldDef, StructDef};
    use trust_ir::value::StructId;
    let mut mb = ModuleBuilder::new("w5b_drop_glue");
    let mut tys = Vec::new();
    for (i, name) in [
        "Counter", "Outer", "Node", "First", "Second", "Panics", "Orphan",
    ]
    .iter()
    .enumerate()
    {
        tys.push(Ty::Struct(mb.add_struct(StructDef {
            id: StructId::new(i as u32),
            name: (*name).into(),
            fields: vec![FieldDef {
                name: "f".into(),
                ty: Ty::Ptr,
                offset: None,
            }],
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        })));
    }
    let [counter, outer, node, first, second, panics, orphan] =
        <[Ty; 7]>::try_from(tys).expect("seven struct types");
    let glue_ty = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let add_glue = |mb: &mut ModuleBuilder,
                    name: &str,
                    body: &dyn Fn(
        &mut trust_ir_build::FunctionBuilder<'_>,
        trust_ir::value::ValueId,
    )| {
        let mut fb = mb.function(name, glue_ty);
        let b0 = fb.create_block();
        let p = fb.add_block_param(b0, Ty::Ptr);
        fb.switch_to_block(b0);
        body(&mut fb, p);
        fb.build()
    };
    // x * 10 + d over the i32 at p (d = 0 means "+ 1", the counter).
    let digit = |d: i128| {
        move |fb: &mut trust_ir_build::FunctionBuilder<'_>, p: trust_ir::value::ValueId| {
            let x = fb.load(Ty::I32, p);
            let y = if d == 0 {
                let one = fb.iconst(Ty::I32, 1);
                fb.add(Ty::I32, x, one)
            } else {
                let ten = fb.iconst(Ty::I32, 10);
                let t = fb.binop(trust_ir::inst::BinOp::Mul, Ty::I32, x, ten);
                let dd = fb.iconst(Ty::I32, d);
                fb.add(Ty::I32, t, dd)
            };
            fb.store(Ty::I32, p, y);
            fb.ret(vec![]);
        }
    };
    let g_counter = add_glue(&mut mb, "drop_counter", &digit(0));
    let counter_for_outer = counter.clone();
    let g_outer = add_glue(&mut mb, "drop_outer", &move |fb, p| {
        fb.drop(counter_for_outer.clone(), p);
        fb.ret(vec![]);
    });
    // drop_node(p): if *p != 0 { *p -= 1; drop Node, p }. Pointer-free, so
    // the cell is an `i32` both engines compare natively.
    let node_for_glue = node.clone();
    let g_node = add_glue(&mut mb, "drop_node", &move |fb, p| {
        let c = fb.load(Ty::I32, p);
        let zero = fb.iconst(Ty::I32, 0);
        let is_zero = fb.icmp(trust_ir::ICmpOp::Eq, Ty::I32, c, zero);
        let recurse = fb.create_block();
        let done = fb.create_block();
        fb.condbr(is_zero, done, vec![], recurse, vec![]);
        fb.switch_to_block(recurse);
        let one = fb.iconst(Ty::I32, 1);
        let d = fb.binop(trust_ir::inst::BinOp::Sub, Ty::I32, c, one);
        fb.store(Ty::I32, p, d);
        fb.drop(node_for_glue.clone(), p);
        fb.ret(vec![]);
        fb.switch_to_block(done);
        fb.ret(vec![]);
    });
    let g_first = add_glue(&mut mb, "drop_first", &digit(1));
    let g_second = add_glue(&mut mb, "drop_second", &digit(2));
    let g_panics = add_glue(&mut mb, "drop_panics", &|fb, _p| {
        let no = fb.const_value(Ty::Bool, trust_ir::Constant::Bool(false));
        fb.assert_kind(no, trust_ir::AssertKind::NullPtr);
        fb.ret(vec![]);
    });
    for (ty, glue) in [
        (counter.clone(), g_counter),
        (outer.clone(), g_outer),
        (node.clone(), g_node),
        (first.clone(), g_first),
        (second.clone(), g_second),
        (panics.clone(), g_panics),
    ] {
        mb.set_drop_glue(ty, glue).expect("one row per type");
    }

    let ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::I32]);
    let mut ids = Vec::new();
    for (i, (cell, _, _)) in DROP_CELLS.iter().enumerate() {
        let mut fb = mb.function(format!("cell{i}_{cell:?}"), ft);
        let entry = fb.create_block();
        let flag = fb.add_block_param(entry, Ty::Bool);
        fb.switch_to_block(entry);
        let p = fb.alloca(Ty::I32);
        let init = fb.iconst(Ty::I32, if *cell == DropCell::Order { 0 } else { 7 });
        fb.store(Ty::I32, p, init);
        match cell {
            DropCell::Resolved => fb.drop(counter.clone(), p),
            DropCell::Nested => fb.drop(outer.clone(), p),
            // Seven levels of glue through the table, counting 7 down to 0.
            DropCell::Recursive => fb.drop(node.clone(), p),
            DropCell::Order => {
                fb.drop(first.clone(), p);
                fb.drop(second.clone(), p);
            }
            DropCell::FlagTaken | DropCell::FlagNotTaken => {
                let taken = fb.create_block();
                let join = fb.create_block();
                fb.condbr(flag, taken, vec![], join, vec![]);
                fb.switch_to_block(taken);
                fb.drop(counter.clone(), p);
                fb.br(join, vec![]);
                fb.switch_to_block(join);
            }
            DropCell::DropInvokeNormal => {
                let normal = fb.create_block();
                let pad = fb.create_block();
                fb.drop_invoke(counter.clone(), p, normal, vec![], pad);
                fb.switch_to_block(pad);
                let (exn, _) = fb.landingpad(true, vec![]);
                fb.resume(exn);
                fb.switch_to_block(normal);
            }
            DropCell::PanickingGlue => fb.drop(panics.clone(), p),
            DropCell::Unresolved => fb.drop(orphan.clone(), p),
            DropCell::PoisonPointer => {
                let poison = fb.undef(Ty::Ptr);
                fb.drop(counter.clone(), poison);
            }
        }
        let v = fb.load(Ty::I32, p);
        fb.ret(vec![v]);
        ids.push(fb.build());
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errs = trust_ir_build::validate_module(&module);
    assert!(
        errs.is_empty(),
        "every drop-glue cell is well-formed: {errs:?}"
    );
    (module, ids)
}

#[test]
fn drop_glue_execution_agrees_across_engines() {
    let (module, ids) = drop_glue_matrix_module();
    let args = |cell: DropCell| vec![InterpretValue::bool(cell != DropCell::FlagNotTaken)];

    // The interpreter half runs without `lake`.
    for ((cell, class, value), f) in DROP_CELLS.iter().zip(&ids) {
        let rust = canonical_verdict(run_rust(&module, *f, &args(*cell)));
        assert_eq!(rust.class(), *class, "interpreter, {cell:?}: {rust:?}");
        if *class == "ok" {
            assert_eq!(rust, i32_verdict(*value as i32), "{cell:?}");
        }
    }

    let Oracle::Ready(exe) = oracle() else { return };
    let batches = vec![Batch {
        label: "drop-glue matrix (decided)".into(),
        module: &module,
        runs: DROP_CELLS
            .iter()
            .zip(&ids)
            .map(|((cell, _, _), f)| (*f, args(*cell)))
            .collect(),
    }];
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), DROP_CELLS.len());
    for ((cell, class, _), r) in DROP_CELLS.iter().zip(&reports) {
        assert_eq!(
            r.lean.class(),
            *class,
            "{cell:?}: expected verdict class {class} (rust {:?}; lean {:?})",
            r.rust,
            r.lean
        );
        if *class == "unsupported" {
            // Both engines refuse an unresolved drop by name.
            assert_eq!(r.rust.class(), "unsupported", "{cell:?}: {:?}", r.rust);
        } else {
            assert_eq!(
                r.comparison,
                Comparison::Agree,
                "{cell:?}: the engines must agree (rust {:?}; lean {:?})",
                r.rust,
                r.lean
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Amendment D, Part 2 (§21): unwinding as an exit, in both engines
// ---------------------------------------------------------------------------

/// The decided unwind matrix (`common/unwind_matrix.rs`) under BOTH
/// strategies, in both engines: every cell, including typed indirect calls,
/// must reach
/// its decided verdict class in each engine, and the engines must agree —
/// values for values, panic MESSAGE and site for panics. An escaping
/// unwinding is the original raise's panic in both; a typed catch is refused
/// by name in both. The request without a `panic_strategy` field is the
/// `abort` run, so an older oracle and request keep their meaning.
#[test]
fn unwind_paths_agree_message_for_message() {
    use common::unwind_matrix::{CELLS, Expect};
    let (module, ids) = common::unwind_matrix::module();
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "the matrix validates: {errors:?}");
    let class = |expect: Expect| match expect {
        Expect::Ok(_) => "ok",
        Expect::Panic { .. } => "panic",
        Expect::Ub => "ub",
        Expect::Unsupported => "unsupported",
    };
    assert_eq!(ids.len(), CELLS.len(), "every decided cell has a function");
    let cells: Vec<_> = CELLS.iter().zip(&ids).collect();
    assert!(
        cells.len() >= 17,
        "the complete unwind matrix is not vacuous"
    );

    // The interpreter half runs without `lake`.
    for strategy in [PanicStrategy::Abort, PanicStrategy::Unwind] {
        for (cell, f) in &cells {
            let expect = if strategy == PanicStrategy::Abort {
                cell.abort
            } else {
                cell.unwind
            };
            let rust = canonical_verdict(run_rust_under(&module, **f, &[], strategy));
            assert_eq!(
                rust.class(),
                class(expect),
                "interpreter, {} under {strategy:?}: {rust:?}",
                cell.name
            );
        }
    }

    let Oracle::Ready(exe) = oracle() else { return };
    let batch = Batch {
        label: "unwind matrix (decided)".into(),
        module: &module,
        runs: cells.iter().map(|(_, f)| (**f, Vec::new())).collect(),
    };
    for (strategy, field) in [
        (PanicStrategy::Abort, None),
        (PanicStrategy::Abort, Some(PanicStrategy::Abort)),
        (PanicStrategy::Unwind, Some(PanicStrategy::Unwind)),
    ] {
        let lean = run_lean_under(exe, std::slice::from_ref(&batch), field);
        assert_eq!(lean.len(), 1);
        for ((cell, f), lean) in cells.iter().zip(&lean[0]) {
            let expect = if strategy == PanicStrategy::Abort {
                cell.abort
            } else {
                cell.unwind
            };
            let rust = canonical_verdict(run_rust_under(&module, **f, &[], strategy));
            let lean = canonical_verdict(lean.clone());
            assert_eq!(
                lean.class(),
                class(expect),
                "Lean, {} under {strategy:?} (request field {field:?}): rust {rust:?}, lean {lean:?}",
                cell.name
            );
            if expect != Expect::Unsupported {
                assert_eq!(
                    compare(&rust, &lean),
                    Comparison::Agree,
                    "{} under {strategy:?}: rust {rust:?} vs lean {lean:?}",
                    cell.name
                );
            }
        }
    }
}

/// Fifty-two decided target-bound runs cover both model widths, actual byte
/// images/provenance and bounds. No existing corpus/coverage ledger changes.
#[test]
fn selected_target_models_agree_on_images_steps_and_refusals() {
    use common::target_model::{self, CELLS, Cell};
    let modules: Vec<_> = [32, 64]
        .into_iter()
        .flat_map(|bits| {
            CELLS.iter().map(move |&cell| {
                let (module, fid) = target_model::module(cell, bits);
                (bits, cell, module, fid)
            })
        })
        .collect();
    assert_eq!(modules.len(), 52);
    for (_, cell, module, _) in &modules {
        assert!(
            trust_ir_build::validate_module(module).is_empty(),
            "{cell:?}"
        );
        assert_eq!(
            module.check_conformance_subset().is_ok(),
            cell.in_subset(),
            "{cell:?}"
        );
        assert_eq!(
            module_subset_violations(module).is_empty(),
            cell.in_subset(),
            "{cell:?}"
        );
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(bits, cell, module, fid)| Batch {
            label: format!("{bits}/{cell:?}"),
            module,
            runs: vec![(
                *fid,
                match cell {
                    Cell::UnsignedInput => vec![InterpretValue::int(Ty::Usize, 2).unwrap()],
                    Cell::SignedInput => vec![InterpretValue::int(Ty::Isize, -1).unwrap()],
                    _ => vec![],
                },
            )],
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 52);
    let tally = tally(&reports);
    assert_no_mismatch(&tally, "selected byte models");
    assert_eq!(
        tally.unsupported,
        BTreeMap::new(),
        "all 52 target cells execute, including the six formerly refused legacy 64-bit layouts"
    );
    assert_eq!(tally.vacuous, 0);
    for (report, (bits, cell, _, _)) in reports.iter().zip(&modules) {
        if let Some(raw) = cell.expected(*bits) {
            let expected = Verdict::Ok(vec![Val::Int { width: 64, raw }]);
            assert_eq!(
                canonical_verdict(report.rust.clone()),
                expected,
                "{bits}/{cell:?}"
            );
            assert_eq!(
                canonical_verdict(report.lean.clone()),
                expected,
                "{bits}/{cell:?}"
            );
        } else {
            assert_eq!(
                report.rust.class(),
                cell.refusal(*bits).unwrap(),
                "{bits}/{cell:?}"
            );
            assert_eq!(
                report.lean.class(),
                cell.refusal(*bits).unwrap(),
                "{bits}/{cell:?}"
            );
        }
    }
}

/// Target refusal is per batch: an unsupported model must not erase the
/// adjacent admitted runs or their denominator. Entry overflow is refused,
/// never narrowed modulo2^32 into a successful call.
#[test]
fn target_selection_and_entry_width_refusals_keep_all_results() {
    use common::target_model::{self, Cell};
    let (module, fid) = target_model::module(Cell::UnsignedInput, 32);
    let mut invalid = module.clone();
    invalid.target_info.as_mut().unwrap().pointer_size = u32::MAX;
    let args = || vec![InterpretValue::int(Ty::Usize, 2).unwrap()];
    let Oracle::Ready(exe) = oracle() else { return };
    let batches = [
        Batch {
            label: "before".into(),
            module: &module,
            runs: vec![(fid, args())],
        },
        Batch {
            label: "invalid target".into(),
            module: &invalid,
            runs: vec![(fid, args()), (fid, args())],
        },
        Batch {
            label: "after".into(),
            module: &module,
            runs: vec![(fid, args())],
        },
    ];
    let results = run_lean(exe, &batches);
    assert_eq!(results.iter().map(Vec::len).collect::<Vec<_>>(), [1, 2, 1]);
    assert_eq!(results[0], results[2]);
    assert!(results[0].iter().all(|v| v.class() == "ok"));
    assert!(
        results[1]
            .iter()
            .all(|v| matches!(v, Verdict::Unsupported(feature) if feature == "target.byte_model"))
    );
    let overflow = vec![InterpretValue::int(Ty::Usize, 1i128 << 32).unwrap()];
    let batch = Batch {
        label: "overflow".into(),
        module: &module,
        runs: vec![(fid, overflow.clone())],
    };
    assert!(matches!(
        run_rust(&module, fid, &overflow),
        Verdict::TypeError(_)
    ));
    assert!(matches!(
        &run_lean(exe, &[batch])[0][0],
        Verdict::TypeError(_)
    ));
}

/// The new32-bit entry adapter preserves mathematical signed inputs and
/// leaves every arity refusal intact; it cannot zip excess arguments away.
#[test]
fn target_entry_signed_overflow_and_arity_are_refused() {
    use common::target_model::{self, Cell};
    let (signed, sf) = target_model::module(Cell::SignedInput, 32);
    let (unsigned, uf) = target_model::module(Cell::UnsignedInput, 32);
    let signed_bad = [0x8000_0000_i128, -0x8000_0001_i128]
        .into_iter()
        .map(|n| (sf, vec![InterpretValue::int(Ty::Isize, n).unwrap()]))
        .collect::<Vec<_>>();
    let arity_bad = vec![
        (uf, vec![]),
        (
            uf,
            vec![
                InterpretValue::int(Ty::Usize, 2).unwrap(),
                InterpretValue::int(Ty::Usize, 3).unwrap(),
            ],
        ),
    ];
    let Oracle::Ready(exe) = oracle() else { return };
    let batches = [
        Batch {
            label: "signed overflow".into(),
            module: &signed,
            runs: signed_bad,
        },
        Batch {
            label: "bad arity".into(),
            module: &unsigned,
            runs: arity_bad,
        },
    ];
    let lean = run_lean(exe, &batches);
    assert_eq!(lean.iter().map(Vec::len).collect::<Vec<_>>(), [2, 2]);
    for (batch, rows) in batches.iter().zip(&lean) {
        for ((fid, args), row) in batch.runs.iter().zip(rows) {
            assert!(
                matches!(run_rust(batch.module, *fid, args), Verdict::TypeError(_)),
                "{}",
                batch.label
            );
            assert!(
                matches!(row, Verdict::TypeError(_)),
                "{}: {row:?}",
                batch.label
            );
        }
    }
}

// ---------------------------------------------------------------------------
// SemR (Trust proven-core plan, RM4): the second Lean engine, on the BINARY
// ---------------------------------------------------------------------------
//
// `lean/semr/SemR.lean` is SemR v0: trust-ir level R's syntax, a decoder of
// the binary wire image (`serialize_module`'s bytes, read by SemR's own
// decoder, not by this crate), and a step semantics, in one Lean 4.30 file
// with no `native_decide` and no `partial def`, whose theorems Clean's
// reference entry re-checks (Clean `crates/clean-olean/tests/
// semr_reference.rs`). Its executable `semr_eval` answers in the W5b verdict
// grammar, so the SAME `compare` rule holds it to the reference interpreter:
//
//   * the request is the module's binary image plus one line per run, so the
//     whole path from the artifact's bytes to the verdict is SemR's;
//   * an `unsupported` on SemR's side is coverage, ratcheted per feature by
//     `SEMR_UNSUPPORTED_LEDGER` (generator corpus) and
//     `SEMR_FIXTURE_UNSUPPORTED_LEDGER` (subset fixtures), and may only go
//     down; every other difference is a mismatch and fails the test;
//   * the decoder differential holds SemR's decoder to `deserialize_module`
//     on every one-byte mutation of corpus blobs: a blob Rust accepts SemR
//     must not call malformed, and a blob Rust refuses SemR must not decode.
//
// The SemR oracle is built with `lake build semr_eval` in `lean/semr`, whose
// `lean-toolchain` pins `leanprover/lean4:v4.30.0-rc2`; it is located and
// required exactly as the W5b oracle is (`TRUST_IR_REQUIRE_LEAN`).

/// Runs of the generator corpus SemR refused by name. Measured 2026-10-26: 0
/// — SemR v0 decodes and runs the whole corpus.
const SEMR_UNSUPPORTED_LEDGER: usize = 0;

/// Fixture runs refused by name, per `side:feature` (`rust:` rows are the
/// interpreter's own refusals, which `compare` attributes first). Measured
/// 2026-10-26 against SemR v0 (176 runs; 80 agree: 72 `ok`, 4 `panic`, 4
/// `ub`); re-measured 2026-10-27 once the decoder reads a compiled artifact's
/// side records (VF5: node proof annotations, formula-free obligations, a
/// little-endian 64-bit target): 88 agree (77 `ok`, 4 `panic`, 7 `ub`), the
/// eight target-record runs among them, and 0 mismatches. Re-measured
/// 2026-11-03 after decoding scalar catalogs, function annotations and textual
/// obligation records: 96 agree (85 `ok`, 4 `panic`, 7 `ub`), zero mismatches
/// and zero vacuous runs. Each `semr:` row is a
/// construct SemR does not decode, so the whole fixture is refused: globals,
/// explicit struct size metadata, the declared-type table and compound types
/// remain outside the fragment; metadata-free flat scalar structs decode. Typed
/// obligation bindings, proof certificates, the obligation-diagnostics sidecar,
/// function summaries,
/// module imports and evidenced body gates are proof sidecars SemR does not
/// read. Formula text and function annotations grant no authority; decoding
/// them reveals later unsupported fields in some fixtures. A `char`, borrows and a
/// 128-bit enum tag (`repr(u128)`/`repr(i128)`) are not in the fragment yet.
/// (The `enum.explicit_discriminants` row became `enum.repr128` when SemR
/// learned fieldless enums with explicit discriminants, D-2(b), 2026-10-27: the
/// same 4 runs now stop at the fixture's 128-bit tag.) The W5b oracle
/// refuses 8 of these runs (`FIXTURE_UNSUPPORTED_LEDGER`), so SemR does not yet
/// cover what the old model covers (RM4's DG-08 flip).
// The refreshed certificate_binding fixture contributes eight evidence
// refusals. Its stale predecessor failed validation and vanished from the
// subset input list; that disappearance earned no execution coverage.
const SEMR_FIXTURE_UNSUPPORTED_LEDGER: &[(&str, usize)] = &[
    ("rust:unsupported_call", 4),
    ("semr:body_gate.evidence", 8),
    ("semr:enum.repr128", 4),
    ("semr:function_summary", 4),
    ("semr:globals", 20),
    ("semr:imports", 4),
    ("semr:inst.borrow", 4),
    ("semr:obligation.binding_sort", 4),
    ("semr:obligation_diagnostics", 4),
    ("semr:proof_certificates", 4),
    ("semr:struct.size", 4),
    ("semr:ty.char", 4),
    ("semr:ty.compound", 12),
];

/// SHA-256 of the local `lean/semr/SemR.lean` used by this differential.
/// Clean's reference-entry fixture has its own historical revision and digest;
/// this local source check does not establish identity with that fixture or
/// transfer an independent kernel-replay receipt to a changed source.
const SEMR_SOURCE_SHA256: &str = "0ea0e29f2b0d70a158f0ac54725d5175b9be81f4fc5b0a4d0839e9b968ee180d";

fn semr_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean/semr")
}

/// Build `semr_eval` once per test process and return its path.
fn semr_oracle() -> &'static Oracle {
    static ORACLE: OnceLock<Result<Oracle, String>> = OnceLock::new();
    cached_oracle(&ORACLE, || {
        let require = std::env::var("TRUST_IR_REQUIRE_LEAN")
            .map(|v| v == "1")
            .unwrap_or(false);
        let Some(lake) = find_semr_lake() else {
            if require {
                return Err(
                    "TRUST_IR_REQUIRE_LEAN=1 but no `lake` was found (TRUST_IR_LAKE, \
                     $HOME/.elan/bin/lake, PATH)"
                        .to_owned(),
                );
            }
            eprintln!("SKIPPED: the SemR oracle needs `lake` (elan); none found.");
            return Ok(Oracle::Absent);
        };
        let dir = semr_dir();
        let out = lake_build_command(&lake, &dir, "semr_eval")
            .arg("PanicRelationCheck")
            .output()
            .map_err(|e| format!("cannot run {}: {e}", lake.display()))?;
        if !out.status.success() {
            return Err(format!(
                "`lake build semr_eval PanicRelationCheck` failed in {}:\n{}\n{}",
                dir.display(),
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            ));
        }
        let exe = dir.join(".lake/build/bin/semr_eval");
        if !exe.is_file() {
            return Err(format!(
                "lake reported success but {} is missing",
                exe.display()
            ));
        }
        Ok(Oracle::Ready(exe))
    })
}

/// The differential's actual SemR source has its recorded digest (no `lake`
/// needed). Independent Clean replay retains its separate source identity.
#[test]
fn semr_source_digest_is_pinned() {
    use sha2::{Digest, Sha256};
    let path = semr_dir().join("SemR.lean");
    let bytes = fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let hex: String = Sha256::digest(&bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    assert_eq!(
        hex, SEMR_SOURCE_SHA256,
        "lean/semr/SemR.lean changed: review and update the local SEMR_SOURCE_SHA256; \
         any independent Clean fixture/replay claim must bind its own exact source"
    );
}

/// SemR's spelling of an integer type (`intTyOfCode` in `lean/semr/Main.lean`).
fn semr_int_code(ty: &Ty) -> u32 {
    match ty {
        Ty::I8 => 0,
        Ty::I16 => 1,
        Ty::I32 => 2,
        Ty::I64 => 3,
        Ty::I128 => 4,
        Ty::Isize => 5,
        Ty::U8 => 6,
        Ty::U16 => 7,
        Ty::U32 => 8,
        Ty::U64 => 9,
        Ty::U128 => 10,
        Ty::Usize => 11,
        other => panic!("not an integer argument type: {other}"),
    }
}

fn semr_arg(v: &InterpretValue) -> String {
    match &v.kind {
        InterpretValueKind::Int(i) => format!("i{}:{}:{}", semr_int_code(&v.ty), i.bits, i.raw),
        InterpretValueKind::Bool(b) => if *b { "b1" } else { "b0" }.to_string(),
        // A fieldless enum value: its one lane is the tag.
        InterpretValueKind::Aggregate(lanes) if matches!(v.ty, Ty::Enum(_)) => {
            let (Ty::Enum(eid), [tag]) = (&v.ty, lanes.as_slice()) else {
                panic!("only fieldless enum arguments are sent to SemR, got {v:?}")
            };
            let InterpretValueKind::Int(i) = &tag.kind else {
                panic!("an enum tag lane is an integer, got {tag:?}")
            };
            format!("e{}:{}:{}", eid.0, semr_int_code(&tag.ty), i.raw)
        }
        // A tensor (v67): `t<element code>:<element source bits>:<extents>:
        // <residues>`, its residues at the width they were built at (as an
        // `i<code>:<bits>:<raw>` scalar's), so SemR re-expresses a
        // pointer-width element at the target width as the interpreter's
        // entry does. An empty tensor states its type's reference width.
        InterpretValueKind::Tensor { dims, elems } => {
            let Ty::Tensor(elem, _) = &v.ty else {
                panic!("a tensor value has a tensor type, got {v:?}")
            };
            let ints: Vec<&trust_ir::InterpretInt> = elems
                .iter()
                .map(|e| match &e.kind {
                    InterpretValueKind::Int(i) => i,
                    other => panic!("a tensor element is an integer, got {other:?}"),
                })
                .collect();
            let bits = ints.first().map_or_else(
                || {
                    elem.bit_width_with(64)
                        .expect("an integer element has a width")
                },
                |i| i.bits,
            );
            assert!(
                ints.iter().all(|i| i.bits == bits),
                "a tensor's elements share one width: {v:?}"
            );
            let dims: Vec<String> = dims.iter().map(u64::to_string).collect();
            let residues: Vec<String> = ints.iter().map(|i| i.raw.to_string()).collect();
            format!(
                "t{}:{bits}:{}:{}",
                semr_int_code(elem),
                dims.join(","),
                residues.join(",")
            )
        }
        other => panic!(
            "only integer / bool / fieldless-enum / tensor arguments are sent to SemR, got {other:?}"
        ),
    }
}

/// A scratch directory unique to this process, call and `tag`, under the
/// test target's own scratch root (`CARGO_TARGET_TMPDIR`, inside the build
/// directory), removed when the guard drops — on a panic too. A process that
/// dies mid-run leaves it in the build directory, which goes with the build
/// output, never in the system temp directory.
struct SemrScratch(PathBuf);

impl SemrScratch {
    fn new(tag: &str) -> Self {
        // A per-process counter, not the thread's name: helper threads
        // (`on_a_deep_stack`) are unnamed, and two of them run at once.
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let call = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("semr-{}-{call}-{tag}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap_or_else(|e| panic!("scratch {}: {e}", dir.display()));
        SemrScratch(dir)
    }

    fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for SemrScratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn semr_verdicts(stdout: &[u8], expected: usize, what: &str) -> Vec<Verdict> {
    let text = String::from_utf8_lossy(stdout);
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(
        lines.len(),
        expected,
        "{what}: one SemR verdict per run:\n{text}"
    );
    lines
        .iter()
        .map(|l| match serde_json::from_str::<Json>(l) {
            Ok(j) if j.get("out_of_memory").is_some() => Verdict::OutOfMemory,
            Ok(j) => status_or_semr_verdict(&j),
            Err(e) => Verdict::Error(format!("SemR reply is not JSON ({e}): {l}")),
        })
        .collect()
}

/// The interpreter's verdict as the SemR differential reads it: [`rust_verdict`]
/// with two classes kept apart that the W5b rule merges — the address space
/// exhausted ([`Verdict::OutOfMemory`]) is not the instruction budget spent —
/// and a returned pointer compared by its allocation and offset
/// ([`semr_rust_val`]), never as a bare non-null pointer.
fn semr_rust_verdict(
    result: &Result<trust_ir::interpret::InterpretOutcome, InterpretError>,
) -> Verdict {
    match result {
        Ok(outcome) => {
            assert_eq!(
                outcome.host_calls, 0,
                "no host is installed, so no run can be host-assisted"
            );
            Verdict::Ok(outcome.returns.iter().map(semr_rust_val).collect())
        }
        Err(e) if e.code == InterpretErrorCode::OutOfMemory => Verdict::OutOfMemory,
        Err(_) => rust_verdict(result),
    }
}

/// [`rust_val`], with a pointer that has provenance spelled by its allocation
/// and offset (SemR's `Val.ptr alloc offset`; both engines number allocations
/// from 0 in creation order).
fn semr_rust_val(v: &InterpretValue) -> Val {
    match &v.kind {
        InterpretValueKind::Ptr(p) => Val::PtrAt {
            alloc: p.allocation,
            offset: p.offset,
        },
        InterpretValueKind::Aggregate(vs) => Val::Aggregate(vs.iter().map(semr_rust_val).collect()),
        _ => rust_val(v),
    }
}

/// SemR's verdict on each run of one module: the module goes to SemR as its
/// binary image. A module with no wire image is refused by name on SemR's
/// side (`wire_image`), since there is no level-R artifact to read.
fn run_semr(exe: &Path, batch: &Batch<'_>) -> Vec<Verdict> {
    run_semr_fuel(exe, batch, FUEL)
}

/// [`run_semr`] under instruction budget `fuel`.
fn run_semr_fuel(exe: &Path, batch: &Batch<'_>, fuel: u64) -> Vec<Verdict> {
    let blob = match trust_ir::binary::serialize_module(batch.module) {
        Ok(blob) => blob,
        Err(_) => return vec![Verdict::Unsupported("wire_image".into()); batch.runs.len()],
    };
    if batch.runs.is_empty() {
        return Vec::new();
    }
    let scratch = SemrScratch::new("run");
    let blob_path = scratch.path("module.tmbc");
    let runs_path = scratch.path("runs.txt");
    fs::write(&blob_path, &blob).expect("write SemR blob");
    let mut runs = String::new();
    for (f, args) in &batch.runs {
        runs.push_str(&format!("{fuel} {CALL_DEPTH} {}", f.0));
        for a in args {
            runs.push(' ');
            runs.push_str(&semr_arg(a));
        }
        runs.push('\n');
    }
    fs::write(&runs_path, runs.as_bytes()).expect("write SemR runs");
    let out = Command::new(exe)
        .arg(&blob_path)
        .arg(&runs_path)
        .output()
        .unwrap_or_else(|e| panic!("cannot run {}: {e}", exe.display()));
    drop(scratch);
    assert!(
        out.status.success(),
        "semr_eval exited with {}:\n{}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    semr_verdicts(&out.stdout, batch.runs.len(), &batch.label)
}

/// `compare`, with SemR's refusals attributed to `semr`, and stricter than
/// the W5b rule in two places (the plan's `prod_equiv`: UB is matched BY
/// REASON):
/// * two UB verdicts agree only when they name the same reason
///   ([`semr_ub_reason`]), so a SemR step that reaches UB for the wrong
///   reason is a mismatch, not an agreement;
/// * two type errors (a body the interpreter cannot run: a missing value,
///   block or function, a signature or arity mismatch, a missing terminator)
///   agree when they name the same error code (the text before the first
///   `:`, case and `_` aside); the W5b rule has no type-error arm at all, so
///   it could not test these paths.
fn compare_semr(rust: &Verdict, semr: &Verdict) -> Comparison {
    match (rust, semr) {
        (Verdict::Ub(a), Verdict::Ub(b)) => {
            if semr_ub_reason(a) == semr_ub_reason(b) {
                Comparison::Agree
            } else {
                Comparison::Mismatch(format!("UB reasons differ: rust {a:?} vs semr {b:?}"))
            }
        }
        (Verdict::TypeError(a), Verdict::TypeError(b)) => {
            let code = |m: &str| {
                m.split(':')
                    .next()
                    .unwrap_or_default()
                    .replace('_', "")
                    .to_lowercase()
            };
            if code(a) == code(b) {
                Comparison::Agree
            } else {
                Comparison::Mismatch(format!("type-error codes differ: rust {a:?} vs semr {b:?}"))
            }
        }
        _ => match compare(rust, semr) {
            Comparison::Unsupported("lean", f) => Comparison::Unsupported("semr", f),
            other => other,
        },
    }
}

/// The REASON a UB message names, the same key for the interpreter's text
/// and SemR's. SemR spells most reasons exactly as the interpreter does
/// (division by zero, overflow of `sdiv`/`srem`, a closed frame, executed
/// `unreachable`, a lane out of bounds, …), and the key of those is the text
/// itself. Where the interpreter's text carries operands SemR does not
/// render (the shift amount and width, the enum and variant names, the slot
/// and frame size) or a longer gloss (poison), the key is the reason and its
/// site, never the operands.
fn semr_ub_reason(message: &str) -> String {
    const POISON: &str = ": use of an uninitialized value";
    if let Some((site, _)) = message.split_once(POISON) {
        let site = match site {
            "Call arguments" | "Call returns" | "signature boundary" => "signature boundary",
            other => other,
        };
        return format!("poison at {site}");
    }
    if message.starts_with("shift amount ") && message.contains("out of range") {
        return "shift amount out of range".into();
    }
    if message.contains("belongs to no field of") {
        return "enum lane belongs to no field of the active variant".into();
    }
    for slot_op in ["BindSlot", "LoadSlot"] {
        if message.starts_with(&format!("{slot_op}: slot")) && message.contains("out of range") {
            return format!("{slot_op}: slot out of range");
        }
    }
    if message.starts_with("LoadSlot:")
        && message.contains("poison of")
        && message.contains("non-scalar")
    {
        return "LoadSlot: poison of a non-scalar type".into();
    }
    message.to_string()
}

/// Every batch through the interpreter and SemR, compared run by run.
fn semr_differential(exe: &Path, batches: &[Batch<'_>]) -> Vec<RunReport> {
    semr_differential_fuel(exe, batches, FUEL)
}

/// [`semr_differential`] with both engines under instruction budget `fuel`.
fn semr_differential_fuel(exe: &Path, batches: &[Batch<'_>], fuel: u64) -> Vec<RunReport> {
    let mut reports = Vec::new();
    for batch in batches {
        let semr = run_semr_fuel(exe, batch, fuel);
        for ((func, args), semr) in batch.runs.iter().zip(semr) {
            let interp = Interpreter::with_module(batch.module).with_options(InterpretOptions {
                fuel,
                max_call_depth: CALL_DEPTH,
                panic_strategy: PanicStrategy::Abort,
            });
            let rust = canonical_verdict(semr_rust_verdict(
                &interp.execute_func(*func, args.to_vec()),
            ));
            let semr = canonical_verdict(semr);
            let comparison = compare_semr(&rust, &semr);
            reports.push(RunReport {
                label: batch.label.clone(),
                func: *func,
                args: args.clone(),
                rust,
                lean: semr,
                comparison,
            });
        }
    }
    reports
}

fn generator_corpus() -> Vec<(u64, Module, Vec<FnSpec>)> {
    SEEDS
        .map(|seed| {
            let (module, specs) = gen_module_exec(seed);
            (seed, module, specs)
        })
        .collect()
}

fn generator_batches(modules: &[(u64, Module, Vec<FnSpec>)]) -> Vec<Batch<'_>> {
    modules
        .iter()
        .map(|(seed, module, specs)| {
            let mut arg_rng = Rng::new(seed ^ 0xA5A5_A5A5_A5A5_A5A5);
            Batch {
                label: format!("seed {seed}"),
                module,
                runs: specs
                    .iter()
                    .map(|s| (s.id, build_args(&s.params, &mut arg_rng)))
                    .collect(),
            }
        })
        .collect()
}

/// RM4's accept item: 0 disagreements between SemR's executable and the
/// reference interpreter over the generator corpus (the W5b corpus, the same
/// seeds and arguments), with SemR's refusals ratcheted.
#[test]
fn semr_generated_corpus_agrees_with_the_interpreter() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let modules = generator_corpus();
    let batches = generator_batches(&modules);
    let t = tally(&semr_differential(exe, &batches));
    assert_no_mismatch(&t, "SemR, generator corpus");
    let ok = t.agreed.get("ok").copied().unwrap_or(0);
    let ub = t.agreed.get("ub").copied().unwrap_or(0);
    assert!(ok > 300, "only {ok} runs executed to Ok in both engines");
    assert!(ub > 20, "only {ub} runs reached UB in both engines");
    let unsupported: usize = t.unsupported.values().sum();
    assert_eq!(
        unsupported, SEMR_UNSUPPORTED_LEDGER,
        "SemR coverage RATCHET: {unsupported} generator run(s) refused by name ({:?}); \
         the ledger says {SEMR_UNSUPPORTED_LEDGER}",
        t.unsupported
    );
}

/// SemR is cheap to run, so it also takes 2000 seeds past the W5b range
/// (`SEMR_WIDE_SEEDS`), the same generator and argument rule: 0
/// disagreements and 0 refusals there too.
const SEMR_WIDE_SEEDS: std::ops::RangeInclusive<u64> = 385..=2384;

#[test]
fn semr_wide_generator_corpus_agrees_with_the_interpreter() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let modules: Vec<(u64, Module, Vec<FnSpec>)> = SEMR_WIDE_SEEDS
        .map(|seed| {
            let (module, specs) = gen_module_exec(seed);
            (seed, module, specs)
        })
        .collect();
    let batches = generator_batches(&modules);
    let t = tally(&semr_differential(exe, &batches));
    assert_no_mismatch(&t, "SemR, wide generator corpus");
    assert!(t.unsupported.is_empty(), "{:?}", t.unsupported);
    let ok = t.agreed.get("ok").copied().unwrap_or(0);
    assert!(ok > 1500, "only {ok} runs executed to Ok in both engines");
}

/// The subset fixtures through SemR, refusals pinned per feature.
#[test]
fn semr_subset_fixtures_agree_with_the_interpreter() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let fixtures = subset_fixtures();
    let batches: Vec<Batch<'_>> = fixtures
        .iter()
        .enumerate()
        .map(|(i, (name, module))| Batch {
            label: format!("fixture {name}"),
            module,
            runs: module_runs(module, 4, 0x5B5B_0000 + i as u64),
        })
        .collect();
    let reports = semr_differential(exe, &batches);
    // Keep the body_gate fixture's separate identity controls exact. They
    // do not replace the certificate_binding fixture's evidence refusals.
    let identity_controls: Vec<_> = reports
        .iter()
        .filter(|report| {
            report.label == "fixture body_gate" && matches!(report.func.index(), 1 | 2)
        })
        .collect();
    assert_eq!(
        identity_controls.len(),
        8,
        "two annotated bodies, four inputs each"
    );
    for report in identity_controls {
        assert_eq!(report.args.len(), 1);
        let expected = Verdict::Ok(vec![rust_val(&report.args[0])]);
        assert_eq!(report.rust, expected, "Rust body-gate row: {report:?}");
        assert_eq!(report.lean, expected, "SemR body-gate row: {report:?}");
        assert_eq!(report.comparison, Comparison::Agree);
        eprintln!(
            "SemR body-gate identity control: {:?} input {:?}; Rust {:?}; SemR {:?}",
            report.func,
            rust_val(&report.args[0]),
            report.rust,
            report.lean
        );
    }
    let target_frontier: BTreeMap<_, usize> = reports
        .iter()
        .filter(|r| {
            batches
                .iter()
                .any(|b| b.label == r.label && b.module.target_info.is_some())
        })
        .fold(BTreeMap::new(), |mut rows, r| {
            *rows.entry((r.label.clone(), r.lean.class())).or_default() += 1;
            rows
        });
    eprintln!("SemR target-bearing fixture frontier: {target_frontier:?}");
    let t = tally(&reports);
    assert_no_mismatch(&t, "SemR, subset fixtures");
    let expected: BTreeMap<String, usize> = SEMR_FIXTURE_UNSUPPORTED_LEDGER
        .iter()
        .map(|(k, n)| ((*k).to_string(), *n))
        .collect();
    assert_eq!(
        t.unsupported, expected,
        "SemR coverage RATCHET (fixtures): refusals per side:feature differ from \
         SEMR_FIXTURE_UNSUPPORTED_LEDGER. A higher count is a regression; a lower one is \
         progress — edit the ledger in the same commit."
    );
}

/// Metadata-free flat structs already admitted by SemR retain nominal types
/// in the decoder summary, through an actual call boundary and field updates.
/// Explicit physical layout metadata keeps its named decoder refusal.
#[test]
fn semr_flat_scalar_structs_preserve_decode_and_runtime() {
    use trust_ir::constant::Constant;
    use trust_ir::ty::{FieldDef, StructDef};
    use trust_ir::value::StructId;

    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let mut mb = ModuleBuilder::new("semr_flat_scalar_struct");
    let id = mb.add_struct(StructDef {
        id: StructId::new(0),
        name: "LogicalPair".into(),
        fields: vec![
            FieldDef {
                name: "number".into(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "flag".into(),
                ty: Ty::Bool,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    let ty = Ty::Struct(id);
    let callee_ty = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
    let mut fb = mb.function("identity", callee_ty);
    let entry = fb.create_block();
    let argument = fb.add_block_param(entry, ty.clone());
    fb.switch_to_block(entry);
    let copied = fb.copy(ty.clone(), argument);
    fb.ret(vec![copied]);
    let callee = fb.build();
    let driver_ty = mb.add_func_type(vec![], vec![Ty::I64, Ty::Bool]);
    let mut fb = mb.function("driver", driver_ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let seed = fb.const_value(
        ty.clone(),
        Constant::Aggregate(vec![Constant::Int(-7), Constant::Bool(true)]),
    );
    let copied = fb.copy(ty.clone(), seed);
    let replacement = fb.iconst(Ty::I64, 9);
    let updated = fb.insert_field(ty, copied, 0, replacement);
    let returned = fb.call(callee, vec![updated]);
    let number = fb.extract_field(Ty::I64, returned, 0);
    let flag = fb.extract_field(Ty::Bool, returned, 1);
    fb.ret(vec![number, flag]);
    let driver = fb.build();
    let module = mb.build().expect("validated flat struct module");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let blob = trust_ir::binary::serialize_module(&module).expect("flat struct wire image");
    let decoded = trust_ir::binary::deserialize_module(&blob).expect("Rust flat struct decoder");
    assert!(trust_ir_build::validate_module(&decoded).is_empty());
    assert_eq!(semr_ty_str(&Ty::Struct(id)), "struct0");
    assert_eq!(
        semr_decode(exe, std::slice::from_ref(&blob)),
        vec![json!({"decoded": semr_summary_of(&decoded)})]
    );
    let batch = Batch {
        label: "decoded flat scalar struct call/update".into(),
        module: &decoded,
        runs: vec![(driver, vec![])],
    };
    let expected = Verdict::Ok(vec![Val::Int { width: 64, raw: 9 }, Val::Bool(true)]);
    let reports = semr_differential(exe, &[batch]);
    assert_eq!(reports.len(), 1);
    assert_eq!(reports[0].rust, expected);
    assert_eq!(reports[0].lean, expected);
    assert_eq!(reports[0].comparison, Comparison::Agree);
    let executed = semr_executed(
        exe,
        &semr_fragment_rows(),
        &Batch {
            label: "flat scalar struct executed nodes".into(),
            module: &decoded,
            runs: vec![(driver, vec![])],
        },
    );
    let expected_nodes = [
        "Const",
        "Copy",
        "InsertField",
        "Call",
        "ExtractField",
        "Return",
    ]
    .into_iter()
    .map(str::to_string)
    .collect::<BTreeSet<_>>();
    assert_eq!(executed, vec![expected_nodes]);
    eprintln!(
        "SemR flat struct witness: 1 exact decoded module, 1 Ok agreement, executed {executed:?}"
    );

    let mut images = vec![("positive", blob)];
    for boundary in ["struct.field_offset", "struct.size", "struct.align"] {
        let mut with_layout = module.clone();
        match boundary {
            "struct.field_offset" => with_layout.structs[0].fields[0].offset = Some(0),
            "struct.size" => with_layout.structs[0].size = Some(16),
            "struct.align" => with_layout.structs[0].align = Some(8),
            _ => unreachable!("fixed layout boundary census"),
        }
        assert!(
            trust_ir_build::validate_module(&with_layout).is_empty(),
            "{boundary}"
        );
        assert_eq!(run_rust(&with_layout, driver, &[]), expected, "{boundary}");
        let blob = trust_ir::binary::serialize_module(&with_layout).expect("layout wire image");
        assert_eq!(
            semr_decode(exe, std::slice::from_ref(&blob)),
            vec![json!({"unsupported": boundary})],
            "{boundary}"
        );
        images.push((boundary, blob));
    }
    // Preserve exact new positive/refusal bytes when the qualification driver
    // requests evidence. This does not alter any decoder or verdict policy.
    if let Some(directory) = std::env::var_os("TRUST_IR_ORACLE_EVIDENCE_DIR") {
        let directory = PathBuf::from(directory);
        fs::create_dir_all(&directory).expect("flat struct evidence directory");
        for (name, blob) in images {
            fs::write(
                directory.join(format!("semr-flat-struct-{name}.tmbc")),
                blob,
            )
            .expect("preserve flat struct wire image");
        }
    }
}

/// NEGATIVE CONTROL: SemR runs `sub(a, b)` from its blob while the
/// interpreter runs the same module with the `Sub` flipped to `Add`; the
/// comparison must report every run with `b ≠ 0` as a mismatch, and the
/// unmutated pair must agree. A harness that could not see a disagreement
/// would pass the corpus tests vacuously.
#[test]
fn semr_mutation_control_flipped_sub_is_reported() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let (module, id) = sub_module();
    let mut mutant = module.clone();
    for f in &mut mutant.functions {
        for b in &mut f.blocks {
            for n in &mut b.body {
                if let trust_ir::Inst::BinOp { op, .. } = &mut n.inst {
                    assert_eq!(*op, trust_ir::inst::BinOp::Sub);
                    *op = trust_ir::inst::BinOp::Add;
                }
            }
        }
    }
    let arg = |v: i32| InterpretValue::int(Ty::I32, i128::from(v)).expect("i32 argument");
    let runs = vec![
        (id, vec![arg(5), arg(3)]),
        (id, vec![arg(3), arg(5)]),
        (id, vec![arg(i32::MIN), arg(1)]),
    ];
    let batch = Batch {
        label: "sub".into(),
        module: &module,
        runs: runs.clone(),
    };
    let semr = run_semr(exe, &batch);
    assert_eq!(semr[0], i32_verdict(2));
    assert_eq!(semr[1], i32_verdict(-2));
    assert_eq!(semr[2], i32_verdict(i32::MAX));
    for ((f, args), s) in runs.iter().zip(&semr) {
        assert_eq!(
            compare_semr(&run_rust(&module, *f, args), s),
            Comparison::Agree
        );
        assert!(
            matches!(
                compare_semr(&run_rust(&mutant, *f, args), s),
                Comparison::Mismatch(_)
            ),
            "the flipped interpreter run {args:?} was not reported"
        );
    }
}

/// SemR's verdict on each blob from its decoder alone (`semr_eval --decode
/// <dir> <n>`, blobs written as `<dir>/<i>.tmbc`).
fn semr_decode(exe: &Path, blobs: &[Vec<u8>]) -> Vec<Json> {
    let scratch = SemrScratch::new("decode");
    let dir = scratch.0.clone();
    let paths: Vec<PathBuf> = blobs
        .iter()
        .enumerate()
        .map(|(i, b)| {
            let p = dir.join(format!("{i}.tmbc"));
            fs::write(&p, b).expect("write blob");
            p
        })
        .collect();
    let out = Command::new(exe)
        .arg("--decode")
        .arg(&dir)
        .arg(paths.len().to_string())
        .output()
        .unwrap_or_else(|e| panic!("cannot run {}: {e}", exe.display()));
    drop(scratch);
    assert!(
        out.status.success(),
        "semr_eval --decode exited with {}",
        out.status
    );
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    let lines: Vec<Json> = text
        .lines()
        .map(|l| serde_json::from_str(l).unwrap_or_else(|e| panic!("not JSON ({e}): {l}")))
        .collect();
    assert_eq!(lines.len(), blobs.len(), "one decode verdict per blob");
    lines
}

// --- the decoder differential ------------------------------------------------

/// SemR's spelling of a type in a decoded module's summary (`tyStr` in
/// `lean/semr/Main.lean`).
fn semr_ty_str(ty: &Ty) -> String {
    match ty {
        Ty::I8 => "i8".into(),
        Ty::I16 => "i16".into(),
        Ty::I32 => "i32".into(),
        Ty::I64 => "i64".into(),
        Ty::I128 => "i128".into(),
        Ty::Isize => "isize".into(),
        Ty::U8 => "u8".into(),
        Ty::U16 => "u16".into(),
        Ty::U32 => "u32".into(),
        Ty::U64 => "u64".into(),
        Ty::U128 => "u128".into(),
        Ty::Usize => "usize".into(),
        Ty::Bool => "bool".into(),
        Ty::Ptr => "ptr".into(),
        Ty::Unit => "unit".into(),
        Ty::Never => "never".into(),
        Ty::Enum(id) => format!("enum{}", id.0),
        Ty::Struct(id) => format!("struct{}", id.0),
        Ty::Tensor(elem, rank) if elem.is_integer() => {
            format!("tensor<{},{rank}>", semr_ty_str(elem))
        }
        other => format!("outside-the-fragment:{other}"),
    }
}

fn semr_const_str(c: &trust_ir::constant::Constant) -> String {
    use trust_ir::constant::Constant as C;
    match c {
        C::Int(v) => format!("i{}", *v as u128),
        C::Bool(b) => if *b { "b1" } else { "b0" }.to_string(),
        C::Aggregate(es) => format!(
            "({})",
            es.iter().map(semr_const_str).collect::<Vec<_>>().join(",")
        ),
        // v70: the digest's bytes in decimal, `.`-joined, then the extents.
        C::TensorBlob { digest, dims } => format!(
            "blob<{}>[{}]",
            digest
                .0
                .iter()
                .map(u8::to_string)
                .collect::<Vec<_>>()
                .join("."),
            dims.iter()
                .map(u64::to_string)
                .collect::<Vec<_>>()
                .join(",")
        ),
        other => format!("outside-the-fragment:{other:?}"),
    }
}

/// SemR's summary of one instruction (`instSummary` in `Main.lean`): its name
/// with op, type and immediates, and its operand ids.
fn semr_inst_summary(inst: &trust_ir::Inst) -> (String, Vec<u32>) {
    use trust_ir::Inst as I;
    use trust_ir::inst::{AssertKind, AssertOverflowOp, OverflowOp};
    let low = |d: String| d.to_lowercase();
    let ids = |xs: &[trust_ir::value::ValueId]| xs.iter().map(|x| x.0).collect::<Vec<u32>>();
    match inst {
        I::BinOp { op, ty, lhs, rhs } => (
            format!("binop.{}.{}", low(format!("{op:?}")), semr_ty_str(ty)),
            vec![lhs.0, rhs.0],
        ),
        I::UnOp { op, ty, operand } => (
            format!("unop.{}.{}", low(format!("{op:?}")), semr_ty_str(ty)),
            vec![operand.0],
        ),
        I::Overflow { op, ty, lhs, rhs } => {
            let name = match op {
                OverflowOp::AddOverflow => "add",
                OverflowOp::SubOverflow => "sub",
                OverflowOp::MulOverflow => "mul",
            };
            (
                format!("overflow.{name}.{}", semr_ty_str(ty)),
                vec![lhs.0, rhs.0],
            )
        }
        I::ICmp { op, ty, lhs, rhs } => (
            format!("icmp.{}.{}", low(format!("{op:?}")), semr_ty_str(ty)),
            vec![lhs.0, rhs.0],
        ),
        I::Const { ty, value } => (
            format!("const.{}.{}", semr_ty_str(ty), semr_const_str(value)),
            vec![],
        ),
        I::Copy { ty, operand } => (format!("copy.{}", semr_ty_str(ty)), vec![operand.0]),
        I::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => (
            format!("select.{}", semr_ty_str(ty)),
            vec![cond.0, then_val.0, else_val.0],
        ),
        I::ExtractField {
            ty,
            aggregate,
            field,
        } => (
            format!("extract.{}.{field}", semr_ty_str(ty)),
            vec![aggregate.0],
        ),
        I::InsertField {
            ty,
            aggregate,
            field,
            value,
        } => (
            format!("insert.{}.{field}", semr_ty_str(ty)),
            vec![aggregate.0, value.0],
        ),
        I::OpenFrame { def } => (
            format!(
                "open.{}",
                def.slots
                    .iter()
                    .map(|s| semr_ty_str(&s.ty))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            vec![],
        ),
        I::BindSlot { frame, slot, value } => (format!("bind.{slot}"), vec![frame.0, value.0]),
        I::LoadSlot { frame, slot, ty } => {
            (format!("load.{slot}.{}", semr_ty_str(ty)), vec![frame.0])
        }
        I::CloseFrame { frame } => ("close".into(), vec![frame.0]),
        I::NullPtr => ("nullptr".into(), vec![]),
        I::Unreachable => ("unreachable".into(), vec![]),
        I::Assert { cond, kind, .. } => {
            let k = match kind {
                AssertKind::Unspecified => "unspecified".to_string(),
                AssertKind::Overflow(op) => format!(
                    "overflow{}",
                    match op {
                        AssertOverflowOp::Add => 0,
                        AssertOverflowOp::Sub => 1,
                        AssertOverflowOp::Mul => 2,
                        AssertOverflowOp::Div => 3,
                        AssertOverflowOp::Rem => 4,
                        AssertOverflowOp::Shl => 5,
                        AssertOverflowOp::Shr => 6,
                        AssertOverflowOp::Neg => 7,
                    }
                ),
                AssertKind::DivByZero => "div0".into(),
                AssertKind::RemByZero => "rem0".into(),
                AssertKind::BoundsCheck { index, len } => format!("bounds{},{}", index.0, len.0),
                AssertKind::MisalignedPtr { required, found } => {
                    format!("misaligned{},{}", required.0, found.0)
                }
                AssertKind::NullPtr => "null".into(),
            };
            (format!("assert.{k}"), vec![cond.0])
        }
        I::Call { callee, args, .. } => (format!("call.{}", callee.0), ids(args)),
        I::Br { target, args } => (format!("br.{}", target.0), ids(args)),
        I::CondBr {
            cond,
            then_target,
            then_args,
            else_target,
            else_args,
        } => {
            let mut ops = vec![cond.0];
            ops.extend(ids(then_args));
            ops.extend(ids(else_args));
            (
                format!(
                    "condbr.{}.{}.{}",
                    then_target.0,
                    then_args.len(),
                    else_target.0
                ),
                ops,
            )
        }
        I::Assume { cond } => ("assume".into(), vec![cond.0]),
        I::Return { values } => ("ret".into(), ids(values)),
        I::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => (
            format!(
                "cast.{}.{}.{}",
                low(format!("{op:?}")),
                semr_ty_str(src_ty),
                semr_ty_str(dst_ty)
            ),
            vec![operand.0],
        ),
        I::Switch {
            value,
            default,
            default_args,
            cases,
            ..
        } => {
            let mut ops = vec![value.0];
            ops.extend(ids(default_args));
            for c in cases {
                ops.extend(ids(&c.args));
            }
            (
                format!(
                    "switch.{}.{}.{}",
                    default.0,
                    default_args.len(),
                    cases
                        .iter()
                        .map(|c| format!(
                            "{}:{}:{}",
                            semr_const_str(&c.value),
                            c.target.0,
                            c.args.len()
                        ))
                        .collect::<Vec<_>>()
                        .join(",")
                ),
                ops,
            )
        }
        I::Alloca { ty, count, align } => (
            format!("alloca.{}.{}", semr_ty_str(ty), semr_opt_u64(*align)),
            count.iter().map(|c| c.0).collect(),
        ),
        I::Load {
            ty,
            ptr,
            volatile,
            align,
        } => (
            format!(
                "mload.{}.{}.{}",
                semr_ty_str(ty),
                u8::from(*volatile),
                semr_opt_u64(*align)
            ),
            vec![ptr.0],
        ),
        I::Store {
            ty,
            ptr,
            value,
            volatile,
            align,
        } => (
            format!(
                "mstore.{}.{}.{}",
                semr_ty_str(ty),
                u8::from(*volatile),
                semr_opt_u64(*align)
            ),
            vec![ptr.0, value.0],
        ),
        I::GEP {
            pointee_ty,
            base,
            indices,
            ..
        } => {
            let mut ops = vec![base.0];
            ops.extend(ids(indices));
            (format!("gep.{}", semr_ty_str(pointee_ty)), ops)
        }
        I::Dealloc { ptr } => ("dealloc".into(), vec![ptr.0]),
        I::TensorContract {
            ty,
            lhs,
            rhs,
            batch,
            contract,
        } => {
            let pairs = |ps: &[(u32, u32)]| {
                let ps: Vec<String> = ps.iter().map(|(a, b)| format!("{a}:{b}")).collect();
                format!("[{}]", ps.join(","))
            };
            (
                format!(
                    "tensor_contract.{}.{}.{}",
                    semr_ty_str(ty),
                    pairs(batch),
                    pairs(contract)
                ),
                vec![lhs.0, rhs.0],
            )
        }
        I::TensorMap { ty, args, body } => {
            use trust_ir::inst::TensorMapNode as N;
            let node = |n: &N<trust_ir::level::NoExt>| match n {
                N::BinOp { op, ty, lhs, rhs } => format!(
                    "binop.{}.{}.{lhs}.{rhs}",
                    low(format!("{op:?}")),
                    semr_ty_str(ty)
                ),
                N::UnOp { op, ty, operand } => format!(
                    "unop.{}.{}.{operand}",
                    low(format!("{op:?}")),
                    semr_ty_str(ty)
                ),
                N::ICmp { op, ty, lhs, rhs } => format!(
                    "icmp.{}.{}.{lhs}.{rhs}",
                    low(format!("{op:?}")),
                    semr_ty_str(ty)
                ),
                N::Select {
                    ty,
                    cond,
                    then_lane,
                    else_lane,
                } => format!("select.{}.{cond}.{then_lane}.{else_lane}", semr_ty_str(ty)),
                N::Cast {
                    op,
                    src_ty,
                    dst_ty,
                    operand,
                } => format!(
                    "cast.{}.{}.{}.{operand}",
                    low(format!("{op:?}")),
                    semr_ty_str(src_ty),
                    semr_ty_str(dst_ty)
                ),
            };
            (
                format!(
                    "tensor_map.{}.[{}]",
                    semr_ty_str(ty),
                    body.iter().map(node).collect::<Vec<_>>().join(";")
                ),
                ids(args),
            )
        }
        I::TensorReduce {
            ty, src, op, axes, ..
        } => (
            format!(
                "tensor_reduce.{}.{}.{}",
                op.name(),
                semr_ty_str(ty),
                semr_nats(axes)
            ),
            vec![src.0],
        ),
        I::TensorView {
            ty,
            src,
            params,
            exprs,
            shape,
            index,
            fill,
        } => {
            use trust_ir::inst::TensorIndexExpr as E;
            let expr = |e: &E| match *e {
                E::Lit(n) => format!("lit{n}"),
                E::Param(k) => format!("param{k}"),
                E::SrcExtent(j) => format!("src_extent{j}"),
                E::Coord(i) => format!("coord{i}"),
                E::Add(a, b) => format!("add{a}:{b}"),
                E::Sub(a, b) => format!("sub{a}:{b}"),
                E::Mul(a, b) => format!("mul{a}:{b}"),
                E::Div(a, b) => format!("div{a}:{b}"),
                E::Rem(a, b) => format!("rem{a}:{b}"),
                E::Min(a, b) => format!("min{a}:{b}"),
                E::Max(a, b) => format!("max{a}:{b}"),
            };
            let mut ops = vec![src.0];
            ops.extend(ids(params));
            ops.extend(fill.iter().map(|f| f.0));
            (
                format!(
                    "tensor_view.{}.[{}].{}.{}.{}",
                    semr_ty_str(ty),
                    exprs.iter().map(expr).collect::<Vec<_>>().join(";"),
                    semr_nats(shape),
                    semr_nats(index),
                    if fill.is_some() { "1" } else { "-" }
                ),
                ops,
            )
        }
        // v69: the data, then the coordinate tensors in axis order.
        I::TensorGather { ty, data, coords } => {
            let mut ops = vec![data.0];
            ops.extend(ids(coords));
            (format!("tensor_gather.{}", semr_ty_str(ty)), ops)
        }
        // v69: the initial tensor, the source, then the coordinate tensors.
        I::TensorScatter {
            ty,
            init,
            src,
            coords,
        } => {
            let mut ops = vec![init.0, src.0];
            ops.extend(ids(coords));
            (format!("tensor_scatter.{}", semr_ty_str(ty)), ops)
        }
        other => (format!("outside-the-fragment:{other:?}"), vec![]),
    }
}

/// A list of numbers as SemR's summary spells it (`natsStr`): `[a,b,…]`.
fn semr_nats(xs: &[u32]) -> String {
    format!(
        "[{}]",
        xs.iter().map(u32::to_string).collect::<Vec<_>>().join(",")
    )
}

/// An optional immediate as SemR's summary spells it (`optNatStr`).
fn semr_opt_u64(x: Option<u64>) -> String {
    x.map_or_else(|| "-".into(), |n| n.to_string())
}

/// The summary of a module `deserialize_module` read, in the spelling
/// `semr_eval --decode` prints for the module SemR's decoder read
/// (`moduleSummary`): signatures, enums' variant field types, and every
/// function's blocks, block parameters and nodes (instruction, operands,
/// results).
fn semr_summary_of(m: &Module) -> Json {
    let tys = |ts: &[Ty]| Json::Array(ts.iter().map(|t| json!(semr_ty_str(t))).collect());
    json!({
        "tys": m.func_types.iter().map(|ft| json!([tys(&ft.params), tys(&ft.returns), ft.is_vararg])).collect::<Vec<_>>(),
        "structs": m.structs.iter().map(|s| json!([s.id.0, s.fields.iter().map(|f| semr_ty_str(&f.ty)).collect::<Vec<_>>()])).collect::<Vec<_>>(),
        "enums": m.enums.iter().map(|e| json!([
            e.id.0,
            e.variants.iter().map(|v| tys(&v.fields)).collect::<Vec<_>>(),
            e.effective_discriminants().unwrap_or_default().iter().map(|d| d.to_string()).collect::<Vec<_>>(),
            e.canonical_tag_repr().map(|r| semr_ty_str(&r.ty())).unwrap_or_default(),
        ])).collect::<Vec<_>>(),
        "fns": m.functions.iter().map(|f| json!([
            f.id.0,
            f.ty.0,
            f.entry.0,
            f.blocks.iter().map(|b| json!([
                b.id.0,
                b.params.iter().map(|(x, t)| json!([x.0, semr_ty_str(t)])).collect::<Vec<_>>(),
                b.body.iter().map(|n| {
                    let (name, ops) = semr_inst_summary(&n.inst);
                    json!([name, ops, n.results.iter().map(|r| r.0).collect::<Vec<_>>()])
                }).collect::<Vec<_>>(),
            ])).collect::<Vec<_>>(),
            // The symbol, byte for byte (VF5 identifies a row's function by it).
            f.name.as_bytes(),
        ])).collect::<Vec<_>>(),
        "target": m.target_info.as_ref().map(|t| json!([
            t.triple.as_bytes(), t.pointer_size, t.endianness == trust_ir::Endianness::Big,
            t.abi.as_ref().map(|a| a.as_bytes()),
            match t.struct_passing {
                trust_ir::StructPassingPolicy::NativeC => 0,
                trust_ir::StructPassingPolicy::AlwaysMemory => 1,
                trust_ir::StructPassingPolicy::Unclassified => 2,
            },
        ])),
        // v70: the blob table, each row its digest's bytes and its own.
        "blobs": m.blobs.iter().map(|b| json!([b.digest.0.to_vec(), b.data])).collect::<Vec<_>>(),
    })
}

/// How a blob of the decoder differential was made, which fixes what SemR
/// must say when the Rust reader refuses it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BlobKind {
    /// A blob as `serialize_module` wrote it: SemR must decode it, to the
    /// same module.
    Written,
    /// A proper prefix, the blob with a byte appended, or a byte of the magic
    /// changed: a header or trailer fault, so SemR must say `malformed`
    /// (never `unsupported`) whenever the reader refuses.
    HeaderOrTrailerFault,
    /// Any other one-byte change, or a relabelled version: SemR may stop at an
    /// unmodelled construct before the bad byte (`unsupported` is fail-closed
    /// and allowed), but must not decode what the reader refuses.
    Mutated,
    /// A blob relabelled to another wire version in v38–v62 (its bytes
    /// unchanged): when the reader accepts it, SemR must decode it to the
    /// same module; when the reader refuses it, SemR must not decode it.
    Relabelled,
    /// An invalid UTF-8 rewrite of a pooled string: SemR must say
    /// `malformed` whenever the reader refuses it.
    StringFault,
    /// A blob whose layout this test rewrote to a later version's (gated
    /// sections inserted): the reader must accept it, and SemR must decode it
    /// to the same module.
    Synthesized,
}

/// Judge SemR's decode verdicts against `deserialize_module`, blob by blob.
/// Returns `(accepted by Rust, decoded by SemR with an equal summary)`.
fn judge_decodes(exe: &Path, blobs: &[(BlobKind, String, Vec<u8>)], what: &str) -> (usize, usize) {
    let bytes: Vec<Vec<u8>> = blobs.iter().map(|(_, _, b)| b.clone()).collect();
    let verdicts = semr_decode(exe, &bytes);
    let mut rust_ok = 0usize;
    let mut equal = 0usize;
    let mut failures = Vec::new();
    for ((kind, label, blob), v) in blobs.iter().zip(&verdicts) {
        let rust = trust_ir::binary::deserialize_module(blob);
        let decoded = v.get("decoded");
        let malformed = v.get("error").is_some();
        match (&rust, decoded) {
            (Ok(m), Some(summary)) => {
                rust_ok += 1;
                let want = semr_summary_of(m);
                if *summary == want {
                    equal += 1;
                } else {
                    failures.push(format!(
                        "{label} ({kind:?}): both decode, to different modules:\n      semr {summary}\n      rust {want}"
                    ));
                }
            }
            (Ok(_), None) => {
                rust_ok += 1;
                let allowed = *kind == BlobKind::Mutated && !malformed;
                if !allowed {
                    failures.push(format!("{label} ({kind:?}): Rust accepts, SemR says {v}"));
                }
            }
            (Err(e), Some(_)) => {
                failures.push(format!("{label} ({kind:?}): Rust refuses ({e}), SemR decodes"))
            }
            (Err(e), None) => match kind {
                BlobKind::Written | BlobKind::Synthesized => failures.push(format!(
                    "{label} ({kind:?}): the reader refuses a blob this test expects it to read ({e})"
                )),
                BlobKind::HeaderOrTrailerFault | BlobKind::StringFault if !malformed => failures.push(format!(
                    "{label} ({kind:?}): Rust refuses ({e}), SemR says {v}, not malformed"
                )),
                _ => {}
            },
        }
    }
    eprintln!(
        "SemR decoder differential ({what}): {} blobs, {rust_ok} accepted by Rust, {equal} decoded \
         by SemR to the same module",
        blobs.len()
    );
    assert!(
        failures.is_empty(),
        "{what}: {} decoder disagreement(s):\n  {}",
        failures.len(),
        failures
            .iter()
            .take(40)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n  ")
    );
    (rust_ok, equal)
}

/// Every one-byte change of `blob`: each of the eight single-bit flips and
/// `0xff`, at every position (the magic's bytes are header faults).
fn one_byte_mutations(label: &str, blob: &[u8], out: &mut Vec<(BlobKind, String, Vec<u8>)>) {
    for i in 0..blob.len() {
        for flip in [0x01u8, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0xff] {
            let mut m = blob.to_vec();
            m[i] ^= flip;
            let kind = if i < 8 {
                BlobKind::HeaderOrTrailerFault
            } else {
                BlobKind::Mutated
            };
            out.push((kind, format!("{label} byte {i} ^ {flip:#04x}"), m));
        }
    }
}

/// The decoder differential: SemR's decoder against `deserialize_module` on
/// every proper prefix, one appended byte, and every one-byte change (the
/// eight single-bit flips and `0xff`) at every position of corpus blobs.
/// Each unmutated blob must decode in SemR to the module Rust reads (the
/// summary compares signatures, enums, blocks and nodes); a blob both
/// decode must decode to the same module; a blob Rust accepts SemR must not
/// call malformed; a blob Rust refuses SemR must not decode, and must call
/// malformed (not unsupported) when the fault is a truncation, a trailing
/// byte or the magic.
#[test]
fn semr_decoder_agrees_with_the_binary_reader_on_mutated_blobs() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let modules = generator_corpus();
    let mut blobs: Vec<(BlobKind, String, Vec<u8>)> = Vec::new();
    for (seed, module, _) in modules.iter().take(6) {
        let blob = trust_ir::binary::serialize_module(module).expect("corpus blob");
        let label = format!("seed {seed}");
        for cut in 0..blob.len() {
            blobs.push((
                BlobKind::HeaderOrTrailerFault,
                format!("{label} cut {cut}"),
                blob[..cut].to_vec(),
            ));
        }
        for extra in [0u8, 1, 0xff] {
            let mut longer = blob.clone();
            longer.push(extra);
            blobs.push((
                BlobKind::HeaderOrTrailerFault,
                format!("{label} + {extra:#04x}"),
                longer,
            ));
        }
        one_byte_mutations(&label, &blob, &mut blobs);
        blobs.push((BlobKind::Written, label, blob));
    }
    let (rust_ok, equal) = judge_decodes(exe, &blobs, "corpus mutations");
    let written = blobs
        .iter()
        .filter(|(k, _, _)| *k == BlobKind::Written)
        .count();
    assert_eq!(written, 6);
    assert!(
        equal >= written && rust_ok >= written,
        "the unmutated blobs must decode"
    );
}

/// A fieldless enum value of `eid` carrying variant `i`'s effective
/// discriminant at the canonical tag type (what `Const` builds).
fn fieldless_enum_value(module: &Module, eid: trust_ir::value::EnumId, i: usize) -> InterpretValue {
    let def = module.enum_def(eid).expect("enum def");
    let tag = def.canonical_tag_repr().expect("a canonical tag").ty();
    let disc = def.effective_discriminants().expect("discriminants")[i];
    InterpretValue {
        ty: Ty::Enum(eid),
        kind: InterpretValueKind::Aggregate(vec![InterpretValue::int(tag, disc).expect("tag")]),
    }
}

/// Every function whose parameters are integers, `Bool`s or fieldless enums,
/// run once per variant of each enum parameter (D-2(b): the range a
/// fieldless enum restricts its tag to), integers at zero and one.
fn enum_runs(module: &Module) -> Vec<(FuncId, Vec<InterpretValue>)> {
    let mut runs = Vec::new();
    for f in &module.functions {
        let Some(sig) = module.func_type(f.ty) else {
            continue;
        };
        if f.is_declaration() || !sig.params.iter().any(|p| matches!(p, Ty::Enum(_))) {
            continue;
        }
        let mut choices: Vec<Vec<InterpretValue>> = Vec::new();
        for p in &sig.params {
            choices.push(match p {
                Ty::Enum(eid) => {
                    let def = module.enum_def(*eid).expect("enum def");
                    assert!(
                        def.variants.iter().all(|v| v.fields.is_empty()),
                        "fieldless"
                    );
                    (0..def.variants.len())
                        .map(|i| fieldless_enum_value(module, *eid, i))
                        .collect()
                }
                Ty::Bool => vec![InterpretValue::bool(false), InterpretValue::bool(true)],
                other => vec![
                    InterpretValue::int(other.clone(), 0).expect("int"),
                    InterpretValue::int(other.clone(), 1).expect("int"),
                ],
            });
        }
        let mut combos: Vec<Vec<InterpretValue>> = vec![vec![]];
        for c in &choices {
            combos = combos
                .into_iter()
                .flat_map(|prefix| {
                    c.iter().map(move |v| {
                        let mut p = prefix.clone();
                        p.push(v.clone());
                        p
                    })
                })
                .collect();
        }
        runs.extend(combos.into_iter().map(|args| (f.id, args)));
    }
    runs
}

/// VF5: the stage-2 compiler's own artifacts (`tests/fixtures/semr_compiled/`,
/// written by `-Ztrust-dump=ir:`), which carry a target record, per-node proof
/// annotations and formula-free proof obligations, decode in SemR to the module
/// `deserialize_module` reads and run as the interpreter runs them (24 runs per
/// function, edges included, plus all-zero arguments, so a zero divisor and
/// each overflow are reached). A target SemR does not execute is refused by
/// name, never run: mismatched pointer widths, big-endian, and an architecture outside
/// the interpreter's canonical scalar table.
#[test]
fn semr_compiled_artifacts_agree_with_the_interpreter() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let dir = fixtures_dir().join("semr_compiled");
    let mut paths: Vec<PathBuf> = fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "bin"))
        .collect();
    paths.sort();
    assert_eq!(paths.len(), 10, "the ten compiled artifacts");
    let mut blobs: Vec<(BlobKind, String, Vec<u8>)> = Vec::new();
    let mut modules: Vec<(String, Module)> = Vec::new();
    for path in &paths {
        let name = path.file_stem().unwrap().to_string_lossy().into_owned();
        let bytes = fs::read(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let module = trust_ir::binary::deserialize_module(&bytes)
            .unwrap_or_else(|e| panic!("{name}: the reader refuses the compiler's artifact: {e}"));
        let target = module
            .target_info
            .as_ref()
            .expect("a compiled artifact has a target");
        assert_eq!(target.pointer_size, 8, "{name}: 8-byte pointers");
        assert!(
            !module.proof_obligations.is_empty(),
            "{name}: the compiler records its obligations"
        );
        assert!(
            module
                .functions
                .iter()
                .flat_map(|f| f.blocks.iter())
                .flat_map(|b| b.body.iter())
                .any(|n| !n.proofs.is_empty()),
            "{name}: some node carries a proof annotation"
        );
        blobs.push((BlobKind::Written, name.clone(), bytes));
        modules.push((name, module));
    }
    let (rust_ok, equal) = judge_decodes(exe, &blobs, "compiled artifacts");
    assert_eq!(
        (rust_ok, equal),
        (10, 10),
        "every artifact decodes to the same module"
    );

    let batches: Vec<Batch<'_>> = modules
        .iter()
        .enumerate()
        .map(|(i, (name, module))| {
            let mut runs = module_runs(module, 24, 0x5F5F_0000 + i as u64);
            runs.extend(enum_runs(module));
            for f in &module.functions {
                let sig = module.func_type(f.ty).expect("signature");
                if !sig.params.iter().all(scalar_param) {
                    continue;
                }
                let zeros = sig
                    .params
                    .iter()
                    .map(|p| match p {
                        Ty::Bool => InterpretValue::bool(false),
                        other => InterpretValue::int(other.clone(), 0).expect("integer"),
                    })
                    .collect();
                runs.push((f.id, zeros));
            }
            Batch {
                label: format!("compiled {name}"),
                module,
                runs,
            }
        })
        .collect();
    let t = tally(&semr_differential(exe, &batches));
    assert_no_mismatch(&t, "SemR, compiled artifacts");
    assert!(
        t.unsupported.is_empty(),
        "SemR runs every compiled artifact: {:?}",
        t.unsupported
    );
    assert!(
        t.agreed.get("ok").copied().unwrap_or(0) > 0
            && t.agreed.get("panic").copied().unwrap_or(0) > 0,
        "the runs reach both returns and panics: {:?}",
        t.agreed
    );

    // The same ten artifacts also execute under the canonical32-bit table.
    let wasm32: Vec<_> = modules
        .iter()
        .map(|(name, module)| {
            let mut module = module.clone();
            module.target_info = Some(semr_target(32));
            (format!("wasm32 {name}"), module)
        })
        .collect();
    let wasm_blobs: Vec<_> = wasm32
        .iter()
        .map(|(name, module)| {
            (
                BlobKind::Written,
                name.clone(),
                trust_ir::binary::serialize_module(module).expect("serialize"),
            )
        })
        .collect();
    assert_eq!(
        judge_decodes(exe, &wasm_blobs, "compiled artifacts, wasm32"),
        (10, 10)
    );
    let wasm_batches: Vec<_> = wasm32
        .iter()
        .enumerate()
        .map(|(i, (name, module))| {
            let mut runs = module_runs(module, 24, 0x5F5F_0000 + i as u64);
            runs.extend(enum_runs(module));
            Batch {
                label: name.clone(),
                module,
                runs,
            }
        })
        .collect();
    let wasm = tally(&semr_differential(exe, &wasm_batches));
    assert_no_mismatch(&wasm, "SemR, compiled artifacts, wasm32");
    assert!(wasm.unsupported.is_empty(), "{:?}", wasm.unsupported);
    assert!(wasm.agreed.get("ok").copied().unwrap_or(0) > 0);

    // Metadata stays transportable. Execution alone refuses layouts outside
    // the interpreter's canonical scalar table, before evaluating a body.
    let (_, base) = &modules[0];
    let mut refused: Vec<(BlobKind, String, Vec<u8>)> = Vec::new();
    for (what, triple, pointer_size, endianness) in [
        (
            "mismatched pointer width",
            "aarch64-unknown-linux-gnu",
            4,
            trust_ir::Endianness::Little,
        ),
        (
            "big-endian",
            "aarch64-unknown-linux-gnu",
            8,
            trust_ir::Endianness::Big,
        ),
        (
            "non-canonical arch",
            "sparc64-unknown-linux-gnu",
            8,
            trust_ir::Endianness::Little,
        ),
    ] {
        let mut m = base.clone();
        let target = m.target_info.as_mut().expect("target");
        target.triple = triple.into();
        target.pointer_size = pointer_size;
        target.endianness = endianness;
        let bytes = trust_ir::binary::serialize_module(&m).expect("serialize");
        trust_ir::binary::deserialize_module(&bytes).expect("the reader accepts the record");
        refused.push((BlobKind::Mutated, what.to_string(), bytes));
    }
    assert_eq!(
        judge_decodes(exe, &refused, "non-executable target metadata"),
        (3, 3)
    );
    for (_, what, blob) in &refused {
        let module = trust_ir::binary::deserialize_module(blob).expect("target metadata");
        let runs = module_runs(&module, 1, 0x5F5F_0200);
        assert!(!runs.is_empty(), "{what}: an execution must be attempted");
        let batch = Batch {
            label: what.clone(),
            module: &module,
            runs,
        };
        for report in semr_differential(exe, &[batch]) {
            assert!(
                matches!(&report.rust, Verdict::Unsupported(_)),
                "{report:?}"
            );
            assert_eq!(
                report.lean,
                Verdict::Unsupported("target.byte_model".into()),
                "{report:?}"
            );
        }
    }
}

/// The compiled artifacts of `tests/fixtures/semr_compiled/`, by file stem, in
/// name order, each with its bytes and the module the reader reads.
fn compiled_artifacts() -> Vec<(String, Vec<u8>, Module)> {
    let dir = fixtures_dir().join("semr_compiled");
    let mut paths: Vec<PathBuf> = fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "bin"))
        .collect();
    paths.sort();
    paths
        .into_iter()
        .map(|path| {
            let name = path.file_stem().unwrap().to_string_lossy().into_owned();
            let bytes = fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            let module = trust_ir::binary::deserialize_module(&bytes)
                .unwrap_or_else(|e| panic!("{name}: the reader refuses it: {e}"));
            (name, bytes, module)
        })
        .collect()
}

/// A module derived from the compiled fieldless-enum artifact. Variant 0
/// drops every enum's layout record and keeps its discriminants (the decoder's
/// no-layout arm on the compiler's own explicit discriminants); every other
/// variant, per enum, keeps the enum as compiled, drops its layout record, or
/// permutes or redraws its discriminants (distinct, fitting its `repr`) with
/// the layout record dropped. The bodies are the compiler's, so a redrawn
/// assignment can make a switch or a cast take another arm: what both engines
/// must still agree on.
fn fieldless_variant(base: &Module, variant: u64) -> Module {
    let mut rng = Rng::new(0xD2B0_0000 + variant);
    let mut m = base.clone();
    for e in &mut m.enums {
        let mode = if variant == 0 { 1 } else { rng.bounded(4) };
        let n = e.variants.len();
        let mut discs = e
            .effective_discriminants()
            .expect("a well-formed assignment");
        match mode {
            0 => continue,
            1 => {}
            2 => {
                for i in (1..n).rev() {
                    let j = rng.bounded(i as u32 + 1) as usize;
                    discs.swap(i, j);
                }
            }
            _ => {
                let mut fresh: Vec<i128> = Vec::new();
                while fresh.len() < n {
                    let d = i128::from(rng.bounded(700)) - 350;
                    if !fresh.contains(&d) && e.repr.is_none_or(|r| r.fits(d)) {
                        fresh.push(d);
                    }
                }
                discs = fresh;
            }
        }
        if mode >= 2 {
            e.discriminants = discs.into_iter().map(Some).collect();
        }
        e.layout = None;
    }
    m
}

/// D-2(b)'s decoder arms and runs beyond the one compiled assignment: 160
/// modules derived from `fieldless.bin` (`fieldless_variant`) each decode in
/// SemR to the module `deserialize_module` reads (the summary compares every
/// enum's effective discriminants and tag type, so a reversed or shifted list in
/// either arm is a disagreement), and run as the interpreter runs them, every
/// enum parameter at every variant and the integers at random.
#[test]
fn semr_compiled_fieldless_variants_agree_with_the_interpreter() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let base = compiled_artifacts()
        .into_iter()
        .find(|(name, _, _)| name == "fieldless")
        .expect("fieldless.bin")
        .2;
    let mut blobs: Vec<(BlobKind, String, Vec<u8>)> = Vec::new();
    let mut modules: Vec<(String, Module)> = Vec::new();
    let (mut explicit_no_layout, mut with_layout) = (0usize, 0usize);
    for variant in 0..160u64 {
        let m = fieldless_variant(&base, variant);
        let label = format!("fieldless variant {variant}");
        let bytes = trust_ir::binary::serialize_module(&m)
            .unwrap_or_else(|e| panic!("{label}: serialize: {e}"));
        let read = trust_ir::binary::deserialize_module(&bytes)
            .unwrap_or_else(|e| panic!("{label}: the reader refuses it: {e}"));
        explicit_no_layout += read
            .enums
            .iter()
            .filter(|e| !e.discriminants.is_empty() && e.layout.is_none())
            .count();
        with_layout += read.enums.iter().filter(|e| e.layout.is_some()).count();
        blobs.push((BlobKind::Written, label.clone(), bytes));
        modules.push((label, read));
    }
    assert!(
        explicit_no_layout >= 160 && with_layout >= 100,
        "both arms are exercised: {explicit_no_layout} explicit-discriminant enums without a \
         layout record, {with_layout} with one"
    );
    let (rust_ok, equal) = judge_decodes(exe, &blobs, "fieldless variants");
    assert_eq!(
        (rust_ok, equal),
        (160, 160),
        "every variant decodes to the same module"
    );
    let batches: Vec<Batch<'_>> = modules
        .iter()
        .enumerate()
        .map(|(i, (label, module))| {
            let mut runs = enum_runs(module);
            runs.extend(module_runs(module, 6, 0xD2B1_0000 + i as u64));
            runs.extend(invalid_tag_runs(module));
            Batch {
                label: label.clone(),
                module,
                runs,
            }
        })
        .collect();
    let t = tally(&semr_differential(exe, &batches));
    assert_no_mismatch(&t, "SemR, fieldless variants");
    assert!(
        t.unsupported.is_empty(),
        "SemR runs every variant: {:?}",
        t.unsupported
    );
    let agreed: usize = t.agreed.values().sum();
    assert!(
        agreed > 14_000
            && t.agreed.get("ok").copied().unwrap_or(0) > 0
            && t.agreed.get("panic").copied().unwrap_or(0) > 0
            && t.agreed.get("type_error").copied().unwrap_or(0) > 0,
        "the runs reach returns, panics and type errors: {:?}",
        t.agreed
    );
}

/// Each function with one fieldless enum parameter, run once with that
/// parameter's tag one past its largest discriminant (no variant's, when the
/// tag type holds it): Rust's validity invariant broken on purpose, so a body
/// that relies on it (`headroom`'s `+ 1`) reaches what the two engines must
/// still agree on.
fn invalid_tag_runs(module: &Module) -> Vec<(FuncId, Vec<InterpretValue>)> {
    let mut runs = Vec::new();
    for f in &module.functions {
        let Some(sig) = module.func_type(f.ty) else {
            continue;
        };
        let [Ty::Enum(eid)] = sig.params.as_slice() else {
            continue;
        };
        if f.is_declaration() {
            continue;
        }
        let def = module.enum_def(*eid).expect("enum def");
        let tag = def.canonical_tag_repr().expect("a canonical tag");
        let discs = def.effective_discriminants().expect("discriminants");
        let bad = discs.iter().max().expect("a variant") + 1;
        if !tag.fits(bad) || discs.contains(&bad) {
            continue;
        }
        runs.push((
            f.id,
            vec![InterpretValue {
                ty: Ty::Enum(*eid),
                kind: InterpretValueKind::Aggregate(vec![
                    InterpretValue::int(tag.ty(), bad).expect("tag"),
                ]),
            }],
        ));
    }
    runs
}

/// The decoder differential over the compiler's own artifacts (target
/// record, proof annotations, obligations, explicit discriminants, layout
/// records, casts, `switch`), and `fieldless.bin` with its layout records
/// dropped: every unmutated artifact decodes to the reader's module, and
/// every one-byte change (the low and high bit flipped, and `0xff`) is judged
/// as `semr_decoder_agrees_with_the_binary_reader_on_mutated_blobs` judges one.
#[test]
fn semr_decoder_agrees_on_mutated_compiled_artifacts() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let mut artifacts: Vec<(String, Vec<u8>)> = compiled_artifacts()
        .into_iter()
        .map(|(name, bytes, _)| (name, bytes))
        .collect();
    let base = trust_ir::binary::deserialize_module(
        &artifacts
            .iter()
            .find(|(name, _)| name == "fieldless")
            .expect("fieldless.bin")
            .1,
    )
    .expect("fieldless.bin reads");
    artifacts.push((
        "fieldless without layout records".into(),
        trust_ir::binary::serialize_module(&fieldless_variant(&base, 0)).expect("serialize"),
    ));
    let mut blobs: Vec<(BlobKind, String, Vec<u8>)> = Vec::new();
    for (label, blob) in &artifacts {
        for i in 0..blob.len() {
            for flip in [0x01u8, 0x80, 0xff] {
                let mut m = blob.clone();
                m[i] ^= flip;
                let kind = if i < 8 {
                    BlobKind::HeaderOrTrailerFault
                } else {
                    BlobKind::Mutated
                };
                blobs.push((kind, format!("{label} byte {i} ^ {flip:#04x}"), m));
            }
        }
        blobs.push((BlobKind::Written, label.clone(), blob.clone()));
    }
    let (rust_ok, equal) = judge_decodes(exe, &blobs, "mutated compiled artifacts");
    let written = artifacts.len();
    assert_eq!(
        written, 11,
        "ten artifacts and the layout-free fieldless module"
    );
    assert!(
        rust_ok > written && equal > written,
        "the unmutated artifacts decode, and some mutations decode in both: {rust_ok} accepted, \
         {equal} equal"
    );
}

/// Direct calls (the generator mints none): a callee's environment is its
/// own, results bind in the caller, the call depth is exhausted by name
/// (`OutOfFuel` in both engines at the 65th nested call under depth 64), and
/// a callee's panic is the run's. (A binding frame cannot cross a call: the
/// validator refuses a slot read through a `Ptr` parameter,
/// `BindingFrameNotOpen`.)
#[test]
fn semr_direct_calls_agree_with_the_interpreter() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    // The interpreter recurses once per call level; 65 debug-build levels
    // outgrow the default test-thread stack.
    std::thread::Builder::new()
        .stack_size(512 << 20)
        .spawn(|| semr_direct_calls_body(exe))
        .expect("spawn")
        .join()
        .expect("the direct-call differential");
}

/// The direct-call module and runs (`semr_direct_calls_agree_with_the_interpreter`, and the
/// parity gate; the interpreter needs a deep stack for them).
fn semr_direct_calls_case() -> SemrCase {
    use trust_ir::inst::{BinOp, ICmpOp};
    let mut mb = ModuleBuilder::new("semr_calls");
    let ft_ii_i = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
    let ft_i_i = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let ft_u_u = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let ft_b_x = mb.add_func_type(vec![Ty::Bool], vec![Ty::I32]);
    // fn0: a * b + 1
    let mut fb = mb.function("mul_plus", ft_ii_i);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let p = fb.binop(BinOp::Mul, Ty::I64, a, b);
    let one = fb.iconst(Ty::I64, 1);
    let r = fb.binop(BinOp::Add, Ty::I64, p, one);
    fb.ret(vec![r]);
    let mul_plus = fb.build();
    // fn1: mul_plus(x, x) - 3
    let mut fb = mb.function("f", ft_i_i);
    let e = fb.create_block();
    let x = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let g = fb.call(mul_plus, vec![x, x]);
    let three = fb.iconst(Ty::I64, 3);
    let r = fb.binop(BinOp::Sub, Ty::I64, g, three);
    fb.ret(vec![r]);
    let f = fb.build();
    // fn2: count(n) = if n == 0 { 0 } else { count(n - 1) + 1 }
    let count = FuncId::new(2);
    let mut fb = mb.function("count", ft_u_u);
    let e = fb.create_block();
    let zero_bb = fb.create_block();
    let rec_bb = fb.create_block();
    let n = fb.add_block_param(e, Ty::U32);
    fb.switch_to_block(e);
    let z = fb.iconst(Ty::U32, 0);
    let c = fb.icmp(ICmpOp::Eq, Ty::U32, n, z);
    fb.condbr(c, zero_bb, vec![], rec_bb, vec![]);
    fb.switch_to_block(zero_bb);
    let z2 = fb.iconst(Ty::U32, 0);
    fb.ret(vec![z2]);
    fb.switch_to_block(rec_bb);
    let one = fb.iconst(Ty::U32, 1);
    let m = fb.binop(BinOp::Sub, Ty::U32, n, one);
    let r = fb.call(count, vec![m]);
    let s = fb.binop(BinOp::Add, Ty::U32, r, one);
    fb.ret(vec![s]);
    assert_eq!(fb.build(), count);
    // fn3 / fn4: a callee that asserts its argument.
    let checker = FuncId::new(4);
    let mut fb = mb.function("calls_checker", ft_b_x);
    let e = fb.create_block();
    let c = fb.add_block_param(e, Ty::Bool);
    fb.switch_to_block(e);
    let r = fb.call(checker, vec![c]);
    fb.ret(vec![r]);
    let calls_checker = fb.build();
    let mut fb = mb.function("checker", ft_b_x);
    let e = fb.create_block();
    let c = fb.add_block_param(e, Ty::Bool);
    fb.switch_to_block(e);
    fb.assert(c);
    let k = fb.iconst(Ty::I32, 9);
    fb.ret(vec![k]);
    assert_eq!(fb.build(), checker);
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errs = trust_ir_build::validate_module(&module);
    assert!(errs.is_empty(), "the call module validates: {errs:?}");

    let i64a = |v: i64| InterpretValue::int(Ty::I64, i128::from(v)).expect("i64");
    let u32a = |v: u32| InterpretValue::int(Ty::U32, i128::from(v)).expect("u32");
    let runs = vec![
        (f, vec![i64a(5)]),
        (f, vec![i64a(i64::MIN)]),
        (count, vec![u32a(3)]),
        (count, vec![u32a(64)]),
        (count, vec![u32a(65)]),
        (count, vec![u32a(500)]),
        (calls_checker, vec![InterpretValue::bool(true)]),
        (calls_checker, vec![InterpretValue::bool(false)]),
    ];
    SemrCase {
        label: "calls".into(),
        module,
        runs,
    }
}

fn semr_direct_calls_body(exe: &Path) {
    let case = semr_direct_calls_case();
    let batch = case.batch();
    let reports = semr_differential(exe, std::slice::from_ref(&batch));
    let t = tally(&reports);
    assert_no_mismatch(&t, "SemR, direct calls");
    assert!(t.unsupported.is_empty(), "{:?}", t.unsupported);
    assert_eq!(t.agreed.get("ok").copied(), Some(5), "{:?}", t.agreed);
    assert_eq!(
        t.agreed.get("out_of_fuel").copied(),
        Some(2),
        "{:?}",
        t.agreed
    );
    assert_eq!(t.agreed.get("panic").copied(), Some(1), "{:?}", t.agreed);
    assert_eq!(
        reports[3].lean,
        Verdict::Ok(vec![Val::Int { width: 32, raw: 64 }])
    );
}

/// Repeat the COMPLETE operator roster on both explicit layouts, including
/// signed division, shift bounds and checked overflow at the pointer width.
#[test]
fn semr_target_operator_cells_agree_with_the_interpreter() {
    for bits in [32, 64] {
        semr_operator_cells(Some(semr_target(bits)));
    }
}

fn semr_target(bits: u32) -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: if bits == 32 {
            "wasm32-unknown-unknown"
        } else {
            "aarch64-apple-darwin"
        }
        .into(),
        pointer_size: bits / 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    }
}

/// Casts use the actual pointer width, including signed residues and a
/// target-dependent bitcast mismatch. Switch transfers typed block arguments.
#[test]
fn semr_target_casts_and_switch_arguments_agree() {
    use trust_ir::inst::{CastOp, SwitchCase};
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    for bits in [32, 64] {
        let mut mb = ModuleBuilder::new_with_target_info("semr_target_casts", semr_target(bits));
        let mut runs = Vec::new();
        for (name, op, src, dst, values) in [
            (
                "widen_signed",
                CastOp::SExt,
                Ty::Isize,
                Ty::I64,
                vec![-7, -1, 0, (1i128 << (bits - 1)) - 1],
            ),
            (
                "widen_unsigned",
                CastOp::ZExt,
                Ty::Usize,
                Ty::U64,
                vec![0, 1, (1i128 << bits) - 1],
            ),
            (
                "small_signed",
                CastOp::SExt,
                Ty::I8,
                Ty::Isize,
                vec![-128, -7, 127],
            ),
            (
                "narrow_pointer",
                CastOp::Trunc,
                Ty::U64,
                Ty::Usize,
                vec![0, (1i128 << 32) + 3, u64::MAX as i128],
            ),
            (
                "narrow_signed",
                CastOp::Trunc,
                Ty::Isize,
                Ty::I8,
                vec![-7, -1, 257],
            ),
            (
                "same_width",
                CastOp::Bitcast,
                Ty::Isize,
                Ty::Usize,
                vec![-7, -1, 0],
            ),
            (
                "target_dependent_width",
                CastOp::Bitcast,
                Ty::U32,
                Ty::Usize,
                vec![0, u32::MAX as i128],
            ),
        ] {
            let ft = mb.add_func_type(vec![src.clone()], vec![dst.clone()]);
            let mut fb = mb.function(name, ft);
            let entry = fb.create_block();
            let arg = fb.add_block_param(entry, src.clone());
            fb.switch_to_block(entry);
            let result = fb.cast(op, src.clone(), dst, arg);
            fb.ret(vec![result]);
            let fid = fb.build();
            runs.extend(values.into_iter().map(|value| {
                (
                    fid,
                    vec![InterpretValue::int(src.clone(), value).expect("integer argument")],
                )
            }));
        }
        let ft = mb.add_func_type(vec![Ty::Isize, Ty::I64], vec![Ty::Isize]);
        let mut fb = mb.function("switch_arguments", ft);
        let entry = fb.create_block();
        let value = fb.add_block_param(entry, Ty::Isize);
        let tag = fb.add_block_param(entry, Ty::I64);
        let matched = fb.create_block();
        let forwarded = fb.add_block_param(matched, Ty::Isize);
        let default = fb.create_block();
        let fallback = fb.add_block_param(default, Ty::Isize);
        fb.switch_to_block(entry);
        let seven = fb.iconst(Ty::Isize, -7);
        fb.switch(
            tag,
            vec![SwitchCase {
                value: trust_ir::Constant::Int(1),
                target: matched,
                args: vec![value],
            }],
            default,
            vec![seven],
        );
        fb.switch_to_block(matched);
        fb.ret(vec![forwarded]);
        fb.switch_to_block(default);
        fb.ret(vec![fallback]);
        let fid = fb.build();
        for value in [-1, 0, (1i128 << (bits - 1)) - 1] {
            for tag in [0, 1, 2] {
                runs.push((
                    fid,
                    vec![
                        InterpretValue::int(Ty::Isize, value).unwrap(),
                        InterpretValue::int(Ty::I64, tag).unwrap(),
                    ],
                ));
            }
        }
        let module = mb.build().expect("cast and switch fixture");
        let batch = Batch {
            label: format!("target{bits} casts and switch"),
            module: &module,
            runs,
        };
        let reports = semr_differential(exe, &[batch]);
        assert_eq!(reports.len(), 30);
        let tally = tally(&reports);
        assert_no_mismatch(&tally, &format!("target{bits} casts and switch"));
        assert!(tally.unsupported.is_empty(), "{:?}", tally.unsupported);
        assert_eq!(
            tally.agreed.get("type_error").copied().unwrap_or(0),
            if bits == 64 { 2 } else { 0 }
        );
    }
}

/// Entry integers carry their actual source width. Preserve signed values
/// through real direct calls and returns; reject overflow and arity errors
/// rather than truncating them. Constants use the target width as well.
#[test]
fn semr_target_entries_calls_constants_and_refusals_agree() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    for bits in [32, 64] {
        let mut mb = ModuleBuilder::new_with_target_info("semr_target_values", semr_target(bits));
        let mut identities = Vec::new();
        for ty in [Ty::Isize, Ty::Usize] {
            let ft = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
            let mut fb = mb.function(format!("identity_{ty}"), ft);
            let block = fb.create_block();
            let x = fb.add_block_param(block, ty.clone());
            fb.switch_to_block(block);
            fb.ret(vec![x]);
            let identity = fb.build();
            let mut fb = mb.function(format!("caller_{ty}"), ft);
            let block = fb.create_block();
            let x = fb.add_block_param(block, ty.clone());
            fb.switch_to_block(block);
            let r = fb.call(identity, vec![x]);
            fb.ret(vec![r]);
            identities.push((ty, fb.build()));
        }
        let ft = mb.add_func_type(vec![], vec![Ty::Usize, Ty::Isize]);
        let mut fb = mb.function("constants", ft);
        let block = fb.create_block();
        fb.switch_to_block(block);
        let u = fb.const_value(Ty::Usize, trust_ir::Constant::Int((1i128 << 32) + 3));
        let s = fb.const_value(Ty::Isize, trust_ir::Constant::Int(-7));
        fb.ret(vec![u, s]);
        let constants = fb.build();
        let module = mb.build().expect("target value fixture");
        let min = -(1i128 << (bits - 1));
        let max = (1i128 << (bits - 1)) - 1;
        let mut runs = vec![(constants, vec![])];
        for (ty, id) in &identities {
            let values = if *ty == Ty::Isize {
                vec![min, -7, -1, 0, max]
            } else {
                vec![0, 7, (1i128 << bits) - 1]
            };
            for source_bits in [bits, 64, 128] {
                for value in &values {
                    runs.push((
                        *id,
                        vec![InterpretValue::int_at(ty.clone(), *value, source_bits).unwrap()],
                    ));
                }
            }
            // A narrower embedder value widens by its signed meaning, not
            // by zero-extending its residue (e.g. i8(-7) to isize64).
            for source_bits in [8, 32] {
                let value = if *ty == Ty::Isize { -7 } else { 7 };
                runs.push((
                    *id,
                    vec![InterpretValue::int_at(ty.clone(), value, source_bits).unwrap()],
                ));
            }
        }
        let positives = runs.len();
        let signed = identities[0].1;
        let unsigned = identities[1].1;
        for value in [min - 1, max + 1] {
            runs.push((
                signed,
                vec![InterpretValue::int_at(Ty::Isize, value, 128).unwrap()],
            ));
        }
        runs.push((
            unsigned,
            vec![InterpretValue::int_at(Ty::Usize, 1i128 << bits, 128).unwrap()],
        ));
        let range_end = runs.len();
        runs.push((signed, vec![]));
        runs.push((signed, vec![InterpretValue::int(Ty::Isize, 1).unwrap(); 2]));
        let batch = Batch {
            label: format!("target values {bits}"),
            module: &module,
            runs,
        };
        let reports = semr_differential(exe, &[batch]);
        assert_eq!(reports.len(), range_end + 2);
        let counts = tally(&reports);
        assert_no_mismatch(&counts, "SemR target entry/call/return/constant");
        assert!(counts.unsupported.is_empty(), "{:?}", counts.unsupported);
        for report in &reports[..positives] {
            assert_eq!(report.rust.class(), "ok", "{report:?}");
            assert_eq!(
                report.lean, report.rust,
                "exact width and value: {report:?}"
            );
        }
        for report in &reports[positives..range_end] {
            assert_eq!(report.rust.class(), "type_error", "{report:?}");
            assert_eq!(report.lean.class(), "type_error", "{report:?}");
        }
        for report in &reports[range_end..] {
            assert!(
                matches!(&report.rust, Verdict::TypeError(m) if m.starts_with("signature_mismatch:")),
                "{report:?}"
            );
            assert!(
                matches!(&report.lean, Verdict::TypeError(m) if m.starts_with("SignatureMismatch:")),
                "{report:?}"
            );
        }
        let mask = (1u128 << bits) - 1;
        assert_eq!(
            reports[0].lean,
            Verdict::Ok(vec![
                Val::Int {
                    width: bits,
                    raw: ((1u128 << 32) + 3) & mask
                },
                Val::Int {
                    width: bits,
                    raw: (1u128 << bits) - 7
                },
            ])
        );

        // Adversarial unvalidated fixture: both engines must still check the
        // actual return against the declared signature, at the target width.
        let mut forged = module.clone();
        let sig = forged.functions.iter().find(|f| f.id == signed).unwrap().ty;
        forged.func_types[sig.0 as usize].returns = vec![Ty::Usize];
        let batch = Batch {
            label: format!("wrong return {bits}"),
            module: &forged,
            runs: vec![(signed, vec![InterpretValue::int(Ty::Isize, -7).unwrap()])],
        };
        let reports = semr_differential(exe, &[batch]);
        assert_no_mismatch(&tally(&reports), "SemR target return guard");
        assert!(
            matches!(&reports[0].lean, Verdict::TypeError(m) if m.starts_with("SignatureMismatch:"))
        );
    }
}

/// Decode every target field exactly, including UTF-8 ABI bytes and aggregate
/// classification. Invalid layout is transportable but never executable;
/// malformed tags/string references remain decoder failures.
#[test]
fn semr_target_records_decode_exactly_and_execution_refuses_unknown_layouts() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let mut mb = ModuleBuilder::new("semr_target_record");
    let ft = mb.add_func_type(vec![], vec![Ty::Usize]);
    let mut fb = mb.function("seven", ft);
    let block = fb.create_block();
    fb.switch_to_block(block);
    let seven = fb.const_value(Ty::Usize, trust_ir::Constant::Int(7));
    fb.ret(vec![seven]);
    let fid = fb.build();
    let base = mb.build().unwrap();
    let mut modules = Vec::new();
    for (arch, bytes) in [
        ("x86_64", 8),
        ("x64", 8),
        ("aarch64", 8),
        ("arm64", 8),
        ("wasm64", 8),
        ("riscv64gc", 8),
        ("wasm32", 4),
    ] {
        let mut m = base.clone();
        let mut target = semr_target(bytes * 8);
        target.triple = format!("{arch}-unknown-test");
        target.abi = Some("ABI-α-\"\\".into());
        modules.push((true, m.clone())); // targetless compatibility for every adjacent case
        m.target_info = Some(target);
        modules.push((true, m));
    }
    for policy in [
        trust_ir::StructPassingPolicy::NativeC,
        trust_ir::StructPassingPolicy::AlwaysMemory,
    ] {
        let mut m = base.clone();
        let mut target = semr_target(64);
        target.struct_passing = policy;
        m.target_info = Some(target);
        modules.push((true, m));
    }
    for (arch, bytes, endian) in [
        ("aarch64", 8, trust_ir::Endianness::Big),
        ("aarch64", 4, trust_ir::Endianness::Little),
        ("wasm32", 8, trust_ir::Endianness::Little),
        ("i686", 4, trust_ir::Endianness::Little),
        ("aarch64x", 8, trust_ir::Endianness::Little),
        ("aarch64", 0, trust_ir::Endianness::Little),
        ("aarch64", u32::MAX, trust_ir::Endianness::Little),
    ] {
        let mut m = base.clone();
        let mut t = semr_target(64);
        t.triple = arch.into();
        t.pointer_size = bytes;
        t.endianness = endian;
        m.target_info = Some(t);
        modules.push((false, m));
    }
    let batches: Vec<_> = modules
        .iter()
        .enumerate()
        .map(|(i, (_, m))| Batch {
            label: format!("target record {i}"),
            module: m,
            runs: vec![(fid, vec![])],
        })
        .collect();
    let reports = semr_differential(exe, &batches);
    assert_eq!(reports.len(), modules.len());
    for ((allowed, m), report) in modules.iter().zip(&reports) {
        if *allowed {
            let bits = m.pointer_bits();
            let expected = Verdict::Ok(vec![Val::Int {
                width: bits,
                raw: 7,
            }]);
            assert_eq!(report.rust, expected, "{report:?}");
            assert_eq!(report.lean, expected, "{report:?}");
        } else {
            assert!(
                matches!(&report.rust, Verdict::Unsupported(_)),
                "{report:?}"
            );
            assert_eq!(
                report.lean,
                Verdict::Unsupported("target.byte_model".into())
            );
        }
    }
    let mut blobs = Vec::new();
    for (i, (_, m)) in modules.iter().enumerate() {
        let blob = trust_ir::binary::serialize_module(m).unwrap();
        blobs.push((BlobKind::Written, format!("target {i}"), blob.clone()));
        one_byte_mutations(&format!("target {i}"), &blob, &mut blobs);
    }
    let (_, equal) = judge_decodes(exe, &blobs, "complete target records and mutations");
    assert!(
        equal >= modules.len(),
        "every original target record is decoded exactly"
    );
}

fn semr_operator_cells(target: Option<trust_ir::TargetInfo>) {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let case = semr_operator_cells_case_for_target(target);
    let batch = case.batch();
    let t = tally(&semr_differential(exe, std::slice::from_ref(&batch)));
    assert_no_mismatch(&t, "SemR, explicit-target operator cells");
    assert!(t.unsupported.is_empty(), "{:?}", t.unsupported);
    let ok = t.agreed.get("ok").copied().unwrap_or(0);
    let ub = t.agreed.get("ub").copied().unwrap_or(0);
    assert!(ok > 30_000 && ub > 1_000, "{:?}", t.agreed);
}

/// The complete default-target operator corpus also feeds the parity gate.
fn semr_operator_cells_case() -> SemrCase {
    semr_operator_cells_case_for_target(None)
}

fn semr_operator_cells_case_for_target(target: Option<trust_ir::TargetInfo>) -> SemrCase {
    use trust_ir::inst::{BinOp, ICmpOp, OverflowOp, UnOp};
    let int_tys = semr_int_tys();
    let binops = [
        BinOp::Add,
        BinOp::Sub,
        BinOp::Mul,
        BinOp::UDiv,
        BinOp::SDiv,
        BinOp::URem,
        BinOp::SRem,
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
        BinOp::Shl,
        BinOp::LShr,
        BinOp::AShr,
        BinOp::RotL,
        BinOp::RotR,
    ];
    let unops = [
        UnOp::Neg,
        UnOp::Not,
        UnOp::CtPop,
        UnOp::CtLz,
        UnOp::CtTz,
        UnOp::BSwap,
        UnOp::BitReverse,
    ];
    let icmps = [
        ICmpOp::Eq,
        ICmpOp::Ne,
        ICmpOp::Ult,
        ICmpOp::Ule,
        ICmpOp::Ugt,
        ICmpOp::Uge,
        ICmpOp::Slt,
        ICmpOp::Sle,
        ICmpOp::Sgt,
        ICmpOp::Sge,
    ];
    let ovfs = [
        OverflowOp::AddOverflow,
        OverflowOp::SubOverflow,
        OverflowOp::MulOverflow,
    ];
    let pointer_bits = target.as_ref().map_or(64, |t| t.pointer_size * 8);
    let edges = |ty: &Ty| -> Vec<InterpretValue> {
        let bits = if matches!(ty, Ty::Isize | Ty::Usize) {
            pointer_bits
        } else {
            semr_bits(ty)
        };
        let sign = 1i128 << (bits - 1);
        let min = if bits == 128 { i128::MIN } else { -sign };
        let max = if bits == 128 { i128::MAX } else { sign - 1 };
        [
            0,
            1,
            2,
            3,
            7,
            -1,
            -2,
            -7,
            min,
            max,
            i128::from(bits) - 1,
            i128::from(bits),
        ]
        .into_iter()
        .map(|v| InterpretValue::int_at(ty.clone(), v, pointer_bits).expect("edge operand"))
        .collect()
    };
    let mut mb = match target {
        None => ModuleBuilder::new("semr_cells"),
        Some(target) => ModuleBuilder::new_with_target_info("semr_cells", target),
    };
    let mut runs: Vec<(FuncId, Vec<InterpretValue>)> = Vec::new();
    for ty in &int_tys {
        let e = edges(ty);
        let pairs: Vec<Vec<InterpretValue>> = e
            .iter()
            .flat_map(|a| e.iter().map(move |b| vec![a.clone(), b.clone()]))
            .collect();
        let ft2 = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
        for op in binops {
            let mut fb = mb.function(format!("{op:?}_{ty}"), ft2);
            let b0 = fb.create_block();
            let x = fb.add_block_param(b0, ty.clone());
            let y = fb.add_block_param(b0, ty.clone());
            fb.switch_to_block(b0);
            let r = fb.binop(op, ty.clone(), x, y);
            fb.ret(vec![r]);
            let id = fb.build();
            runs.extend(pairs.iter().map(|p| (id, p.clone())));
        }
        let ftc = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![Ty::Bool]);
        for op in icmps {
            let mut fb = mb.function(format!("{op:?}_{ty}"), ftc);
            let b0 = fb.create_block();
            let x = fb.add_block_param(b0, ty.clone());
            let y = fb.add_block_param(b0, ty.clone());
            fb.switch_to_block(b0);
            let r = fb.icmp(op, ty.clone(), x, y);
            fb.ret(vec![r]);
            let id = fb.build();
            runs.extend(pairs.iter().map(|p| (id, p.clone())));
        }
        let fto = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone(), Ty::Bool]);
        for op in ovfs {
            let mut fb = mb.function(format!("{op:?}_{ty}"), fto);
            let b0 = fb.create_block();
            let x = fb.add_block_param(b0, ty.clone());
            let y = fb.add_block_param(b0, ty.clone());
            fb.switch_to_block(b0);
            let (r, f) = fb.overflow(op, ty.clone(), x, y);
            fb.ret(vec![r, f]);
            let id = fb.build();
            runs.extend(pairs.iter().map(|p| (id, p.clone())));
        }
        let ft1 = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
        for op in unops {
            let mut fb = mb.function(format!("{op:?}_{ty}"), ft1);
            let b0 = fb.create_block();
            let x = fb.add_block_param(b0, ty.clone());
            fb.switch_to_block(b0);
            let r = fb.unop(op, ty.clone(), x);
            fb.ret(vec![r]);
            let id = fb.build();
            runs.extend(e.iter().map(|a| (id, vec![a.clone()])));
        }
    }
    let bools = [false, true];
    let bool_pairs: Vec<Vec<InterpretValue>> = bools
        .iter()
        .flat_map(|a| {
            bools
                .iter()
                .map(move |b| vec![InterpretValue::bool(*a), InterpretValue::bool(*b)])
        })
        .collect();
    let ftb = mb.add_func_type(vec![Ty::Bool, Ty::Bool], vec![Ty::Bool]);
    for op in [
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
        BinOp::BAnd,
        BinOp::BOr,
        BinOp::BXor,
    ] {
        let mut fb = mb.function(format!("{op:?}_bool"), ftb);
        let b0 = fb.create_block();
        let x = fb.add_block_param(b0, Ty::Bool);
        let y = fb.add_block_param(b0, Ty::Bool);
        fb.switch_to_block(b0);
        let r = fb.binop(op, Ty::Bool, x, y);
        fb.ret(vec![r]);
        let id = fb.build();
        runs.extend(bool_pairs.iter().map(|p| (id, p.clone())));
    }
    for op in icmps {
        let mut fb = mb.function(format!("{op:?}_bool"), ftb);
        let b0 = fb.create_block();
        let x = fb.add_block_param(b0, Ty::Bool);
        let y = fb.add_block_param(b0, Ty::Bool);
        fb.switch_to_block(b0);
        let r = fb.icmp(op, Ty::Bool, x, y);
        fb.ret(vec![r]);
        let id = fb.build();
        runs.extend(bool_pairs.iter().map(|p| (id, p.clone())));
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errs = trust_ir_build::validate_module(&module);
    assert!(errs.is_empty(), "the cell module validates: {errs:?}");
    SemrCase {
        label: "operator cells".into(),
        module,
        runs,
    }
}

/// The operator layer cell by cell: every integer `BinOp` (the rotates
/// included), `UnOp`, `ICmp` and `Overflow` at every integer type (`isize` and
/// `usize` at the 64 bits a module with no target record has),
/// and the `Bool` binops and compares, over the edge operands (0, 1, 2, 3, 7,
/// −1, −2, −7, MIN, MAX, width − 1, width) in every pair. The generator draws
/// small magnitudes, so on its own it leaves the signed paths thin: SemR
/// mutants that drop `sdiv`'s sign, `ashr`'s fill or the signed-multiply
/// overflow edge survive the generator corpus and die here.
#[test]
fn semr_operator_cells_agree_with_the_interpreter() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let case = semr_operator_cells_case();
    let batch = case.batch();
    let t = tally(&semr_differential(exe, std::slice::from_ref(&batch)));
    assert_no_mismatch(&t, "SemR, operator cells");
    assert!(t.unsupported.is_empty(), "{:?}", t.unsupported);
    let ok = t.agreed.get("ok").copied().unwrap_or(0);
    let ub = t.agreed.get("ub").copied().unwrap_or(0);
    assert!(ok > 30_000 && ub > 1_000, "{:?}", t.agreed);
}

/// The unvalidated frame-discipline bodies and runs
/// (`semr_frame_discipline_agrees_on_unvalidated_bodies`, and the parity gate).
fn semr_frame_discipline_case() -> SemrCase {
    use trust_ir::inst::{BindingFrameDef, BindingSlot};
    use trust_ir::value::BindingFrameId;
    let mut mb = ModuleBuilder::new("semr_frames");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let def = || {
        BindingFrameDef::new(
            BindingFrameId::new(0),
            "q",
            vec![
                BindingSlot::new("s0", Ty::I32),
                BindingSlot::new("s1", Ty::I32),
            ],
        )
    };
    let mut ids = Vec::new();
    // double close
    let mut fb = mb.function("double_close", ft);
    let b0 = fb.create_block();
    let x = fb.add_block_param(b0, Ty::I32);
    fb.switch_to_block(b0);
    let h = fb.open_frame(def());
    fb.close_frame(h);
    fb.close_frame(h);
    fb.ret(vec![x]);
    ids.push(fb.build());
    // bind through a closed lineage
    let mut fb = mb.function("bind_after_close", ft);
    let b0 = fb.create_block();
    let x = fb.add_block_param(b0, Ty::I32);
    fb.switch_to_block(b0);
    let h = fb.open_frame(def());
    fb.close_frame(h);
    let h2 = fb.bind_slot(h, 0, x);
    let _ = h2;
    fb.ret(vec![x]);
    ids.push(fb.build());
    // unbound slot read, returned: poison at the return boundary
    let mut fb = mb.function("return_poison", ft);
    let b0 = fb.create_block();
    let _x = fb.add_block_param(b0, Ty::I32);
    fb.switch_to_block(b0);
    let h = fb.open_frame(def());
    let v = fb.load_slot(h, 1, Ty::I32);
    let c = fb.copy(Ty::I32, v);
    fb.close_frame(h);
    fb.ret(vec![c]);
    ids.push(fb.build());
    // unbound slot read, only transported through a select; the bound value returned
    let mut fb = mb.function("transport_poison", ft);
    let b0 = fb.create_block();
    let x = fb.add_block_param(b0, Ty::I32);
    fb.switch_to_block(b0);
    let h = fb.open_frame(def());
    let h1 = fb.bind_slot(h, 0, x);
    let p = fb.load_slot(h1, 1, Ty::I32);
    let t = fb.bool_const(true);
    let s = fb.select(Ty::I32, t, x, p);
    let v = fb.load_slot(h1, 0, Ty::I32);
    let r = fb.binop(trust_ir::inst::BinOp::Add, Ty::I32, s, v);
    fb.close_frame(h1);
    fb.ret(vec![r]);
    ids.push(fb.build());
    // poison inspected by arithmetic
    let mut fb = mb.function("inspect_poison", ft);
    let b0 = fb.create_block();
    let x = fb.add_block_param(b0, Ty::I32);
    fb.switch_to_block(b0);
    let h = fb.open_frame(def());
    let p = fb.load_slot(h, 0, Ty::I32);
    let r = fb.binop(trust_ir::inst::BinOp::Add, Ty::I32, p, x);
    fb.close_frame(h);
    fb.ret(vec![r]);
    ids.push(fb.build());
    // slot out of range
    let mut fb = mb.function("slot_out_of_range", ft);
    let b0 = fb.create_block();
    let x = fb.add_block_param(b0, Ty::I32);
    fb.switch_to_block(b0);
    let h = fb.open_frame(def());
    let h1 = fb.bind_slot(h, 5, x);
    fb.close_frame(h1);
    fb.ret(vec![x]);
    ids.push(fb.build());
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(
        !trust_ir_build::validate_module(&module).is_empty(),
        "the validator refuses these bodies"
    );
    let arg = InterpretValue::int(Ty::I32, 21).expect("i32");
    SemrCase {
        label: "frames".into(),
        module,
        runs: ids.iter().map(|id| (*id, vec![arg.clone()])).collect(),
    }
}

/// Binding-frame discipline and poison on bodies the VALIDATOR refuses (it
/// rules these out statically, so no validated corpus reaches them, yet both
/// engines execute what they are given): a double close, a bind through a
/// closed lineage, an unbound slot read that is returned (poison crossing the
/// return boundary) or only copied and branched past, and a slot index out of
/// range. Each is UB, or `Ok` where poison is only transported, in both.
#[test]
fn semr_frame_discipline_agrees_on_unvalidated_bodies() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let case = semr_frame_discipline_case();
    let batch = case.batch();
    let reports = semr_differential(exe, std::slice::from_ref(&batch));
    let t = tally(&reports);
    assert_no_mismatch(&t, "SemR, frame discipline");
    assert!(t.unsupported.is_empty(), "{:?}", t.unsupported);
    assert_eq!(t.agreed.get("ub").copied(), Some(5), "{:?}", t.agreed);
    assert_eq!(t.agreed.get("ok").copied(), Some(1), "{:?}", t.agreed);
}

// ---------------------------------------------------------------------------
// SemR, the paths the RM4 reviews found unguarded (2026-10-26): the wire
// version gates, UTF-8, the pointer-width types, constants outside their
// type's range, the instruction budget's boundary, poison and type-error
// paths, every assert kind's message, and the enum tag width.
// ---------------------------------------------------------------------------

/// The wire version a blob's header names.
fn header_version(blob: &[u8]) -> u32 {
    u32::from_le_bytes(blob[8..12].try_into().expect("a header"))
}

fn relabelled(blob: &[u8], version: u32) -> Vec<u8> {
    let mut b = blob.to_vec();
    b[8..12].copy_from_slice(&version.to_le_bytes());
    b
}

/// Geometry-only storage has a real v64 spelling, while SemR's wire fragment
/// keeps its explicit type refusal. Earlier tags and invalid geometry remain
/// malformed; a future version is refused before reading its payload.
#[test]
fn semr_storage_wire_boundary_is_explicit() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let mut mb = ModuleBuilder::new("semr_storage_boundary");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("root", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.alloca(Ty::Storage(trust_ir::StorageLayout::new(80, 8)));
    let answer = fb.uconst(Ty::U64, 42);
    fb.ret(vec![answer]);
    let root = fb.build();
    let module = mb.build().expect("valid geometry-only allocation");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    assert_eq!(
        run_rust(&module, root, &[]),
        Verdict::Ok(vec![Val::Int { width: 64, raw: 42 }])
    );
    let blob = trust_ir::binary::serialize_module(&module).expect("storage wire");
    assert_eq!(header_version(&blob), 64);
    assert_eq!(trust_ir::binary::deserialize_module(&blob).unwrap(), module);
    let old = relabelled(&blob, 63);
    // Serialization chooses the oldest sufficient format (v64 here), while
    // the decoder also accepts later shipped formats. A future version must
    // exceed the current reader ceiling, not just this witness's format.
    let future = relabelled(
        &blob,
        trust_ir::binary::FORMAT_VERSION
            .checked_add(1)
            .expect("wire format has an expressible future version"),
    );
    assert!(trust_ir::binary::deserialize_module(&old).is_err());
    assert!(trust_ir::binary::deserialize_module(&future).is_err());
    let positions: Vec<_> = blob
        .windows(3)
        .enumerate()
        .filter_map(|(i, bytes)| (bytes == [40, 80, 8]).then_some(i))
        .collect();
    assert_eq!(positions.len(), 1, "exact storage type in this witness");
    let mut invalid = blob.clone();
    invalid[positions[0] + 2] = 0;
    assert!(trust_ir::binary::deserialize_module(&invalid).is_err());
    assert_eq!(
        semr_decode(exe, &[blob, old, invalid, future]),
        vec![
            json!({"unsupported": "ty.storage"}),
            json!({"error": "decode: invalid Ty tag"}),
            json!({"error": "decode: invalid storage geometry"}),
            json!({"unsupported": "wire_version"}),
        ]
    );
}

/// Read one LEB128 `v32` at `*at` (the test's own witnesses only).
fn read_leb(blob: &[u8], at: &mut usize) -> u64 {
    let (mut v, mut shift) = (0u64, 0u32);
    loop {
        let b = blob[*at];
        *at += 1;
        v |= u64::from(b & 0x7f) << shift;
        if b < 0x80 {
            return v;
        }
        shift += 7;
    }
}

/// Skip one `Ty` of a witness (a primitive tag, or an enum's tag 19 and id).
fn skip_witness_ty(blob: &[u8], at: &mut usize) {
    let tag = blob[*at];
    *at += 1;
    match tag {
        0..=15 | 33 | 34 => {}
        19 => {
            read_leb(blob, at);
        }
        other => panic!("witnesses name primitive and enum types only (tag {other})"),
    }
}

/// Where a later version inserts a byte into a witness blob: just past each
/// signature record (`params`, `returns`, `vararg`; the v60 signature-ABI
/// presence byte) and just past each enum definition's layout byte (the v58
/// nominal-origin presence byte).
fn witness_insertion_points(blob: &[u8]) -> (Vec<usize>, Vec<usize>) {
    let mut at = 12;
    let strings = read_leb(blob, &mut at);
    for _ in 0..strings {
        let len = read_leb(blob, &mut at) as usize;
        at += len;
    }
    let _module_name = read_leb(blob, &mut at);
    let sigs = read_leb(blob, &mut at);
    let mut sig_ends = Vec::new();
    for _ in 0..sigs {
        for _ in 0..2 {
            let n = read_leb(blob, &mut at);
            for _ in 0..n {
                skip_witness_ty(blob, &mut at);
            }
        }
        at += 1; // vararg
        sig_ends.push(at);
    }
    assert_eq!(read_leb(blob, &mut at), 0, "witnesses declare no structs");
    let enums = read_leb(blob, &mut at);
    let mut enum_ends = Vec::new();
    for _ in 0..enums {
        let _id = read_leb(blob, &mut at);
        let _name = read_leb(blob, &mut at);
        let variants = read_leb(blob, &mut at);
        for _ in 0..variants {
            let _name = read_leb(blob, &mut at);
            let fields = read_leb(blob, &mut at);
            for _ in 0..fields {
                skip_witness_ty(blob, &mut at);
            }
            let names = read_leb(blob, &mut at);
            for _ in 0..names {
                read_leb(blob, &mut at);
            }
        }
        assert_eq!(read_leb(blob, &mut at), 0, "implicit discriminants");
        assert_eq!(blob[at], 0, "no tag representation");
        assert_eq!(blob[at + 1], 0, "no declared layout");
        at += 2;
        enum_ends.push(at);
    }
    (sig_ends, enum_ends)
}

/// `blob` (written at its own version, which is `>= 45`) rewritten to the
/// layout of the later version `to`: the trailing `drop_glue` (v55) and
/// `closure_layouts` (v58) counts appended as empty, the nominal-origin
/// presence byte (v58) inserted, absent, after each enum definition, and the
/// signature-ABI presence byte (v60) after each signature. Nothing else
/// changes between v45 and v62 for a module the witnesses build; the reader
/// accepting every rewritten blob is the check of that claim.
fn layout_at(blob: &[u8], to: u32) -> Vec<u8> {
    let from = header_version(blob);
    assert!(from >= 45 && to > from && to <= 62);
    let (sig_ends, enum_ends) = witness_insertion_points(blob);
    let mut points: Vec<usize> = Vec::new();
    if from < 60 && to >= 60 {
        points.extend(sig_ends);
    }
    if from < 58 && to >= 58 {
        points.extend(enum_ends);
    }
    points.sort_unstable();
    let mut b = blob.to_vec();
    for at in points.into_iter().rev() {
        b.insert(at, 0);
    }
    for gate in [55, 58] {
        if from < gate && to >= gate {
            b.push(0);
        }
    }
    relabelled(&b, to)
}

/// One small function per witness feature, each SemR decodes; the builder
/// raises the wire version by content.
fn gate_witnesses() -> Vec<(&'static str, u32, Module)> {
    use trust_ir::inst::{AssertOverflowOp, BinOp, UnOp};
    use trust_ir::{ArgExt, AssertKind, CallingConv, Linkage, ParamAttrs};
    let simple = |name: &str,
                  f: &dyn Fn(
        &mut trust_ir_build::FunctionBuilder<'_>,
        trust_ir::value::ValueId,
        trust_ir::value::ValueId,
    )|
     -> Module {
        let mut mb = ModuleBuilder::new(name);
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("w", ft);
        let b0 = fb.create_block();
        let x = fb.add_block_param(b0, Ty::I32);
        let y = fb.add_block_param(b0, Ty::I32);
        fb.switch_to_block(b0);
        f(&mut fb, x, y);
        fb.build();
        mb.build().expect("ModuleBuilder::build: witness")
    };
    let plain = |fb: &mut trust_ir_build::FunctionBuilder<'_>, x, y| {
        let r = fb.binop(BinOp::Add, Ty::I32, x, y);
        fb.ret(vec![r]);
    };
    let mut w41 = simple("w41", &plain);
    w41.functions[0].attrs.naked = true;
    w41.functions[0].attrs.params = vec![
        ParamAttrs {
            nonnull: true,
            ..ParamAttrs::default()
        },
        ParamAttrs::default(),
    ];
    w41.functions[0].linkage = Linkage::AvailableExternally;
    let mut w45 = simple("w45", &plain);
    w45.functions[0].attrs.params = vec![
        ParamAttrs {
            ext: ArgExt::SignExt,
            ..ParamAttrs::default()
        },
        ParamAttrs {
            noalias: true,
            ..ParamAttrs::default()
        },
    ];
    w45.functions[0].calling_conv = CallingConv::SysV64;
    // One module per v51 operator: a module holding two of them is refused
    // at v50 by the first, so the second's gate would go unread.
    let w51_binop = |op: BinOp| {
        simple("w51", &move |fb, x, y| {
            let r = fb.binop(op, Ty::I32, x, y);
            fb.ret(vec![r]);
        })
    };
    let w51_unop = |op: UnOp| {
        simple("w51", &move |fb, x, _| {
            let r = fb.unop(op, Ty::I32, x);
            fb.ret(vec![r]);
        })
    };
    let w52 = simple("w52", &|fb, x, y| {
        let t = fb.bool_const(true);
        fb.assert_kind(t, AssertKind::DivByZero);
        fb.assert_kind(t, AssertKind::Overflow(AssertOverflowOp::Mul));
        fb.assert_kind(t, AssertKind::BoundsCheck { index: x, len: y });
        let r = fb.binop(BinOp::RotL, Ty::I32, x, y);
        fb.ret(vec![r]);
    });
    // An enum beside a kinded assert: the v58 origin byte is per enum.
    let mut w52e = w52.clone();
    {
        use trust_ir::ty::{EnumDef, EnumVariant};
        use trust_ir::value::EnumId;
        w52e.enums.push(EnumDef::new(
            EnumId::new(0),
            "E",
            vec![
                EnumVariant {
                    name: "A".into(),
                    fields: vec![],
                    field_names: vec![],
                },
                EnumVariant {
                    name: "B".into(),
                    fields: vec![Ty::I32],
                    field_names: vec![],
                },
            ],
        ));
    }
    let (corpus, _) = gen_module_exec(1);
    vec![
        ("w38 (corpus seed 1)", 38, corpus),
        ("w41 (naked, linkage, param attrs)", 41, w41),
        ("w45 (signext, calling convention)", 45, w45),
        ("w51 rotl", 51, w51_binop(BinOp::RotL)),
        ("w51 rotr", 51, w51_binop(BinOp::RotR)),
        ("w51 ctlz", 51, w51_unop(UnOp::CtLz)),
        ("w51 cttz", 51, w51_unop(UnOp::CtTz)),
        ("w51 bswap", 51, w51_unop(UnOp::BSwap)),
        ("w51 bitreverse", 51, w51_unop(UnOp::BitReverse)),
        ("w52 (kinded asserts)", 52, w52),
        ("w52 (kinded asserts, an enum)", 52, w52e),
    ]
}

/// The version gates of the wire, v37–v63: each witness relabelled to every
/// version (a gate SemR reads at the wrong version decodes what the reader
/// refuses, or refuses what it reads), rewritten to the layout of each later
/// version of its epoch (v41–v44 gain the `tuple_layouts` count; v45–v62 the
/// `drop_glue` and `closure_layouts` counts and the signature-ABI byte), and
/// changed one bit at a time at its own version (the parameter-attribute
/// flag bits of v20/v45 and the `naked` bit of v41 among them).
#[test]
fn semr_decoder_version_gates_agree_with_the_binary_reader() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let mut blobs: Vec<(BlobKind, String, Vec<u8>)> = Vec::new();
    let mut synthesized = 0usize;
    for (label, version, module) in gate_witnesses() {
        let blob = trust_ir::binary::serialize_module(&module).expect("witness blob");
        assert_eq!(
            header_version(&blob),
            version,
            "{label}: the witness is written at v{version}"
        );
        for v in 37..=63u32 {
            if v != version {
                blobs.push((
                    if (38..=62).contains(&v) {
                        BlobKind::Relabelled
                    } else {
                        BlobKind::Mutated
                    },
                    format!("{label} relabelled v{v}"),
                    relabelled(&blob, v),
                ));
            }
        }
        // The same bytes are the layout of every version of the epoch
        // (v38–v40 for a v38 blob): one-bit changes there too, so a flag-bit
        // gate inside the epoch (the `naked` bit of v41, at v40) is read.
        if version == 38 {
            for v in [39u32, 40] {
                one_byte_mutations(
                    &format!("{label} relabelled v{v}"),
                    &relabelled(&blob, v),
                    &mut blobs,
                );
            }
        }
        if version == 41 {
            let mut b = blob.clone();
            b.push(0);
            for v in 42..=44u32 {
                blobs.push((
                    BlobKind::Synthesized,
                    format!("{label} laid out at v{v}"),
                    relabelled(&b, v),
                ));
                synthesized += 1;
            }
            one_byte_mutations(
                &format!("{label} laid out at v44"),
                &relabelled(&b, 44),
                &mut blobs,
            );
        }
        if version >= 45 {
            for v in version + 1..=62 {
                blobs.push((
                    BlobKind::Synthesized,
                    format!("{label} laid out at v{v}"),
                    layout_at(&blob, v),
                ));
                synthesized += 1;
            }
            if version < 62 {
                one_byte_mutations(
                    &format!("{label} laid out at v62"),
                    &layout_at(&blob, 62),
                    &mut blobs,
                );
            }
        }
        one_byte_mutations(label, &blob, &mut blobs);
        let mut longer = blob.clone();
        longer.push(0);
        blobs.push((
            BlobKind::HeaderOrTrailerFault,
            format!("{label} + 0x00"),
            longer,
        ));
        blobs.push((BlobKind::Written, label.to_string(), blob));
    }
    let (_, equal) = judge_decodes(exe, &blobs, "version gates");
    assert!(synthesized >= 100, "{synthesized}");
    let must_decode = blobs
        .iter()
        .filter(|(k, _, _)| matches!(k, BlobKind::Written | BlobKind::Synthesized))
        .count();
    assert!(equal >= must_decode, "{equal} < {must_decode}");
}

/// Rust's `String::from_utf8` rules in SemR's string pool: a surrogate, a
/// scalar past U+10FFFF, overlong forms, a lead byte no scalar starts with and
/// a bad continuation byte are each `malformed` in SemR exactly when the
/// reader refuses them; the valid originals decode.
#[test]
fn semr_decoder_utf8_agrees_with_the_binary_reader() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let mut mb = ModuleBuilder::new("utf8");
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let names = [
        "f_\u{e9}",
        "f_\u{20ac}",
        "f_\u{1d11e}",
        "f_\u{ffff}",
        "f_\u{10ffff}",
        "f_\u{7ff}",
    ];
    for name in names {
        let mut fb = mb.function(name, ft);
        let b0 = fb.create_block();
        fb.switch_to_block(b0);
        let k = fb.iconst(Ty::I32, 1);
        fb.ret(vec![k]);
        fb.build();
    }
    let module = mb.build().expect("utf8 module");
    let blob = trust_ir::binary::serialize_module(&module).expect("utf8 blob");
    let swaps: &[(&[u8], &[u8], &str)] = &[
        (&[0xc3, 0xa9], &[0xc0, 0xa9], "overlong 2-byte lead C0"),
        (&[0xc3, 0xa9], &[0xc1, 0x81], "overlong 2-byte lead C1"),
        (&[0xc3, 0xa9], &[0xc3, 0x41], "bad continuation"),
        (&[0xe2, 0x82, 0xac], &[0xed, 0xa0, 0x80], "surrogate U+D800"),
        (&[0xe2, 0x82, 0xac], &[0xed, 0xbf, 0xbf], "surrogate U+DFFF"),
        (&[0xe2, 0x82, 0xac], &[0xe0, 0x80, 0x80], "overlong 3-byte"),
        (
            &[0xe2, 0x82, 0xac],
            &[0xe0, 0x9f, 0xbf],
            "overlong 3-byte at U+07FF",
        ),
        (
            &[0xf0, 0x9d, 0x84, 0x9e],
            &[0xf4, 0x90, 0x80, 0x80],
            "U+110000",
        ),
        (
            &[0xf0, 0x9d, 0x84, 0x9e],
            &[0xf0, 0x80, 0x80, 0x80],
            "overlong 4-byte",
        ),
        (
            &[0xf0, 0x9d, 0x84, 0x9e],
            &[0xf0, 0x8f, 0xbf, 0xbf],
            "overlong 4-byte at U+FFFF",
        ),
        (
            &[0xf0, 0x9d, 0x84, 0x9e],
            &[0xf5, 0x80, 0x80, 0x80],
            "lead F5",
        ),
        (
            &[0xf0, 0x9d, 0x84, 0x9e],
            &[0xf8, 0x80, 0x80, 0x80],
            "lead F8",
        ),
        (
            &[0xf4, 0x8f, 0xbf, 0xbf],
            &[0xf4, 0x8f, 0xbf, 0x7f],
            "truncated scalar",
        ),
        (&[0xdf, 0xbf], &[0x80, 0xbf], "lone continuation"),
        // Valid rewrites (the reader accepts them; SemR must decode them):
        (&[0xc3, 0xa9], &[0xc2, 0x80], "U+0080"),
        (&[0xe2, 0x82, 0xac], &[0xed, 0x9f, 0xbf], "U+D7FF"),
        (&[0xe2, 0x82, 0xac], &[0xee, 0x80, 0x80], "U+E000"),
        (
            &[0xf0, 0x9d, 0x84, 0x9e],
            &[0xf0, 0x90, 0x80, 0x80],
            "U+10000",
        ),
    ];
    let mut blobs = vec![(BlobKind::Written, "utf8 module".to_string(), blob.clone())];
    for (from, to, what) in swaps {
        let at = blob
            .windows(from.len())
            .position(|w| w == *from)
            .unwrap_or_else(|| panic!("{what}: the original bytes {from:02x?} are in the pool"));
        let mut b = blob.clone();
        b[at..at + from.len()].copy_from_slice(to);
        let kind = if std::str::from_utf8(to).is_ok() {
            BlobKind::Synthesized
        } else {
            BlobKind::StringFault
        };
        blobs.push((kind, (*what).to_string(), b));
    }
    let (rust_ok, equal) = judge_decodes(exe, &blobs, "UTF-8");
    assert_eq!((rust_ok, equal), (5, 5));
}

/// The out-of-range constant module and runs
/// (`semr_out_of_range_constants_agree_with_the_interpreter`, and the parity gate).
fn semr_out_of_range_constants_case() -> SemrCase {
    use trust_ir::inst::{BinOp, ICmpOp};
    let mut mb = ModuleBuilder::new("semr_consts");
    let mut runs: Vec<(FuncId, Vec<InterpretValue>)> = Vec::new();
    for ty in semr_int_tys() {
        let bits = semr_bits(&ty);
        let mut lits: Vec<i128> = vec![
            0,
            -1,
            i128::MIN,
            i128::MAX,
            0x1234_5678_9abc_def0_1122_3344_5566_7788,
        ];
        if bits < 128 {
            let m = 1i128 << bits;
            let h = 1i128 << (bits - 1);
            lits.extend([m, m + 5, -m, -h - 1, h, -h, h - 1 + m, 3 * m + 7]);
        }
        let ft0 = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
        let ftc = mb.add_func_type(vec![ty.clone()], vec![Ty::Bool]);
        let zero = InterpretValue::int(ty.clone(), 0).expect("zero");
        let one = InterpretValue::int(ty.clone(), 1).expect("one");
        for lit in lits {
            let mut fb = mb.function(format!("ret_{ty}_{lit}"), ft0);
            let b0 = fb.create_block();
            let _x = fb.add_block_param(b0, ty.clone());
            fb.switch_to_block(b0);
            let c = fb.iconst(ty.clone(), lit);
            fb.ret(vec![c]);
            let id = fb.build();
            runs.push((id, vec![zero.clone()]));
            let mut fb = mb.function(format!("xor_{ty}_{lit}"), ft0);
            let b0 = fb.create_block();
            let x = fb.add_block_param(b0, ty.clone());
            fb.switch_to_block(b0);
            let c = fb.iconst(ty.clone(), lit);
            let r = fb.binop(BinOp::Xor, ty.clone(), c, x);
            fb.ret(vec![r]);
            let id = fb.build();
            runs.push((id, vec![zero.clone()]));
            runs.push((id, vec![one.clone()]));
            for op in [ICmpOp::Slt, ICmpOp::Ult, ICmpOp::Eq] {
                let mut fb = mb.function(format!("{op:?}_{ty}_{lit}"), ftc);
                let b0 = fb.create_block();
                let x = fb.add_block_param(b0, ty.clone());
                fb.switch_to_block(b0);
                let c = fb.iconst(ty.clone(), lit);
                let r = fb.icmp(op, ty.clone(), c, x);
                fb.ret(vec![r]);
                let id = fb.build();
                runs.push((id, vec![zero.clone()]));
            }
        }
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    SemrCase {
        label: "out-of-range constants".into(),
        module,
        runs,
    }
}

/// Constants outside their type's range (a wider literal, a negative literal
/// at an unsigned type, `i128::MIN`/`MAX` at every width): the stored value is
/// the literal's residue at the type's width, returned, combined and compared.
#[test]
fn semr_out_of_range_constants_agree_with_the_interpreter() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let case = semr_out_of_range_constants_case();
    let batch = case.batch();
    let t = tally(&semr_differential(exe, std::slice::from_ref(&batch)));
    assert_no_mismatch(&t, "SemR, out-of-range constants");
    assert!(t.unsupported.is_empty(), "{:?}", t.unsupported);
    assert!(
        t.agreed.get("ok").copied().unwrap_or(0) > 600,
        "{:?}",
        t.agreed
    );
}

/// Every integer type SemR carries, the pointer-width ones included (64 bits:
/// a module with no target record, the interpreter's default and SemR's pin).
fn semr_int_tys() -> [Ty; 12] {
    [
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::Isize,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::U128,
        Ty::Usize,
    ]
}

fn semr_bits(ty: &Ty) -> u32 {
    match ty {
        Ty::Isize | Ty::Usize => 64,
        other => other.bit_width().expect("integer type"),
    }
}

/// `count(n)`: a loop of six nodes per iteration (`6n + 5` nodes in all),
/// padded by `pad` copies on entry. Run at every budget from 0 to past the
/// end, the run ends `Ok` exactly from the budget that covers its last node
/// and is out of fuel at every budget below, in both engines; and at the
/// harness's own budget (`FUEL`), runs of exactly `FUEL - 1`, `FUEL` and
/// `FUEL + 1` nodes land on each side of it.
#[test]
fn semr_instruction_budget_boundary_agrees_with_the_interpreter() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    use trust_ir::inst::{BinOp, ICmpOp};
    let mut mb = ModuleBuilder::new("semr_fuel");
    let ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let mut ids = Vec::new();
    for pad in 0..=6u32 {
        let mut fb = mb.function(format!("count_pad{pad}"), ft);
        let entry = fb.create_block();
        let head = fb.create_block();
        let body = fb.create_block();
        let exit = fb.create_block();
        let n = fb.add_block_param(entry, Ty::U32);
        let i = fb.add_block_param(head, Ty::U32);
        fb.switch_to_block(entry);
        let mut v = n;
        for _ in 0..pad {
            v = fb.copy(Ty::U32, v);
        }
        fb.br(head, vec![v]);
        fb.switch_to_block(head);
        let z = fb.iconst(Ty::U32, 0);
        let c = fb.icmp(ICmpOp::Eq, Ty::U32, i, z);
        fb.condbr(c, exit, vec![], body, vec![]);
        fb.switch_to_block(body);
        let one = fb.iconst(Ty::U32, 1);
        let j = fb.binop(BinOp::Sub, Ty::U32, i, one);
        fb.br(head, vec![j]);
        fb.switch_to_block(exit);
        fb.ret(vec![i]);
        ids.push(fb.build());
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errs = trust_ir_build::validate_module(&module);
    assert!(errs.is_empty(), "the loop module validates: {errs:?}");
    let u = |v: u32| InterpretValue::int(Ty::U32, i128::from(v)).expect("u32");
    let mut ok = 0usize;
    let mut out = 0usize;
    for n in 0..=3u32 {
        let total = 6 * u64::from(n) + 5;
        for fuel in 0..=total + 2 {
            let batch = Batch {
                label: format!("count({n}) at fuel {fuel}"),
                module: &module,
                runs: vec![(ids[0], vec![u(n)])],
            };
            let reports = semr_differential_fuel(exe, std::slice::from_ref(&batch), fuel);
            let t = tally(&reports);
            assert_no_mismatch(&t, &batch.label);
            let want = if fuel >= total { "ok" } else { "out_of_fuel" };
            assert_eq!(reports[0].rust.class(), want, "{}", batch.label);
            ok += usize::from(want == "ok");
            out += usize::from(want == "out_of_fuel");
        }
    }
    // 6 * 1665 + 5 = 9995 nodes; pads 4, 5, 6 make FUEL - 1, FUEL, FUEL + 1.
    let runs: Vec<(FuncId, Vec<InterpretValue>)> =
        (4..=6).map(|pad| (ids[pad], vec![u(1665)])).collect();
    let batch = Batch {
        label: "count(1665) padded to FUEL - 1, FUEL, FUEL + 1".into(),
        module: &module,
        runs,
    };
    let reports = semr_differential(exe, std::slice::from_ref(&batch));
    assert_no_mismatch(&tally(&reports), &batch.label);
    let classes: Vec<&str> = reports.iter().map(|r| r.lean.class()).collect();
    assert_eq!(classes, ["ok", "ok", "out_of_fuel"]);
    assert!(ok > 0 && out > 0);
}

/// The poison and type-error bodies, their runs, and each run's expected verdict class
/// (`semr_poison_and_type_error_paths_agree_with_the_interpreter`, and the parity gate).
fn semr_poison_paths_case() -> (SemrCase, Vec<&'static str>) {
    use trust_ir::inst::{BinOp, BindingFrameDef, BindingSlot};
    use trust_ir::value::{BindingFrameId, BlockId};
    let mut mb = ModuleBuilder::new("semr_paths");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let def = || {
        BindingFrameDef::new(
            BindingFrameId::new(0),
            "q",
            vec![
                BindingSlot::new("b", Ty::Bool),
                BindingSlot::new("i", Ty::I32),
                BindingSlot::new("u", Ty::Unit),
            ],
        )
    };
    let mut cases: Vec<(FuncId, &'static str)> = Vec::new();
    let mut fb = mb.function("id", ft);
    let b0 = fb.create_block();
    let x = fb.add_block_param(b0, Ty::I32);
    fb.switch_to_block(b0);
    fb.ret(vec![x]);
    let id_fn = fb.build();
    cases.push((id_fn, "ok"));
    macro_rules! case {
        ($name:expr, $want:expr, |$fb:ident, $x:ident| $body:block) => {{
            let mut $fb = mb.function($name, ft);
            let b0 = $fb.create_block();
            let $x = $fb.add_block_param(b0, Ty::I32);
            $fb.switch_to_block(b0);
            $body
            cases.push(($fb.build(), $want));
        }};
    }
    case!("select_poison_cond", "ub", |fb, x| {
        let h = fb.open_frame(def());
        let p = fb.load_slot(h, 0, Ty::Bool);
        let s = fb.select(Ty::I32, p, x, x);
        fb.close_frame(h);
        fb.ret(vec![s]);
    });
    case!("condbr_poison", "ub", |fb, x| {
        let h = fb.open_frame(def());
        let p = fb.load_slot(h, 0, Ty::Bool);
        let t = fb.create_block();
        let e = fb.create_block();
        fb.condbr(p, t, vec![], e, vec![]);
        fb.switch_to_block(t);
        fb.ret(vec![x]);
        fb.switch_to_block(e);
        fb.ret(vec![x]);
    });
    case!("assert_poison", "ub", |fb, x| {
        let h = fb.open_frame(def());
        let p = fb.load_slot(h, 0, Ty::Bool);
        fb.assert(p);
        fb.close_frame(h);
        fb.ret(vec![x]);
    });
    case!("load_unbound_unit_slot", "ub", |fb, x| {
        let h = fb.open_frame(def());
        let _u = fb.load_slot(h, 2, Ty::Unit);
        fb.close_frame(h);
        fb.ret(vec![x]);
    });
    case!("bind_at_slot_count", "ub", |fb, x| {
        let h = fb.open_frame(def());
        let h1 = fb.bind_slot(h, 3, x);
        fb.close_frame(h1);
        fb.ret(vec![x]);
    });
    case!("bind_last_slot", "ok", |fb, x| {
        let h = fb.open_frame(def());
        let h1 = fb.bind_slot(h, 1, x);
        let v = fb.load_slot(h1, 1, Ty::I32);
        fb.close_frame(h1);
        fb.ret(vec![v]);
    });
    case!("call_with_poison", "ub", |fb, x| {
        let h = fb.open_frame(def());
        let p = fb.load_slot(h, 1, Ty::I32);
        let r = fb.call(id_fn, vec![p]);
        fb.close_frame(h);
        let _ = x;
        fb.ret(vec![r]);
    });
    case!("call_wrong_type", "type_error", |fb, x| {
        let b = fb.bool_const(true);
        let r = fb.call(id_fn, vec![b]);
        let _ = x;
        fb.ret(vec![r]);
    });
    case!("call_wrong_arity", "type_error", |fb, x| {
        let r = fb.call(id_fn, vec![x, x]);
        fb.ret(vec![r]);
    });
    case!("call_missing_function", "type_error", |fb, x| {
        let r = fb.call(FuncId::new(99), vec![x]);
        fb.ret(vec![r]);
    });
    case!("copy_wrong_type", "type_error", |fb, x| {
        let c = fb.copy(Ty::I64, x);
        fb.ret(vec![c]);
    });
    case!("add_wrong_type", "type_error", |fb, x| {
        let c = fb.binop(BinOp::Add, Ty::I64, x, x);
        fb.ret(vec![c]);
    });
    case!("return_wrong_type", "type_error", |fb, x| {
        let b = fb.bool_const(false);
        let _ = x;
        fb.ret(vec![b]);
    });
    case!("branch_to_missing_block", "type_error", |fb, x| {
        let t = fb.create_block();
        fb.br(t, vec![]);
        fb.switch_to_block(t);
        fb.ret(vec![x]);
    });
    case!("no_terminator", "type_error", |fb, x| {
        let c = fb.copy(Ty::I32, x);
        fb.ret(vec![c]);
    });
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    // Rewrites the builder will not spell: a branch to block 99, and a block
    // whose terminator is gone.
    for f in &mut module.functions {
        if f.name == "branch_to_missing_block" {
            let br = &mut f.blocks[0].body.last_mut().expect("br").inst;
            let trust_ir::Inst::Br { target, .. } = br else {
                panic!("the block ends in its branch");
            };
            *target = BlockId::new(99);
        }
        if f.name == "no_terminator" {
            f.blocks[0].body.pop();
        }
    }
    let arg = InterpretValue::int(Ty::I32, 21).expect("i32");
    let wants = cases.iter().map(|(_, w)| *w).collect();
    (
        SemrCase {
            label: "poison and type-error paths".into(),
            module,
            runs: cases
                .iter()
                .map(|(id, _)| (*id, vec![arg.clone()]))
                .collect(),
        },
        wants,
    )
}

/// Poison and type-error paths on bodies the validator refuses (each engine
/// runs what it is given): poison as a `select`, `cond_br` or `assert`
/// condition and at a call boundary, an unbound non-scalar slot, a bind at
/// the slot count, a call with the wrong argument type or arity, to a missing
/// function, a branch to a missing block, a `copy` or `add` at the wrong
/// type, a wrong-typed return and a block with no terminator. Each is UB (by
/// the same reason) or a type error (by the same code) in both engines.
#[test]
fn semr_poison_and_type_error_paths_agree_with_the_interpreter() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let (case, wants) = semr_poison_paths_case();
    let batch = case.batch();
    let reports = semr_differential(exe, std::slice::from_ref(&batch));
    let t = tally(&reports);
    assert_no_mismatch(&t, "SemR, poison and type-error paths");
    assert!(t.unsupported.is_empty(), "{:?}", t.unsupported);
    for (r, want) in reports.iter().zip(&wants) {
        assert_eq!(r.rust.class(), *want, "{:?}: rust {:?}", r.func, r.rust);
    }
}

/// The assert-kind golden through SemR: every kind fails once with its
/// `core` message (the bounds and misalignment messages with their operands
/// in place) and every passing twin returns, in both engines.
#[test]
fn semr_assert_kind_panics_agree_message_for_message() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let (module, runs) = assert_kind_runs();
    let batch = Batch {
        label: "assert_kind (every kind fails once)".into(),
        module: &module,
        runs: runs.iter().map(|(f, a, _)| (*f, a.clone())).collect(),
    };
    let reports = semr_differential(exe, std::slice::from_ref(&batch));
    let t = tally(&reports);
    assert_no_mismatch(&t, "SemR, assert kinds");
    assert!(t.unsupported.is_empty(), "{:?}", t.unsupported);
    let mut panics = 0;
    for (r, (_, _, expected)) in reports.iter().zip(&runs) {
        if let Some(message) = expected {
            assert_eq!(r.lean, Verdict::Panic((*message).into(), None));
            panics += 1;
        }
    }
    assert_eq!(panics, 14, "every kind's message was compared");
}

/// The enum tag width: SemR carries an enum of up to 256 variants (tag `u8`)
/// and runs its variant 255, as the interpreter does; at 257 variants (a
/// `u16` tag) it refuses the module by name.
#[test]
fn semr_enum_tag_width_boundary() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    use trust_ir::constant::Constant;
    use trust_ir::ty::{EnumDef, EnumVariant};
    use trust_ir::value::EnumId;
    let module_with = |n: usize| -> (Module, FuncId) {
        let mut mb = ModuleBuilder::new(format!("enum{n}"));
        let variants = (0..n)
            .map(|i| EnumVariant {
                name: format!("V{i}"),
                fields: vec![],
                field_names: vec![],
            })
            .collect();
        let e = mb.add_enum(EnumDef::new(EnumId::new(0), "E", variants));
        let ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::U8]);
        let mut fb = mb.function("tag", ft);
        let b0 = fb.create_block();
        let _b = fb.add_block_param(b0, Ty::Bool);
        fb.switch_to_block(b0);
        let v = fb.const_value(Ty::Enum(e), Constant::Aggregate(vec![Constant::Int(255)]));
        let t = fb.extract_field(Ty::U8, v, 0);
        fb.ret(vec![t]);
        let id = fb.build();
        (mb.build().expect("enum module"), id)
    };
    let (m256, f256) = module_with(256);
    let batch = Batch {
        label: "256 variants".into(),
        module: &m256,
        runs: vec![(f256, vec![InterpretValue::bool(true)])],
    };
    let reports = semr_differential(exe, std::slice::from_ref(&batch));
    let t = tally(&reports);
    assert_no_mismatch(&t, "SemR, 256 variants");
    assert_eq!(
        reports[0].lean,
        Verdict::Ok(vec![Val::Int { width: 8, raw: 255 }])
    );
    let (m257, f257) = module_with(257);
    let batch = Batch {
        label: "257 variants".into(),
        module: &m257,
        runs: vec![(f257, vec![InterpretValue::bool(true)])],
    };
    assert_eq!(
        run_semr(exe, &batch),
        vec![Verdict::Unsupported("enum.tag_width".into())]
    );
}

/// The SemR comparison rule itself (no `lake` needed): UB agrees by reason,
/// type errors by code, and each reason key keeps distinct reasons apart —
/// the negative controls are pairs that the W5b rule calls agreement.
#[test]
fn semr_comparison_matches_ub_by_reason_and_type_errors_by_code() {
    let ub = |m: &str| Verdict::Ub(m.into());
    let te = |m: &str| Verdict::TypeError(m.into());
    let poison = |site: &str| {
        format!(
            "{site}: use of an uninitialized value — poison (uninitialized bytes, `undef`, or an \
             unbound slot) may only be copied or stored, never inspected"
        )
    };
    let agree: &[(Verdict, Verdict)] = &[
        (
            ub("unsigned division by zero"),
            ub("unsigned division by zero"),
        ),
        (
            ub("shift amount 64 is out of range for 64-bit integer"),
            ub("shift amount out of range"),
        ),
        (
            ub(&poison("Call returns")),
            ub("signature boundary: use of an uninitialized value (poison)"),
        ),
        (
            ub(&poison("select")),
            ub("select: use of an uninitialized value (poison)"),
        ),
        (
            ub("BindSlot: slot 3 out of range for frame of 3 slots"),
            ub("BindSlot: slot out of range"),
        ),
        (
            ub("enum enum.0: lane 1 belongs to no field of active variant c (c has 0 field(s))"),
            ub("enum lane belongs to no field of the active variant"),
        ),
        (
            te("signature_mismatch: Call arguments arity mismatch: expected 1, got 2"),
            te("SignatureMismatch: arity mismatch"),
        ),
        (
            te("malformed_instruction: block ended without a terminator"),
            te("MalformedInstruction: block ended without a terminator"),
        ),
    ];
    for (r, s) in agree {
        assert_eq!(compare_semr(r, s), Comparison::Agree, "{r:?} / {s:?}");
    }
    let differ: &[(Verdict, Verdict)] = &[
        (
            ub("unsigned division by zero"),
            ub("signed division by zero"),
        ),
        (
            ub("signed division by zero"),
            ub("signed division overflow"),
        ),
        (
            ub("shift amount 64 is out of range for 64-bit integer"),
            ub("unsigned remainder by zero"),
        ),
        (
            ub(&poison("select")),
            ub("cond_br: use of an uninitialized value (poison)"),
        ),
        (
            ub("BindSlot: slot 3 out of range for frame of 3 slots"),
            ub("LoadSlot: slot out of range"),
        ),
        (
            ub("CloseFrame: frame is not open (double close)"),
            ub("executed unreachable"),
        ),
        (
            te("missing_block: block 99 not found"),
            te("MissingFunction: undefined function"),
        ),
        (
            te("type_error: expected value of type i64, got i32"),
            ub("integer use: use of an uninitialized value (poison)"),
        ),
    ];
    for (r, s) in differ {
        assert!(
            matches!(compare_semr(r, s), Comparison::Mismatch(_)),
            "{r:?} / {s:?} must be a mismatch"
        );
    }
    // The W5b rule, for contrast: any UB agrees with any UB.
    assert_eq!(
        compare(
            &ub("unsigned division by zero"),
            &ub("signed division by zero")
        ),
        Comparison::Agree
    );
}

/// The SemR rule on the memory slice's verdicts (no `lake` needed): running
/// out of memory is its own class, never out of fuel, and a returned pointer
/// agrees only with a pointer into the same allocation at the same offset.
/// The negative controls are the pairs the comparison used to call agreement
/// (both budgets one class; every non-null pointer one value); the positive
/// controls keep equal verdicts agreeing. The parsing halves are pinned too:
/// SemR's `{"out_of_memory":true}` and `{"ptr":{"alloc":A,"offset":O}}`, and
/// the interpreter's `OutOfMemory` and `Ptr`.
#[test]
fn semr_comparison_tells_memory_out_of_fuel_and_pointers_apart() {
    let at = |alloc, offset| Val::PtrAt { alloc, offset };
    let ok = |v: Val| Verdict::Ok(vec![v]);
    for (r, s) in [
        (Verdict::OutOfMemory, Verdict::OutOfMemory),
        (Verdict::OutOfFuel, Verdict::OutOfFuel),
        (ok(at(0, 0)), ok(at(0, 0))),
        (ok(at(2, 7)), ok(at(2, 7))),
    ] {
        assert_eq!(compare_semr(&r, &s), Comparison::Agree, "{r:?} / {s:?}");
    }
    for (r, s) in [
        (Verdict::OutOfMemory, Verdict::OutOfFuel),
        (Verdict::OutOfFuel, Verdict::OutOfMemory),
        (ok(at(0, 0)), ok(at(0, 7))),
        (ok(at(0, 0)), ok(at(1, 0))),
        (ok(at(0, 0)), ok(Val::Ptr { null: false })),
        (ok(at(0, 0)), ok(Val::Ptr { null: true })),
    ] {
        assert!(
            matches!(compare_semr(&r, &s), Comparison::Mismatch(_)),
            "{r:?} / {s:?} must be a mismatch"
        );
    }
    let lines = b"{\"out_of_memory\":true}\n{\"out_of_fuel\":true}\n\
        {\"ok\":[{\"ptr\":{\"alloc\":3,\"offset\":8}}]}\n{\"ok\":[{\"ptr\":\"null\"}]}\n";
    assert_eq!(
        semr_verdicts(lines, 4, "parse"),
        [
            Verdict::OutOfMemory,
            Verdict::OutOfFuel,
            ok(at(3, 8)),
            ok(Val::Ptr { null: true }),
        ]
    );
    let ptr = InterpretValue {
        ty: Ty::Ptr,
        kind: InterpretValueKind::Ptr(trust_ir::interpret::InterpretPointer {
            allocation: 3,
            offset: 8,
        }),
    };
    assert_eq!(semr_rust_val(&ptr), at(3, 8));
    assert_eq!(rust_val(&ptr), Val::Ptr { null: false });
}

// ===========================================================================
// RM4, second slice: SemR's small-step relation, the MiniRust operator lemma,
// and trust-ir's parity gate on SemR (Trust proven-core RM4; RM0 decision 4).
//
// * `lean/semr/SemR.lean`'s `Exec` is now stated over `Step`, an inductive
//   relation with one rule per instruction that never mentions the executable
//   `stepCore`; `step_sound`/`step_complete` prove the executable is exactly the
//   relation, so `run_sound`/`run_complete` are no longer the relation's own
//   definition read back. `semr_step_relation_refuses_mutated_executables`
//   is the negative control: an executable that drifts from the rules does
//   not kernel-check.
// * `lean/semr/SemRMiniRust.lean` proves SemR's operator layer is MiniRust's
//   generated operators (`lean/semr/MiniRust.lean`, Trust's specr translator
//   output verbatim) for every integer type; `semr_operator_lemma_*` build it
//   and kill operator mutants with it.
// * `semr_parity_gate_*`: the parity gate for SemR's fragment
//   (`lean/semr/FRAGMENT.tsv`) is SemR — every variant of the fragment runs in
//   an agreeing SemR/interpreter run, and one disagreement fails the gate.
// ===========================================================================

/// SHA-256 of `lean/semr/SemRMiniRust.lean` (the operator lemma). Clean's
/// `semr_reference.rs` pins its fixture copy's digest to the same value.
const SEMR_MINIRUST_SHA256: &str =
    "edc17ec135c79a02e2e3a36e51c03c3c56bbec5adec8371c57087e9ef29e965c";

/// SHA-256 of `lean/semr/MiniRust.lean`: Trust's `SpecrPrelude.lean` and
/// generated `MiniRustSlice.lean` in a `noncomputable section`.
const MINIRUST_WRAPPER_SHA256: &str =
    "0de8e8aa1c30f277e4a2bca00b44696d5cf803fffc081767e067d5f713ecef51";

/// SHA-256 of Trust's `scripts/trust_core/specr/SpecrPrelude.lean` and
/// `scripts/trust_core/specr/generated/MiniRustSlice.lean`. The runtime
/// preserves libspecr's u32 exponent-conversion panic; the generated slice
/// remains byte-identical. These identities require fresh proof qualification
/// and an exact independent Clean intake; they transport no earlier verdict.
const SPECR_PRELUDE_SHA256: &str =
    "c66f7b7197384e328dc7192fc48b62b5ae5c3a3ee04e09298e2f0c4dd20e1cfd";
const MINIRUST_SLICE_SHA256: &str =
    "c3aa8cef33a80fadccd1d27a52e652c3212d7dcf574259dc0a869d0d501c3c47";

fn sha256_hex(bytes: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    Sha256::digest(bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// `MiniRust.lean` split back into Trust's two files: it must be exactly
/// `noncomputable section\n` + prelude + slice + `\nend\n`, the slice starting
/// at its `-- GENERATED by specr2clean` header line.
fn split_minirust_wrapper(text: &str) -> Result<(&str, &str), String> {
    let body = text
        .strip_prefix("noncomputable section\n")
        .ok_or("MiniRust.lean does not open with `noncomputable section`")?
        .strip_suffix("\nend\n")
        .ok_or("MiniRust.lean does not close with `end`")?;
    let header = "\n-- GENERATED by specr2clean";
    let at = body
        .find(header)
        .ok_or("MiniRust.lean carries no generated slice header")?;
    if body[at + 1..].contains(header) {
        return Err("MiniRust.lean carries two generated slice headers".into());
    }
    Ok((&body[..at + 1], &body[at + 1..]))
}

/// The operator lemma's sources are the ones Clean re-checks, and MiniRust's
/// operators are Trust's generated ones, byte for byte (no `lake` needed).
#[test]
fn semr_minirust_sources_are_pinned() {
    let read = |name: &str| {
        let path = semr_dir().join(name);
        fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
    };
    assert_eq!(
        sha256_hex(&read("SemRMiniRust.lean")),
        SEMR_MINIRUST_SHA256,
        "lean/semr/SemRMiniRust.lean changed: update SEMR_MINIRUST_SHA256 here and Clean's \
         fixture copy and its pin in crates/clean-olean/tests/semr_reference.rs together"
    );
    let wrapper = read("MiniRust.lean");
    assert_eq!(
        sha256_hex(&wrapper),
        MINIRUST_WRAPPER_SHA256,
        "lean/semr/MiniRust.lean changed"
    );
    let text = String::from_utf8(wrapper).expect("UTF-8");
    let (prelude, slice) = split_minirust_wrapper(&text).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(
        sha256_hex(prelude.as_bytes()),
        SPECR_PRELUDE_SHA256,
        "MiniRust.lean's prelude is not Trust's SpecrPrelude.lean at the pinned digest"
    );
    assert_eq!(
        sha256_hex(slice.as_bytes()),
        MINIRUST_SLICE_SHA256,
        "MiniRust.lean's slice is not Trust's generated MiniRustSlice.lean at the pinned digest"
    );
    // Controls: the splitter refuses what is not the wrapper.
    assert!(split_minirust_wrapper(&text[1..]).is_err());
    assert!(split_minirust_wrapper(text.trim_end()).is_err());
    let doubled = text.replacen(
        "\n-- GENERATED by specr2clean",
        "\n-- GENERATED by specr2clean\n-- GENERATED by specr2clean",
        1,
    );
    assert!(split_minirust_wrapper(&doubled).is_err());
    let mut edited = text.clone();
    edited.insert(edited.len() - "\nend\n".len(), ' ');
    let (_, s) = split_minirust_wrapper(&edited).expect("still a wrapper");
    assert_ne!(sha256_hex(s.as_bytes()), MINIRUST_SLICE_SHA256);
}

/// The kernel builds the operator lemma (Lean 4.30; `lake build SemRMiniRust`).
#[test]
fn semr_operator_lemma_kernel_checks() {
    let Some(lake) = semr_lake() else {
        return;
    };
    let dir = semr_dir();
    let out = lake_build_command(&lake, &dir, "SemRMiniRust")
        .output()
        .unwrap_or_else(|e| panic!("cannot run {}: {e}", lake.display()));
    assert!(
        out.status.success(),
        "`lake build SemRMiniRust` failed in {}:\n{}\n{}",
        dir.display(),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}

/// `lake`, or `None` (a skip) when this machine has none and Lean is not required.
fn semr_lake() -> Option<PathBuf> {
    let require = std::env::var("TRUST_IR_REQUIRE_LEAN")
        .map(|v| v == "1")
        .unwrap_or(false);
    let lake = find_semr_lake();
    if lake.is_none() {
        assert!(!require, "TRUST_IR_REQUIRE_LEAN=1 but no `lake` was found");
        eprintln!("SKIPPED: the SemR Lean mutation controls need `lake` (elan); none found.");
    }
    lake
}

/// The files of the SemR package: every regular file of `lean/semr`, its
/// build output (`.lake/`) excluded.
fn semr_package_files() -> Vec<String> {
    let mut files: Vec<String> = fs::read_dir(semr_dir())
        .expect("read lean/semr")
        .map(|e| e.expect("dir entry"))
        .filter(|e| e.file_type().expect("file type").is_file())
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .collect();
    files.sort();
    assert!(
        files.iter().any(|f| f == "SemR.lean") && files.iter().any(|f| f == "SemRMiniRust.lean"),
        "the SemR package is incomplete: {files:?}"
    );
    files
}

fn copy_dir_all(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap_or_else(|e| panic!("mkdir {}: {e}", to.display()));
    for entry in fs::read_dir(from).unwrap_or_else(|e| panic!("read {}: {e}", from.display())) {
        let entry = entry.expect("dir entry");
        let target = to.join(entry.file_name());
        if entry.file_type().expect("file type").is_dir() {
            copy_dir_all(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), &target)
                .unwrap_or_else(|e| panic!("copy {}: {e}", entry.path().display()));
        }
    }
}

/// The 1-based lines of `file` that a Lean build's output reports errors at.
fn lean_error_lines(output: &str, file: &str) -> Vec<usize> {
    let needle = format!("error: {file}:");
    output
        .lines()
        .filter_map(|l| l.find(&needle).map(|i| &l[i + needle.len()..]))
        .filter_map(|rest| rest.split(':').next()?.parse().ok())
        .collect()
}

/// The line span `[start, end)` of top-level declaration `theorem <name>` in
/// `src`: from its header (or the `/--` of the doc comment directly above it,
/// which is part of the declaration: Lean reports a declaration-level error,
/// such as a `:= rfl` that is not a definitional equality, at the
/// declaration's first line) to the next top-level item.
fn lean_theorem_span(src: &str, name: &str) -> (usize, usize) {
    let lines: Vec<&str> = src.lines().collect();
    let header = lines
        .iter()
        .position(|l| l.starts_with(&format!("theorem {name} ")))
        .unwrap_or_else(|| panic!("no `theorem {name}`"));
    // The comment that closes on the line above opens at the nearest `/-`
    // above it; only a doc comment's (`/--`) is the declaration's own.
    let start = match header.checked_sub(1).map(|above| lines[above].trim_end()) {
        Some(above) if above.ends_with("-/") => lines[..header]
            .iter()
            .rposition(|l| l.starts_with("/-"))
            .filter(|&open| lines[open].starts_with("/--"))
            .unwrap_or(header),
        _ => header,
    };
    let end = lines[header + 1..]
        .iter()
        .position(|l| {
            !l.is_empty() && !l.starts_with(' ') && !l.starts_with(')') && !l.starts_with("--")
        })
        .map(|i| header + 1 + i)
        .unwrap_or(lines.len());
    (start + 1, end + 1)
}

/// One Lean mutant: replace `from` (which occurs exactly `times` times: a
/// definition and the unfolding lemma that restates its body move together,
/// so the relation's theorems are what must notice) by `to` in `file`.
struct LeanMutant {
    name: &'static str,
    file: &'static str,
    from: &'static str,
    to: &'static str,
    times: usize,
}

/// Build the SemR package once unmutated (the positive control), then each
/// mutant from a copy of that build; each mutant must fail to build `target`
/// with every error inside `blamed` — the file, and (when named) the theorems
/// the mutation breaks — never a slip elsewhere (every other package file
/// still builds).
fn run_lean_mutants(
    tag: &str,
    target: &str,
    blamed: (&str, Option<&[&str]>),
    mutants: &[LeanMutant],
) {
    let Some(lake) = semr_lake() else {
        return;
    };
    let scratch = SemrScratch::new(tag);
    let control = scratch.path("control");
    fs::create_dir_all(&control).expect("control dir");
    let package = semr_package_files();
    for f in &package {
        fs::copy(semr_dir().join(f), control.join(f)).unwrap_or_else(|e| panic!("copy {f}: {e}"));
    }
    let out = lake_build_command(&lake, &control, target)
        .output()
        .expect("run lake");
    assert!(
        out.status.success(),
        "the unmutated SemR package must build `{target}` (positive control):\n{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    for m in mutants {
        let dir = scratch.path(m.name);
        copy_dir_all(&control, &dir);
        let path = dir.join(m.file);
        let src = fs::read_to_string(&path).expect("mutant source");
        assert_eq!(
            src.matches(m.from).count(),
            m.times,
            "mutant {}: `{}` must occur exactly {} time(s) in {}",
            m.name,
            m.from,
            m.times,
            m.file
        );
        fs::write(&path, src.replacen(m.from, m.to, m.times)).expect("write mutant");
        let out = lake_build_command(&lake, &dir, target)
            .output()
            .expect("run lake");
        let text = format!(
            "{}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(
            !out.status.success(),
            "mutant {} kernel-checks: the theorems did not notice it\n{text}",
            m.name
        );
        let (file, theorems) = blamed;
        let lines = lean_error_lines(&text, file);
        assert!(
            !lines.is_empty(),
            "mutant {}: no error in {file}\n{text}",
            m.name
        );
        for other in package.iter().filter(|f| f.as_str() != file) {
            assert!(
                lean_error_lines(&text, other).is_empty(),
                "mutant {}: {other} no longer builds (the mutation is a slip, not a drift)\n{text}",
                m.name
            );
        }
        if let Some(theorems) = theorems {
            let blamed_src = fs::read_to_string(dir.join(file)).expect("blamed source");
            let spans: Vec<(usize, usize)> = theorems
                .iter()
                .map(|t| lean_theorem_span(&blamed_src, t))
                .collect();
            for line in &lines {
                assert!(
                    spans.iter().any(|(s, e)| s <= line && line < e),
                    "mutant {}: an error at {file}:{line} lies outside {theorems:?}\n{text}",
                    m.name
                );
            }
        }
        let _ = fs::remove_dir_all(&dir);
    }
}

/// NEGATIVE CONTROL for the small-step relation: an executable step that
/// drifts from `Step`'s rules (the wrong resume point, branch edge, call
/// depth, frame lineage or program counter; a slot access without the
/// frame-open check, block parameters left unbound, a signature boundary that
/// lets poison through) no longer kernel-checks, and the
/// failure is in the theorems that tie the two (`SEMR_STEP_THEOREMS`).
#[test]
fn semr_step_relation_refuses_mutated_executables() {
    run_lean_mutants(
        "step-mutants",
        "SemR",
        ("SemR.lean", Some(SEMR_STEP_THEOREMS)),
        &[
            LeanMutant {
                name: "return-resumes-at-the-call",
                file: "SemR.lean",
                from: "bindResults { k with fn := c.fn, sig := c.sig, block := c.block, pc := c.pc + 1,",
                to: "bindResults { k with fn := c.fn, sig := c.sig, block := c.block, pc := c.pc,",
                times: 1,
            },
            LeanMutant {
                name: "cond-br-true-takes-the-else-edge",
                file: "SemR.lean",
                from: "| some true => do let vs ← getVs k tA; jump pointerBits k tT vs",
                to: "| some true => do let vs ← getVs k tA; jump pointerBits k eT vs",
                times: 1,
            },
            LeanMutant {
                name: "call-does-not-descend",
                file: "SemR.lean",
                from: "depth := k.depth - 1, stack := suspend k node :: k.stack",
                to: "depth := k.depth, stack := suspend k node :: k.stack",
                times: 1,
            },
            LeanMutant {
                name: "open-frame-reuses-its-lineage",
                file: "SemR.lean",
                from: "                                   nextFrame := k.nextFrame + 1 }",
                to: "                                   nextFrame := k.nextFrame }",
                times: 1,
            },
            LeanMutant {
                name: "passing-assert-does-not-advance",
                file: "SemR.lean",
                from: "| some true => pure (next k)",
                to: "| some true => pure k",
                times: 1,
            },
            // The state checks the relation states itself (`Opened`,
            // `ParamsBind`, `SigChecks`), not through the executable's
            // helpers: a helper that drops its check or its binding is a
            // drift the relation's theorems refuse.
            LeanMutant {
                name: "slot-access-skips-the-frame-open-check",
                file: "SemR.lean",
                from: "if memNat k.openFrames l then c else ubR s!\"{what}: frame is not open\"",
                to: "c",
                times: 1,
            },
            LeanMutant {
                name: "block-params-are-not-bound",
                file: "SemR.lean",
                from: "bindParams pointerBits ((x, v) :: env) ps vs",
                to: "bindParams pointerBits env ps vs",
                times: 2,
            },
            LeanMutant {
                name: "signature-boundary-admits-poison",
                file: "SemR.lean",
                from: "    rejectPoison v \"signature boundary\"\n    if v.ty.beq t",
                to: "    if v.ty.beq t",
                times: 2,
            },
            // v67: an executable contraction that swaps its operands drifts
            // from `Step.tensorContract` (which reads `lhs` then `rhs`).
            LeanMutant {
                name: "tensor-contract-swaps-its-operands",
                file: "SemR.lean",
                from: "  let v ← evalContract pointerBits ty batch contract a b\n",
                to: "  let v ← evalContract pointerBits ty batch contract b a\n",
                times: 1,
            },
            // v68: a map that reads its operands in reverse, a reduction that
            // ignores its axes and a view that drops its fill each drift from
            // `Step.tensorMap` / `Step.tensorReduce` / `Step.tensorView`.
            LeanMutant {
                name: "tensor-map-reverses-its-operands",
                file: "SemR.lean",
                from: "  let v ← evalMap pointerBits ty vs body\n",
                to: "  let v ← evalMap pointerBits ty vs.reverse body\n",
                times: 1,
            },
            LeanMutant {
                name: "tensor-reduce-ignores-its-axes",
                file: "SemR.lean",
                from: "  let v ← evalReduce pointerBits ty op axes a\n",
                to: "  let v ← evalReduce pointerBits ty op [] a\n",
                times: 1,
            },
            LeanMutant {
                name: "tensor-view-drops-its-fill",
                file: "SemR.lean",
                from: "  let v ← evalView pointerBits ty a ps exprs shape index f\n",
                to: "  let v ← evalView pointerBits ty a ps exprs shape index none\n",
                times: 1,
            },
            // v69: a gather that reads its coordinate tensors in reverse axis
            // order and a scatter that swaps its initial tensor and its source
            // each drift from `Step.tensorGather` / `Step.tensorScatter`.
            LeanMutant {
                name: "tensor-gather-reverses-its-coordinates",
                file: "SemR.lean",
                from: "  let v ← evalGather pointerBits ty d cs\n",
                to: "  let v ← evalGather pointerBits ty d cs.reverse\n",
                times: 1,
            },
            LeanMutant {
                name: "tensor-scatter-swaps-init-and-source",
                file: "SemR.lean",
                from: "  let v ← evalScatter pointerBits ty a s cs\n",
                to: "  let v ← evalScatter pointerBits ty s a cs\n",
                times: 1,
            },
        ],
    );
}

/// The theorems that tie SemR's executable step to its relation (every
/// `*_complete`/`*_sound` lemma): a step mutant must break one of them.
const SEMR_STEP_THEOREMS: &[&str] = &[
    "step_complete",
    "step_sound",
    "opened_complete",
    "opened_sound",
    "sigChecks_complete",
    "sigChecks_sound",
    "paramsBind_complete",
    "paramsBind_sound",
    "binds_complete",
    "binds_sound",
    "jumps_complete",
    "jumps_sound",
    "selects_complete",
    "selects_sound",
    "slotWrite_complete",
    "slotWrite_sound",
    "slotRead_complete",
    "slotRead_sound",
    "closes_complete",
    "closes_sound",
    "asserts_complete",
    "asserts_sound",
    "branches_complete",
    "branches_sound",
    "enters_complete",
    "enters_sound",
    "callSigned_complete",
    "callSig_complete",
    "calls_complete",
    "calls_sound",
    "returns_complete",
    "returns_sound",
    "binop_sound",
    "unop_sound",
    "overflow_sound",
    "icmp_sound",
    "const_sound",
    "copy_sound",
    "select_sound",
    "extractField_sound",
    "insertField_sound",
    "bindSlot_sound",
    "loadSlot_sound",
    "closeFrame_sound",
    "assert_sound",
    "call_sound",
    "br_sound",
    "condBr_sound",
    "ret_sound",
    // RM4c: the memory pieces and instructions.
    "accessAt_some",
    "accesses_complete",
    "accesses_sound",
    "reads_complete",
    "reads_sound",
    "allocates_complete",
    "allocates_sound",
    "freeAt_some",
    "frees_complete",
    "frees_sound",
    "offsets_complete",
    "offsets_sound",
    "alloca_sound",
    "load_sound",
    "store_sound",
    "gep_sound",
    "dealloc_sound",
    // v67: the tensor contraction.
    "tensorContract_sound",
    "tensorMap_sound",
    "tensorReduce_sound",
    "tensorView_sound",
    // v69: the gather and the scatter.
    "tensorGather_sound",
    "tensorScatter_sound",
];

/// NEGATIVE CONTROL for the operator lemma: SemR operators that drift from
/// MiniRust's (a wrong overflow test, sign fill, overflow flag, comparison,
/// negation, bitwise operator or bit count, or a value operator that feeds
/// the residue layer the wrong operands) no longer kernel-check against the
/// generated MiniRust operators.
/// SemR itself still builds: every error is in the lemma's file.
#[test]
fn semr_operator_lemma_refuses_mutated_operators() {
    run_lean_mutants(
        "operator-mutants",
        "SemRMiniRust",
        ("SemRMiniRust.lean", None),
        &[
            LeanMutant {
                name: "sdiv-overflow-on-min-by-one",
                file: "SemR.lean",
                from: "else if a == half w && b == m - 1 then .ub \"signed division overflow\"",
                to: "else if a == half w && b == 1 then .ub \"signed division overflow\"",
                times: 1,
            },
            LeanMutant {
                name: "ashr-fills-one-bit-short",
                file: "SemR.lean",
                from: "else .ok (a / 2 ^ b + (if isNeg w a then m - 2 ^ (w - b) else 0))",
                to: "else .ok (a / 2 ^ b + (if isNeg w a then m - 2 ^ (w - b - 1) else 0))",
                times: 1,
            },
            LeanMutant {
                name: "signed-sub-flag-on-equal-signs",
                file: "SemR.lean",
                from: "(r, if signed then isNeg w a != isNeg w b && isNeg w r != isNeg w a",
                to: "(r, if signed then isNeg w a == isNeg w b && isNeg w r != isNeg w a",
                times: 1,
            },
            LeanMutant {
                name: "sle-is-strict",
                file: "SemR.lean",
                from: "| .sle => decide (biased w a ≤ biased w b)",
                to: "| .sle => decide (biased w a < biased w b)",
                times: 1,
            },
            LeanMutant {
                name: "neg-off-by-one",
                file: "SemR.lean",
                from: "| .neg => negR w a",
                to: "| .neg => negR w (a + 1)",
                times: 1,
            },
            // `and` at a signed type (`bitwise_resid`'s signed arm).
            LeanMutant {
                name: "and-is-or",
                file: "SemR.lean",
                from: "| .and => .ok (Nat.land a b % m)",
                to: "| .and => .ok (Nat.lor a b % m)",
                times: 1,
            },
            // `ctpop` (`ctpop_minirust`).
            LeanMutant {
                name: "ctpop-one-bit-short",
                file: "SemR.lean",
                from: "| .ctpop => popcount w a",
                to: "| .ctpop => popcount (w - 1) a",
                times: 1,
            },
            // The value level (`evalBinop_minirust`): the residue operator
            // is right, the value operator feeds it swapped operands.
            LeanMutant {
                name: "binop-value-swaps-operands",
                file: "SemR.lean",
                from: "    let r ← liftOp (intBin op (t.bits pointerBits) x y)",
                to: "    let r ← liftOp (intBin op (t.bits pointerBits) y x)",
                times: 1,
            },
        ],
    );
}

/// The complete positive-width bounds law observes both the conversion panic
/// and the successful residue. All admitted integer types derive the bound.
/// Removing it, admitting its upper endpoint, or changing the panic must fail
/// in the semantic proofs while the mutated runtime still parses and builds.
#[test]
fn semr_power_conversion_domain_refuses_mutants() {
    run_lean_mutants(
        "power-conversion-mutants",
        "SemRMiniRust",
        ("SemRMiniRust.lean", None),
        &[
            LeanMutant {
                name: "power-conversion-domain-removed",
                file: "MiniRust.lean",
                from: "if k < 4294967296 then",
                to: "if True then",
                times: 1,
            },
            LeanMutant {
                name: "power-conversion-admits-upper-endpoint",
                file: "MiniRust.lean",
                from: "if k < 4294967296 then",
                to: "if k ≤ 4294967296 then",
                times: 1,
            },
            LeanMutant {
                name: "power-conversion-wrong-panic-payload",
                file: "MiniRust.lean",
                from: "else SOut.panic \"called `Option::unwrap()` on a `None` value\"",
                to: "else SOut.panic \"wrong exponent conversion panic\"",
                times: 1,
            },
        ],
    );
}

// --- The parity gate on SemR -------------------------------------------------

/// Quoted model syntax has no wire admission or runtime parity credit. Bind
/// every quoted ledger row to a validated canonical module that actually runs
/// in the interpreter. Quoted-only operations keep their named decoder refusal;
/// the quoted closure constructor retains its nonempty-table/tag refusal;
/// private cells' public counterparts must decode to the distinct byte-memory
/// instructions and execute with the same result. Put Load/Store callees before
/// their allocating caller so every tested operation also occurs in a callee.
#[test]
fn quoted_model_decoder_boundary_controls() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let rows: BTreeSet<Vec<String>> = fs::read_to_string(semr_dir().join("QUOTED_MODEL.tsv"))
        .expect("quoted model ledger")
        .lines()
        .filter(|l| !l.trim().is_empty() && !l.trim_start().starts_with('#'))
        .map(|l| l.split('\t').map(str::to_string).collect())
        .collect();
    let controls = [
        ("undef", "Undef", "inst.undef", "quoted-op"),
        ("allocaCell", "Alloca", "decoded.memory", "abstract-cell"),
        ("loadCell", "Load", "decoded.memory", "abstract-cell"),
        ("storeCell", "Store", "decoded.memory", "abstract-cell"),
        (
            "makeClosure",
            "MakeClosure",
            "closure_types",
            "quoted-closure",
        ),
    ];
    let controlled: BTreeSet<Vec<String>> = controls
        .iter()
        .map(|(a, b, c, d)| [a, b, c, d].into_iter().map(|s| (*s).to_string()).collect())
        .collect();
    assert_eq!(
        rows, controlled,
        "every quoted-only row has an exact native boundary control"
    );
    for (constructor, wire, boundary, scope) in controls {
        if scope == "quoted-closure" {
            use trust_ir::constant::Constant;
            use trust_ir::ty::{ClosureTy, FuncTy};
            use trust_ir::{Block, BlockId, Function, Inst, InstrNode, ValueId};

            // A real constructor with a checked capture-prefix target. Keep it
            // separate so the existing controls retain their exact modules
            // and serializer version selection.
            assert_eq!(
                (constructor, wire, boundary),
                ("makeClosure", "MakeClosure", "closure_types")
            );
            let mut module = Module::new("quoted_boundary_MakeClosure");
            let apparent = module
                .add_func_type(FuncTy {
                    params: vec![],
                    returns: vec![Ty::Bool],
                    is_vararg: false,
                    abi: None,
                })
                .expect("apparent signature");
            let physical = module
                .add_func_type(FuncTy {
                    params: vec![Ty::Bool],
                    returns: vec![Ty::Bool],
                    is_vararg: false,
                    abi: None,
                })
                .expect("capture-prefix physical signature");
            let closure = module
                .add_closure_type(ClosureTy {
                    func: apparent,
                    captures: vec![Ty::Bool],
                })
                .expect("nominal closure type");
            let target_id = FuncId::new(0);
            let driver_id = FuncId::new(1);
            let mut target = Function::new(target_id, "target", physical, BlockId::new(0));
            let mut body = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::Bool);
            body.body.push(InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }));
            target.blocks.push(body);
            module.functions.push(target);
            let mut driver = Function::new(driver_id, "driver", apparent, BlockId::new(0));
            let mut body = Block::new(BlockId::new(0));
            body.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(true),
                })
                .with_result(ValueId::new(0)),
            );
            body.body.push(
                InstrNode::new(Inst::MakeClosure {
                    ty: closure,
                    func: target_id,
                    captures: vec![ValueId::new(0)],
                })
                .with_result(ValueId::new(1)),
            );
            body.body.push(
                InstrNode::new(Inst::ExtractField {
                    ty: Ty::Bool,
                    aggregate: ValueId::new(1),
                    field: 0,
                })
                .with_result(ValueId::new(2)),
            );
            body.body.push(InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }));
            driver.blocks.push(body);
            module.functions.push(driver);
            assert!(
                trust_ir_build::validate_module(&module).is_empty(),
                "{wire}"
            );
            assert_eq!(
                run_rust(&module, driver_id, &[]),
                Verdict::Ok(vec![Val::Bool(true)])
            );
            let blob =
                trust_ir::binary::serialize_module(&module).expect("canonical closure module");
            assert!(header_version(&blob) >= trust_ir::binary::MAKE_CLOSURE_FORMAT_VERSION);
            let decoded = trust_ir::binary::deserialize_module(&blob)
                .expect("canonical decoder accepts closure");
            assert!(trust_ir_build::validate_module(&decoded).is_empty());
            assert_eq!(
                run_rust(&decoded, driver_id, &[]),
                Verdict::Ok(vec![Val::Bool(true)])
            );
            let reply = semr_decode(exe, &[blob]);
            assert_eq!(
                reply[0],
                json!({"unsupported": boundary}),
                "{constructor} / {wire}"
            );
            continue;
        }
        let mut mb = ModuleBuilder::new(format!("quoted_boundary_{wire}"));
        let driver_ty = mb.add_func_type(vec![], vec![Ty::Bool]);
        let mut access = None;
        if matches!(wire, "Load" | "Store") {
            let (params, returns) = if wire == "Load" {
                (vec![Ty::Ptr], vec![Ty::Bool])
            } else {
                (vec![Ty::Ptr, Ty::Bool], vec![])
            };
            let access_ty = mb.add_func_type(params, returns);
            let mut fb = mb.function("access", access_ty);
            let entry = fb.create_block();
            let ptr = fb.add_block_param(entry, Ty::Ptr);
            let value = (wire == "Store").then(|| fb.add_block_param(entry, Ty::Bool));
            fb.switch_to_block(entry);
            if let Some(value) = value {
                fb.store(Ty::Bool, ptr, value);
                fb.ret(vec![]);
            } else {
                let value = fb.load(Ty::Bool, ptr);
                fb.ret(vec![value]);
            }
            access = Some(fb.build());
        }
        let mut fb = mb.function("driver", driver_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        match wire {
            "Undef" => {
                let value = fb.undef(Ty::Bool);
                fb.ret(vec![value]);
            }
            "Alloca" | "Load" | "Store" => {
                let ptr = fb.alloca(Ty::Bool);
                let yes = fb.bool_const(true);
                let loaded = if wire == "Store" {
                    fb.call_void(access.unwrap(), vec![ptr, yes]);
                    fb.load(Ty::Bool, ptr)
                } else {
                    fb.store(Ty::Bool, ptr, yes);
                    if wire == "Load" {
                        fb.call(access.unwrap(), vec![ptr])
                    } else {
                        fb.load(Ty::Bool, ptr)
                    }
                };
                fb.ret(vec![loaded]);
            }
            _ => unreachable!("every ledger control is implemented"),
        }
        let driver = fb.build();
        let module = mb.build().expect("well-formed boundary module");
        assert!(
            trust_ir_build::validate_module(&module).is_empty(),
            "{wire}"
        );
        let verdict = run_rust(&module, driver, &[]);
        if wire == "Undef" {
            assert!(matches!(verdict, Verdict::Ub(_)), "{verdict:?}");
        } else {
            assert_eq!(verdict, Verdict::Ok(vec![Val::Bool(true)]), "{wire}");
        }
        let blob = trust_ir::binary::serialize_module(&module).expect("canonical wire module");
        let decoded =
            trust_ir::binary::deserialize_module(&blob).expect("canonical decoder accepts");
        assert!(trust_ir_build::validate_module(&decoded).is_empty());
        let reply = semr_decode(exe, &[blob]);
        if scope == "abstract-cell" {
            // Compare every signature, block, operand, result and instruction
            // tag. In particular, private.alloca/load/store spellings cannot
            // replace the canonical memory operations while keeping this equal.
            assert_eq!(
                reply[0],
                json!({"decoded": semr_summary_of(&decoded)}),
                "{constructor} / {wire}: public memory must not become a private cell"
            );
            let batch = Batch {
                label: format!("quoted boundary {constructor} / {wire}"),
                module: &module,
                runs: vec![(driver, vec![])],
            };
            assert_eq!(
                run_semr(exe, &batch),
                vec![Verdict::Ok(vec![Val::Bool(true)])],
                "{constructor} / {wire}: canonical memory execution"
            );
        } else {
            assert_eq!(
                reply[0],
                json!({"unsupported": boundary}),
                "{constructor} / {wire}"
            );
        }
    }
}

/// The decoded Assume retains its operand and runtime domain check. A false
/// assumption is not an agreeing/proved run: the interpreter calls it vacuous,
/// while canonical SemR reports the same explicit domain-exit as its quoted
/// semantics. Every truncated image still fails both binary readers.
#[test]
fn semr_assume_wire_preserves_domain_and_operand() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    eprintln!("Assume controls: Oracle::Ready {}", exe.display());
    let mut mb = ModuleBuilder::new("assume_wire");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
    let mut fb = mb.function("domain", ft);
    let b0 = fb.create_block();
    let x = fb.add_block_param(b0, Ty::Bool);
    fb.switch_to_block(b0);
    fb.assume(x);
    fb.ret(vec![x]);
    let id = fb.build();
    let module = mb.build().expect("validated assumption function");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let blob = trust_ir::binary::serialize_module(&module).expect("serialize");
    assert_eq!(
        semr_decode(exe, std::slice::from_ref(&blob))[0],
        json!({"decoded": semr_summary_of(&module)})
    );
    let runs = vec![
        (id, vec![InterpretValue::bool(true)]),
        (id, vec![InterpretValue::bool(false)]),
    ];
    let batch = Batch {
        label: "assume true/false".into(),
        module: &module,
        runs,
    };
    let actual = run_semr(exe, &batch);
    assert_eq!(actual[0], Verdict::Ok(vec![Val::Bool(true)]));
    assert_eq!(
        compare_semr(&run_rust(&module, id, &batch.runs[0].1), &actual[0]),
        Comparison::Agree
    );
    assert!(matches!(
        run_rust(&module, id, &batch.runs[1].1),
        Verdict::Vacuous(_)
    ));
    assert_eq!(
        actual[1],
        Verdict::Ub(
            "assume condition evaluated to false: the input lies outside the assumed domain".into()
        )
    );
    assert_eq!(
        compare_semr(&run_rust(&module, id, &batch.runs[1].1), &actual[1]),
        Comparison::Vacuous
    );
    let executed = semr_executed(exe, &semr_fragment_rows(), &batch);
    assert!(executed[0].contains("Assume"));

    let truncated: Vec<Vec<u8>> = (0..blob.len()).map(|end| blob[..end].to_vec()).collect();
    for (end, reply) in semr_decode(exe, &truncated).iter().enumerate() {
        assert!(
            trust_ir::binary::deserialize_module(&truncated[end]).is_err(),
            "prefix {end}"
        );
        assert!(
            reply
                .get("error")
                .and_then(Json::as_str)
                .is_some_and(|message| message.starts_with("decode:")),
            "prefix {end}: {reply}"
        );
    }

    let mut missing = module.clone();
    let trust_ir::Inst::Assume { cond } = &mut missing.functions[0].blocks[0].body[0].inst else {
        panic!("assume")
    };
    *cond = trust_ir::ValueId::new(999);
    assert!(!trust_ir_build::validate_module(&missing).is_empty());
    let missing_blob = trust_ir::binary::serialize_module(&missing).expect("structural image");
    assert_eq!(
        semr_decode(exe, &[missing_blob])[0],
        json!({"decoded": semr_summary_of(&missing)})
    );
    let invalid = Batch {
        label: "missing assumption operand".into(),
        module: &missing,
        runs: vec![(id, vec![InterpretValue::bool(true)])],
    };
    assert!(matches!(run_semr(exe, &invalid)[0], Verdict::TypeError(_)));

    // Neither a false formula nor scalar binding metadata changes a run.
    use trust_ir::proof::{
        ClauseBinding, ClausePlace, ClauseSort, ObligationKind, ProofFormula, ProofObligation,
        ProofStatus,
    };
    let mut annotated = module.clone();
    let mut formula = ProofFormula::new("diagnostic-only", "false");
    formula.bindings = vec![
        (
            "arg".into(),
            ClauseBinding {
                sort: ClauseSort::Bool,
                place: ClausePlace::Param { index: 0 },
            },
        ),
        (
            "result".into(),
            ClauseBinding {
                sort: ClauseSort::BitVec(64),
                place: ClausePlace::ResultSlot { index: 0 },
            },
        ),
    ];
    annotated.proof_obligations.push(
        ProofObligation::new(
            trust_ir::ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Pending,
            "metadata only",
        )
        .with_function(id)
        .with_formula(formula),
    );
    let encoded = trust_ir::binary::serialize_module(&annotated).expect("scalar metadata");
    assert_eq!(
        semr_decode(exe, &[encoded])[0],
        json!({"decoded": semr_summary_of(&module)})
    );
    assert_eq!(
        run_semr(
            exe,
            &Batch {
                label: "inert scalar bindings".into(),
                module: &annotated,
                runs: batch.runs.clone()
            }
        ),
        actual
    );
    let mut compound = annotated.clone();
    compound.proof_obligations[0]
        .formula
        .as_mut()
        .unwrap()
        .bindings[0]
        .1
        .sort = ClauseSort::Array(Box::new(ClauseSort::Bool), Box::new(ClauseSort::Bool));
    let encoded = trust_ir::binary::serialize_module(&compound).expect("compound metadata");
    assert_eq!(
        semr_decode(exe, &[encoded])[0],
        json!({"unsupported":"obligation.binding_sort"})
    );
    let mut world = annotated;
    world.proof_obligations[0]
        .formula
        .as_mut()
        .unwrap()
        .bindings[0]
        .1
        .place = ClausePlace::World;
    let encoded = trust_ir::binary::serialize_module(&world).expect("world metadata");
    assert_eq!(
        semr_decode(exe, &[encoded])[0],
        json!({"unsupported":"obligation.binding_place"})
    );
    // The full parity gate's existing coverage module must now execute Assume
    // on an agreeing path, not merely classify an unexercised constructor.
    let (coverage, runs) = semr_fragment_coverage_module();
    let coverage = Batch {
        label: "updated fragment coverage".into(),
        module: &coverage,
        runs,
    };
    let reports = semr_differential(exe, std::slice::from_ref(&coverage));
    assert_eq!(reports.len(), 3);
    assert!(
        reports
            .iter()
            .all(|row| row.comparison == Comparison::Agree)
    );
    assert!(
        semr_executed(exe, &semr_fragment_rows(), &coverage)
            .iter()
            .any(|row| row.contains("Assume"))
    );
    let lake = find_semr_lake().expect("Oracle::Ready has SemR lake");
    let checked_metadata = lake_build_command(&lake, &semr_dir(), "MetadataCheck")
        .output()
        .expect("MetadataCheck process");
    assert!(
        checked_metadata.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&checked_metadata.stdout),
        String::from_utf8_lossy(&checked_metadata.stderr)
    );
    eprintln!(
        "Assume controls passed: 2 domain inputs, {} truncated prefixes, 1 missing operand, 1 inert metadata case, 2 unsupported metadata cases; MetadataCheck compiled",
        blob.len()
    );
}

/// `lean/semr/FRAGMENT.tsv`'s `(Rust variant, SemR constructor)` rows (the
/// trust-ir crate's `lean_schema_parity` holds the ledger to both sides).
fn semr_fragment_rows() -> Vec<(String, String)> {
    let path = semr_dir().join("FRAGMENT.tsv");
    let text = fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    text.lines()
        .filter(|l| !l.trim().is_empty() && !l.trim_start().starts_with('#'))
        .map(|l| {
            let mut it = l.split('\t');
            let (Some(r), Some(s), None) = (it.next(), it.next(), it.next()) else {
                panic!("FRAGMENT.tsv: malformed row `{l}`");
            };
            (r.to_string(), s.to_string())
        })
        .collect()
}

/// `lean/semr/CONSTANT_FRAGMENT.tsv`'s `(Rust Constant variant, SemR Const
/// constructor)` rows: the constants the lean_schema_parity Constant axis
/// judges by SemR (and no longer by the old Lean model), so the parity gate
/// must see each EXECUTED by an agreeing run (`semr_const_parity_gate`).
fn semr_const_fragment_rows() -> Vec<(String, String)> {
    let path = semr_dir().join("CONSTANT_FRAGMENT.tsv");
    let text = fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    text.lines()
        .filter(|l| !l.trim().is_empty() && !l.trim_start().starts_with('#'))
        .map(|l| {
            let mut it = l.split('\t');
            let (Some(r), Some(s), None) = (it.next(), it.next(), it.next()) else {
                panic!("CONSTANT_FRAGMENT.tsv: malformed row `{l}`");
            };
            (r.to_string(), s.to_string())
        })
        .collect()
}

/// The SemR constructors each run of `batch` EXECUTED (`semr_eval --executed`:
/// the node at the program counter of every step the run took, the step
/// that stops it included), as the fragment's Rust variant names, and, as
/// `const:<variant>`, the `CONSTANT_FRAGMENT.tsv` constants those executed
/// `const` nodes named (`consts`). A module with no wire image executed
/// nothing on SemR's side.
fn semr_executed(
    exe: &Path,
    fragment: &[(String, String)],
    batch: &Batch<'_>,
) -> Vec<BTreeSet<String>> {
    let Ok(blob) = trust_ir::binary::serialize_module(batch.module) else {
        return vec![BTreeSet::new(); batch.runs.len()];
    };
    if batch.runs.is_empty() {
        return Vec::new();
    }
    let by_semr: BTreeMap<&str, &str> = fragment
        .iter()
        .map(|(r, s)| (s.as_str(), r.as_str()))
        .collect();
    let constants = semr_const_fragment_rows();
    let const_by_semr: BTreeMap<&str, &str> = constants
        .iter()
        .map(|(r, s)| (s.as_str(), r.as_str()))
        .collect();
    let scratch = SemrScratch::new("executed");
    let blob_path = scratch.path("module.tmbc");
    let runs_path = scratch.path("runs.txt");
    fs::write(&blob_path, &blob).expect("write SemR blob");
    let mut runs = String::new();
    for (f, args) in &batch.runs {
        runs.push_str(&format!("{FUEL} {CALL_DEPTH} {}", f.0));
        for a in args {
            runs.push(' ');
            runs.push_str(&semr_arg(a));
        }
        runs.push('\n');
    }
    fs::write(&runs_path, runs.as_bytes()).expect("write SemR runs");
    let out = Command::new(exe)
        .arg("--executed")
        .arg(&blob_path)
        .arg(&runs_path)
        .output()
        .unwrap_or_else(|e| panic!("cannot run {}: {e}", exe.display()));
    drop(scratch);
    assert!(
        out.status.success(),
        "semr_eval --executed exited with {}:\n{}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    let text = String::from_utf8_lossy(&out.stdout);
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(
        lines.len(),
        batch.runs.len(),
        "{}: one executed set per run:\n{text}",
        batch.label
    );
    lines
        .iter()
        .map(|l| {
            let j: Json = serde_json::from_str(l)
                .unwrap_or_else(|e| panic!("semr_eval --executed reply is not JSON ({e}): {l}"));
            let Some(names) = j.get("executed").and_then(Json::as_array) else {
                return BTreeSet::new();
            };
            let consts = j
                .get("consts")
                .and_then(Json::as_array)
                .unwrap_or_else(|| panic!("semr_eval --executed reply has no `consts`: {l}"));
            names
                .iter()
                .map(|n| {
                    let n = n.as_str().expect("a constructor name");
                    by_semr
                        .get(n)
                        .unwrap_or_else(|| {
                            panic!("semr_eval executed `{n}`, which FRAGMENT.tsv does not name")
                        })
                        .to_string()
                })
                .chain(consts.iter().map(|c| {
                    let c = c.as_str().expect("a Const constructor name");
                    let variant = const_by_semr.get(c).unwrap_or_else(|| {
                        panic!(
                            "semr_eval executed constant `{c}`, which CONSTANT_FRAGMENT.tsv \
                             does not name"
                        )
                    });
                    format!("const:{variant}")
                }))
                .collect()
        })
        .collect()
}

/// trust-ir's parity gate on SemR's fragment: no run of the differential
/// disagrees, and every variant of the fragment is EXECUTED by at least one
/// run on which SemR and the reference interpreter agree (each run carries
/// the variants it executed, [`semr_executed`]; a node in a dead block, or
/// after the step that stopped the run, is not credited). Returns the
/// agreeing runs per fragment variant.
fn semr_parity_gate(
    fragment: &[(String, String)],
    runs: &[(BTreeSet<String>, Comparison)],
) -> Result<BTreeMap<String, usize>, String> {
    let disagreements: Vec<String> = runs
        .iter()
        .filter_map(|(v, c)| match c {
            Comparison::Mismatch(m) => Some(format!("{m} (executing {v:?})")),
            _ => None,
        })
        .collect();
    if !disagreements.is_empty() {
        return Err(format!(
            "parity gate (SemR): {} run(s) where SemR and interpret.rs disagree; the first: {:?}",
            disagreements.len(),
            &disagreements[..disagreements.len().min(3)]
        ));
    }
    let mut counts: BTreeMap<String, usize> =
        fragment.iter().map(|(r, _)| (r.clone(), 0)).collect();
    for (variants, c) in runs {
        if matches!(c, Comparison::Agree) {
            for v in variants {
                if let Some(n) = counts.get_mut(v) {
                    *n += 1;
                }
            }
        }
    }
    let unexercised: Vec<&String> = counts
        .iter()
        .filter(|(_, n)| **n == 0)
        .map(|(v, _)| v)
        .collect();
    if !unexercised.is_empty() {
        return Err(format!(
            "parity gate (SemR): fragment variant(s) {unexercised:?} executed by no agreeing \
             run: SemR's semantics of them is unchecked against interpret.rs"
        ));
    }
    Ok(counts)
}

/// The gate's controls on synthetic runs (no `lake` needed): all variants
/// executed and agreeing passes; one disagreement fails by name; a variant
/// executed only by refused or vacuous runs fails as unexercised.
#[test]
fn semr_parity_gate_controls() {
    let fragment = semr_fragment_rows();
    let all: BTreeSet<String> = fragment.iter().map(|(r, _)| r.clone()).collect();
    let ok = vec![(all.clone(), Comparison::Agree)];
    assert!(semr_parity_gate(&fragment, &ok).is_ok());
    let mut bad = ok.clone();
    bad.push((
        BTreeSet::from(["BinOp".to_string()]),
        Comparison::Mismatch("ok vs ub".into()),
    ));
    let e = semr_parity_gate(&fragment, &bad).unwrap_err();
    assert!(e.contains("disagree") && e.contains("ok vs ub"), "{e}");
    let mut without_select = all.clone();
    without_select.remove("Select");
    let partial = vec![
        (without_select, Comparison::Agree),
        (
            all.clone(),
            Comparison::Unsupported("semr", "inst.memory".into()),
        ),
        (all, Comparison::Vacuous),
    ];
    let e = semr_parity_gate(&fragment, &partial).unwrap_err();
    assert!(
        e.contains("\"Select\"") && e.contains("no agreeing run"),
        "{e}"
    );

    // The Ty axis: a type-fragment type is credited only by an agreeing run.
    let tys = semr_ty_fragment_rows();
    assert!(tys.contains("Tensor"), "{tys:?}");
    let credited: BTreeSet<String> = tys.iter().map(|t| format!("ty:{t}")).collect();
    assert!(semr_ty_parity_gate(&tys, &[(credited.clone(), Comparison::Agree)]).is_ok());
    let refused_only = [
        (
            credited.clone(),
            Comparison::Unsupported("semr", "tensor.element".into()),
        ),
        (credited, Comparison::Vacuous),
        (BTreeSet::new(), Comparison::Agree),
    ];
    let e = semr_ty_parity_gate(&tys, &refused_only).unwrap_err();
    assert!(
        e.contains("\"Tensor\"") && e.contains("no agreeing run"),
        "{e}"
    );
    // A run's credits come from its signature, not from a name: a tensor
    // signature is credited, a scalar one is not.
    let (case, _) = semr_tensor_case(None);
    let (func, _) = &case.runs[0];
    assert_eq!(semr_ty_credits(&case.module, *func, &tys), ["ty:Tensor"; 3]);
    let (scalar, id) = sub_module();
    assert!(semr_ty_credits(&scalar, id, &tys).is_empty());

    // The Constant axis: a constant-fragment constant is credited only by an
    // agreeing run that executed it.
    let constants = semr_const_fragment_rows();
    assert!(
        constants
            .iter()
            .any(|(r, s)| r == "TensorBlob" && s == "tensorBlob"),
        "{constants:?}"
    );
    let executed: BTreeSet<String> = constants
        .iter()
        .map(|(r, _)| format!("const:{r}"))
        .collect();
    assert!(semr_const_parity_gate(&constants, &[(executed.clone(), Comparison::Agree)]).is_ok());
    let refused_only = [
        (
            executed.clone(),
            Comparison::Unsupported("semr", "tensor.float_element".into()),
        ),
        (executed.clone(), Comparison::Vacuous),
        (executed, Comparison::Mismatch("ok vs type_error".into())),
        (BTreeSet::from(["Const".to_string()]), Comparison::Agree),
    ];
    let e = semr_const_parity_gate(&constants, &refused_only).unwrap_err();
    assert!(
        e.contains("\"TensorBlob\"") && e.contains("no agreeing run"),
        "{e}"
    );
}

/// The runs the gate judges, each with the fragment variants it executed:
/// EVERY SemR differential's corpus run at the harness budget — the
/// generator corpus and its wide range, the subset fixtures, the operator
/// cells, the direct calls, the unvalidated frame bodies, the out-of-range
/// constants, the poison and type-error paths, the assert kinds, and
/// `semr_fragment_coverage_module`'s bodies — so a run on which a test above
/// sees SemR and the interpreter disagree fails the gate too. (The budget
/// boundary's runs are at other budgets, the decoder's are not runs.) The
/// interpreter recurses once per call level: call this on a deep stack.
fn semr_gate_runs(exe: &Path) -> Vec<(BTreeSet<String>, Comparison)> {
    let fragment = semr_fragment_rows();
    let modules = generator_corpus();
    let wide: Vec<(u64, Module, Vec<FnSpec>)> = SEMR_WIDE_SEEDS
        .map(|seed| {
            let (module, specs) = gen_module_exec(seed);
            (seed, module, specs)
        })
        .collect();
    let fixtures = subset_fixtures();
    let (cover, cover_runs) = semr_fragment_coverage_module();
    let (assert_module, assert_runs) = assert_kind_runs();
    // VF5: the compiler's own artifacts (casts, `switch`, fieldless enums).
    let compiled = compiled_artifacts();
    let cases = [
        semr_operator_cells_case(),
        semr_direct_calls_case(),
        semr_frame_discipline_case(),
        semr_out_of_range_constants_case(),
        semr_poison_paths_case().0,
        // RM4c: the memory slice's rules, each path once.
        semr_memory_case().0,
        // v67: the tensor contraction, on the reference layout and wasm32.
        semr_tensor_case(None).0,
        semr_tensor_case(Some(semr_target(32))).0,
        // v68: the tensor map, reduction and view, on both layouts.
        semr_tensor_region_case(None).0,
        semr_tensor_region_case(Some(semr_target(32))).0,
        // v69: the tensor gather and scatter, on both layouts.
        semr_tensor_gather_scatter_case(None).0,
        semr_tensor_gather_scatter_case(Some(semr_target(32))).0,
        // v70: content-addressed weight blobs, on both layouts.
        semr_tensor_blob_case(None).0,
        semr_tensor_blob_case(Some(semr_target(32))).0,
    ];
    // RM4c: the generated memory corpus's first seeds.
    let memory = mem_corpus(0..300);
    let mut batches = generator_batches(&modules);
    batches.extend(memory.iter().enumerate().map(|(i, (module, runs))| Batch {
        label: format!("memory seed {i}"),
        module,
        runs: runs.clone(),
    }));
    batches.extend(generator_batches(&wide));
    batches.extend(
        fixtures
            .iter()
            .enumerate()
            .map(|(i, (name, module))| Batch {
                label: format!("fixture {name}"),
                module,
                runs: module_runs(module, 4, 0x5B5B_0000 + i as u64),
            }),
    );
    batches.push(Batch {
        label: "fragment coverage".into(),
        module: &cover,
        runs: cover_runs,
    });
    batches.push(Batch {
        label: "assert_kind (every kind fails once)".into(),
        module: &assert_module,
        runs: assert_runs
            .iter()
            .map(|(f, a, _)| (*f, a.clone()))
            .collect(),
    });
    batches.extend(cases.iter().map(SemrCase::batch));
    batches.extend(compiled.iter().enumerate().map(|(i, (name, _, module))| {
        let mut runs = enum_runs(module);
        runs.extend(module_runs(module, 4, 0xC0_4F00 + i as u64));
        Batch {
            label: format!("compiled {name}"),
            module,
            runs,
        }
    }));
    let reports = semr_differential(exe, &batches);
    let mut out = Vec::new();
    let mut i = 0;
    let ty_fragment = semr_ty_fragment_rows();
    for batch in &batches {
        let executed = semr_executed(exe, &fragment, batch);
        assert_eq!(executed.len(), batch.runs.len(), "{}", batch.label);
        for (mut executed, (func, _)) in executed.into_iter().zip(&batch.runs) {
            executed.extend(semr_ty_credits(batch.module, *func, &ty_fragment));
            out.push((executed, reports[i].comparison.clone()));
            i += 1;
        }
    }
    assert_eq!(i, reports.len(), "one executed set per run");
    out
}

/// `lean/semr/TY_FRAGMENT.tsv`'s Rust `Ty` variants: the types the
/// lean_schema_parity Ty axis judges by SemR (and no longer by the old Lean
/// model), so the parity gate must see each carried by an agreeing run.
fn semr_ty_fragment_rows() -> BTreeSet<String> {
    let path = semr_dir().join("TY_FRAGMENT.tsv");
    let text = fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    text.lines()
        .filter(|l| !l.trim().is_empty() && !l.trim_start().starts_with('#'))
        .map(|l| {
            let mut it = l.split('\t');
            let (Some(r), Some(_), None) = (it.next(), it.next(), it.next()) else {
                panic!("TY_FRAGMENT.tsv: malformed row `{l}`");
            };
            r.to_string()
        })
        .collect()
}

/// The `ty:<variant>` credits of one run: each type of SemR's type fragment
/// its function's signature carries (a parameter or a return). A run that
/// AGREES on such a signature had SemR decode the type and both engines
/// produce or consume a value of it, which a name match cannot show.
fn semr_ty_credits(module: &Module, func: FuncId, ty_fragment: &BTreeSet<String>) -> Vec<String> {
    let Some(f) = module.functions.iter().find(|f| f.id == func) else {
        return Vec::new();
    };
    let Some(sig) = module.func_types.get(f.ty.0 as usize) else {
        return Vec::new();
    };
    sig.params
        .iter()
        .chain(&sig.returns)
        .filter_map(|ty| {
            let debug = format!("{ty:?}");
            let variant = debug.split(['(', ' ', '{']).next().unwrap_or_default();
            ty_fragment
                .contains(variant)
                .then(|| format!("ty:{variant}"))
        })
        .collect()
}

/// The gate's Ty axis: every type of SemR's type fragment is carried by at
/// least one agreeing run (`semr_ty_credits`). Returns the agreeing runs per
/// type.
fn semr_ty_parity_gate(
    ty_fragment: &BTreeSet<String>,
    runs: &[(BTreeSet<String>, Comparison)],
) -> Result<BTreeMap<String, usize>, String> {
    let mut counts: BTreeMap<String, usize> = ty_fragment.iter().map(|t| (t.clone(), 0)).collect();
    for (credits, c) in runs {
        if matches!(c, Comparison::Agree) {
            for (t, n) in counts.iter_mut() {
                if credits.contains(&format!("ty:{t}")) {
                    *n += 1;
                }
            }
        }
    }
    let unexercised: Vec<&String> = counts
        .iter()
        .filter(|(_, n)| **n == 0)
        .map(|(t, _)| t)
        .collect();
    if unexercised.is_empty() {
        Ok(counts)
    } else {
        Err(format!(
            "parity gate (SemR): type-fragment type(s) {unexercised:?} carried by no agreeing \
             run: SemR's decoding and semantics of them is unchecked against interpret.rs"
        ))
    }
}

/// The gate's Constant axis: every constant of SemR's constant fragment
/// (`CONSTANT_FRAGMENT.tsv`) is EXECUTED by at least one agreeing run, as a
/// `const` node `semr_eval --executed` names (`const:<variant>`; a constant
/// in a dead block, or after the step that stopped the run, earns nothing).
/// Returns the agreeing runs per constant.
fn semr_const_parity_gate(
    const_fragment: &[(String, String)],
    runs: &[(BTreeSet<String>, Comparison)],
) -> Result<BTreeMap<String, usize>, String> {
    let mut counts: BTreeMap<String, usize> =
        const_fragment.iter().map(|(r, _)| (r.clone(), 0)).collect();
    for (credits, c) in runs {
        if matches!(c, Comparison::Agree) {
            for (variant, n) in counts.iter_mut() {
                if credits.contains(&format!("const:{variant}")) {
                    *n += 1;
                }
            }
        }
    }
    let unexercised: Vec<&String> = counts
        .iter()
        .filter(|(_, n)| **n == 0)
        .map(|(v, _)| v)
        .collect();
    if unexercised.is_empty() {
        Ok(counts)
    } else {
        Err(format!(
            "parity gate (SemR): constant-fragment constant(s) {unexercised:?} executed by no \
             agreeing run: SemR's semantics of them is unchecked against interpret.rs"
        ))
    }
}

/// `f` on a thread with the deep stack the direct-call runs need.
fn on_a_deep_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(512 << 20)
        .spawn(f)
        .expect("spawn")
        .join()
        .expect("the deep-stack thread")
}

/// RM4's parity gate: over every SemR differential's runs, every variant of
/// SemR's fragment, and every constant of its constant fragment, is executed
/// by agreeing runs, every type of its type fragment is carried by one, and
/// none disagrees.
#[test]
fn semr_parity_gate_holds_on_semrs_fragment() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let (counts, ty_counts, const_counts) = on_a_deep_stack(move || {
        let runs = semr_gate_runs(exe);
        (
            semr_parity_gate(&semr_fragment_rows(), &runs).unwrap_or_else(|e| panic!("{e}")),
            semr_ty_parity_gate(&semr_ty_fragment_rows(), &runs).unwrap_or_else(|e| panic!("{e}")),
            semr_const_parity_gate(&semr_const_fragment_rows(), &runs)
                .unwrap_or_else(|e| panic!("{e}")),
        )
    });
    eprintln!("parity gate (SemR): agreeing runs per fragment variant: {counts:?}");
    eprintln!("parity gate (SemR): agreeing runs per type-fragment type: {ty_counts:?}");
    eprintln!("parity gate (SemR): agreeing runs per constant-fragment constant: {const_counts:?}");
}

/// NEGATIVE CONTROL, end to end: SemR runs the `sub` module while the
/// interpreter runs it with `Sub` flipped to `Add` — a real SemR/interpreter
/// disagreement — and the gate over the corpus plus those runs fails, naming
/// the disagreement; the corpus alone passes (the control).
#[test]
fn semr_parity_gate_fails_on_a_semr_interpreter_disagreement() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let fragment = semr_fragment_rows();
    let mut runs = on_a_deep_stack(move || semr_gate_runs(exe));
    assert!(semr_parity_gate(&fragment, &runs).is_ok());
    let (module, id) = sub_module();
    let mut mutant = module.clone();
    for f in &mut mutant.functions {
        for b in &mut f.blocks {
            for n in &mut b.body {
                if let trust_ir::Inst::BinOp { op, .. } = &mut n.inst {
                    *op = trust_ir::inst::BinOp::Add;
                }
            }
        }
    }
    let arg = |v: i32| InterpretValue::int(Ty::I32, i128::from(v)).expect("i32 argument");
    let batch = Batch {
        label: "sub".into(),
        module: &module,
        runs: vec![(id, vec![arg(5), arg(3)])],
    };
    let semr = canonical_verdict(run_semr(exe, &batch).remove(0));
    let rust = canonical_verdict(run_rust(&mutant, id, &[arg(5), arg(3)]));
    let executed = semr_executed(exe, &fragment, &batch).remove(0);
    assert!(executed.contains("BinOp"), "{executed:?}");
    runs.push((executed, compare_semr(&rust, &semr)));
    let e = semr_parity_gate(&fragment, &runs).unwrap_err();
    assert!(e.contains("disagree"), "{e}");
}

/// The gate credits what a run EXECUTED, not what its function contains:
/// `semr_eval --executed` on a body whose `unreachable` sits in a block the
/// run never enters, and on one whose `select` follows a division by zero,
/// names neither (both are in the function, so a static reach would credit
/// them); and the gate over those runs alone fails with both unexercised.
/// The control: the run that takes the other edge executes `unreachable`.
#[test]
fn semr_parity_gate_credits_executed_nodes_only() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    use trust_ir::inst::BinOp;
    let fragment = semr_fragment_rows();
    let mut mb = ModuleBuilder::new("semr_executed");
    let ft = mb.add_func_type(vec![Ty::Bool, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("dead_unreachable", ft);
    let entry = fb.create_block();
    let live = fb.create_block();
    let dead = fb.create_block();
    let c = fb.add_block_param(entry, Ty::Bool);
    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    fb.condbr(c, live, vec![], dead, vec![]);
    fb.switch_to_block(live);
    fb.ret(vec![x]);
    fb.switch_to_block(dead);
    fb.unreachable();
    let dead_fn = fb.build();
    let mut fb = mb.function("select_after_ub", ft);
    let b0 = fb.create_block();
    let c = fb.add_block_param(b0, Ty::Bool);
    let x = fb.add_block_param(b0, Ty::I32);
    fb.switch_to_block(b0);
    let z = fb.iconst(Ty::I32, 0);
    let q = fb.binop(BinOp::UDiv, Ty::I32, x, z);
    let s = fb.select(Ty::I32, c, q, x);
    fb.ret(vec![s]);
    let ub_fn = fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let in_module = |f: FuncId, variant: &str| {
        module
            .functions
            .iter()
            .filter(|g| g.id == f)
            .flat_map(|g| &g.blocks)
            .flat_map(|b| &b.body)
            .any(|n| format!("{:?}", n.inst).starts_with(variant))
    };
    assert!(in_module(dead_fn, "Unreachable") && in_module(ub_fn, "Select"));
    let t = InterpretValue::bool(true);
    let f = InterpretValue::bool(false);
    let seven = InterpretValue::int(Ty::I32, 7).expect("i32");
    let batch = Batch {
        label: "executed".into(),
        module: &module,
        runs: vec![
            (dead_fn, vec![t.clone(), seven.clone()]),
            (ub_fn, vec![t, seven.clone()]),
            (dead_fn, vec![f, seven]),
        ],
    };
    let executed = semr_executed(exe, &fragment, &batch);
    let names = |xs: &[&str]| -> BTreeSet<String> { xs.iter().map(|x| x.to_string()).collect() };
    assert_eq!(executed[0], names(&["CondBr", "Return"]));
    assert_eq!(executed[1], names(&["BinOp", "Const"]));
    assert_eq!(executed[2], names(&["CondBr", "Unreachable"]));
    let reports = semr_differential(exe, std::slice::from_ref(&batch));
    let runs: Vec<(BTreeSet<String>, Comparison)> = executed
        .iter()
        .take(2)
        .cloned()
        .zip(reports.iter().map(|r| r.comparison.clone()))
        .collect();
    assert!(
        runs.iter().all(|(_, c)| matches!(c, Comparison::Agree)),
        "{runs:?}"
    );
    let e = semr_parity_gate(&fragment, &runs).unwrap_err();
    assert!(
        e.contains("\"Select\"") && e.contains("\"Unreachable\"") && e.contains("no agreeing run"),
        "{e}"
    );
}

/// NEGATIVE CONTROL for the gate's reach below the instruction: SemR
/// operators that differ from the interpreter's only on some operands (the
/// signed remainder's sign, `ashr`'s sign fill, `rotl`'s wrap-around term,
/// `ctpop`'s width, the signed multiply's overflow flag — mutants the first
/// gate, over the generator corpus alone, let through; and the tensor
/// contraction's accumulation and the gather/scatter coordinate's sign test,
/// which only the tensor cases reach) are each built into a
/// `semr_mutant_eval` of their own, and the gate over that oracle's runs fails
/// on a disagreement. This target uses production's exact shared I/O driver
/// without its proof imports, so the runtime control must build and execute;
/// the separate operator-lemma controls require named kernel rejection.
#[test]
fn semr_parity_gate_refuses_semr_operator_mutants() {
    let Oracle::Ready(_) = semr_oracle() else {
        return;
    };
    let Some(lake) = semr_lake() else {
        return;
    };
    let mutants: [(&str, &str, &str); 7] = [
        (
            "srem-takes-the-divisor-sign",
            "      .ok (if isNeg w a then negR w r else r % m)",
            "      .ok (if isNeg w b then negR w r else r % m)",
        ),
        (
            "ashr-without-sign-fill",
            "else .ok (a / 2 ^ b + (if isNeg w a then m - 2 ^ (w - b) else 0))",
            "else .ok (a / 2 ^ b)",
        ),
        (
            "rotl-drops-its-wrap-around",
            "| .rotl => let n := b % w; .ok ((a * 2 ^ n) % m + a / 2 ^ (w - n))",
            "| .rotl => let n := b % w; .ok ((a * 2 ^ n) % m)",
        ),
        (
            "ctpop-one-bit-short",
            "| .ctpop => popcount w a",
            "| .ctpop => popcount (w - 1) a",
        ),
        (
            "signed-mul-flag-strict",
            "(if isNeg w a != isNeg w b then decide (half w < p) else decide (half w ≤ p))",
            "(if isNeg w a != isNeg w b then decide (half w < p) else decide (half w < p))",
        ),
        // v67: the contraction's shared accumulation step squares its left
        // factor (only the tensor case's runs can see it).
        (
            "tensor-mac-squares-its-left-factor",
            "def macR (w acc x y : Nat) : Nat := (acc + (x * y) % modulus w) % modulus w",
            "def macR (w acc x y : Nat) : Nat := (acc + (x * x) % modulus w) % modulus w",
        ),
        // v69: the gather's and the scatter's shared coordinate reading drops
        // its sign test, so a negative signed coordinate whose residue lies
        // inside the axis (`i8` -128, residue 128, at extent 130) reads an
        // element (only the gather/scatter case's runs can see it).
        (
            "tensor-coordinate-read-without-its-sign",
            "  !(t.signed && isNeg (t.bits pointerBits) x) && decide (x < d)",
            "  decide (x < d)",
        ),
    ];
    let scratch = SemrScratch::new("gate-mutants");
    let package = semr_package_files();
    let fragment = semr_fragment_rows();
    let control = scratch.path("control");
    fs::create_dir_all(&control).expect("control dir");
    for f in &package {
        fs::copy(semr_dir().join(f), control.join(f)).unwrap_or_else(|e| panic!("copy {f}: {e}"));
    }
    let out = lake_build_command(&lake, &control, "semr_mutant_eval")
        .output()
        .expect("run lake");
    assert!(
        out.status.success(),
        "the unmodified shared runtime must build (positive control):\n{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let exe = control.join(".lake/build/bin/semr_mutant_eval");
    let runs = on_a_deep_stack(move || semr_gate_runs(&exe));
    let counts = semr_parity_gate(&fragment, &runs)
        .expect("the unmodified shared runtime must pass the complete parity gate");
    eprintln!("unmodified shared SemR runtime parity: {counts:?}");
    let _ = fs::remove_dir_all(&control);
    for (name, from, to) in mutants {
        let dir = scratch.path(name);
        fs::create_dir_all(&dir).expect("mutant dir");
        for f in &package {
            fs::copy(semr_dir().join(f), dir.join(f)).unwrap_or_else(|e| panic!("copy {f}: {e}"));
        }
        let path = dir.join("SemR.lean");
        let src = fs::read_to_string(&path).expect("SemR source");
        assert_eq!(
            src.matches(from).count(),
            1,
            "mutant {name}: `{from}` must occur once"
        );
        fs::write(&path, src.replacen(from, to, 1)).expect("write mutant");
        let out = lake_build_command(&lake, &dir, "semr_mutant_eval")
            .output()
            .expect("run lake");
        assert!(
            out.status.success(),
            "mutant {name}: SemR must still build (only the differential can see it):\n{}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        let exe = dir.join(".lake/build/bin/semr_mutant_eval");
        let runs = on_a_deep_stack(move || semr_gate_runs(&exe));
        let e = semr_parity_gate(&fragment, &runs).expect_err(&format!(
            "mutant {name}: the parity gate passed a SemR operator mutant"
        ));
        assert!(e.contains("disagree"), "mutant {name}: {e}");
        let _ = fs::remove_dir_all(&dir);
    }
}

/// Bodies that put the fragment's frame, assertion, call and `unreachable`
/// variants on agreeing paths (the generator corpus has no frames or calls).
fn semr_fragment_coverage_module() -> (Module, Vec<(FuncId, Vec<InterpretValue>)>) {
    use trust_ir::inst::{BindingFrameDef, BindingSlot, ICmpOp, OverflowOp, UnOp};
    use trust_ir::value::BindingFrameId;
    let mut mb = ModuleBuilder::new("semr_fragment_coverage");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut ids = Vec::new();
    let mut fb = mb.function("id", ft);
    let b0 = fb.create_block();
    let x = fb.add_block_param(b0, Ty::I32);
    fb.switch_to_block(b0);
    fb.ret(vec![x]);
    let id_fn = fb.build();
    // A binding frame: open, bind, load, close.
    let mut fb = mb.function("frame", ft);
    let b0 = fb.create_block();
    let x = fb.add_block_param(b0, Ty::I32);
    fb.switch_to_block(b0);
    let h = fb.open_frame(BindingFrameDef::new(
        BindingFrameId::new(0),
        "q",
        vec![BindingSlot::new("i", Ty::I32)],
    ));
    let h1 = fb.bind_slot(h, 0, x);
    let v = fb.load_slot(h1, 0, Ty::I32);
    fb.close_frame(h1);
    fb.ret(vec![v]);
    ids.push(fb.build());
    // A direct call, a passing assertion, a null pointer, a copy, a select,
    // a negation and a checked add.
    let mut fb = mb.function("scalars", ft);
    let b0 = fb.create_block();
    let x = fb.add_block_param(b0, Ty::I32);
    fb.switch_to_block(b0);
    let r = fb.call(id_fn, vec![x]);
    let z = fb.iconst(Ty::I32, 0);
    let ok = fb.icmp(ICmpOp::Ne, Ty::I32, r, z);
    fb.assert(ok);
    fb.assume(ok);
    let _p = fb.null_ptr();
    let c = fb.copy(Ty::I32, r);
    let s = fb.select(Ty::I32, ok, c, z);
    let n = fb.unop(UnOp::Neg, Ty::I32, s);
    let (sum, _flag) = fb.overflow(OverflowOp::AddOverflow, Ty::I32, n, x);
    fb.ret(vec![sum]);
    ids.push(fb.build());
    // `unreachable`, executed (undefined behaviour in both engines).
    let mut fb = mb.function("unreachable", ft);
    let b0 = fb.create_block();
    let _x = fb.add_block_param(b0, Ty::I32);
    fb.switch_to_block(b0);
    fb.unreachable();
    ids.push(fb.build());
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let arg = InterpretValue::int(Ty::I32, 21).expect("i32");
    (
        module,
        ids.into_iter().map(|id| (id, vec![arg.clone()])).collect(),
    )
}

// ---------------------------------------------------------------------------
// SemR, the first memory slice (Trust proven-core RM4c): stack slots
// ---------------------------------------------------------------------------
//
// SemR's memory (`lean/semr/SemR.lean`, "Memory"): `Alloca` (a stack slot, the
// producer's `StorageLive`), `Load` and `Store` of integers and `Bool`s
// through a pointer, `GEP` (address arithmetic), `Dealloc` (`StorageDead`),
// over MiniRust's model (an allocation is abstract bytes at an address, a
// pointer an allocation id and an offset) at the reference interpreter's
// addresses. The corpus below is built node by node (no builder door adds an
// `Alloca` count, an explicit alignment or a volatile access), runs through
// both engines and is compared by the SemR rule: UB by reason, every reason
// the interpreter's text.

/// One straight-line body under construction: its parameters first, then
/// every node's result numbered in order.
struct MemBody {
    next: u32,
    params: Vec<(trust_ir::value::ValueId, Ty)>,
    body: Vec<trust_ir::node::InstrNode>,
}

impl MemBody {
    fn new(params: &[Ty]) -> Self {
        let mut b = MemBody {
            next: 0,
            params: Vec::new(),
            body: Vec::new(),
        };
        for ty in params {
            let v = b.fresh();
            b.params.push((v, ty.clone()));
        }
        b
    }

    fn fresh(&mut self) -> trust_ir::value::ValueId {
        let v = trust_ir::value::ValueId::new(self.next);
        self.next += 1;
        v
    }

    fn param(&self, i: usize) -> trust_ir::value::ValueId {
        self.params[i].0
    }

    fn val(&mut self, inst: trust_ir::Inst) -> trust_ir::value::ValueId {
        let v = self.fresh();
        self.body
            .push(trust_ir::node::InstrNode::new(inst).with_result(v));
        v
    }

    fn void(&mut self, inst: trust_ir::Inst) {
        self.body.push(trust_ir::node::InstrNode::new(inst));
    }

    fn konst(&mut self, ty: Ty, v: i128) -> trust_ir::value::ValueId {
        let value = if ty == Ty::Bool {
            trust_ir::constant::Constant::Bool(v != 0)
        } else {
            trust_ir::constant::Constant::Int(v)
        };
        self.val(trust_ir::Inst::Const { ty, value })
    }

    fn alloca(
        &mut self,
        ty: Ty,
        count: Option<trust_ir::value::ValueId>,
        align: Option<u64>,
    ) -> trust_ir::value::ValueId {
        self.val(trust_ir::Inst::Alloca { ty, count, align })
    }

    fn load(
        &mut self,
        ty: Ty,
        ptr: trust_ir::value::ValueId,
        volatile: bool,
        align: Option<u64>,
    ) -> trust_ir::value::ValueId {
        self.val(trust_ir::Inst::Load {
            ty,
            ptr,
            volatile,
            align,
        })
    }

    fn store(
        &mut self,
        ty: Ty,
        ptr: trust_ir::value::ValueId,
        value: trust_ir::value::ValueId,
        volatile: bool,
        align: Option<u64>,
    ) {
        self.void(trust_ir::Inst::Store {
            ty,
            ptr,
            value,
            volatile,
            align,
        });
    }

    fn gep(
        &mut self,
        pointee_ty: Ty,
        base: trust_ir::value::ValueId,
        indices: Vec<trust_ir::value::ValueId>,
    ) -> trust_ir::value::ValueId {
        self.val(trust_ir::Inst::GEP {
            pointee_ty,
            base,
            indices,
            inbounds: false,
        })
    }

    /// A `GEP` with its `inbounds` flag set (both engines ignore it; MiniRust
    /// does not: `semr_memory_minirust_divergences_are_pinned`).
    fn gep_inbounds(
        &mut self,
        pointee_ty: Ty,
        base: trust_ir::value::ValueId,
        indices: Vec<trust_ir::value::ValueId>,
    ) -> trust_ir::value::ValueId {
        self.val(trust_ir::Inst::GEP {
            pointee_ty,
            base,
            indices,
            inbounds: true,
        })
    }

    fn dealloc(&mut self, ptr: trust_ir::value::ValueId) {
        self.void(trust_ir::Inst::Dealloc { ptr });
    }

    /// Return the first parameter.
    fn ret_param0(self) -> trust_ir::Block {
        let x = self.param(0);
        self.ret(vec![x])
    }

    fn ret(mut self, values: Vec<trust_ir::value::ValueId>) -> trust_ir::Block {
        self.void(trust_ir::Inst::Return { values });
        let mut b = trust_ir::Block::new(trust_ir::value::BlockId::new(0));
        b.params = self.params;
        b.body = self.body;
        b
    }
}

/// A module of the given functions, each `(name, params, returns, body)`,
/// function `i` its `i`-th, with signature `i`.
fn mem_module(name: &str, fns: Vec<(&str, Vec<Ty>, Vec<Ty>, trust_ir::Block)>) -> Module {
    let mut m = Module::new(name);
    for (i, (fname, params, returns, block)) in fns.into_iter().enumerate() {
        m.func_types.push(trust_ir::ty::FuncTy {
            params,
            returns,
            is_vararg: false,
            abi: None,
        });
        let mut f = trust_ir::Function::new(
            FuncId::new(i as u32),
            fname,
            trust_ir::value::FuncTyId::new(i as u32),
            trust_ir::value::BlockId::new(0),
        );
        f.blocks.push(block);
        m.functions.push(f);
    }
    m
}

fn i32_arg(v: i32) -> InterpretValue {
    InterpretValue::int(Ty::I32, i128::from(v)).expect("i32 argument")
}

/// The hand-written memory cases: each path of each memory rule once, with
/// the verdict both engines must reach (`ok`, `ub` with its reason, a type
/// error, out of memory, or a named SemR refusal).
fn semr_memory_case() -> (SemrCase, Vec<&'static str>) {
    use trust_ir::inst::BinOp;
    let mut fns: Vec<(&str, Vec<Ty>, Vec<Ty>, trust_ir::Block)> = Vec::new();
    let mut expect: Vec<&'static str> = Vec::new();
    let p_i32 = || vec![Ty::I32];
    // 0: a slot written and read back.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    b.store(Ty::I32, p, b.param(0), false, None);
    let y = b.load(Ty::I32, p, false, None);
    fns.push(("roundtrip", p_i32(), vec![Ty::I32], b.ret(vec![y])));
    expect.push("ok");
    // 1: an unwritten slot read plainly is poison, refused at the return.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    let y = b.load(Ty::I32, p, false, None);
    fns.push(("uninit_returned", p_i32(), vec![Ty::I32], b.ret(vec![y])));
    expect.push("ub");
    // 2: ... and read volatile, UB at its first byte.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    let y = b.load(Ty::I32, p, true, None);
    fns.push(("uninit_volatile", p_i32(), vec![Ty::I32], b.ret(vec![y])));
    expect.push("ub");
    // 3: use after StorageDead (load).
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    b.store(Ty::I32, p, b.param(0), false, None);
    b.dealloc(p);
    let y = b.load(Ty::I32, p, false, None);
    fns.push(("load_after_dealloc", p_i32(), vec![Ty::I32], b.ret(vec![y])));
    expect.push("ub");
    // 4: use after StorageDead (store).
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    b.dealloc(p);
    b.store(Ty::I32, p, b.param(0), false, None);
    fns.push((
        "store_after_dealloc",
        p_i32(),
        vec![Ty::I32],
        b.ret_param0(),
    ));
    expect.push("ub");
    // 5: a double StorageDead.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    b.dealloc(p);
    b.dealloc(p);
    fns.push(("double_dealloc", p_i32(), vec![Ty::I32], b.ret_param0()));
    expect.push("ub");
    // 6: a Dealloc through an interior pointer.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    let one = b.konst(Ty::I64, 1);
    let q = b.gep(Ty::I8, p, vec![one]);
    b.dealloc(q);
    fns.push(("interior_dealloc", p_i32(), vec![Ty::I32], b.ret_param0()));
    expect.push("ub");
    // 7: one element past the slot.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    let one = b.konst(Ty::I64, 1);
    let q = b.gep(Ty::I32, p, vec![one]);
    let y = b.load(Ty::I32, q, false, None);
    fns.push(("past_the_slot", p_i32(), vec![Ty::I32], b.ret(vec![y])));
    expect.push("ub");
    // 8: a wider read than the slot.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I16, None, None);
    let y = b.load(Ty::I32, p, false, None);
    fns.push((
        "wider_than_the_slot",
        p_i32(),
        vec![Ty::I32],
        b.ret(vec![y]),
    ));
    expect.push("ub");
    // 9: a misaligned read (address 1025 for an `i32`).
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I64, None, None);
    let one = b.konst(Ty::I64, 1);
    let q = b.gep(Ty::I8, p, vec![one]);
    let y = b.load(Ty::I32, q, false, None);
    fns.push(("misaligned", p_i32(), vec![Ty::I32], b.ret(vec![y])));
    expect.push("ub");
    // 10: an explicit alignment that is no power of two.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    let y = b.load(Ty::I32, p, false, Some(3));
    fns.push(("bad_align", p_i32(), vec![Ty::I32], b.ret(vec![y])));
    expect.push("type_error");
    // 11: byte 1 of a stored `u32` (little-endian), read as a `u8`.
    let mut b = MemBody::new(&[Ty::U32]);
    let p = b.alloca(Ty::U32, None, None);
    b.store(Ty::U32, p, b.param(0), false, None);
    let one = b.konst(Ty::I64, 1);
    let q = b.gep(Ty::U8, p, vec![one]);
    let y = b.load(Ty::U8, q, false, None);
    fns.push(("byte_one", vec![Ty::U32], vec![Ty::U8], b.ret(vec![y])));
    expect.push("ok");
    // 12: two `i16` halves read back as one `i32`.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    let lo = b.konst(Ty::I16, 0x1234);
    let hi = b.konst(Ty::I16, -2);
    b.store(Ty::I16, p, lo, false, None);
    let one = b.konst(Ty::I64, 1);
    let q = b.gep(Ty::I16, p, vec![one]);
    b.store(Ty::I16, q, hi, false, None);
    let y = b.load(Ty::I32, p, false, None);
    fns.push(("halves", p_i32(), vec![Ty::I32], b.ret(vec![y])));
    expect.push("ok");
    // 13: partly written bytes are poison that keeps its bytes: moved to
    //     another slot whole, its written byte reads back.
    let mut b = MemBody::new(&[Ty::U8]);
    let p = b.alloca(Ty::I32, None, None);
    b.store(Ty::U8, p, b.param(0), false, None);
    let part = b.load(Ty::I32, p, false, None);
    let q = b.alloca(Ty::I32, None, None);
    b.store(Ty::I32, q, part, false, None);
    let y = b.load(Ty::U8, q, false, None);
    fns.push((
        "poison_keeps_its_bytes",
        vec![Ty::U8],
        vec![Ty::U8],
        b.ret(vec![y]),
    ));
    expect.push("ok");
    // 14: ... and inspecting it is UB.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    let z = b.konst(Ty::I8, 7);
    b.store(Ty::I8, p, z, false, None);
    let part = b.load(Ty::I32, p, false, None);
    let s = b.val(trust_ir::Inst::BinOp {
        op: BinOp::Add,
        ty: Ty::I32,
        lhs: part,
        rhs: b.param(0),
    });
    fns.push(("poison_inspected", p_i32(), vec![Ty::I32], b.ret(vec![s])));
    expect.push("ub");
    // 15: a volatile store of poison.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    let part = b.load(Ty::I32, p, false, None);
    b.store(Ty::I32, p, part, true, None);
    fns.push((
        "poison_stored_volatile",
        p_i32(),
        vec![Ty::I32],
        b.ret_param0(),
    ));
    expect.push("ub");
    // 16-19: through the null pointer.
    for (name, op) in [
        ("null_load", 0),
        ("null_store", 1),
        ("null_gep", 2),
        ("null_dealloc", 3),
    ] {
        let mut b = MemBody::new(&p_i32());
        let n = b.val(trust_ir::Inst::NullPtr);
        match op {
            0 => {
                let _ = b.load(Ty::I32, n, false, None);
            }
            1 => b.store(Ty::I32, n, b.param(0), false, None),
            2 => {
                let z = b.konst(Ty::I64, 0);
                let _ = b.gep(Ty::I32, n, vec![z]);
            }
            _ => b.dealloc(n),
        }
        fns.push((name, p_i32(), vec![Ty::I32], b.ret_param0()));
        expect.push("ub");
    }
    // 20: a `Bool` stored at an `i32`.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    let t = b.konst(Ty::Bool, 1);
    b.store(Ty::I32, p, t, false, None);
    fns.push(("store_wrong_type", p_i32(), vec![Ty::I32], b.ret_param0()));
    expect.push("type_error");
    // 21: a load through an integer.
    let mut b = MemBody::new(&p_i32());
    let y = b.load(Ty::I32, b.param(0), false, None);
    fns.push(("load_through_int", p_i32(), vec![Ty::I32], b.ret(vec![y])));
    expect.push("type_error");
    // 22: four `i32`s (a counted Alloca): the last written and read.
    let mut b = MemBody::new(&p_i32());
    let four = b.konst(Ty::U64, 4);
    let p = b.alloca(Ty::I32, Some(four), None);
    let three = b.konst(Ty::U64, 3);
    let q = b.gep(Ty::I32, p, vec![three]);
    b.store(Ty::I32, q, b.param(0), false, None);
    let y = b.load(Ty::I32, q, false, None);
    fns.push(("array_last", p_i32(), vec![Ty::I32], b.ret(vec![y])));
    expect.push("ok");
    // 23: ... and one past it.
    let mut b = MemBody::new(&p_i32());
    let four = b.konst(Ty::U64, 4);
    let p = b.alloca(Ty::I32, Some(four), None);
    let q = b.gep(Ty::I32, p, vec![four]);
    b.store(Ty::I32, q, b.param(0), false, None);
    fns.push(("array_past", p_i32(), vec![Ty::I32], b.ret_param0()));
    expect.push("ub");
    // 24-25: a count of zero, a negative count.
    for (name, v) in [("count_zero", 0i128), ("count_negative", -3)] {
        let mut b = MemBody::new(&p_i32());
        let c = b.konst(Ty::I32, v);
        let _ = b.alloca(Ty::U8, Some(c), None);
        fns.push((name, p_i32(), vec![Ty::I32], b.ret_param0()));
        expect.push("ub");
    }
    // 26: a negative GEP index.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    let m1 = b.konst(Ty::I64, -1);
    let _ = b.gep(Ty::I32, p, vec![m1]);
    fns.push(("gep_negative", p_i32(), vec![Ty::I32], b.ret_param0()));
    expect.push("ub");
    // 27: a GEP index wider than u64.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    let big = b.konst(Ty::I128, 1i128 << 70);
    let _ = b.gep(Ty::I8, p, vec![big]);
    fns.push(("gep_index_too_wide", p_i32(), vec![Ty::I32], b.ret_param0()));
    expect.push("ub");
    // 28: a scaled index past 2^64.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    let big = b.konst(Ty::U64, i128::from(u64::MAX));
    let _ = b.gep(Ty::I32, p, vec![big]);
    fns.push((
        "gep_scaled_overflow",
        p_i32(),
        vec![Ty::I32],
        b.ret_param0(),
    ));
    expect.push("ub");
    // 29: an offset past 2^64 over two GEPs.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    let big = b.konst(Ty::U64, i128::from(u64::MAX));
    let q = b.gep(Ty::I8, p, vec![big]);
    let one = b.konst(Ty::U64, 1);
    let _ = b.gep(Ty::I8, q, vec![one]);
    fns.push((
        "gep_offset_overflow",
        p_i32(),
        vec![Ty::I32],
        b.ret_param0(),
    ));
    expect.push("ub");
    // 30: an address past 2^64 (the GEP is fine; the load is not).
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I8, None, None);
    let big = b.konst(Ty::U64, i128::from(u64::MAX - 100));
    let q = b.gep(Ty::I8, p, vec![big]);
    let y = b.load(Ty::I8, q, false, None);
    fns.push(("address_overflow", p_i32(), vec![Ty::I8], b.ret(vec![y])));
    expect.push("ub");
    // 31: a pointer passed to a callee, which writes through it (function 32).
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    let _ = b.val(trust_ir::Inst::Call {
        callee: FuncId::new(32),
        args: vec![p, b.param(0)],
    });
    let y = b.load(Ty::I32, p, false, None);
    fns.push(("callee_writes", p_i32(), vec![Ty::I32], b.ret(vec![y])));
    expect.push("ok");
    // 32: the callee.
    let mut b = MemBody::new(&[Ty::Ptr, Ty::I32]);
    b.store(Ty::I32, b.param(0), b.param(1), false, None);
    let r = b.konst(Ty::I32, 0);
    fns.push((
        "write_through",
        vec![Ty::Ptr, Ty::I32],
        vec![Ty::I32],
        b.ret(vec![r]),
    ));
    expect.push("skip");
    // 33: a slot's address returned.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I8, None, None);
    fns.push(("address_returned", p_i32(), vec![Ty::Ptr], b.ret(vec![p])));
    expect.push("ok");
    // 34: the bump allocator's addresses: two one-byte slots at 1024 and
    //     1025, the second read at alignment 2.
    let mut b = MemBody::new(&p_i32());
    let _ = b.alloca(Ty::U8, None, None);
    let q = b.alloca(Ty::U8, None, None);
    let y = b.load(Ty::U8, q, false, Some(2));
    fns.push(("bump_addresses", p_i32(), vec![Ty::U8], b.ret(vec![y])));
    expect.push("ub");
    // 35: a zero-sized slot still takes one address.
    let mut b = MemBody::new(&p_i32());
    let _ = b.alloca(Ty::Unit, None, None);
    let q = b.alloca(Ty::U16, None, Some(1));
    let y = b.load(Ty::U16, q, true, Some(2));
    fns.push(("zero_sized_slot", p_i32(), vec![Ty::U16], b.ret(vec![y])));
    expect.push("ub");
    // 36: out of memory (two 2^63-byte slots).
    let mut b = MemBody::new(&p_i32());
    let half = b.konst(Ty::U64, 1i128 << 63);
    let _ = b.alloca(Ty::U8, Some(half), None);
    let _ = b.alloca(Ty::U8, Some(half), None);
    fns.push(("out_of_memory", p_i32(), vec![Ty::I32], b.ret_param0()));
    expect.push("out_of_memory");
    // 37: an allocation size past 2^64.
    let mut b = MemBody::new(&p_i32());
    let quarter = b.konst(Ty::U64, 1i128 << 62);
    let _ = b.alloca(Ty::I32, Some(quarter), None);
    fns.push(("size_overflow", p_i32(), vec![Ty::I32], b.ret_param0()));
    expect.push("ub");
    // 38: an explicit alignment of 0.
    let mut b = MemBody::new(&p_i32());
    let _ = b.alloca(Ty::I32, None, Some(0));
    fns.push(("align_zero", p_i32(), vec![Ty::I32], b.ret_param0()));
    expect.push("type_error");
    // 39: an over-aligned slot: 1024 rounded up to 4096.
    let mut b = MemBody::new(&p_i32());
    let _ = b.alloca(Ty::U8, None, None);
    let p = b.alloca(Ty::U8, None, Some(4096));
    let y = b.load(Ty::U8, p, true, Some(8192));
    fns.push(("over_aligned", p_i32(), vec![Ty::U8], b.ret(vec![y])));
    expect.push("ub");
    // 40: a `Bool` from a byte `1`.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::Bool, None, None);
    let one = b.konst(Ty::U8, 1);
    b.store(Ty::U8, p, one, false, None);
    let y = b.load(Ty::Bool, p, false, None);
    fns.push(("bool_byte_one", p_i32(), vec![Ty::Bool], b.ret(vec![y])));
    expect.push("ok");
    // 41: a `Bool` from a byte `2`: refused by name on SemR's side.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::Bool, None, None);
    let two = b.konst(Ty::U8, 2);
    b.store(Ty::U8, p, two, false, None);
    let y = b.load(Ty::Bool, p, false, None);
    fns.push(("bool_byte_two", p_i32(), vec![Ty::Bool], b.ret(vec![y])));
    expect.push("unsupported");
    // 42: a pointer-typed load: outside the slice.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::Ptr, None, None);
    let _ = b.load(Ty::Ptr, p, false, None);
    fns.push(("pointer_load", p_i32(), vec![Ty::I32], b.ret_param0()));
    expect.push("unsupported");
    // 43: a 128-bit value, stored and read back.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::U128, None, None);
    let x = b.val(trust_ir::Inst::Cast {
        op: trust_ir::inst::CastOp::SExt,
        src_ty: Ty::I32,
        dst_ty: Ty::U128,
        operand: b.param(0),
    });
    b.store(Ty::U128, p, x, false, None);
    let y = b.load(Ty::U128, p, true, None);
    fns.push(("wide_roundtrip", p_i32(), vec![Ty::U128], b.ret(vec![y])));
    expect.push("ok");
    // 44: an unbound slot's poison (`LoadSlot`) stored into a stack slot keeps
    //     its bytes uninitialized: a byte of it, read back and returned, is
    //     poison at the return.
    let mut b = MemBody::new(&p_i32());
    let h = b.val(trust_ir::Inst::OpenFrame {
        def: trust_ir::inst::BindingFrameDef::new(
            trust_ir::value::BindingFrameId::new(0),
            "q",
            vec![trust_ir::inst::BindingSlot::new("s0", Ty::I32)],
        ),
    });
    let poison = b.val(trust_ir::Inst::LoadSlot {
        frame: h,
        slot: 0,
        ty: Ty::I32,
    });
    b.void(trust_ir::Inst::CloseFrame { frame: h });
    let p = b.alloca(Ty::I32, None, None);
    b.store(Ty::I32, p, poison, false, None);
    let y = b.load(Ty::U8, p, false, None);
    fns.push((
        "unbound_slot_poison_stored",
        p_i32(),
        vec![Ty::U8],
        b.ret(vec![y]),
    ));
    expect.push("ub");
    // 45: a slot of two pointers is 16 bytes: a store at element 2 is past
    //     its end, and the bounds name the pointer layout (8 bytes, aligned 8).
    let mut b = MemBody::new(&p_i32());
    let two = b.konst(Ty::U64, 2);
    let p = b.alloca(Ty::Ptr, Some(two), None);
    let q = b.gep(Ty::Ptr, p, vec![two]);
    b.store(Ty::I32, q, b.param(0), false, None);
    fns.push(("pointer_slots_end", p_i32(), vec![Ty::I32], b.ret_param0()));
    expect.push("ub");
    // 46: ... and element 1 of it, behind a one-byte slot, returned: the
    //     pointer is compared by allocation and offset (slot 1, offset 8).
    let mut b = MemBody::new(&p_i32());
    let _ = b.alloca(Ty::U8, None, None);
    let two = b.konst(Ty::U64, 2);
    let p = b.alloca(Ty::Ptr, Some(two), None);
    let one = b.konst(Ty::U64, 1);
    let q = b.gep(Ty::Ptr, p, vec![one]);
    b.store(Ty::I32, q, b.param(0), false, None);
    fns.push((
        "pointer_slot_element",
        p_i32(),
        vec![Ty::Ptr],
        b.ret(vec![q]),
    ));
    expect.push("ok");
    // 47: a count that fits `u128` but not `u64`.
    let mut b = MemBody::new(&p_i32());
    let wide = b.konst(Ty::U128, 1i128 << 64);
    let _ = b.alloca(Ty::U8, Some(wide), None);
    fns.push((
        "count_wider_than_u64",
        p_i32(),
        vec![Ty::I32],
        b.ret_param0(),
    ));
    expect.push("ub");
    // 48: an unbound slot's poison (an `i32`) stored at `i64`: a type error,
    //     poison or not.
    let mut b = MemBody::new(&p_i32());
    let h = b.val(trust_ir::Inst::OpenFrame {
        def: trust_ir::inst::BindingFrameDef::new(
            trust_ir::value::BindingFrameId::new(0),
            "q",
            vec![trust_ir::inst::BindingSlot::new("s0", Ty::I32)],
        ),
    });
    let poison = b.val(trust_ir::Inst::LoadSlot {
        frame: h,
        slot: 0,
        ty: Ty::I32,
    });
    b.void(trust_ir::Inst::CloseFrame { frame: h });
    let p = b.alloca(Ty::I64, None, None);
    b.store(Ty::I64, p, poison, false, None);
    fns.push((
        "poison_stored_at_another_type",
        p_i32(),
        vec![Ty::I32],
        b.ret_param0(),
    ));
    expect.push("type_error");
    // 49: partly uninitialized bytes read at `i32`, stored at `u32` (the
    //     same size): a type error too.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::I32, None, None);
    let part = b.load(Ty::I32, p, false, None);
    let q = b.alloca(Ty::U32, None, None);
    b.store(Ty::U32, q, part, false, None);
    fns.push((
        "partial_bytes_stored_at_another_type",
        p_i32(),
        vec![Ty::I32],
        b.ret_param0(),
    ));
    expect.push("type_error");
    // 50: a slot whose end is exactly 2^64 is out of memory (its last byte's
    //     successor is no address) ...
    let mut b = MemBody::new(&p_i32());
    let n = b.konst(Ty::U64, (1i128 << 64) - 1024);
    let _ = b.alloca(Ty::U8, Some(n), None);
    fns.push((
        "slot_ending_at_2_64",
        p_i32(),
        vec![Ty::I32],
        b.ret_param0(),
    ));
    expect.push("out_of_memory");
    // 51: ... and one byte shorter fits.
    let mut b = MemBody::new(&p_i32());
    let n = b.konst(Ty::U64, (1i128 << 64) - 1025);
    let _ = b.alloca(Ty::U8, Some(n), None);
    fns.push(("largest_slot", p_i32(), vec![Ty::I32], b.ret_param0()));
    expect.push("ok");
    // 52: a `Bool` `true` is the byte 1.
    let mut b = MemBody::new(&p_i32());
    let p = b.alloca(Ty::U8, None, None);
    let t = b.konst(Ty::Bool, 1);
    b.store(Ty::Bool, p, t, false, None);
    let y = b.load(Ty::U8, p, false, None);
    fns.push(("bool_true_byte", p_i32(), vec![Ty::U8], b.ret(vec![y])));
    expect.push("ok");
    let module = mem_module("semr_memory", fns);
    let runs: Vec<(FuncId, Vec<InterpretValue>)> = module
        .functions
        .iter()
        .zip(&expect)
        .filter(|(_, e)| **e != "skip")
        .map(|(f, _)| {
            let ft = &module.func_types[f.ty.0 as usize];
            let args = ft
                .params
                .iter()
                .map(|t| match t {
                    Ty::U32 => InterpretValue::int(Ty::U32, 0xDEAD_BEEF).expect("u32"),
                    Ty::U8 => InterpretValue::int(Ty::U8, 0xA5).expect("u8"),
                    _ => i32_arg(-123_456),
                })
                .collect();
            (f.id, args)
        })
        .collect();
    let expect = expect.into_iter().filter(|e| *e != "skip").collect();
    (
        SemrCase {
            label: "memory".into(),
            module,
            runs,
        },
        expect,
    )
}

/// RM4c: each path of each memory rule, through both engines, with the
/// verdict class each must reach. 0 disagreements, the UB matched by reason
/// (the reason text names the address, the offset, the bounds), and the two
/// named refusals (a `Bool` byte that is neither 0 nor 1, a pointer-typed
/// access) exactly where expected.
#[test]
fn semr_memory_rules_agree_with_the_interpreter() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let (case, expect) = semr_memory_case();
    let batch = case.batch();
    let reports = semr_differential(exe, std::slice::from_ref(&batch));
    let mut failures = Vec::new();
    for (r, want) in reports.iter().zip(&expect) {
        let fname = &case.module.functions[r.func.0 as usize].name;
        let got = match &r.comparison {
            Comparison::Agree => r.rust.class(),
            Comparison::Unsupported(..) => "unsupported",
            Comparison::Vacuous => "vacuous",
            Comparison::Mismatch(m) => {
                failures.push(format!(
                    "{fname}: MISMATCH {m}\n    rust {:?}\n    semr {:?}",
                    r.rust, r.lean
                ));
                continue;
            }
        };
        eprintln!("  {fname}: {got} (rust {:?}; semr {:?})", r.rust, r.lean);
        if got != *want {
            failures.push(format!(
                "{fname}: {got}, expected {want} (rust {:?}; semr {:?})",
                r.rust, r.lean
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Target addresses are narrower than the u64 count/offset arithmetic on
/// wasm32. Cross-type reads distinguish a jointly wrong store/load width;
/// sparse large slots exercise address limits without allocating host GiB.
fn semr_target_memory_case(bits: u32) -> (SemrCase, Vec<Verdict>) {
    let mut fns = Vec::new();
    let mut expected = Vec::new();
    let seven = || Verdict::Ok(vec![Val::Int { width: 32, raw: 7 }]);
    for (name, count, extra) in [
        ("last_target_byte", (1i128 << 32) - 1024, false),
        ("after_last_target_byte", (1i128 << 32) - 1024, true),
        ("past_target_space", 1i128 << 32, false),
    ] {
        let mut b = MemBody::new(&[]);
        let n = b.konst(Ty::U64, count);
        b.alloca(Ty::U8, Some(n), None);
        if extra {
            b.alloca(Ty::U8, None, None);
        }
        let v = b.konst(Ty::I32, 7);
        fns.push((name, vec![], vec![Ty::I32], b.ret(vec![v])));
        expected.push(if bits == 32 && (extra || count == 1i128 << 32) {
            Verdict::OutOfMemory
        } else {
            seven()
        });
    }
    // Zero-sized elements still accept u64-sized counts and indices on wasm32.
    let mut b = MemBody::new(&[]);
    let n = b.konst(Ty::U64, 1i128 << 32);
    let p = b.alloca(Ty::Unit, Some(n), None);
    let q = b.gep(Ty::Unit, p, vec![n]);
    fns.push((
        "zero_size_u64_count_and_index",
        vec![],
        vec![Ty::Ptr],
        b.ret(vec![q]),
    ));
    expected.push(Verdict::Ok(vec![Val::PtrAt {
        alloc: 0,
        offset: 0,
    }]));

    let mut b = MemBody::new(&[]);
    let two = b.konst(Ty::U64, 2);
    let p = b.alloca(Ty::Usize, Some(two), None);
    let x = b.konst(Ty::Usize, 0x1122_3344);
    b.store(Ty::Usize, p, x, false, None);
    let one = b.konst(Ty::U64, 1);
    let q = b.gep(Ty::Usize, p, vec![one]);
    let y = b.konst(Ty::Usize, 0x5566_7788);
    b.store(Ty::Usize, q, y, false, None);
    let v = b.load(Ty::U64, p, true, Some(1));
    fns.push((
        "usize_stride_cross_read",
        vec![],
        vec![Ty::U64],
        b.ret(vec![v]),
    ));
    expected.push(Verdict::Ok(vec![Val::Int {
        width: 64,
        raw: if bits == 32 {
            0x5566_7788_1122_3344
        } else {
            0x1122_3344
        },
    }]));

    let mut b = MemBody::new(&[]);
    let p = b.alloca(Ty::U64, None, None);
    let x = b.konst(Ty::U32, 0x4433_2211);
    b.store(Ty::U32, p, x, false, None);
    let v = b.load(Ty::Usize, p, true, None);
    fns.push((
        "four_initialized_bytes",
        vec![],
        vec![Ty::Usize],
        b.ret(vec![v]),
    ));
    expected.push(if bits == 32 {
        Verdict::Ok(vec![Val::Int {
            width: 32,
            raw: 0x4433_2211,
        }])
    } else {
        Verdict::Ub("Load: reading uninitialized byte at offset 4".into())
    });

    // The encoder must not write eight bytes into a four-byte usize lane.
    // Round trips hide that spill; a strict read of the untouched next lane
    // must still find poison at the target-sized offset.
    let mut b = MemBody::new(&[]);
    let two = b.konst(Ty::U64, 2);
    let p = b.alloca(Ty::Usize, Some(two), None);
    let x = b.konst(Ty::Usize, 0x1234);
    b.store(Ty::Usize, p, x, false, None);
    let one = b.konst(Ty::U64, 1);
    let q = b.gep(Ty::Usize, p, vec![one]);
    let v = b.load(Ty::Usize, q, true, None);
    fns.push((
        "usize_store_leaves_neighbor_uninitialized",
        vec![],
        vec![Ty::Usize],
        b.ret(vec![v]),
    ));
    expected.push(Verdict::Ub(format!(
        "Load: reading uninitialized byte at offset {}",
        bits / 8
    )));

    for (name, delta) in [
        ("gep_last_target_address", (1i128 << 32) - 1025),
        ("gep_outside_target_address", (1i128 << 32) - 1024),
    ] {
        let mut b = MemBody::new(&[]);
        let p = b.alloca(Ty::U8, None, None);
        let n = b.konst(Ty::U64, delta);
        let q = b.gep_inbounds(Ty::U8, p, vec![n]);
        fns.push((name, vec![], vec![Ty::Ptr], b.ret(vec![q])));
        expected.push(if bits == 32 && delta == (1i128 << 32) - 1024 {
            Verdict::Ub("GEP: address 0x100000000 is outside the target's address space (highest address 0xffffffff)".into())
        } else {
            Verdict::Ok(vec![Val::PtrAt { alloc: 0, offset: delta as u64 }])
        });
    }
    let mut b = MemBody::new(&[]);
    let p = b.alloca(Ty::U8, None, None);
    b.dealloc(p);
    let zero = b.konst(Ty::U64, 0);
    let q = b.gep_inbounds(Ty::U8, p, vec![zero]);
    fns.push((
        "dead_gep_is_not_a_dereference",
        vec![],
        vec![Ty::Ptr],
        b.ret(vec![q]),
    ));
    expected.push(Verdict::Ok(vec![Val::PtrAt {
        alloc: 0,
        offset: 0,
    }]));

    for (name, allocation) in [("isize_count_sign", true), ("isize_index_sign", false)] {
        let mut b = MemBody::new(&[]);
        let n = b.konst(Ty::Isize, 1i128 << 31);
        let p = if allocation {
            b.alloca(Ty::U8, Some(n), None)
        } else {
            let p = b.alloca(Ty::U8, None, None);
            b.gep(Ty::U8, p, vec![n])
        };
        fns.push((name, vec![], vec![Ty::Ptr], b.ret(vec![p])));
        expected.push(if bits == 32 {
            Verdict::Ub(
                if allocation {
                    "Alloca: count must be positive"
                } else {
                    "GEP: negative index -2147483648"
                }
                .into(),
            )
        } else {
            Verdict::Ok(vec![Val::PtrAt {
                alloc: 0,
                offset: if allocation { 0 } else { 1 << 31 },
            }])
        });
    }
    let mut b = MemBody::new(&[]);
    let p = b.alloca(Ty::Ptr, None, None);
    let one = b.konst(Ty::U64, 1);
    let q = b.gep(Ty::Ptr, p, vec![one]);
    fns.push((
        "pointer_layout_stride",
        vec![],
        vec![Ty::Ptr],
        b.ret(vec![q]),
    ));
    expected.push(Verdict::Ok(vec![Val::PtrAt {
        alloc: 0,
        offset: u64::from(bits / 8),
    }]));

    // A plain poison image has the actual pointer-sized extent when copied.
    let mut b = MemBody::new(&[]);
    let p = b.alloca(Ty::Usize, None, None);
    let q = b.alloca(Ty::Usize, None, None);
    let poison = b.load(Ty::Usize, p, false, None);
    b.store(Ty::Usize, q, poison, false, None);
    let v = b.konst(Ty::I32, 7);
    fns.push((
        "pointer_sized_poison_copy",
        vec![],
        vec![Ty::I32],
        b.ret(vec![v]),
    ));
    expected.push(seven());

    // Calls share normal memory while retaining the pointer-sized signature.
    let callee = FuncId::new(fns.len() as u32 + 1);
    let mut b = MemBody::new(&[]);
    let p = b.alloca(Ty::Usize, None, None);
    let x = b.konst(Ty::Usize, 0x7654_3210);
    let r = b.val(trust_ir::Inst::Call {
        callee,
        args: vec![p, x],
    });
    let v = b.load(Ty::Usize, p, true, None);
    fns.push((
        "call_shares_target_memory",
        vec![],
        vec![Ty::Usize, Ty::Usize],
        b.ret(vec![r, v]),
    ));
    expected.push(Verdict::Ok(vec![
        Val::Int {
            width: bits,
            raw: 0x7654_3210
        };
        2
    ]));
    let mut b = MemBody::new(&[Ty::Ptr, Ty::Usize]);
    b.store(Ty::Usize, b.param(0), b.param(1), false, None);
    let x = b.param(1);
    fns.push((
        "target_memory_callee",
        vec![Ty::Ptr, Ty::Usize],
        vec![Ty::Usize],
        b.ret(vec![x]),
    ));

    let mut module = mem_module("semr_target_memory", fns);
    module.target_info = Some(semr_target(bits));
    let runs = module
        .functions
        .iter()
        .filter(|f| module.func_types[f.ty.0 as usize].params.is_empty())
        .map(|f| (f.id, vec![]))
        .collect();
    (
        SemrCase {
            label: format!("target memory {bits}"),
            module,
            runs,
        },
        expected,
    )
}

#[test]
fn semr_target_memory_rules_agree_with_the_interpreter() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    for bits in [32, 64] {
        let (case, expected) = semr_target_memory_case(bits);
        let reports = semr_differential(exe, &[case.batch()]);
        assert_eq!(reports.len(), expected.len());
        for (report, want) in reports.iter().zip(expected) {
            let name = &case.module.functions[report.func.0 as usize].name;
            assert_eq!(report.rust, want, "interpreter {bits}/{name}");
            assert_eq!(report.lean, want, "SemR {bits}/{name}");
            assert_eq!(report.comparison, Comparison::Agree, "{bits}/{name}");
            eprintln!("target{bits}/{name}: {:?}", report.lean);
        }
    }
}

// ---------------------------------------------------------------------------
// v67 (PKG-U13a): the integer tensor contraction. Tensor values reach both
// engines as entry arguments (`semr_arg`'s `t<code>:<dims>:<residues>`), so
// each run is one contraction of its parameters, returned.
// ---------------------------------------------------------------------------

/// What both engines must say about one tensor run.
#[derive(Debug)]
enum TensorWant {
    /// The one returned value.
    Ok(Val),
    /// Undefined behaviour with exactly this message (SPEC: byte for byte).
    Ub(&'static str),
    /// A type error (an ill-formed instruction or operand value).
    TypeError,
}

const TENSOR_EXTENT_MISMATCH: &str = "tensor contraction: paired axes have different extents";
const TENSOR_RESULT_TOO_LARGE: &str =
    "tensor contraction: the result has more elements than usize holds";

fn tensor_ty(elem: &Ty, rank: u32) -> Ty {
    Ty::Tensor(Box::new(elem.clone()), rank)
}

/// A tensor argument of `elem` with extents `dims` and row-major `values`
/// (its element count is NOT checked here: the ill-formed runs need that).
fn tensor_arg(elem: &Ty, dims: &[u64], values: &[i128]) -> InterpretValue {
    let elems = values
        .iter()
        .map(|&v| InterpretValue::int(elem.clone(), v).expect("tensor element"))
        .collect();
    InterpretValue {
        ty: tensor_ty(elem, dims.len() as u32),
        kind: InterpretValueKind::Tensor {
            dims: dims.to_vec(),
            elems: trust_ir::ArrayValue::from_vec(elems),
        },
    }
}

/// The expected tensor value: element code, extents, residues.
fn tensor_val(elem: &Ty, dims: &[u64], residues: &[u128]) -> Val {
    Val::Tensor {
        elem: semr_int_code(elem),
        dims: dims.to_vec(),
        elems: residues.to_vec(),
    }
}

/// One contraction run: `fn name(%0: lhs, %1: rhs) -> result { %2 =
/// tensor_contract result %0, %1 batch [..] contract [..]; return %2 }`.
struct TensorRun {
    name: &'static str,
    result: Ty,
    batch: Vec<(u32, u32)>,
    contract: Vec<(u32, u32)>,
    lhs: InterpretValue,
    rhs: InterpretValue,
    want: TensorWant,
}

/// The hand-written tensor runs, on the 64-bit reference layout (`target`
/// `None`) or a 32-bit target: every result shape the contraction has
/// (matrix multiply, batched, two contracted axes, `A·Bᵀ`, the outer product,
/// rank 0), wrapping at 8, 64 and 128 bits and in two's complement, empty
/// contracted and result extents, both undefined behaviours (paired extents,
/// the result count at the target's `usize`), pointer-width elements
/// re-expressed and wrapped at the target's width, an extent the 32-bit
/// `usize` cannot hold refused at entry, and the type errors (an ill-formed
/// operand, element and rank mismatches, an axis out of range or named
/// twice). Every run's verdict is written here, not computed.
fn semr_tensor_case(target: Option<trust_ir::TargetInfo>) -> (SemrCase, Vec<TensorWant>) {
    let (i8t, i32t, u32t, i64t, i128t, u8t, u16t, usizet) = (
        Ty::I8,
        Ty::I32,
        Ty::U32,
        Ty::I64,
        Ty::I128,
        Ty::U8,
        Ty::U16,
        Ty::Usize,
    );
    let wasm = target.as_ref().is_some_and(|t| t.pointer_size == 4);
    let a23 = || tensor_arg(&i32t, &[2, 3], &[1, 2, 3, 4, 5, 6]);
    let b32 = || tensor_arg(&i32t, &[3, 2], &[7, 8, 9, 10, 11, 12]);
    let a22 = || tensor_arg(&i32t, &[2, 2], &[1, 2, 3, 4]);
    let b22 = || tensor_arg(&i32t, &[2, 2], &[5, 6, 7, 8]);
    let mm = vec![(1, 0)];
    let mut runs = vec![
        TensorRun {
            name: "matmul_i32",
            result: tensor_ty(&i32t, 2),
            batch: vec![],
            contract: mm.clone(),
            lhs: a23(),
            rhs: b32(),
            want: TensorWant::Ok(tensor_val(&i32t, &[2, 2], &[58, 64, 139, 154])),
        },
        TensorRun {
            name: "a_times_b_transposed",
            result: tensor_ty(&i32t, 2),
            batch: vec![],
            contract: vec![(1, 1)],
            lhs: a22(),
            rhs: b22(),
            want: TensorWant::Ok(tensor_val(&i32t, &[2, 2], &[17, 23, 39, 53])),
        },
        TensorRun {
            name: "batched_matmul",
            result: tensor_ty(&i32t, 3),
            batch: vec![(0, 0)],
            contract: vec![(2, 1)],
            lhs: tensor_arg(&i32t, &[2, 1, 2], &[1, 2, 3, 4]),
            rhs: tensor_arg(&i32t, &[2, 2, 1], &[5, 6, 7, 8]),
            want: TensorWant::Ok(tensor_val(&i32t, &[2, 1, 1], &[17, 53])),
        },
        TensorRun {
            name: "two_contracted_axes",
            result: tensor_ty(&i64t, 0),
            batch: vec![],
            contract: vec![(0, 0), (1, 1)],
            lhs: tensor_arg(&i64t, &[2, 2], &[1, 2, 3, 4]),
            rhs: tensor_arg(&i64t, &[2, 2], &[5, 6, 7, 8]),
            want: TensorWant::Ok(tensor_val(&i64t, &[], &[70])),
        },
        TensorRun {
            name: "rank_zero_product",
            result: tensor_ty(&u16t, 0),
            batch: vec![],
            contract: vec![],
            lhs: tensor_arg(&u16t, &[], &[6]),
            rhs: tensor_arg(&u16t, &[], &[7]),
            want: TensorWant::Ok(tensor_val(&u16t, &[], &[42])),
        },
        TensorRun {
            name: "u8_products_and_sums_wrap",
            result: tensor_ty(&u8t, 2),
            batch: vec![],
            contract: mm.clone(),
            lhs: tensor_arg(&u8t, &[1, 2], &[200, 100]),
            rhs: tensor_arg(&u8t, &[2, 1], &[2, 3]),
            want: TensorWant::Ok(tensor_val(&u8t, &[1, 1], &[188])),
        },
        TensorRun {
            name: "i8_is_twos_complement",
            result: tensor_ty(&i8t, 2),
            batch: vec![],
            contract: mm.clone(),
            lhs: tensor_arg(&i8t, &[1, 2], &[-3, 4]),
            rhs: tensor_arg(&i8t, &[2, 1], &[5, -6]),
            want: TensorWant::Ok(tensor_val(&i8t, &[1, 1], &[256 - 39])),
        },
        TensorRun {
            name: "i128_product_wraps",
            result: tensor_ty(&i128t, 2),
            batch: vec![],
            contract: mm.clone(),
            lhs: tensor_arg(&i128t, &[1, 1], &[i128::MAX]),
            rhs: tensor_arg(&i128t, &[1, 1], &[2]),
            want: TensorWant::Ok(tensor_val(&i128t, &[1, 1], &[u128::MAX - 1])),
        },
        TensorRun {
            name: "empty_contracted_extent_sums_to_zero",
            result: tensor_ty(&i32t, 2),
            batch: vec![],
            contract: mm.clone(),
            lhs: tensor_arg(&i32t, &[2, 0], &[]),
            rhs: tensor_arg(&i32t, &[0, 3], &[]),
            want: TensorWant::Ok(tensor_val(&i32t, &[2, 3], &[0; 6])),
        },
        TensorRun {
            name: "empty_result_extent",
            result: tensor_ty(&i32t, 2),
            batch: vec![],
            contract: mm.clone(),
            lhs: tensor_arg(&i32t, &[0, 2], &[]),
            rhs: tensor_arg(&i32t, &[2, 3], &[1, 2, 3, 4, 5, 6]),
            want: TensorWant::Ok(tensor_val(&i32t, &[0, 3], &[])),
        },
        TensorRun {
            name: "contracted_extents_differ",
            result: tensor_ty(&i32t, 2),
            batch: vec![],
            contract: mm.clone(),
            lhs: a23(),
            rhs: a22(),
            want: TensorWant::Ub(TENSOR_EXTENT_MISMATCH),
        },
        TensorRun {
            name: "batch_extents_differ",
            result: tensor_ty(&i32t, 3),
            batch: vec![(0, 0)],
            contract: vec![(2, 1)],
            lhs: tensor_arg(&i32t, &[2, 1, 2], &[1, 2, 3, 4]),
            rhs: tensor_arg(&i32t, &[3, 2, 1], &[1, 2, 3, 4, 5, 6]),
            want: TensorWant::Ub(TENSOR_EXTENT_MISMATCH),
        },
        TensorRun {
            // The result has `2^(pointer bits)` elements; both operands
            // have none (an empty contracted extent).
            name: "result_count_reaches_usize",
            result: tensor_ty(&i32t, 2),
            batch: vec![],
            contract: mm.clone(),
            lhs: tensor_arg(&i32t, &[if wasm { 1 << 16 } else { 1 << 32 }, 0], &[]),
            rhs: tensor_arg(&i32t, &[0, if wasm { 1 << 16 } else { 1 << 32 }], &[]),
            want: TensorWant::Ub(TENSOR_RESULT_TOO_LARGE),
        },
        TensorRun {
            name: "operand_has_too_few_elements",
            result: tensor_ty(&i32t, 2),
            batch: vec![],
            contract: mm.clone(),
            lhs: tensor_arg(&i32t, &[2, 2], &[1, 2, 3]),
            rhs: b22(),
            want: TensorWant::TypeError,
        },
        TensorRun {
            name: "operand_elements_differ",
            result: tensor_ty(&i32t, 2),
            batch: vec![],
            contract: mm.clone(),
            lhs: a22(),
            rhs: tensor_arg(&u32t, &[2, 2], &[5, 6, 7, 8]),
            want: TensorWant::TypeError,
        },
        TensorRun {
            name: "result_rank_is_not_batch_and_free",
            result: tensor_ty(&i32t, 3),
            batch: vec![],
            contract: mm.clone(),
            lhs: a22(),
            rhs: b22(),
            want: TensorWant::TypeError,
        },
        TensorRun {
            name: "axis_out_of_range",
            result: tensor_ty(&i32t, 2),
            batch: vec![],
            contract: vec![(2, 0)],
            lhs: a22(),
            rhs: b22(),
            want: TensorWant::TypeError,
        },
        TensorRun {
            name: "axis_named_twice",
            result: tensor_ty(&i32t, 0),
            batch: vec![],
            contract: vec![(1, 0), (1, 1)],
            lhs: a22(),
            rhs: b22(),
            want: TensorWant::TypeError,
        },
    ];
    // Pointer-width elements at the run's pointer width: built at 64 bits,
    // re-expressed at the target's on entry by both engines, then wrapped
    // there.
    let isizet = Ty::Isize;
    let ptr_max = if wasm { 1u128 << 32 } else { 1u128 << 64 };
    runs.push(TensorRun {
        name: "isize_minus_one_at_the_target_width",
        result: tensor_ty(&isizet, 0),
        batch: vec![],
        contract: vec![(0, 0)],
        lhs: tensor_arg(&isizet, &[1], &[-1]),
        rhs: tensor_arg(&isizet, &[1], &[1]),
        want: TensorWant::Ok(tensor_val(&isizet, &[], &[ptr_max - 1])),
    });
    let half: i128 = if wasm { 1 << 31 } else { 1 << 63 };
    runs.push(TensorRun {
        name: "usize_product_wraps_at_the_target_width",
        result: tensor_ty(&usizet, 0),
        batch: vec![],
        contract: vec![(0, 0)],
        lhs: tensor_arg(&usizet, &[2], &[half, 3]),
        rhs: tensor_arg(&usizet, &[2], &[2, 1]),
        want: TensorWant::Ok(tensor_val(&usizet, &[], &[3])),
    });
    runs.push(TensorRun {
        name: "i64_product_wraps",
        result: tensor_ty(&i64t, 2),
        batch: vec![],
        contract: mm.clone(),
        lhs: tensor_arg(&i64t, &[1, 1], &[i128::from(i64::MAX)]),
        rhs: tensor_arg(&i64t, &[1, 1], &[2]),
        want: TensorWant::Ok(tensor_val(&i64t, &[1, 1], &[(1u128 << 64) - 2])),
    });
    if wasm {
        // An extent the 32-bit `usize` cannot hold is refused at entry, by
        // both engines, before any contraction reads it.
        runs.push(TensorRun {
            name: "entry_extent_past_the_target_usize",
            result: tensor_ty(&i32t, 2),
            batch: vec![],
            contract: mm.clone(),
            lhs: tensor_arg(&i32t, &[1 << 32, 0], &[]),
            rhs: tensor_arg(&i32t, &[0, 1], &[]),
            want: TensorWant::TypeError,
        });
    }
    if !wasm {
        // A pointer-width element at the reference layout's 64 bits.
        runs.push(TensorRun {
            name: "outer_product_usize",
            result: tensor_ty(&usizet, 2),
            batch: vec![],
            contract: vec![],
            lhs: tensor_arg(&usizet, &[2], &[1, 2]),
            rhs: tensor_arg(&usizet, &[3], &[3, 4, 5]),
            want: TensorWant::Ok(tensor_val(&usizet, &[2, 3], &[3, 4, 5, 6, 8, 10])),
        });
    }
    let mut fns = Vec::new();
    let mut args = Vec::new();
    let mut wants = Vec::new();
    for run in runs {
        let mut b = MemBody::new(&[run.lhs.ty.clone(), run.rhs.ty.clone()]);
        let r = b.val(trust_ir::Inst::TensorContract {
            ty: run.result.clone(),
            lhs: b.param(0),
            rhs: b.param(1),
            batch: run.batch,
            contract: run.contract,
        });
        fns.push((
            run.name,
            vec![run.lhs.ty.clone(), run.rhs.ty.clone()],
            vec![run.result],
            b.ret(vec![r]),
        ));
        args.push(vec![run.lhs, run.rhs]);
        wants.push(run.want);
    }
    // A tensor crosses the signature boundary unchanged.
    let x = tensor_arg(&i32t, &[2, 2], &[1, -2, 3, -4]);
    let b = MemBody::new(std::slice::from_ref(&x.ty));
    fns.push((
        "tensor_identity",
        vec![x.ty.clone()],
        vec![x.ty.clone()],
        b.ret_param0(),
    ));
    args.push(vec![x]);
    wants.push(TensorWant::Ok(tensor_val(
        &i32t,
        &[2, 2],
        &[1, (1u128 << 32) - 2, 3, (1u128 << 32) - 4],
    )));
    let mut module = mem_module("semr_tensor_contraction", fns);
    let label = match &target {
        Some(t) => format!("tensor contraction {}", t.pointer_size * 8),
        None => "tensor contraction reference".to_string(),
    };
    module.target_info = target;
    let runs = module.functions.iter().map(|f| f.id).zip(args).collect();
    (
        SemrCase {
            label,
            module,
            runs,
        },
        wants,
    )
}

/// SemR's `TensorContract` agrees with the reference interpreter on every
/// hand-written tensor run, at the reference layout and on wasm32, and both
/// reach the verdict written in `semr_tensor_case` (a computed tensor, the
/// exact undefined-behaviour text, or a type error).
#[test]
fn semr_tensor_contraction_agrees_with_the_interpreter() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    for target in [None, Some(semr_target(32))] {
        let (case, wants) = semr_tensor_case(target);
        let reports = semr_differential(exe, &[case.batch()]);
        assert_eq!(reports.len(), wants.len(), "{}", case.label);
        for (report, want) in reports.iter().zip(&wants) {
            let name = &case.module.functions[report.func.0 as usize].name;
            let what = format!("{}/{name}", case.label);
            match want {
                TensorWant::Ok(v) => {
                    assert_eq!(
                        report.rust,
                        Verdict::Ok(vec![v.clone()]),
                        "interpreter {what}"
                    );
                    assert_eq!(report.lean, Verdict::Ok(vec![v.clone()]), "SemR {what}");
                }
                TensorWant::Ub(m) => {
                    assert_eq!(report.rust, Verdict::Ub((*m).into()), "interpreter {what}");
                    assert_eq!(report.lean, Verdict::Ub((*m).into()), "SemR {what}");
                }
                TensorWant::TypeError => {
                    assert!(
                        matches!(report.rust, Verdict::TypeError(_)),
                        "interpreter {what}: {report:?}"
                    );
                    assert!(
                        matches!(report.lean, Verdict::TypeError(_)),
                        "SemR {what}: {report:?}"
                    );
                }
            }
            assert_eq!(report.comparison, Comparison::Agree, "{what}");
            eprintln!("{what}: {:?}", report.lean);
        }
    }
}

// ---------------------------------------------------------------------------
// v68 (PKG-U13c): the tensor map, reduction and view. As for the
// contraction, every operand is an entry argument, so each run is one
// instruction over its parameters, returned.
// ---------------------------------------------------------------------------

const TENSOR_MAP_EXTENTS_DIFFER: &str = "tensor map: operand extents differ";
const TENSOR_REDUCE_TOO_LARGE: &str =
    "tensor reduction: the result has more elements than usize holds";
const TENSOR_VIEW_OVERFLOWS: &str = "tensor view: an index expression overflows";
const TENSOR_VIEW_DIVIDES_BY_ZERO: &str = "tensor view: an index expression divides by zero";
const TENSOR_VIEW_EXTENT: &str = "tensor view: a result extent does not fit usize";
const TENSOR_VIEW_TOO_LARGE: &str = "tensor view: the result has more elements than usize holds";
const TENSOR_VIEW_OUT_OF_RANGE: &str = "tensor view: a source coordinate is out of range";

/// One map, reduction, view, gather or scatter run: `fn name(%0.., %n-1) ->
/// result { %n = inst; return %n }`, `inst` built over the parameter ids
/// `0..n`.
struct RegionRun {
    name: &'static str,
    args: Vec<InterpretValue>,
    result: Ty,
    inst: trust_ir::Inst,
    want: TensorWant,
}

fn vid(n: u32) -> trust_ir::value::ValueId {
    trust_ir::value::ValueId::new(n)
}

fn scalar_arg(ty: &Ty, v: i128) -> InterpretValue {
    InterpretValue::int(ty.clone(), v).expect("scalar argument")
}

/// `%0 .. %{n-1}` as the operand list of a map.
fn map_inst(
    result: &Ty,
    n: u32,
    body: Vec<trust_ir::TensorMapNode<trust_ir::NoExt>>,
) -> trust_ir::Inst {
    trust_ir::Inst::TensorMap {
        ty: result.clone(),
        args: (0..n).map(vid).collect(),
        body,
    }
}

fn reduce_inst(result: &Ty, op: trust_ir::TensorReduceOp, axes: &[u32]) -> trust_ir::Inst {
    trust_ir::Inst::TensorReduce {
        ty: result.clone(),
        src: vid(0),
        op,
        axes: axes.to_vec(),
        order: trust_ir::TensorReduceOrder::RowMajor,
    }
}

/// A view of `%0` with parameters `%1 ..= %params` and, when `fill`, the
/// fill the parameter after them.
fn view_inst(
    result: &Ty,
    params: u32,
    fill: bool,
    exprs: Vec<trust_ir::TensorIndexExpr>,
    shape: &[u32],
    index: &[u32],
) -> trust_ir::Inst {
    trust_ir::Inst::TensorView {
        ty: result.clone(),
        src: vid(0),
        params: (1..=params).map(vid).collect(),
        exprs,
        shape: shape.to_vec(),
        index: index.to_vec(),
        fill: fill.then(|| vid(params + 1)),
    }
}

/// The hand-written map, reduction and view runs, on the 64-bit reference
/// layout (`target` `None`) or a 32-bit target: every map node kind (a
/// scalar operand, a `Bool` connective, a narrowing and a widening cast),
/// wrapping at 8 to 128 bits, rank 0 and empty extents, a node's own scalar
/// verdict; every reduction operator, a middle axis, all axes, no axes and
/// an empty reduced extent; transpose, slice, pad, broadcast, both reshapes,
/// a clamped reversal and Euclidean division of a negative; every
/// undefined-behaviour text of the three (each at one site that raises it),
/// the counts at the target's `usize`; and a type error for each static rule
/// (M1-M5, M4's operation half among them, R1-R3, V1-V6) and for an
/// ill-formed operand. Every run's verdict is written here, not computed.
fn semr_tensor_region_case(target: Option<trust_ir::TargetInfo>) -> (SemrCase, Vec<TensorWant>) {
    use trust_ir::{
        BinOp, CastOp, ICmpOp, TensorIndexExpr as E, TensorMapNode as N, TensorReduceOp as R, UnOp,
    };
    let (i8t, i16t, i32t, i64t, i128t, u8t, u16t, u32t, usizet) = (
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::Usize,
    );
    let wasm = target.as_ref().is_some_and(|t| t.pointer_size == 4);
    let add = |ty: &Ty, lhs, rhs| N::BinOp {
        op: BinOp::Add,
        ty: ty.clone(),
        lhs,
        rhs,
    };
    let x23 = || tensor_arg(&i32t, &[2, 3], &[1, 2, 3, 4, 5, 6]);
    let mut runs = vec![
        // ---- map ----
        RegionRun {
            name: "map_add_wraps",
            args: vec![
                x23(),
                tensor_arg(&i32t, &[2, 3], &[10, 20, 30, 40, 50, i128::from(i32::MAX)]),
            ],
            result: tensor_ty(&i32t, 2),
            inst: map_inst(&tensor_ty(&i32t, 2), 2, vec![add(&i32t, 0, 1)]),
            want: TensorWant::Ok(tensor_val(
                &i32t,
                &[2, 3],
                &[11, 22, 33, 44, 55, 2_147_483_653],
            )),
        },
        RegionRun {
            name: "map_relu_with_a_scalar",
            args: vec![
                tensor_arg(&i32t, &[2, 2], &[-3, 0, 7, -1]),
                scalar_arg(&i32t, 0),
            ],
            result: tensor_ty(&i32t, 2),
            inst: map_inst(
                &tensor_ty(&i32t, 2),
                2,
                vec![
                    N::ICmp {
                        op: ICmpOp::Sgt,
                        ty: i32t.clone(),
                        lhs: 0,
                        rhs: 1,
                    },
                    N::Select {
                        ty: i32t.clone(),
                        cond: 2,
                        then_lane: 0,
                        else_lane: 1,
                    },
                ],
            ),
            want: TensorWant::Ok(tensor_val(&i32t, &[2, 2], &[0, 0, 7, 0])),
        },
        RegionRun {
            name: "map_widen_then_scale",
            args: vec![
                tensor_arg(&i8t, &[3], &[-128, 5, 127]),
                scalar_arg(&i32t, 1000),
            ],
            result: tensor_ty(&i32t, 1),
            inst: map_inst(
                &tensor_ty(&i32t, 1),
                2,
                vec![
                    N::Cast {
                        op: CastOp::SExt,
                        src_ty: i8t.clone(),
                        dst_ty: i32t.clone(),
                        operand: 0,
                    },
                    N::BinOp {
                        op: BinOp::Mul,
                        ty: i32t.clone(),
                        lhs: 2,
                        rhs: 1,
                    },
                ],
            ),
            want: TensorWant::Ok(tensor_val(&i32t, &[3], &[4_294_839_296, 5000, 127_000])),
        },
        RegionRun {
            name: "map_bool_connective_selects",
            args: vec![
                tensor_arg(&u8t, &[4], &[0, 1, 2, 3]),
                tensor_arg(&u8t, &[4], &[3, 2, 1, 0]),
            ],
            result: tensor_ty(&u8t, 1),
            inst: map_inst(
                &tensor_ty(&u8t, 1),
                2,
                vec![
                    N::ICmp {
                        op: ICmpOp::Ult,
                        ty: u8t.clone(),
                        lhs: 0,
                        rhs: 1,
                    },
                    N::ICmp {
                        op: ICmpOp::Ugt,
                        ty: u8t.clone(),
                        lhs: 0,
                        rhs: 1,
                    },
                    N::BinOp {
                        op: BinOp::BOr,
                        ty: Ty::Bool,
                        lhs: 2,
                        rhs: 3,
                    },
                    N::Select {
                        ty: u8t.clone(),
                        cond: 4,
                        then_lane: 1,
                        else_lane: 0,
                    },
                ],
            ),
            want: TensorWant::Ok(tensor_val(&u8t, &[4], &[3, 2, 1, 0])),
        },
        RegionRun {
            name: "map_trunc_then_zext",
            args: vec![tensor_arg(&u16t, &[3], &[0x1234, 0xFFFF, 0x0080])],
            result: tensor_ty(&u16t, 1),
            inst: map_inst(
                &tensor_ty(&u16t, 1),
                1,
                vec![
                    N::Cast {
                        op: CastOp::Trunc,
                        src_ty: u16t.clone(),
                        dst_ty: u8t.clone(),
                        operand: 0,
                    },
                    N::Cast {
                        op: CastOp::ZExt,
                        src_ty: u8t.clone(),
                        dst_ty: u16t.clone(),
                        operand: 1,
                    },
                ],
            ),
            want: TensorWant::Ok(tensor_val(&u16t, &[3], &[0x34, 0xFF, 0x80])),
        },
        RegionRun {
            name: "map_i128_wraps",
            args: vec![
                tensor_arg(&i128t, &[1], &[i128::MAX]),
                tensor_arg(&i128t, &[1], &[1]),
            ],
            result: tensor_ty(&i128t, 1),
            inst: map_inst(&tensor_ty(&i128t, 1), 2, vec![add(&i128t, 0, 1)]),
            want: TensorWant::Ok(tensor_val(&i128t, &[1], &[1u128 << 127])),
        },
        RegionRun {
            name: "map_rank_zero",
            args: vec![tensor_arg(&i64t, &[], &[5])],
            result: tensor_ty(&i64t, 0),
            inst: map_inst(
                &tensor_ty(&i64t, 0),
                1,
                vec![N::UnOp {
                    op: UnOp::Neg,
                    ty: i64t.clone(),
                    operand: 0,
                }],
            ),
            want: TensorWant::Ok(tensor_val(&i64t, &[], &[(1u128 << 64) - 5])),
        },
        RegionRun {
            name: "map_empty_evaluates_no_node",
            args: vec![
                tensor_arg(&u32t, &[0, 3], &[]),
                tensor_arg(&u32t, &[0, 3], &[]),
            ],
            result: tensor_ty(&u32t, 2),
            inst: map_inst(
                &tensor_ty(&u32t, 2),
                2,
                vec![N::BinOp {
                    op: BinOp::UDiv,
                    ty: u32t.clone(),
                    lhs: 0,
                    rhs: 1,
                }],
            ),
            want: TensorWant::Ok(tensor_val(&u32t, &[0, 3], &[])),
        },
        RegionRun {
            name: "map_node_divides_by_zero",
            args: vec![
                tensor_arg(&u32t, &[2], &[6, 7]),
                tensor_arg(&u32t, &[2], &[3, 0]),
            ],
            result: tensor_ty(&u32t, 1),
            inst: map_inst(
                &tensor_ty(&u32t, 1),
                2,
                vec![N::BinOp {
                    op: BinOp::UDiv,
                    ty: u32t.clone(),
                    lhs: 0,
                    rhs: 1,
                }],
            ),
            want: TensorWant::Ub("unsigned division by zero"),
        },
        RegionRun {
            name: "map_extents_differ",
            args: vec![x23(), tensor_arg(&i32t, &[3, 2], &[1, 2, 3, 4, 5, 6])],
            result: tensor_ty(&i32t, 2),
            inst: map_inst(&tensor_ty(&i32t, 2), 2, vec![add(&i32t, 0, 1)]),
            want: TensorWant::Ub(TENSOR_MAP_EXTENTS_DIFFER),
        },
        RegionRun {
            name: "map_operand_of_another_rank",
            args: vec![x23(), tensor_arg(&i32t, &[6], &[1, 2, 3, 4, 5, 6])],
            result: tensor_ty(&i32t, 2),
            inst: map_inst(&tensor_ty(&i32t, 2), 2, vec![add(&i32t, 0, 1)]),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "map_lane_of_another_type",
            args: vec![tensor_arg(&i64t, &[2], &[1, 2])],
            result: tensor_ty(&i32t, 1),
            inst: map_inst(
                &tensor_ty(&i32t, 1),
                1,
                vec![N::UnOp {
                    op: UnOp::Neg,
                    ty: i32t.clone(),
                    operand: 0,
                }],
            ),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "map_reads_its_own_lane",
            args: vec![tensor_arg(&i32t, &[1], &[1])],
            result: tensor_ty(&i32t, 1),
            inst: map_inst(
                &tensor_ty(&i32t, 1),
                1,
                vec![N::UnOp {
                    op: UnOp::Neg,
                    ty: i32t.clone(),
                    operand: 1,
                }],
            ),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "map_last_node_is_not_the_element",
            args: vec![tensor_arg(&i32t, &[1], &[1])],
            result: tensor_ty(&i32t, 1),
            inst: map_inst(
                &tensor_ty(&i32t, 1),
                1,
                vec![N::ICmp {
                    op: ICmpOp::Eq,
                    ty: i32t.clone(),
                    lhs: 0,
                    rhs: 0,
                }],
            ),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "map_ill_formed_operand",
            args: vec![tensor_arg(&i32t, &[2, 2], &[1, 2, 3])],
            result: tensor_ty(&i32t, 2),
            inst: map_inst(
                &tensor_ty(&i32t, 2),
                1,
                vec![N::UnOp {
                    op: UnOp::Neg,
                    ty: i32t.clone(),
                    operand: 0,
                }],
            ),
            want: TensorWant::TypeError,
        },
        // M4's operation half (`TensorMapNode::op_refusal`): checked before
        // any element is read, so over an empty tensor too and ahead of a
        // node's own undefined behaviour.
        RegionRun {
            name: "map_bool_connective_at_an_integer",
            args: vec![tensor_arg(&i32t, &[2], &[3, 0])],
            result: tensor_ty(&i32t, 1),
            inst: map_inst(
                &tensor_ty(&i32t, 1),
                1,
                vec![N::BinOp {
                    op: BinOp::BAnd,
                    ty: i32t.clone(),
                    lhs: 0,
                    rhs: 0,
                }],
            ),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "map_trunc_that_widens",
            args: vec![tensor_arg(&i8t, &[1], &[-1])],
            result: tensor_ty(&i32t, 1),
            inst: map_inst(
                &tensor_ty(&i32t, 1),
                1,
                vec![N::Cast {
                    op: CastOp::Trunc,
                    src_ty: i8t.clone(),
                    dst_ty: i32t.clone(),
                    operand: 0,
                }],
            ),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "map_zext_to_bool",
            args: vec![tensor_arg(&u8t, &[1], &[1])],
            result: tensor_ty(&u8t, 1),
            inst: map_inst(
                &tensor_ty(&u8t, 1),
                1,
                vec![
                    N::Cast {
                        op: CastOp::ZExt,
                        src_ty: u8t.clone(),
                        dst_ty: Ty::Bool,
                        operand: 0,
                    },
                    N::Select {
                        ty: u8t.clone(),
                        cond: 1,
                        then_lane: 0,
                        else_lane: 0,
                    },
                ],
            ),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "map_misapplied_operation_over_an_empty_tensor",
            args: vec![tensor_arg(&i32t, &[0], &[])],
            result: tensor_ty(&i32t, 1),
            inst: map_inst(
                &tensor_ty(&i32t, 1),
                1,
                vec![
                    N::ICmp {
                        op: ICmpOp::Eq,
                        ty: i32t.clone(),
                        lhs: 0,
                        rhs: 0,
                    },
                    N::UnOp {
                        op: UnOp::Neg,
                        ty: Ty::Bool,
                        operand: 1,
                    },
                    N::Select {
                        ty: i32t.clone(),
                        cond: 2,
                        then_lane: 0,
                        else_lane: 0,
                    },
                ],
            ),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "map_static_rule_before_a_division_by_zero",
            args: vec![tensor_arg(&u32t, &[1], &[6]), scalar_arg(&u32t, 0)],
            result: tensor_ty(&u32t, 1),
            inst: map_inst(
                &tensor_ty(&u32t, 1),
                2,
                vec![
                    N::BinOp {
                        op: BinOp::UDiv,
                        ty: u32t.clone(),
                        lhs: 0,
                        rhs: 1,
                    },
                    N::ICmp {
                        op: ICmpOp::Eq,
                        ty: u32t.clone(),
                        lhs: 0,
                        rhs: 0,
                    },
                    N::BinOp {
                        op: BinOp::Add,
                        ty: Ty::Bool,
                        lhs: 3,
                        rhs: 3,
                    },
                    N::Select {
                        ty: u32t.clone(),
                        cond: 4,
                        then_lane: 2,
                        else_lane: 0,
                    },
                ],
            ),
            want: TensorWant::TypeError,
        },
        // ---- reduce ----
        RegionRun {
            name: "reduce_add_rows",
            args: vec![x23()],
            result: tensor_ty(&i32t, 1),
            inst: reduce_inst(&tensor_ty(&i32t, 1), R::Add, &[1]),
            want: TensorWant::Ok(tensor_val(&i32t, &[2], &[6, 15])),
        },
        RegionRun {
            name: "reduce_add_columns",
            args: vec![x23()],
            result: tensor_ty(&i32t, 1),
            inst: reduce_inst(&tensor_ty(&i32t, 1), R::Add, &[0]),
            want: TensorWant::Ok(tensor_val(&i32t, &[3], &[5, 7, 9])),
        },
        RegionRun {
            name: "reduce_mul_everything_wraps",
            args: vec![tensor_arg(&i8t, &[2, 2], &[3, -4, 5, 7])],
            result: tensor_ty(&i8t, 0),
            inst: reduce_inst(&tensor_ty(&i8t, 0), R::Mul, &[0, 1]),
            want: TensorWant::Ok(tensor_val(&i8t, &[], &[92])),
        },
        RegionRun {
            name: "reduce_and",
            args: vec![tensor_arg(&u8t, &[3], &[0xF0, 0x3C, 0xFF])],
            result: tensor_ty(&u8t, 0),
            inst: reduce_inst(&tensor_ty(&u8t, 0), R::And, &[0]),
            want: TensorWant::Ok(tensor_val(&u8t, &[], &[0x30])),
        },
        RegionRun {
            name: "reduce_or",
            args: vec![tensor_arg(&u8t, &[3], &[0x01, 0x10, 0x80])],
            result: tensor_ty(&u8t, 0),
            inst: reduce_inst(&tensor_ty(&u8t, 0), R::Or, &[0]),
            want: TensorWant::Ok(tensor_val(&u8t, &[], &[0x91])),
        },
        RegionRun {
            name: "reduce_xor",
            args: vec![tensor_arg(&u8t, &[3], &[0xFF, 0x0F, 0x01])],
            result: tensor_ty(&u8t, 0),
            inst: reduce_inst(&tensor_ty(&u8t, 0), R::Xor, &[0]),
            want: TensorWant::Ok(tensor_val(&u8t, &[], &[0xF1])),
        },
        RegionRun {
            name: "reduce_smin",
            args: vec![tensor_arg(&i16t, &[2, 3], &[5, -7, 3, 0, 2, -1])],
            result: tensor_ty(&i16t, 1),
            inst: reduce_inst(&tensor_ty(&i16t, 1), R::SMin, &[1]),
            want: TensorWant::Ok(tensor_val(&i16t, &[2], &[65_529, 65_535])),
        },
        RegionRun {
            name: "reduce_smax",
            args: vec![tensor_arg(&i16t, &[2, 3], &[5, -7, 3, 0, 2, -1])],
            result: tensor_ty(&i16t, 1),
            inst: reduce_inst(&tensor_ty(&i16t, 1), R::SMax, &[1]),
            want: TensorWant::Ok(tensor_val(&i16t, &[2], &[5, 2])),
        },
        RegionRun {
            name: "reduce_umin",
            args: vec![tensor_arg(&u8t, &[2, 3], &[200, 3, 255, 0, 17, 128])],
            result: tensor_ty(&u8t, 1),
            inst: reduce_inst(&tensor_ty(&u8t, 1), R::UMin, &[1]),
            want: TensorWant::Ok(tensor_val(&u8t, &[2], &[3, 0])),
        },
        RegionRun {
            name: "reduce_umax",
            args: vec![tensor_arg(&u8t, &[2, 3], &[200, 3, 255, 0, 17, 128])],
            result: tensor_ty(&u8t, 1),
            inst: reduce_inst(&tensor_ty(&u8t, 1), R::UMax, &[1]),
            want: TensorWant::Ok(tensor_val(&u8t, &[2], &[255, 128])),
        },
        RegionRun {
            name: "reduce_a_middle_axis",
            args: vec![tensor_arg(&i32t, &[2, 2, 2], &[1, 2, 3, 4, 5, 6, 7, 8])],
            result: tensor_ty(&i32t, 2),
            inst: reduce_inst(&tensor_ty(&i32t, 2), R::Add, &[1]),
            want: TensorWant::Ok(tensor_val(&i32t, &[2, 2], &[4, 6, 12, 14])),
        },
        RegionRun {
            name: "reduce_no_axes_is_the_source",
            args: vec![tensor_arg(&i32t, &[2], &[1, -2])],
            result: tensor_ty(&i32t, 1),
            inst: reduce_inst(&tensor_ty(&i32t, 1), R::Mul, &[]),
            want: TensorWant::Ok(tensor_val(&i32t, &[2], &[1, (1u128 << 32) - 2])),
        },
        RegionRun {
            name: "reduce_empty_extent_gives_the_smax_identity",
            args: vec![tensor_arg(&i64t, &[3, 0], &[])],
            result: tensor_ty(&i64t, 1),
            inst: reduce_inst(&tensor_ty(&i64t, 1), R::SMax, &[1]),
            want: TensorWant::Ok(tensor_val(&i64t, &[3], &[1u128 << 63; 3])),
        },
        RegionRun {
            name: "reduce_empty_extent_gives_the_and_identity",
            args: vec![tensor_arg(&u8t, &[0], &[])],
            result: tensor_ty(&u8t, 0),
            inst: reduce_inst(&tensor_ty(&u8t, 0), R::And, &[0]),
            want: TensorWant::Ok(tensor_val(&u8t, &[], &[0xFF])),
        },
        RegionRun {
            name: "reduce_result_past_usize",
            args: vec![tensor_arg(
                &i32t,
                &[
                    if wasm { 1 << 16 } else { 1 << 32 },
                    if wasm { 1 << 16 } else { 1 << 32 },
                    0,
                ],
                &[],
            )],
            result: tensor_ty(&i32t, 2),
            inst: reduce_inst(&tensor_ty(&i32t, 2), R::Add, &[2]),
            want: TensorWant::Ub(TENSOR_REDUCE_TOO_LARGE),
        },
        RegionRun {
            name: "reduce_axes_not_ascending",
            args: vec![x23()],
            result: tensor_ty(&i32t, 0),
            inst: reduce_inst(&tensor_ty(&i32t, 0), R::Add, &[1, 0]),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "reduce_result_rank_wrong",
            args: vec![x23()],
            result: tensor_ty(&i32t, 2),
            inst: reduce_inst(&tensor_ty(&i32t, 2), R::Add, &[1]),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "reduce_element_differs",
            args: vec![x23()],
            result: tensor_ty(&i64t, 1),
            inst: reduce_inst(&tensor_ty(&i64t, 1), R::Add, &[1]),
            want: TensorWant::TypeError,
        },
        // ---- view ----
        RegionRun {
            name: "view_transpose",
            args: vec![x23()],
            result: tensor_ty(&i32t, 2),
            inst: view_inst(
                &tensor_ty(&i32t, 2),
                0,
                false,
                vec![E::SrcExtent(1), E::SrcExtent(0), E::Coord(1), E::Coord(0)],
                &[0, 1],
                &[2, 3],
            ),
            want: TensorWant::Ok(tensor_val(&i32t, &[3, 2], &[1, 4, 2, 5, 3, 6])),
        },
        RegionRun {
            name: "view_slice_rows",
            args: vec![
                tensor_arg(&i32t, &[3, 2], &[1, 2, 3, 4, 5, 6]),
                scalar_arg(&usizet, 1),
                scalar_arg(&usizet, 2),
            ],
            result: tensor_ty(&i32t, 2),
            inst: view_inst(
                &tensor_ty(&i32t, 2),
                2,
                false,
                vec![
                    E::Param(1),
                    E::SrcExtent(1),
                    E::Coord(0),
                    E::Param(0),
                    E::Add(2, 3),
                    E::Coord(1),
                ],
                &[0, 1],
                &[4, 5],
            ),
            want: TensorWant::Ok(tensor_val(&i32t, &[2, 2], &[3, 4, 5, 6])),
        },
        RegionRun {
            name: "view_pad_with_a_fill",
            args: vec![tensor_arg(&i32t, &[3], &[1, 2, 3]), scalar_arg(&i32t, -9)],
            result: tensor_ty(&i32t, 1),
            inst: view_inst(
                &tensor_ty(&i32t, 1),
                0,
                true,
                vec![
                    E::SrcExtent(0),
                    E::Lit(2),
                    E::Add(0, 1),
                    E::Coord(0),
                    E::Lit(1),
                    E::Sub(3, 4),
                ],
                &[2],
                &[5],
            ),
            want: TensorWant::Ok(tensor_val(
                &i32t,
                &[5],
                &[4_294_967_287, 1, 2, 3, 4_294_967_287],
            )),
        },
        RegionRun {
            name: "view_broadcast",
            args: vec![tensor_arg(&i32t, &[3], &[1, 2, 3]), scalar_arg(&usizet, 2)],
            result: tensor_ty(&i32t, 2),
            inst: view_inst(
                &tensor_ty(&i32t, 2),
                1,
                false,
                vec![E::Param(0), E::SrcExtent(0), E::Coord(1)],
                &[0, 1],
                &[2],
            ),
            want: TensorWant::Ok(tensor_val(&i32t, &[2, 3], &[1, 2, 3, 1, 2, 3])),
        },
        RegionRun {
            name: "view_reshape_up",
            args: vec![tensor_arg(&i32t, &[6], &[1, 2, 3, 4, 5, 6])],
            result: tensor_ty(&i32t, 2),
            inst: view_inst(
                &tensor_ty(&i32t, 2),
                0,
                false,
                vec![
                    E::Lit(2),
                    E::Lit(3),
                    E::Coord(0),
                    E::Mul(2, 1),
                    E::Coord(1),
                    E::Add(3, 4),
                ],
                &[0, 1],
                &[5],
            ),
            want: TensorWant::Ok(tensor_val(&i32t, &[2, 3], &[1, 2, 3, 4, 5, 6])),
        },
        RegionRun {
            name: "view_reshape_down",
            args: vec![x23()],
            result: tensor_ty(&i32t, 1),
            inst: view_inst(
                &tensor_ty(&i32t, 1),
                0,
                false,
                vec![
                    E::Lit(6),
                    E::Lit(3),
                    E::Coord(0),
                    E::Div(2, 1),
                    E::Rem(2, 1),
                ],
                &[0],
                &[3, 4],
            ),
            want: TensorWant::Ok(tensor_val(&i32t, &[6], &[1, 2, 3, 4, 5, 6])),
        },
        RegionRun {
            name: "view_clamped_reversal",
            args: vec![tensor_arg(&i32t, &[4], &[1, 2, 3, 4])],
            result: tensor_ty(&i32t, 1),
            inst: view_inst(
                &tensor_ty(&i32t, 1),
                0,
                false,
                vec![
                    E::SrcExtent(0),
                    E::Lit(1),
                    E::Sub(0, 1),
                    E::Coord(0),
                    E::Sub(2, 3),
                    E::Min(4, 2),
                    E::Lit(0),
                    E::Max(5, 6),
                ],
                &[0],
                &[7],
            ),
            want: TensorWant::Ok(tensor_val(&i32t, &[4], &[4, 3, 2, 1])),
        },
        RegionRun {
            name: "view_euclidean_rem_of_a_negative",
            args: vec![tensor_arg(&i32t, &[3], &[10, 20, 30])],
            result: tensor_ty(&i32t, 1),
            inst: view_inst(
                &tensor_ty(&i32t, 1),
                0,
                false,
                vec![
                    E::Lit(3),
                    E::Coord(0),
                    E::Lit(4),
                    E::Sub(1, 2),
                    E::Rem(3, 0),
                ],
                &[0],
                &[4],
            ),
            want: TensorWant::Ok(tensor_val(&i32t, &[3], &[30, 10, 20])),
        },
        RegionRun {
            name: "view_euclidean_div_of_a_negative",
            args: vec![tensor_arg(&i32t, &[3], &[10, 20, 30])],
            result: tensor_ty(&i32t, 1),
            inst: view_inst(
                &tensor_ty(&i32t, 1),
                0,
                false,
                vec![
                    E::Lit(3),
                    E::Coord(0),
                    E::Sub(1, 0),
                    E::Div(2, 0),
                    E::Lit(1),
                    E::Add(3, 4),
                ],
                &[0],
                &[5],
            ),
            want: TensorWant::Ok(tensor_val(&i32t, &[3], &[10, 10, 10])),
        },
        RegionRun {
            name: "view_empty_broadcast_reads_nothing",
            args: vec![tensor_arg(&i32t, &[0], &[]), scalar_arg(&usizet, 2)],
            result: tensor_ty(&i32t, 2),
            inst: view_inst(
                &tensor_ty(&i32t, 2),
                1,
                false,
                vec![E::Param(0), E::SrcExtent(0), E::Coord(1)],
                &[0, 1],
                &[2],
            ),
            want: TensorWant::Ok(tensor_val(&i32t, &[2, 0], &[])),
        },
        RegionRun {
            name: "view_out_of_range_without_a_fill",
            args: vec![tensor_arg(&i32t, &[3], &[1, 2, 3])],
            result: tensor_ty(&i32t, 1),
            inst: view_inst(
                &tensor_ty(&i32t, 1),
                0,
                false,
                vec![E::SrcExtent(0), E::Lit(1), E::Add(0, 1), E::Coord(0)],
                &[2],
                &[3],
            ),
            want: TensorWant::Ub(TENSOR_VIEW_OUT_OF_RANGE),
        },
        RegionRun {
            name: "view_index_expression_overflows",
            args: vec![tensor_arg(&i32t, &[3], &[1, 2, 3])],
            result: tensor_ty(&i32t, 1),
            inst: view_inst(
                &tensor_ty(&i32t, 1),
                0,
                false,
                vec![E::Coord(0), E::Lit(u64::MAX), E::Mul(1, 1), E::Lit(1)],
                &[3],
                &[0],
            ),
            want: TensorWant::Ub(TENSOR_VIEW_OVERFLOWS),
        },
        RegionRun {
            name: "view_index_expression_divides_by_zero",
            args: vec![tensor_arg(&i32t, &[3], &[1, 2, 3])],
            result: tensor_ty(&i32t, 1),
            inst: view_inst(
                &tensor_ty(&i32t, 1),
                0,
                false,
                vec![E::Coord(0), E::Lit(1), E::Lit(0), E::Rem(1, 2)],
                &[1],
                &[0],
            ),
            want: TensorWant::Ub(TENSOR_VIEW_DIVIDES_BY_ZERO),
        },
        RegionRun {
            name: "view_negative_extent",
            args: vec![tensor_arg(&i32t, &[3], &[1, 2, 3])],
            result: tensor_ty(&i32t, 1),
            inst: view_inst(
                &tensor_ty(&i32t, 1),
                0,
                false,
                vec![E::Coord(0), E::Lit(0), E::Lit(1), E::Sub(1, 2)],
                &[3],
                &[0],
            ),
            want: TensorWant::Ub(TENSOR_VIEW_EXTENT),
        },
        RegionRun {
            name: "view_extent_past_usize",
            args: vec![tensor_arg(&i32t, &[3], &[1, 2, 3])],
            result: tensor_ty(&i32t, 1),
            inst: view_inst(
                &tensor_ty(&i32t, 1),
                0,
                false,
                vec![E::Coord(0), E::Lit(u64::MAX), E::Lit(1), E::Add(1, 2)],
                &[3],
                &[0],
            ),
            want: TensorWant::Ub(TENSOR_VIEW_EXTENT),
        },
        RegionRun {
            name: "view_count_past_usize",
            args: vec![tensor_arg(&i32t, &[3], &[1, 2, 3])],
            result: tensor_ty(&i32t, 2),
            inst: view_inst(
                &tensor_ty(&i32t, 2),
                0,
                false,
                vec![E::Lit(if wasm { 1 << 16 } else { 1 << 32 }), E::Coord(1)],
                &[0, 0],
                &[1],
            ),
            want: TensorWant::Ub(TENSOR_VIEW_TOO_LARGE),
        },
        RegionRun {
            name: "view_shape_reads_a_coordinate",
            args: vec![tensor_arg(&i32t, &[3], &[1, 2, 3])],
            result: tensor_ty(&i32t, 1),
            inst: view_inst(
                &tensor_ty(&i32t, 1),
                0,
                false,
                vec![E::Coord(0), E::Lit(1), E::Add(0, 1)],
                &[2],
                &[0],
            ),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "view_fill_of_another_type",
            args: vec![tensor_arg(&i32t, &[3], &[1, 2, 3]), scalar_arg(&i64t, 0)],
            result: tensor_ty(&i32t, 1),
            inst: view_inst(
                &tensor_ty(&i32t, 1),
                0,
                true,
                vec![E::SrcExtent(0), E::Coord(0)],
                &[0],
                &[1],
            ),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "view_parameter_not_usize",
            args: vec![tensor_arg(&i32t, &[3], &[1, 2, 3]), scalar_arg(&u32t, 1)],
            result: tensor_ty(&i32t, 1),
            inst: view_inst(
                &tensor_ty(&i32t, 1),
                1,
                false,
                vec![E::Param(0), E::Coord(0)],
                &[0],
                &[1],
            ),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "view_index_count_wrong",
            args: vec![x23()],
            result: tensor_ty(&i32t, 1),
            inst: view_inst(
                &tensor_ty(&i32t, 1),
                0,
                false,
                vec![E::SrcExtent(0), E::Coord(0)],
                &[0],
                &[1],
            ),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "view_element_differs",
            args: vec![x23()],
            result: tensor_ty(&i64t, 1),
            inst: view_inst(
                &tensor_ty(&i64t, 1),
                0,
                false,
                vec![E::Lit(1), E::Coord(0)],
                &[0],
                &[1, 1],
            ),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "view_node_reads_itself",
            args: vec![x23()],
            result: tensor_ty(&i32t, 2),
            inst: view_inst(
                &tensor_ty(&i32t, 2),
                0,
                false,
                vec![E::SrcExtent(0), E::SrcExtent(1), E::Coord(0), E::Add(3, 2)],
                &[0, 1],
                &[3, 2],
            ),
            want: TensorWant::TypeError,
        },
        // ---- map rules M1-M3 ----
        RegionRun {
            name: "map_result_is_not_a_tensor",
            args: vec![x23()],
            result: i32t.clone(),
            inst: map_inst(
                &i32t,
                1,
                vec![N::UnOp {
                    op: UnOp::Neg,
                    ty: i32t.clone(),
                    operand: 0,
                }],
            ),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "map_no_operand_is_a_tensor",
            args: vec![scalar_arg(&i32t, 1)],
            result: tensor_ty(&i32t, 0),
            inst: map_inst(
                &tensor_ty(&i32t, 0),
                1,
                vec![N::UnOp {
                    op: UnOp::Neg,
                    ty: i32t.clone(),
                    operand: 0,
                }],
            ),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "map_body_is_empty",
            args: vec![x23()],
            result: tensor_ty(&i32t, 2),
            inst: map_inst(&tensor_ty(&i32t, 2), 1, vec![]),
            want: TensorWant::TypeError,
        },
    ];
    // A pointer-width map wraps at the target's width.
    let half: i128 = if wasm { 1 << 31 } else { 1 << 63 };
    runs.push(RegionRun {
        name: "map_usize_wraps_at_the_target_width",
        args: vec![tensor_arg(&usizet, &[2], &[half, 3])],
        result: tensor_ty(&usizet, 1),
        inst: map_inst(&tensor_ty(&usizet, 1), 1, vec![add(&usizet, 0, 0)]),
        want: TensorWant::Ok(tensor_val(&usizet, &[2], &[0, 6])),
    });
    // M4's cast widths read `usize` at the target's width: a `bitcast` to
    // `u64` keeps the width on a 64-bit target and changes it on wasm32.
    runs.push(RegionRun {
        name: "map_usize_bitcast_reads_the_target_width",
        args: vec![tensor_arg(&usizet, &[1], &[7])],
        result: tensor_ty(&Ty::U64, 1),
        inst: map_inst(
            &tensor_ty(&Ty::U64, 1),
            1,
            vec![N::Cast {
                op: CastOp::Bitcast,
                src_ty: usizet.clone(),
                dst_ty: Ty::U64,
                operand: 0,
            }],
        ),
        want: if wasm {
            TensorWant::TypeError
        } else {
            TensorWant::Ok(tensor_val(&Ty::U64, &[1], &[7]))
        },
    });
    let mut fns = Vec::new();
    let mut args = Vec::new();
    let mut wants = Vec::new();
    for run in runs {
        let params: Vec<Ty> = run.args.iter().map(|a| a.ty.clone()).collect();
        let mut b = MemBody::new(&params);
        let r = b.val(run.inst);
        fns.push((run.name, params, vec![run.result], b.ret(vec![r])));
        args.push(run.args);
        wants.push(run.want);
    }
    let mut module = mem_module("semr_tensor_map_reduce_view", fns);
    let label = match &target {
        Some(t) => format!("tensor map/reduce/view {}", t.pointer_size * 8),
        None => "tensor map/reduce/view reference".to_string(),
    };
    module.target_info = target;
    let runs = module.functions.iter().map(|f| f.id).zip(args).collect();
    (
        SemrCase {
            label,
            module,
            runs,
        },
        wants,
    )
}

/// SemR's `TensorMap`, `TensorReduce` and `TensorView` agree with the
/// reference interpreter on every hand-written run, at the reference layout
/// and on wasm32, and both reach the verdict written in
/// `semr_tensor_region_case` (a computed tensor, the exact
/// undefined-behaviour text, or a type error).
#[test]
fn semr_tensor_map_reduce_view_agrees_with_the_interpreter() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    for target in [None, Some(semr_target(32))] {
        let (case, wants) = semr_tensor_region_case(target);
        let reports = semr_differential(exe, &[case.batch()]);
        assert_eq!(reports.len(), wants.len(), "{}", case.label);
        for (report, want) in reports.iter().zip(&wants) {
            let name = &case.module.functions[report.func.0 as usize].name;
            let what = format!("{}/{name}", case.label);
            match want {
                TensorWant::Ok(v) => {
                    assert_eq!(
                        report.rust,
                        Verdict::Ok(vec![v.clone()]),
                        "interpreter {what}"
                    );
                    assert_eq!(report.lean, Verdict::Ok(vec![v.clone()]), "SemR {what}");
                }
                TensorWant::Ub(m) => {
                    assert_eq!(report.rust, Verdict::Ub((*m).into()), "interpreter {what}");
                    assert_eq!(report.lean, Verdict::Ub((*m).into()), "SemR {what}");
                }
                TensorWant::TypeError => {
                    assert!(
                        matches!(report.rust, Verdict::TypeError(_)),
                        "interpreter {what}: {report:?}"
                    );
                    assert!(
                        matches!(report.lean, Verdict::TypeError(_)),
                        "SemR {what}: {report:?}"
                    );
                }
            }
            assert_eq!(report.comparison, Comparison::Agree, "{what}");
        }
    }
}

/// A small module spelling every v68 wire shape once: a map through all five
/// node kinds, a reduction, and a view through every index-expression kind
/// with a parameter and a fill.
fn tensor_region_wire_module(target: Option<trust_ir::TargetInfo>) -> Module {
    use trust_ir::{BinOp, CastOp, ICmpOp, TensorIndexExpr as E, TensorMapNode as N, UnOp};
    let map = {
        let params = vec![tensor_ty(&Ty::I8, 1), Ty::I32];
        let mut b = MemBody::new(&params);
        let r = b.val(map_inst(
            &tensor_ty(&Ty::I32, 1),
            2,
            vec![
                N::Cast {
                    op: CastOp::SExt,
                    src_ty: Ty::I8,
                    dst_ty: Ty::I32,
                    operand: 0,
                },
                N::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I32,
                    lhs: 2,
                    rhs: 1,
                },
                N::UnOp {
                    op: UnOp::Neg,
                    ty: Ty::I32,
                    operand: 3,
                },
                N::ICmp {
                    op: ICmpOp::Slt,
                    ty: Ty::I32,
                    lhs: 4,
                    rhs: 1,
                },
                N::Select {
                    ty: Ty::I32,
                    cond: 5,
                    then_lane: 4,
                    else_lane: 3,
                },
            ],
        ));
        (
            "map_every_node",
            params,
            vec![tensor_ty(&Ty::I32, 1)],
            b.ret(vec![r]),
        )
    };
    let reduce = {
        let params = vec![tensor_ty(&Ty::I32, 2)];
        let mut b = MemBody::new(&params);
        let r = b.val(reduce_inst(
            &tensor_ty(&Ty::I32, 1),
            trust_ir::TensorReduceOp::SMax,
            &[1],
        ));
        (
            "reduce_smax",
            params,
            vec![tensor_ty(&Ty::I32, 1)],
            b.ret(vec![r]),
        )
    };
    let view = {
        let params = vec![tensor_ty(&Ty::I32, 1), Ty::Usize, Ty::I32];
        let mut b = MemBody::new(&params);
        let r = b.val(view_inst(
            &tensor_ty(&Ty::I32, 1),
            1,
            true,
            vec![
                E::Param(0),
                E::SrcExtent(0),
                E::Coord(0),
                E::Add(2, 0),
                E::Sub(3, 0),
                E::Mul(2, 0),
                E::Div(5, 0),
                E::Rem(4, 1),
                E::Min(7, 1),
                E::Max(8, 6),
                E::Lit(4),
                E::Min(10, 1),
            ],
            &[11],
            &[9],
        ));
        (
            "view_every_expr",
            params,
            vec![tensor_ty(&Ty::I32, 1)],
            b.ret(vec![r]),
        )
    };
    let mut module = mem_module("semr_tensor_region_wire", vec![map, reduce, view]);
    module.target_info = target;
    module
}

/// The v68 wire boundary in SemR's decoder: a map/reduce/view module is
/// written at exactly `TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION`, validates, and
/// decodes in SemR to the module the Rust reader reads; the same bytes under
/// the version before are malformed in both (Inst tags 72-74 are read-gated).
#[test]
fn semr_tensor_map_reduce_view_wire_boundary_is_explicit() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let module = tensor_region_wire_module(None);
    let errors = trust_ir_build::validate::validate_module(&module);
    assert!(
        errors.is_empty(),
        "the wire module is well-formed: {errors:?}"
    );
    let blob = trust_ir::binary::serialize_module(&module).expect("v68 wire");
    let v68 = trust_ir::binary::TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION;
    assert_eq!(header_version(&blob), v68);
    assert_eq!(trust_ir::binary::deserialize_module(&blob).unwrap(), module);
    let old = relabelled(&blob, v68 - 1);
    assert!(trust_ir::binary::deserialize_module(&old).is_err());
    let verdicts = semr_decode(exe, &[blob, old]);
    assert_eq!(verdicts[0]["decoded"], semr_summary_of(&module));
    assert_eq!(verdicts[1], json!({"error": "decode: invalid Inst tag"}));
}

// ---------------------------------------------------------------------------
// v69 (PKG-U13d): the tensor gather and scatter (SPEC_RATIFICATIONS §26). As
// for the map, reduction and view, every operand is an entry argument, so
// each run is one instruction over its parameters, returned.
// ---------------------------------------------------------------------------

const TENSOR_GATHER_EXTENTS_DIFFER: &str =
    "tensor gather: coordinate tensors have different extents";
const TENSOR_GATHER_OUTSIDE: &str = "tensor gather: a coordinate is outside its axis";
const TENSOR_SCATTER_EXTENTS_DIFFER: &str =
    "tensor scatter: coordinate tensor extents differ from the source's";
const TENSOR_SCATTER_OUTSIDE: &str = "tensor scatter: a coordinate is outside its axis";

/// `tensor_gather result %0 coords [%1 ..= %coords]`.
fn gather_inst(result: &Ty, coords: u32) -> trust_ir::Inst {
    trust_ir::Inst::TensorGather {
        ty: result.clone(),
        data: vid(0),
        coords: (1..=coords).map(vid).collect(),
    }
}

/// `tensor_scatter result %0, %1 coords [%2 .. %{coords + 2})`.
fn scatter_inst(result: &Ty, coords: u32) -> trust_ir::Inst {
    trust_ir::Inst::TensorScatter {
        ty: result.clone(),
        init: vid(0),
        src: vid(1),
        coords: (2..coords + 2).map(vid).collect(),
    }
}

/// The hand-written gather and scatter runs, on the 64-bit reference layout
/// (`target` `None`) or a 32-bit target: gathers of rank-1, -2 and -3 data
/// and scatters into rank-1, -2 and -3 tensors, at coordinate tensors of rank
/// 0, 1 and 2 whose elements are `i8`, `u8`, `i16`, `i32`, `i64`, `u64`,
/// `i128`, `isize` and `usize` (one instruction's coordinate tensors of
/// different types), repeated gather coordinates and repeated scatter
/// coordinates (the row-major-last write wins), empty coordinate tensors and
/// zero extents, 8- to 128-bit and pointer-width elements; every
/// undefined-behaviour text of the two (each extents mismatch, a coordinate
/// at its extent, a negative signed coordinate, among them `i8` -128 whose
/// residue lies inside the axis, a pointer-width coordinate at the target's
/// maximum, a coordinate past a zero extent, the extents precondition ahead
/// of the bounds precondition and the bounds precondition ahead of any
/// write); a poison operand of each kind, ahead of every static rule; and a
/// type error for each static rule (G1-G3, S1-S3: a wrong
/// coordinate count, rank-0 data or result, a wrong coordinate rank, a
/// scalar coordinate, an element or `init` type that is not the result's)
/// and for an ill-formed operand, each ahead of the preconditions. Every
/// run's verdict is written here, not computed.
fn semr_tensor_gather_scatter_case(
    target: Option<trust_ir::TargetInfo>,
) -> (SemrCase, Vec<TensorWant>) {
    let (i8t, i16t, i32t, i64t, i128t) = (Ty::I8, Ty::I16, Ty::I32, Ty::I64, Ty::I128);
    let (u8t, u16t, u32t, u64t, u128t) = (Ty::U8, Ty::U16, Ty::U32, Ty::U64, Ty::U128);
    let (isizet, usizet) = (Ty::Isize, Ty::Usize);
    let wasm = target.as_ref().is_some_and(|t| t.pointer_size == 4);
    // The target's pointer width, and the residue of `-n` at `bits`.
    let w: u32 = if wasm { 32 } else { 64 };
    let neg = |bits: u32, n: u128| 0u128.wrapping_sub(n) & (u128::MAX >> (128 - bits));
    let usize_max = (1i128 << w) - 1;
    let iota = |n: i128| (0..n).collect::<Vec<i128>>();
    let mut at_128 = vec![0u128; 130];
    at_128[128] = 9;
    let runs = vec![
        // ---- gather: results ----
        RegionRun {
            name: "gather_rank1_by_u8_with_repeats",
            args: vec![
                tensor_arg(&i32t, &[5], &[10, -20, 30, -40, 50]),
                tensor_arg(&u8t, &[6], &[4, 0, 0, 3, 1, 4]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::Ok(tensor_val(
                &i32t,
                &[6],
                &[50, 10, 10, neg(32, 40), neg(32, 20), 50],
            )),
        },
        RegionRun {
            name: "gather_rank2_by_two_coordinate_types",
            args: vec![
                tensor_arg(&i32t, &[2, 2], &[1, 2, 3, 4]),
                tensor_arg(&u8t, &[2], &[1, 0]),
                tensor_arg(&i64t, &[2], &[0, 1]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 2),
            want: TensorWant::Ok(tensor_val(&i32t, &[2], &[3, 2])),
        },
        RegionRun {
            name: "gather_rank3_by_rank2_coordinates",
            args: vec![
                tensor_arg(&u16t, &[2, 3, 4], &(100..124).collect::<Vec<i128>>()),
                tensor_arg(&i32t, &[2, 2], &[1, 0, 1, 1]),
                tensor_arg(&u64t, &[2, 2], &[2, 0, 1, 2]),
                tensor_arg(&usizet, &[2, 2], &[3, 0, 2, 3]),
            ],
            result: tensor_ty(&u16t, 2),
            inst: gather_inst(&tensor_ty(&u16t, 2), 3),
            want: TensorWant::Ok(tensor_val(&u16t, &[2, 2], &[123, 100, 118, 123])),
        },
        RegionRun {
            name: "gather_at_a_rank0_coordinate",
            args: vec![
                tensor_arg(&i64t, &[3], &[7, -8, 9]),
                tensor_arg(&isizet, &[], &[1]),
            ],
            result: tensor_ty(&i64t, 0),
            inst: gather_inst(&tensor_ty(&i64t, 0), 1),
            want: TensorWant::Ok(tensor_val(&i64t, &[], &[neg(64, 8)])),
        },
        RegionRun {
            name: "gather_rank2_data_at_rank0_coordinates",
            args: vec![
                tensor_arg(&u8t, &[2, 3], &[1, 2, 3, 4, 5, 6]),
                tensor_arg(&i8t, &[], &[1]),
                tensor_arg(&u32t, &[], &[2]),
            ],
            result: tensor_ty(&u8t, 0),
            inst: gather_inst(&tensor_ty(&u8t, 0), 2),
            want: TensorWant::Ok(tensor_val(&u8t, &[], &[6])),
        },
        RegionRun {
            name: "gather_i128_elements",
            args: vec![
                tensor_arg(&i128t, &[2], &[i128::MIN, i128::MAX]),
                tensor_arg(&i16t, &[3], &[1, 0, 1]),
            ],
            result: tensor_ty(&i128t, 1),
            inst: gather_inst(&tensor_ty(&i128t, 1), 1),
            want: TensorWant::Ok(tensor_val(
                &i128t,
                &[3],
                &[i128::MAX as u128, 1u128 << 127, i128::MAX as u128],
            )),
        },
        RegionRun {
            name: "gather_u64_elements_at_usize_coordinates",
            args: vec![
                tensor_arg(&u64t, &[2], &[i128::from(u64::MAX), 0]),
                tensor_arg(&usizet, &[3], &[0, 1, 0]),
            ],
            result: tensor_ty(&u64t, 1),
            inst: gather_inst(&tensor_ty(&u64t, 1), 1),
            want: TensorWant::Ok(tensor_val(
                &u64t,
                &[3],
                &[u128::from(u64::MAX), 0, u128::from(u64::MAX)],
            )),
        },
        RegionRun {
            name: "gather_pointer_width_elements",
            args: vec![
                tensor_arg(&isizet, &[2], &[-1, 5]),
                tensor_arg(&u8t, &[3], &[1, 0, 0]),
            ],
            result: tensor_ty(&isizet, 1),
            inst: gather_inst(&tensor_ty(&isizet, 1), 1),
            want: TensorWant::Ok(tensor_val(&isizet, &[3], &[5, neg(w, 1), neg(w, 1)])),
        },
        RegionRun {
            name: "gather_unsigned_coordinate_128",
            args: vec![
                tensor_arg(&u8t, &[130], &iota(130)),
                tensor_arg(&u8t, &[1], &[128]),
            ],
            result: tensor_ty(&u8t, 1),
            inst: gather_inst(&tensor_ty(&u8t, 1), 1),
            want: TensorWant::Ok(tensor_val(&u8t, &[1], &[128])),
        },
        RegionRun {
            name: "gather_at_empty_coordinates",
            args: vec![
                tensor_arg(&i32t, &[3], &[1, 2, 3]),
                tensor_arg(&u64t, &[0], &[]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::Ok(tensor_val(&i32t, &[0], &[])),
        },
        RegionRun {
            name: "gather_at_empty_rank2_coordinates",
            args: vec![
                tensor_arg(&i32t, &[2, 2], &[1, 2, 3, 4]),
                tensor_arg(&usizet, &[2, 0], &[]),
                tensor_arg(&i8t, &[2, 0], &[]),
            ],
            result: tensor_ty(&i32t, 2),
            inst: gather_inst(&tensor_ty(&i32t, 2), 2),
            want: TensorWant::Ok(tensor_val(&i32t, &[2, 0], &[])),
        },
        RegionRun {
            name: "gather_from_a_zero_extent_at_no_coordinate",
            args: vec![
                tensor_arg(&u8t, &[3, 0], &[]),
                tensor_arg(&u8t, &[0], &[]),
                tensor_arg(&i64t, &[0], &[]),
            ],
            result: tensor_ty(&u8t, 1),
            inst: gather_inst(&tensor_ty(&u8t, 1), 2),
            want: TensorWant::Ok(tensor_val(&u8t, &[0], &[])),
        },
        // ---- gather: undefined behaviour ----
        RegionRun {
            name: "gather_coordinate_counts_differ",
            args: vec![
                tensor_arg(&i32t, &[2, 2], &[1, 2, 3, 4]),
                tensor_arg(&u8t, &[2], &[0, 1]),
                tensor_arg(&u8t, &[3], &[0, 1, 1]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 2),
            want: TensorWant::Ub(TENSOR_GATHER_EXTENTS_DIFFER),
        },
        RegionRun {
            name: "gather_coordinate_shapes_differ_at_one_count",
            args: vec![
                tensor_arg(&i32t, &[2, 2], &[1, 2, 3, 4]),
                tensor_arg(&u8t, &[2, 3], &[0; 6]),
                tensor_arg(&i32t, &[3, 2], &[0; 6]),
            ],
            result: tensor_ty(&i32t, 2),
            inst: gather_inst(&tensor_ty(&i32t, 2), 2),
            want: TensorWant::Ub(TENSOR_GATHER_EXTENTS_DIFFER),
        },
        RegionRun {
            name: "gather_extents_before_bounds",
            args: vec![
                tensor_arg(&i32t, &[2, 2], &[1, 2, 3, 4]),
                tensor_arg(&u8t, &[2], &[9, 9]),
                tensor_arg(&u8t, &[1], &[9]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 2),
            want: TensorWant::Ub(TENSOR_GATHER_EXTENTS_DIFFER),
        },
        RegionRun {
            name: "gather_coordinate_at_the_extent",
            args: vec![
                tensor_arg(&i32t, &[3], &[1, 2, 3]),
                tensor_arg(&u32t, &[2], &[0, 3]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::Ub(TENSOR_GATHER_OUTSIDE),
        },
        RegionRun {
            name: "gather_negative_i32_coordinate",
            args: vec![
                tensor_arg(&i32t, &[3], &[1, 2, 3]),
                tensor_arg(&i32t, &[2], &[2, -1]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::Ub(TENSOR_GATHER_OUTSIDE),
        },
        RegionRun {
            name: "gather_negative_i8_coordinate_inside_by_residue",
            args: vec![
                tensor_arg(&u8t, &[130], &iota(130)),
                tensor_arg(&i8t, &[1], &[-128]),
            ],
            result: tensor_ty(&u8t, 1),
            inst: gather_inst(&tensor_ty(&u8t, 1), 1),
            want: TensorWant::Ub(TENSOR_GATHER_OUTSIDE),
        },
        RegionRun {
            name: "gather_negative_isize_coordinate",
            args: vec![
                tensor_arg(&i32t, &[3], &[1, 2, 3]),
                tensor_arg(&isizet, &[1], &[-1]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::Ub(TENSOR_GATHER_OUTSIDE),
        },
        RegionRun {
            name: "gather_negative_i128_coordinate",
            args: vec![
                tensor_arg(&i32t, &[3], &[1, 2, 3]),
                tensor_arg(&i128t, &[1], &[i128::MIN]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::Ub(TENSOR_GATHER_OUTSIDE),
        },
        RegionRun {
            name: "gather_u64_coordinate_far_past_the_extent",
            args: vec![
                tensor_arg(&i32t, &[3], &[1, 2, 3]),
                tensor_arg(&u64t, &[1], &[i128::from(u64::MAX)]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::Ub(TENSOR_GATHER_OUTSIDE),
        },
        RegionRun {
            name: "gather_usize_coordinate_at_the_target_maximum",
            args: vec![
                tensor_arg(&i32t, &[3], &[1, 2, 3]),
                tensor_arg(&usizet, &[1], &[usize_max]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::Ub(TENSOR_GATHER_OUTSIDE),
        },
        RegionRun {
            name: "gather_coordinate_past_a_zero_extent",
            args: vec![tensor_arg(&u8t, &[0], &[]), tensor_arg(&u8t, &[1], &[0])],
            result: tensor_ty(&u8t, 1),
            inst: gather_inst(&tensor_ty(&u8t, 1), 1),
            want: TensorWant::Ub(TENSOR_GATHER_OUTSIDE),
        },
        RegionRun {
            name: "gather_second_axis_outside",
            args: vec![
                tensor_arg(&i32t, &[2, 3], &[1, 2, 3, 4, 5, 6]),
                tensor_arg(&u8t, &[1], &[1]),
                tensor_arg(&u8t, &[1], &[3]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 2),
            want: TensorWant::Ub(TENSOR_GATHER_OUTSIDE),
        },
        // ---- gather: type errors (G1-G3, then well-formedness) ----
        RegionRun {
            name: "gather_too_few_coordinates",
            args: vec![
                tensor_arg(&i32t, &[2, 2], &[1, 2, 3, 4]),
                tensor_arg(&u8t, &[1], &[0]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "gather_too_many_coordinates",
            args: vec![
                tensor_arg(&i32t, &[3], &[1, 2, 3]),
                tensor_arg(&u8t, &[1], &[0]),
                tensor_arg(&u8t, &[1], &[0]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 2),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "gather_rank0_data_has_no_axis",
            args: vec![tensor_arg(&i32t, &[], &[5])],
            result: tensor_ty(&i32t, 0),
            inst: gather_inst(&tensor_ty(&i32t, 0), 0),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "gather_rank0_data_at_a_coordinate",
            args: vec![tensor_arg(&i32t, &[], &[5]), tensor_arg(&u8t, &[], &[0])],
            result: tensor_ty(&i32t, 0),
            inst: gather_inst(&tensor_ty(&i32t, 0), 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "gather_coordinate_of_another_rank",
            args: vec![
                tensor_arg(&i32t, &[3], &[1, 2, 3]),
                tensor_arg(&u8t, &[1, 1], &[0]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "gather_scalar_coordinate",
            args: vec![tensor_arg(&i32t, &[3], &[1, 2, 3]), scalar_arg(&u8t, 0)],
            result: tensor_ty(&i32t, 0),
            inst: gather_inst(&tensor_ty(&i32t, 0), 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "gather_element_differs",
            args: vec![
                tensor_arg(&i32t, &[3], &[1, 2, 3]),
                tensor_arg(&u8t, &[1], &[0]),
            ],
            result: tensor_ty(&u32t, 1),
            inst: gather_inst(&tensor_ty(&u32t, 1), 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "gather_result_not_a_tensor",
            args: vec![
                tensor_arg(&i32t, &[3], &[1, 2, 3]),
                tensor_arg(&u8t, &[], &[0]),
            ],
            result: i32t.clone(),
            inst: gather_inst(&i32t, 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "gather_data_not_a_tensor",
            args: vec![scalar_arg(&i32t, 1), tensor_arg(&u8t, &[1], &[0])],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "gather_ill_formed_data",
            args: vec![
                tensor_arg(&i32t, &[2, 2], &[1, 2, 3]),
                tensor_arg(&u8t, &[1], &[0]),
                tensor_arg(&u8t, &[1], &[0]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 2),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "gather_ill_formed_coordinate_before_its_bounds",
            args: vec![
                tensor_arg(&i32t, &[3], &[1, 2, 3]),
                tensor_arg(&u8t, &[2], &[7, 7, 7]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "gather_static_rule_before_the_extents_precondition",
            args: vec![
                tensor_arg(&i32t, &[2, 2], &[1, 2, 3, 4]),
                tensor_arg(&u8t, &[2], &[0, 0]),
                tensor_arg(&u8t, &[2, 1], &[0, 0]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: gather_inst(&tensor_ty(&i32t, 1), 2),
            want: TensorWant::TypeError,
        },
        // ---- scatter: results ----
        RegionRun {
            name: "scatter_rank1_at_distinct_coordinates",
            args: vec![
                tensor_arg(&i32t, &[4], &[0, 0, 0, 0]),
                tensor_arg(&i32t, &[2], &[7, -9]),
                tensor_arg(&u8t, &[2], &[3, 1]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::Ok(tensor_val(&i32t, &[4], &[0, neg(32, 9), 0, 7])),
        },
        RegionRun {
            name: "scatter_repeated_coordinate_keeps_the_row_major_last_write",
            args: vec![
                tensor_arg(&u8t, &[3], &[1, 2, 3]),
                tensor_arg(&u8t, &[4], &[10, 20, 30, 40]),
                tensor_arg(&i32t, &[4], &[1, 0, 1, 1]),
            ],
            result: tensor_ty(&u8t, 1),
            inst: scatter_inst(&tensor_ty(&u8t, 1), 1),
            want: TensorWant::Ok(tensor_val(&u8t, &[3], &[20, 40, 3])),
        },
        RegionRun {
            name: "scatter_rank2_init_from_a_rank1_source",
            args: vec![
                tensor_arg(&i64t, &[2, 3], &[1, 2, 3, 4, 5, 6]),
                tensor_arg(&i64t, &[3], &[-1, -2, -3]),
                tensor_arg(&usizet, &[3], &[1, 0, 1]),
                tensor_arg(&i8t, &[3], &[2, 0, 2]),
            ],
            result: tensor_ty(&i64t, 2),
            inst: scatter_inst(&tensor_ty(&i64t, 2), 2),
            want: TensorWant::Ok(tensor_val(
                &i64t,
                &[2, 3],
                &[neg(64, 2), 2, 3, 4, 5, neg(64, 3)],
            )),
        },
        RegionRun {
            name: "scatter_rank3_init_from_a_rank2_source",
            args: vec![
                tensor_arg(&u32t, &[2, 2, 2], &iota(8)),
                tensor_arg(&u32t, &[2, 2], &[100, 200, 300, 400]),
                tensor_arg(&u64t, &[2, 2], &[1, 0, 1, 1]),
                tensor_arg(&isizet, &[2, 2], &[1, 1, 0, 1]),
                tensor_arg(&u8t, &[2, 2], &[0, 1, 1, 0]),
            ],
            result: tensor_ty(&u32t, 3),
            inst: scatter_inst(&tensor_ty(&u32t, 3), 3),
            want: TensorWant::Ok(tensor_val(
                &u32t,
                &[2, 2, 2],
                &[0, 1, 2, 200, 4, 300, 400, 7],
            )),
        },
        RegionRun {
            name: "scatter_rank0_source_writes_once",
            args: vec![
                tensor_arg(&i16t, &[3], &[5, 6, 7]),
                tensor_arg(&i16t, &[], &[-1]),
                tensor_arg(&u32t, &[], &[2]),
            ],
            result: tensor_ty(&i16t, 1),
            inst: scatter_inst(&tensor_ty(&i16t, 1), 1),
            want: TensorWant::Ok(tensor_val(&i16t, &[3], &[5, 6, neg(16, 1)])),
        },
        RegionRun {
            name: "scatter_empty_source_leaves_init",
            args: vec![
                tensor_arg(&i32t, &[2], &[1, 2]),
                tensor_arg(&i32t, &[0], &[]),
                tensor_arg(&i64t, &[0], &[]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::Ok(tensor_val(&i32t, &[2], &[1, 2])),
        },
        RegionRun {
            name: "scatter_into_an_empty_init",
            args: vec![
                tensor_arg(&u8t, &[0], &[]),
                tensor_arg(&u8t, &[0], &[]),
                tensor_arg(&usizet, &[0], &[]),
            ],
            result: tensor_ty(&u8t, 1),
            inst: scatter_inst(&tensor_ty(&u8t, 1), 1),
            want: TensorWant::Ok(tensor_val(&u8t, &[0], &[])),
        },
        RegionRun {
            name: "scatter_into_a_zero_extent_from_an_empty_rank2_source",
            args: vec![
                tensor_arg(&i32t, &[2, 0], &[]),
                tensor_arg(&i32t, &[0, 3], &[]),
                tensor_arg(&u8t, &[0, 3], &[]),
                tensor_arg(&i8t, &[0, 3], &[]),
            ],
            result: tensor_ty(&i32t, 2),
            inst: scatter_inst(&tensor_ty(&i32t, 2), 2),
            want: TensorWant::Ok(tensor_val(&i32t, &[2, 0], &[])),
        },
        RegionRun {
            name: "scatter_u128_elements",
            args: vec![
                tensor_arg(&u128t, &[2], &[0, 0]),
                tensor_arg(&u128t, &[2], &[-1, 1 << 100]),
                tensor_arg(&u64t, &[2], &[1, 0]),
            ],
            result: tensor_ty(&u128t, 1),
            inst: scatter_inst(&tensor_ty(&u128t, 1), 1),
            want: TensorWant::Ok(tensor_val(&u128t, &[2], &[1u128 << 100, u128::MAX])),
        },
        RegionRun {
            name: "scatter_pointer_width_elements",
            args: vec![
                tensor_arg(&isizet, &[2], &[3, 4]),
                tensor_arg(&isizet, &[1], &[-5]),
                tensor_arg(&i8t, &[1], &[1]),
            ],
            result: tensor_ty(&isizet, 1),
            inst: scatter_inst(&tensor_ty(&isizet, 1), 1),
            want: TensorWant::Ok(tensor_val(&isizet, &[2], &[3, neg(w, 5)])),
        },
        RegionRun {
            name: "scatter_unsigned_coordinate_128",
            args: vec![
                tensor_arg(&u8t, &[130], &[0; 130]),
                tensor_arg(&u8t, &[1], &[9]),
                tensor_arg(&u8t, &[1], &[128]),
            ],
            result: tensor_ty(&u8t, 1),
            inst: scatter_inst(&tensor_ty(&u8t, 1), 1),
            want: TensorWant::Ok(tensor_val(&u8t, &[130], &at_128)),
        },
        // ---- scatter: undefined behaviour ----
        RegionRun {
            name: "scatter_coordinate_count_differs_from_the_source",
            args: vec![
                tensor_arg(&i32t, &[3], &[0, 0, 0]),
                tensor_arg(&i32t, &[2], &[1, 2]),
                tensor_arg(&u8t, &[3], &[0, 1, 2]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::Ub(TENSOR_SCATTER_EXTENTS_DIFFER),
        },
        RegionRun {
            name: "scatter_second_coordinate_extents_differ",
            args: vec![
                tensor_arg(&i32t, &[2, 2], &[0; 4]),
                tensor_arg(&i32t, &[2], &[1, 2]),
                tensor_arg(&u8t, &[2], &[0, 1]),
                tensor_arg(&u8t, &[1], &[0]),
            ],
            result: tensor_ty(&i32t, 2),
            inst: scatter_inst(&tensor_ty(&i32t, 2), 2),
            want: TensorWant::Ub(TENSOR_SCATTER_EXTENTS_DIFFER),
        },
        RegionRun {
            name: "scatter_coordinate_shape_differs_at_one_count",
            args: vec![
                tensor_arg(&i32t, &[6], &[0; 6]),
                tensor_arg(&i32t, &[2, 3], &[1, 2, 3, 4, 5, 6]),
                tensor_arg(&u8t, &[3, 2], &[0; 6]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::Ub(TENSOR_SCATTER_EXTENTS_DIFFER),
        },
        RegionRun {
            name: "scatter_extents_before_bounds",
            args: vec![
                tensor_arg(&i32t, &[3], &[0, 0, 0]),
                tensor_arg(&i32t, &[2], &[1, 2]),
                tensor_arg(&u8t, &[1], &[9]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::Ub(TENSOR_SCATTER_EXTENTS_DIFFER),
        },
        RegionRun {
            name: "scatter_coordinate_at_the_extent",
            args: vec![
                tensor_arg(&u8t, &[3], &[0, 0, 0]),
                tensor_arg(&u8t, &[1], &[7]),
                tensor_arg(&u32t, &[1], &[3]),
            ],
            result: tensor_ty(&u8t, 1),
            inst: scatter_inst(&tensor_ty(&u8t, 1), 1),
            want: TensorWant::Ub(TENSOR_SCATTER_OUTSIDE),
        },
        RegionRun {
            name: "scatter_negative_i64_coordinate",
            args: vec![
                tensor_arg(&i32t, &[3], &[0, 0, 0]),
                tensor_arg(&i32t, &[1], &[7]),
                tensor_arg(&i64t, &[1], &[-1]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::Ub(TENSOR_SCATTER_OUTSIDE),
        },
        RegionRun {
            name: "scatter_negative_i8_coordinate_inside_by_residue",
            args: vec![
                tensor_arg(&u8t, &[130], &[0; 130]),
                tensor_arg(&u8t, &[1], &[9]),
                tensor_arg(&i8t, &[1], &[-128]),
            ],
            result: tensor_ty(&u8t, 1),
            inst: scatter_inst(&tensor_ty(&u8t, 1), 1),
            want: TensorWant::Ub(TENSOR_SCATTER_OUTSIDE),
        },
        RegionRun {
            name: "scatter_negative_isize_coordinate",
            args: vec![
                tensor_arg(&i32t, &[3], &[0, 0, 0]),
                tensor_arg(&i32t, &[1], &[7]),
                tensor_arg(&isizet, &[1], &[-1]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::Ub(TENSOR_SCATTER_OUTSIDE),
        },
        RegionRun {
            name: "scatter_usize_coordinate_at_the_target_maximum",
            args: vec![
                tensor_arg(&i32t, &[3], &[0, 0, 0]),
                tensor_arg(&i32t, &[1], &[7]),
                tensor_arg(&usizet, &[1], &[usize_max]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::Ub(TENSOR_SCATTER_OUTSIDE),
        },
        RegionRun {
            name: "scatter_coordinate_past_a_zero_extent",
            args: vec![
                tensor_arg(&u8t, &[0], &[]),
                tensor_arg(&u8t, &[1], &[9]),
                tensor_arg(&u8t, &[1], &[0]),
            ],
            result: tensor_ty(&u8t, 1),
            inst: scatter_inst(&tensor_ty(&u8t, 1), 1),
            want: TensorWant::Ub(TENSOR_SCATTER_OUTSIDE),
        },
        RegionRun {
            name: "scatter_bounds_decided_before_any_write",
            args: vec![
                tensor_arg(&i32t, &[3], &[0, 0, 0]),
                tensor_arg(&i32t, &[3], &[1, 2, 3]),
                tensor_arg(&u8t, &[3], &[0, 1, 3]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::Ub(TENSOR_SCATTER_OUTSIDE),
        },
        RegionRun {
            name: "scatter_second_axis_outside",
            args: vec![
                tensor_arg(&i32t, &[2, 2], &[0; 4]),
                tensor_arg(&i32t, &[1], &[5]),
                tensor_arg(&usizet, &[1], &[1]),
                tensor_arg(&u16t, &[1], &[2]),
            ],
            result: tensor_ty(&i32t, 2),
            inst: scatter_inst(&tensor_ty(&i32t, 2), 2),
            want: TensorWant::Ub(TENSOR_SCATTER_OUTSIDE),
        },
        // ---- scatter: type errors (S1-S3, then well-formedness) ----
        RegionRun {
            name: "scatter_init_of_another_element",
            args: vec![
                tensor_arg(&i64t, &[2], &[0, 0]),
                tensor_arg(&i32t, &[1], &[7]),
                tensor_arg(&u8t, &[1], &[0]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "scatter_init_of_another_rank",
            args: vec![
                tensor_arg(&i32t, &[2, 1], &[0, 0]),
                tensor_arg(&i32t, &[1], &[7]),
                tensor_arg(&u8t, &[1], &[0]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "scatter_source_of_another_element",
            args: vec![
                tensor_arg(&i32t, &[2], &[0, 0]),
                tensor_arg(&i64t, &[1], &[7]),
                tensor_arg(&u8t, &[1], &[0]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "scatter_source_not_a_tensor",
            args: vec![
                tensor_arg(&i32t, &[2], &[0, 0]),
                scalar_arg(&i32t, 7),
                tensor_arg(&u8t, &[], &[0]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "scatter_rank0_result_has_no_axis",
            args: vec![tensor_arg(&i32t, &[], &[1]), tensor_arg(&i32t, &[], &[2])],
            result: tensor_ty(&i32t, 0),
            inst: scatter_inst(&tensor_ty(&i32t, 0), 0),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "scatter_too_few_coordinates",
            args: vec![
                tensor_arg(&i32t, &[2, 2], &[0; 4]),
                tensor_arg(&i32t, &[1], &[7]),
                tensor_arg(&u8t, &[1], &[0]),
            ],
            result: tensor_ty(&i32t, 2),
            inst: scatter_inst(&tensor_ty(&i32t, 2), 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "scatter_too_many_coordinates",
            args: vec![
                tensor_arg(&i32t, &[2], &[0, 0]),
                tensor_arg(&i32t, &[1], &[7]),
                tensor_arg(&u8t, &[1], &[0]),
                tensor_arg(&u8t, &[1], &[0]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 2),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "scatter_coordinate_of_another_rank",
            args: vec![
                tensor_arg(&i32t, &[2], &[0, 0]),
                tensor_arg(&i32t, &[1], &[7]),
                tensor_arg(&u8t, &[], &[0]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "scatter_scalar_coordinate",
            args: vec![
                tensor_arg(&i32t, &[2], &[0, 0]),
                tensor_arg(&i32t, &[], &[7]),
                scalar_arg(&u8t, 0),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "scatter_result_not_a_tensor",
            args: vec![
                scalar_arg(&i32t, 0),
                tensor_arg(&i32t, &[1], &[7]),
                tensor_arg(&u8t, &[1], &[0]),
            ],
            result: i32t.clone(),
            inst: scatter_inst(&i32t, 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "scatter_ill_formed_init",
            args: vec![
                tensor_arg(&i32t, &[2], &[0]),
                tensor_arg(&i32t, &[1], &[7]),
                tensor_arg(&u8t, &[1], &[0]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "scatter_ill_formed_source",
            args: vec![
                tensor_arg(&i32t, &[2], &[0, 0]),
                tensor_arg(&i32t, &[2], &[7]),
                tensor_arg(&u8t, &[2], &[0, 1]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "scatter_ill_formed_coordinate_before_its_bounds",
            args: vec![
                tensor_arg(&i32t, &[2], &[0, 0]),
                tensor_arg(&i32t, &[1], &[7]),
                tensor_arg(&u8t, &[1], &[9, 9]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::TypeError,
        },
        RegionRun {
            name: "scatter_static_rule_before_the_extents_precondition",
            args: vec![
                tensor_arg(&i64t, &[2], &[0, 0]),
                tensor_arg(&i32t, &[2], &[7, 8]),
                tensor_arg(&u8t, &[1], &[0]),
            ],
            result: tensor_ty(&i32t, 1),
            inst: scatter_inst(&tensor_ty(&i32t, 1), 1),
            want: TensorWant::TypeError,
        },
    ];
    let mut fns = Vec::new();
    let mut args = Vec::new();
    let mut wants = Vec::new();
    for run in runs {
        let params: Vec<Ty> = run.args.iter().map(|a| a.ty.clone()).collect();
        let mut b = MemBody::new(&params);
        let r = b.val(run.inst);
        fns.push((run.name, params, vec![run.result], b.ret(vec![r])));
        args.push(run.args);
        wants.push(run.want);
    }
    // A poison operand (a scalar loaded from an unbound slot of a binding
    // frame: SemR's wire fragment has no `undef`) is undefined behaviour
    // ahead of every static rule: each run below is otherwise a G1, G3, S1
    // or S3 type error, or a result. Each engine glosses poison in its own
    // words, so the want is the reason `semr_ub_reason` keys both by: the
    // poison and its site.
    type Poisoned = fn(trust_ir::value::ValueId) -> trust_ir::Inst;
    // (name, arguments, poison type, result type, instruction, want).
    type PoisonRun = (
        &'static str,
        Vec<InterpretValue>,
        Ty,
        Ty,
        Poisoned,
        &'static str,
    );
    let poisoned: Vec<PoisonRun> = vec![
        (
            "gather_poison_data_before_the_static_rules",
            vec![tensor_arg(&u8t, &[1], &[0])],
            i32t.clone(),
            tensor_ty(&i32t, 1),
            |p| trust_ir::Inst::TensorGather {
                ty: tensor_ty(&Ty::I32, 1),
                data: p,
                coords: vec![vid(0)],
            },
            "poison at tensor_gather",
        ),
        (
            "gather_poison_coordinate_before_the_static_rules",
            vec![tensor_arg(&i32t, &[3], &[1, 2, 3])],
            u8t.clone(),
            tensor_ty(&i32t, 1),
            |p| trust_ir::Inst::TensorGather {
                ty: tensor_ty(&Ty::I32, 1),
                data: vid(0),
                coords: vec![p],
            },
            "poison at tensor_gather",
        ),
        (
            "scatter_poison_init_before_the_static_rules",
            vec![tensor_arg(&i32t, &[1], &[7]), tensor_arg(&u8t, &[1], &[0])],
            i32t.clone(),
            tensor_ty(&i32t, 1),
            |p| trust_ir::Inst::TensorScatter {
                ty: tensor_ty(&Ty::I32, 1),
                init: p,
                src: vid(0),
                coords: vec![vid(1)],
            },
            "poison at tensor_scatter",
        ),
        (
            "scatter_poison_source_before_the_static_rules",
            vec![
                tensor_arg(&i32t, &[2], &[0, 0]),
                tensor_arg(&u8t, &[1], &[0]),
            ],
            i32t.clone(),
            tensor_ty(&i32t, 1),
            |p| trust_ir::Inst::TensorScatter {
                ty: tensor_ty(&Ty::I32, 1),
                init: vid(0),
                src: p,
                coords: vec![vid(1)],
            },
            "poison at tensor_scatter",
        ),
        (
            "scatter_poison_coordinate",
            vec![
                tensor_arg(&i32t, &[2], &[0, 0]),
                tensor_arg(&i32t, &[1], &[7]),
            ],
            u8t.clone(),
            tensor_ty(&i32t, 1),
            |p| trust_ir::Inst::TensorScatter {
                ty: tensor_ty(&Ty::I32, 1),
                init: vid(0),
                src: vid(1),
                coords: vec![p],
            },
            "poison at tensor_scatter",
        ),
    ];
    for (name, run_args, poison, result, inst, reason) in poisoned {
        let params: Vec<Ty> = run_args.iter().map(|a| a.ty.clone()).collect();
        let mut b = MemBody::new(&params);
        let frame = b.val(trust_ir::Inst::OpenFrame {
            def: trust_ir::inst::BindingFrameDef::new(
                trust_ir::value::BindingFrameId::new(0),
                "unbound",
                vec![trust_ir::inst::BindingSlot::new("p", poison.clone())],
            ),
        });
        let p = b.val(trust_ir::Inst::LoadSlot {
            frame,
            slot: 0,
            ty: poison,
        });
        let r = b.val(inst(p));
        b.void(trust_ir::Inst::CloseFrame { frame });
        fns.push((name, params, vec![result], b.ret(vec![r])));
        args.push(run_args);
        wants.push(TensorWant::Ub(reason));
    }
    let mut module = mem_module("semr_tensor_gather_scatter", fns);
    let label = match &target {
        Some(t) => format!("tensor gather/scatter {}", t.pointer_size * 8),
        None => "tensor gather/scatter reference".to_string(),
    };
    module.target_info = target;
    let runs = module.functions.iter().map(|f| f.id).zip(args).collect();
    (
        SemrCase {
            label,
            module,
            runs,
        },
        wants,
    )
}

/// The result a gather or scatter run must have, by a loop written here
/// independently of both engines: each operand (a parameter) resolved to the
/// run's argument, each coordinate read as the integer its element type
/// denotes (it must be inside its axis: this is for the runs that succeed),
/// each element taken as its residue at the target's width; a gather reads
/// `data` at each coordinate-tensor position, row major, and a scatter
/// writes `src`'s elements over `init`'s in the source's row-major order.
fn gather_scatter_hand_loop(
    inst: &trust_ir::Inst,
    args: &[InterpretValue],
    pointer_bits: u32,
) -> Val {
    type Operand = (Ty, Vec<u64>, Vec<trust_ir::InterpretInt>);
    let operand = |id: &trust_ir::value::ValueId| -> Operand {
        let v = &args[id.0 as usize];
        let (Ty::Tensor(elem, _), InterpretValueKind::Tensor { dims, elems }) = (&v.ty, &v.kind)
        else {
            panic!("hand loop: operand {id:?} is not a tensor: {v:?}")
        };
        let ints = elems
            .iter()
            .map(|e| match &e.kind {
                InterpretValueKind::Int(i) => *i,
                other => panic!("hand loop: a tensor element is an integer, got {other:?}"),
            })
            .collect();
        ((**elem).clone(), dims.clone(), ints)
    };
    let residue = |elem: &Ty, i: &trust_ir::InterpretInt| -> u128 {
        let bits = elem
            .bit_width_with(pointer_bits)
            .expect("an integer element has a width");
        let value = if i.signed {
            i.as_signed() as u128
        } else {
            i.raw
        };
        value & (u128::MAX >> (128 - bits))
    };
    // The row-major offset, in a tensor of extents `dims`, of the coordinates
    // the coordinate tensors hold at position `p`.
    let offset = |coords: &[Operand], p: usize, dims: &[u64]| -> usize {
        assert_eq!(
            coords.len(),
            dims.len(),
            "hand loop: one coordinate per axis"
        );
        let mut at = 0u64;
        for (axis, (_, _, cs)) in coords.iter().enumerate() {
            let c = if cs[p].signed {
                cs[p].as_signed()
            } else {
                i128::try_from(cs[p].raw).expect("hand loop: a small coordinate")
            };
            assert!(
                (0..i128::from(dims[axis])).contains(&c),
                "hand loop: coordinate {c} outside an axis of extent {}",
                dims[axis]
            );
            let stride: u64 = dims[axis + 1..].iter().product();
            at += u64::try_from(c).expect("inside its axis") * stride;
        }
        usize::try_from(at).expect("an offset of a tensor in memory")
    };
    match inst {
        trust_ir::Inst::TensorGather { data, coords, .. } => {
            let (elem, dims, xs) = operand(data);
            let coords: Vec<Operand> = coords.iter().map(operand).collect();
            let out: Vec<u128> = (0..coords[0].2.len())
                .map(|p| residue(&elem, &xs[offset(&coords, p, &dims)]))
                .collect();
            tensor_val(&elem, &coords[0].1, &out)
        }
        trust_ir::Inst::TensorScatter {
            init, src, coords, ..
        } => {
            let (elem, dims, xs) = operand(init);
            let (_, src_dims, ys) = operand(src);
            let coords: Vec<Operand> = coords.iter().map(operand).collect();
            assert!(coords.iter().all(|(_, ds, _)| *ds == src_dims));
            let mut out: Vec<u128> = xs.iter().map(|x| residue(&elem, x)).collect();
            for (p, y) in ys.iter().enumerate() {
                out[offset(&coords, p, &dims)] = residue(&elem, y);
            }
            tensor_val(&elem, &dims, &out)
        }
        other => panic!("hand loop: not a gather or a scatter: {other:?}"),
    }
}

/// SemR's `TensorGather` and `TensorScatter` agree with the reference
/// interpreter on every hand-written run of `semr_tensor_gather_scatter_case`,
/// at the reference layout and on wasm32 (UB by reason, type errors by code,
/// no run unsupported by either engine), and both reach the verdict written
/// there: a successful run's tensor, which an independent hand loop over the
/// arguments computes too; the exact undefined-behaviour text; or a type
/// error. Each verdict class (both instructions' results and type errors,
/// each of the four undefined-behaviour texts, a poison operand at each
/// instruction) occurs at each layout, and
/// the successful runs cover data, `init` and coordinate ranks 1-3 / 0-2
/// and the coordinate element types `i8`, `u8`, `i32`, `u64`, `isize` and
/// `usize`.
#[test]
fn semr_tensor_gather_scatter_agrees_with_the_interpreter() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let rank = |v: &InterpretValue| match &v.kind {
        InterpretValueKind::Tensor { dims, .. } => dims.len(),
        other => panic!("not a tensor: {other:?}"),
    };
    let element = |v: &InterpretValue| match &v.ty {
        Ty::Tensor(elem, _) => semr_ty_str(elem),
        other => panic!("not a tensor type: {other}"),
    };
    for target in [None, Some(semr_target(32))] {
        let (case, wants) = semr_tensor_gather_scatter_case(target);
        let pointer_bits = case.module.pointer_bits();
        let reports = semr_differential(exe, &[case.batch()]);
        assert_eq!(reports.len(), wants.len(), "{}", case.label);
        let mut classes: BTreeMap<String, usize> = BTreeMap::new();
        let mut shapes: BTreeSet<(&str, usize, usize)> = BTreeSet::new();
        let mut coordinate_types: BTreeSet<String> = BTreeSet::new();
        for ((report, want), (func, args)) in reports.iter().zip(&wants).zip(&case.runs) {
            assert_eq!(report.func, *func, "{}", case.label);
            let f = &case.module.functions[report.func.0 as usize];
            let what = format!("{}/{}", case.label, f.name);
            let inst = f.blocks[0]
                .body
                .iter()
                .map(|n| &n.inst)
                .find(|i| {
                    matches!(
                        i,
                        trust_ir::Inst::TensorGather { .. } | trust_ir::Inst::TensorScatter { .. }
                    )
                })
                .unwrap_or_else(|| panic!("{what}: no gather or scatter"));
            let (op, indexed, coords) = match inst {
                trust_ir::Inst::TensorGather { data, coords, .. } => ("gather", data, coords),
                trust_ir::Inst::TensorScatter { init, coords, .. } => ("scatter", init, coords),
                other => panic!("{what}: not a gather or a scatter: {other:?}"),
            };
            assert!(
                !matches!(report.rust, Verdict::Unsupported(_))
                    && !matches!(report.lean, Verdict::Unsupported(_)),
                "{what}: a run is unsupported: {report:?}"
            );
            let class = match want {
                TensorWant::Ok(v) => {
                    assert_eq!(
                        &gather_scatter_hand_loop(inst, args, pointer_bits),
                        v,
                        "hand loop {what}"
                    );
                    assert_eq!(
                        report.rust,
                        Verdict::Ok(vec![v.clone()]),
                        "interpreter {what}"
                    );
                    assert_eq!(report.lean, Verdict::Ok(vec![v.clone()]), "SemR {what}");
                    shapes.insert((
                        op,
                        rank(&args[indexed.0 as usize]),
                        rank(&args[coords[0].0 as usize]),
                    ));
                    coordinate_types.extend(coords.iter().map(|c| element(&args[c.0 as usize])));
                    format!("{op} ok")
                }
                // A poison operand: each engine's own gloss, keyed by its
                // reason and site.
                TensorWant::Ub(m) if m.starts_with("poison at ") => {
                    for (engine, verdict) in [("interpreter", &report.rust), ("SemR", &report.lean)]
                    {
                        let Verdict::Ub(text) = verdict else {
                            panic!("{engine} {what}: {verdict:?}, not undefined behaviour");
                        };
                        assert_eq!(semr_ub_reason(text), *m, "{engine} {what}: {text}");
                    }
                    (*m).to_string()
                }
                TensorWant::Ub(m) => {
                    assert_eq!(report.rust, Verdict::Ub((*m).into()), "interpreter {what}");
                    assert_eq!(report.lean, Verdict::Ub((*m).into()), "SemR {what}");
                    (*m).to_string()
                }
                TensorWant::TypeError => {
                    assert!(
                        matches!(report.rust, Verdict::TypeError(_)),
                        "interpreter {what}: {report:?}"
                    );
                    assert!(
                        matches!(report.lean, Verdict::TypeError(_)),
                        "SemR {what}: {report:?}"
                    );
                    format!("{op} type error")
                }
            };
            assert_eq!(report.comparison, Comparison::Agree, "{what}");
            assert_eq!(
                compare_semr(&report.rust, &report.lean),
                Comparison::Agree,
                "{what}"
            );
            *classes.entry(class).or_default() += 1;
            eprintln!("{what}: {:?}", report.lean);
        }
        for class in [
            "gather ok",
            "scatter ok",
            "gather type error",
            "scatter type error",
            TENSOR_GATHER_EXTENTS_DIFFER,
            TENSOR_GATHER_OUTSIDE,
            TENSOR_SCATTER_EXTENTS_DIFFER,
            TENSOR_SCATTER_OUTSIDE,
            "poison at tensor_gather",
            "poison at tensor_scatter",
        ] {
            assert!(
                classes.get(class).is_some_and(|n| *n > 0),
                "{}: no run reaches `{class}`: {classes:?}",
                case.label
            );
        }
        for op in ["gather", "scatter"] {
            for r in 1..=3 {
                assert!(
                    shapes.iter().any(|(o, d, _)| *o == op && *d == r),
                    "{}: no successful {op} indexes a rank-{r} tensor: {shapes:?}",
                    case.label
                );
            }
            for r in 0..=2 {
                assert!(
                    shapes.iter().any(|(o, _, c)| *o == op && *c == r),
                    "{}: no successful {op} has rank-{r} coordinates: {shapes:?}",
                    case.label
                );
            }
        }
        for ty in ["i8", "u8", "i32", "u64", "isize", "usize"] {
            assert!(
                coordinate_types.contains(ty),
                "{}: no successful run has `{ty}` coordinates: {coordinate_types:?}",
                case.label
            );
        }
    }
}

/// A gather and a scatter function over the v69 wire shapes: a gather at two
/// coordinate tensors of different element types, a gather at a rank-0
/// coordinate, and a scatter at a pointer-width coordinate tensor (the
/// gathers first, so the same bytes under an older header stop at Inst tag
/// 75).
fn tensor_gather_scatter_wire_fns() -> Vec<(&'static str, Vec<Ty>, Vec<Ty>, trust_ir::Block)> {
    let one = |name: &'static str, params: Vec<Ty>, result: Ty, inst: trust_ir::Inst| {
        let mut b = MemBody::new(&params);
        let r = b.val(inst);
        (name, params, vec![result], b.ret(vec![r]))
    };
    vec![
        one(
            "gather_two_axes",
            vec![
                tensor_ty(&Ty::I32, 2),
                tensor_ty(&Ty::U8, 1),
                tensor_ty(&Ty::I64, 1),
            ],
            tensor_ty(&Ty::I32, 1),
            gather_inst(&tensor_ty(&Ty::I32, 1), 2),
        ),
        one(
            "gather_at_a_rank0_coordinate",
            vec![tensor_ty(&Ty::U16, 1), tensor_ty(&Ty::Isize, 0)],
            tensor_ty(&Ty::U16, 0),
            gather_inst(&tensor_ty(&Ty::U16, 0), 1),
        ),
        one(
            "scatter_from_a_rank2_source",
            vec![
                tensor_ty(&Ty::U16, 1),
                tensor_ty(&Ty::U16, 2),
                tensor_ty(&Ty::Usize, 2),
            ],
            tensor_ty(&Ty::U16, 1),
            scatter_inst(&tensor_ty(&Ty::U16, 1), 1),
        ),
    ]
}

/// The v69 wire module: every function of [`tensor_gather_scatter_wire_fns`].
fn tensor_gather_scatter_wire_module(target: Option<trust_ir::TargetInfo>) -> Module {
    let mut module = mem_module(
        "semr_tensor_gather_scatter_wire",
        tensor_gather_scatter_wire_fns(),
    );
    module.target_info = target;
    module
}

/// The v69 wire boundary in SemR's decoder: a gather/scatter module (and a
/// scatter alone) is written at exactly `TENSOR_GATHER_SCATTER_FORMAT_VERSION`,
/// validates, and decodes in SemR to the module the Rust reader reads; the
/// same bytes under the version before are refused by both decoders at the
/// instruction tag (Inst tags 75 and 76 are read-gated: the Rust reader's
/// `InvalidTag(75)` / `InvalidTag(76)`, SemR's `invalid Inst tag`); and a
/// header past the newest version is refused by the Rust reader and is
/// `unsupported` (`wire_version`) in SemR, before its payload.
#[test]
fn semr_tensor_gather_scatter_wire_boundary_is_explicit() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let v69 = trust_ir::binary::TENSOR_GATHER_SCATTER_FORMAT_VERSION;
    let module = tensor_gather_scatter_wire_module(None);
    let scatter = mem_module(
        "semr_tensor_scatter_wire",
        tensor_gather_scatter_wire_fns()
            .into_iter()
            .filter(|(name, ..)| name.starts_with("scatter"))
            .collect(),
    );
    let mut blobs = Vec::new();
    for m in [&module, &scatter] {
        let errors = trust_ir_build::validate::validate_module(m);
        assert!(errors.is_empty(), "{} is well-formed: {errors:?}", m.name);
        let blob = trust_ir::binary::serialize_module(m).expect("v69 wire");
        assert_eq!(header_version(&blob), v69, "{}", m.name);
        assert_eq!(&trust_ir::binary::deserialize_module(&blob).unwrap(), m);
        blobs.push(blob);
    }
    let old = relabelled(&blobs[0], v69 - 1);
    let old_scatter = relabelled(&blobs[1], v69 - 1);
    assert_eq!(
        trust_ir::binary::deserialize_module(&old),
        Err(trust_ir::binary::BinaryError::InvalidTag(75))
    );
    assert_eq!(
        trust_ir::binary::deserialize_module(&old_scatter),
        Err(trust_ir::binary::BinaryError::InvalidTag(76))
    );
    let future_version = trust_ir::binary::FORMAT_VERSION
        .checked_add(1)
        .expect("wire format has an expressible future version");
    assert!(future_version > v69);
    let future = relabelled(&blobs[0], future_version);
    assert!(trust_ir::binary::deserialize_module(&future).is_err());
    blobs.extend([old, old_scatter, future]);
    let verdicts = semr_decode(exe, &blobs);
    assert_eq!(verdicts[0]["decoded"], semr_summary_of(&module));
    assert_eq!(verdicts[1]["decoded"], semr_summary_of(&scatter));
    assert_eq!(
        verdicts[2..],
        [
            json!({"error": "decode: invalid Inst tag"}),
            json!({"error": "decode: invalid Inst tag"}),
            json!({"unsupported": "wire_version"}),
        ]
    );
}

/// NEGATIVE CONTROL for the gather's and the scatter's fixture theorems: a
/// helper the executable and the relation share (so `tensorGather_sound` and
/// `tensorScatter_sound` move with it), mutated — a repeated scatter
/// coordinate that keeps the FIRST write, a coordinate at its axis's extent
/// read as inside, one position's coordinates assembled in reverse axis
/// order — no longer kernel-checks SemR.lean, and every error is in the
/// theorems that pin those values.
#[test]
fn semr_tensor_gather_scatter_theorems_refuse_mutated_helpers() {
    run_lean_mutants(
        "gather-scatter-theorem-mutants",
        "SemR",
        (
            "SemR.lean",
            Some(&[
                "scatter_repeated_coordinate_keeps_the_last_write",
                "gather_negative_coordinate_is_outside",
                "scatter_coordinate_at_the_extent_is_outside",
                "gather_reads_the_named_elements",
            ]),
        ),
        &[
            LeanMutant {
                name: "tensor-scatter-keeps-the-first-write",
                file: "SemR.lean",
                from: "  | acc, t :: ts, y :: ys => scatterWrites (setNth acc t y) ts ys\n",
                to: "  | acc, t :: ts, y :: ys => setNth (scatterWrites acc ts ys) t y\n",
                times: 1,
            },
            LeanMutant {
                name: "tensor-coordinate-at-the-extent-is-inside",
                file: "SemR.lean",
                from: "  !(t.signed && isNeg (t.bits pointerBits) x) && decide (x < d)\n",
                to: "  !(t.signed && isNeg (t.bits pointerBits) x) && decide (x ≤ d)\n",
                times: 1,
            },
            LeanMutant {
                name: "tensor-coordinates-in-reverse-axis-order",
                file: "SemR.lean",
                from: "      (coordsAt pointerBits f cs ds).map (getN xs f :: ·)\n",
                to: "      (coordsAt pointerBits f cs ds).map (· ++ [getN xs f])\n",
                times: 1,
            },
        ],
    );
}

/// NEGATIVE CONTROL for the gather and scatter runs: a check `evalGather` /
/// `evalScatter` make, which the executable and the relation share and no
/// fixture theorem pins — the gather's extents precondition, the scatter's,
/// G2's coordinate count, S1's `init` element — dropped or weakened, still
/// kernel-checks (the relation moves with it), and only the differential
/// against the interpreter sees it: each mutant's `semr_mutant_eval`
/// disagrees with the interpreter on `semr_tensor_gather_scatter_case`.
#[test]
fn semr_tensor_gather_scatter_differential_refuses_shared_helper_mutants() {
    let Oracle::Ready(_) = semr_oracle() else {
        return;
    };
    let Some(lake) = semr_lake() else {
        return;
    };
    let mutants: [(&str, &str, &str); 4] = [
        (
            "tensor-gather-extents-unchecked",
            "        if !coords.all (sameDims cds) then\n",
            "        if false then\n",
        ),
        (
            "tensor-scatter-extents-unchecked",
            "    else if !coords.all (sameDims ds) then\n",
            "    else if false then\n",
        ),
        (
            "tensor-gather-admits-too-few-coordinates",
            "coords.length != ds.length",
            "coords.length > ds.length",
        ),
        (
            "tensor-scatter-init-element-unchecked",
            "    if !(ei.code == e.code && di.length == s) then\n",
            "    if !(di.length == s) then\n",
        ),
    ];
    let cases = [
        semr_tensor_gather_scatter_case(None).0,
        semr_tensor_gather_scatter_case(Some(semr_target(32))).0,
    ];
    let scratch = SemrScratch::new("gather-scatter-mutants");
    let package = semr_package_files();
    for (name, from, to) in mutants {
        let dir = scratch.path(name);
        fs::create_dir_all(&dir).expect("mutant dir");
        for f in &package {
            fs::copy(semr_dir().join(f), dir.join(f)).unwrap_or_else(|e| panic!("copy {f}: {e}"));
        }
        let path = dir.join("SemR.lean");
        let src = fs::read_to_string(&path).expect("SemR source");
        assert_eq!(
            src.matches(from).count(),
            1,
            "mutant {name}: `{from}` must occur once"
        );
        fs::write(&path, src.replacen(from, to, 1)).expect("write mutant");
        let out = lake_build_command(&lake, &dir, "semr_mutant_eval")
            .output()
            .expect("run lake");
        assert!(
            out.status.success(),
            "mutant {name}: SemR must still build (only the differential can see it):\n{}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        let exe = dir.join(".lake/build/bin/semr_mutant_eval");
        let batches: Vec<Batch<'_>> = cases.iter().map(SemrCase::batch).collect();
        let t = tally(&semr_differential(&exe, &batches));
        assert!(
            !t.mismatches.is_empty(),
            "mutant {name}: the gather/scatter differential saw no disagreement"
        );
        eprintln!("mutant {name}: {} disagreement(s)", t.mismatches.len());
        let _ = fs::remove_dir_all(&dir);
    }
}

/// The decoder differential on the tensor region's blobs: every third proper
/// prefix, one appended byte and every one-byte change of the v68
/// map/reduce/view wire module and of the v69 gather/scatter wire module
/// (each at both layouts, each written at its own version), judged as
/// `semr_decoder_agrees_with_the_binary_reader_on_tensor_blobs` judges: a
/// blob Rust accepts SemR must not call malformed, and a blob Rust refuses
/// SemR must not decode.
#[test]
fn semr_decoder_agrees_with_the_binary_reader_on_tensor_region_blobs() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let layout = |t: &Option<trust_ir::TargetInfo>| match t {
        Some(t) => format!("{}", t.pointer_size * 8),
        None => "reference".to_string(),
    };
    let modules: Vec<(String, u32, Module)> = [None, Some(semr_target(32))]
        .into_iter()
        .flat_map(|t| {
            [
                (
                    format!("tensor region wire {}", layout(&t)),
                    trust_ir::binary::TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION,
                    tensor_region_wire_module(t.clone()),
                ),
                (
                    format!("tensor gather/scatter wire {}", layout(&t)),
                    trust_ir::binary::TENSOR_GATHER_SCATTER_FORMAT_VERSION,
                    tensor_gather_scatter_wire_module(t),
                ),
            ]
        })
        .collect();
    let mut blobs: Vec<(BlobKind, String, Vec<u8>)> = Vec::new();
    for (label, version, module) in &modules {
        let blob = trust_ir::binary::serialize_module(module).expect("tensor region blob");
        assert_eq!(header_version(&blob), *version, "{label}");
        for cut in (0..blob.len()).step_by(3) {
            blobs.push((
                BlobKind::HeaderOrTrailerFault,
                format!("{label} cut {cut}"),
                blob[..cut].to_vec(),
            ));
        }
        let mut longer = blob.clone();
        longer.push(0);
        blobs.push((
            BlobKind::HeaderOrTrailerFault,
            format!("{label} + 0x00"),
            longer,
        ));
        one_byte_mutations(label, &blob, &mut blobs);
        blobs.push((BlobKind::Written, label.clone(), blob));
    }
    let (rust_ok, equal) = judge_decodes(exe, &blobs, "tensor region blobs");
    assert!(equal >= modules.len() && rust_ok >= modules.len());
}

// ---------------------------------------------------------------------------
// v70 content-addressed weight blobs (PKG-U13e, docs/SPEC_RATIFICATIONS.md
// §27): a `Constant::TensorBlob` names an integer tensor by the SHA-256 of
// its element bytes, which the module blob table holds. Both engines resolve
// the digest, hash the row's bytes, check that the extents describe them and
// read them little-endian; each failure is a type error (an execution of a
// module the validator refuses).
// ---------------------------------------------------------------------------

/// What both engines must say about one blob run: a tensor, undefined
/// behaviour by its message, or a type error whose SemR text is `semr` and
/// whose interpreter message contains `interpreter`.
#[derive(Debug)]
enum BlobWant {
    Ok(Val),
    Ub(&'static str),
    TypeError {
        semr: &'static str,
        interpreter: &'static str,
    },
}

const BLOB_RANK: &str = "TypeError: tensor blob constant rank";
const BLOB_EXTENT: &str = "TypeError: tensor blob constant extent outside usize";
const BLOB_MISSING: &str = "TypeError: tensor blob constant names no blob";
const BLOB_HASH: &str = "TypeError: tensor blob bytes do not hash to the digest";
const BLOB_COUNT: &str = "TypeError: tensor blob byte count";
const BLOB_MISPLACED: &str = "TypeError: misplaced tensor blob constant";

/// `count` deterministic bytes, distinct per `seed`.
fn blob_bytes(seed: u64, count: usize) -> Vec<u8> {
    let mut state = seed
        .wrapping_mul(0x9e37_79b9_7f4a_7c15)
        .wrapping_add(0x2545_f491_4f6c_dd1d);
    (0..count)
        .map(|_| {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (state >> 56) as u8
        })
        .collect()
}

/// `data` read as little-endian `bits`-wide residues: the hand decode every
/// successful run's tensor is held to.
fn blob_residues(data: &[u8], bits: u32) -> Vec<u128> {
    data.chunks_exact((bits / 8) as usize)
        .map(|chunk| {
            chunk
                .iter()
                .rev()
                .fold(0u128, |acc, byte| (acc << 8) | u128::from(*byte))
        })
        .collect()
}

fn blob_const(ty: Ty, digest: trust_ir::blob::BlobDigest, dims: &[u64]) -> trust_ir::Inst {
    trust_ir::Inst::Const {
        ty,
        value: trust_ir::constant::Constant::TensorBlob {
            digest,
            dims: dims.to_vec(),
        },
    }
}

/// The blob runs at one layout (`None`: the 64-bit reference; `Some`: the
/// target's): every integer element type at ranks 0 to 3 (zero extents
/// included), byte strings at each length SHA-256's padding treats apart (0,
/// 1, 55, 56, 63, 64, 65, 119, 120 and 128 bytes: one block, the length word
/// spilling into a second, several blocks), one row named at two element
/// types, a `usize` row whose element width is the layout's, a blob as a
/// contraction's operand (and its extents mismatch, UB by its message), and
/// every refusal: a missing row, a row whose bytes do not hash to its digest,
/// too many and too few bytes, a rank other than the type's, an extent
/// outside `usize`, an element count past it, and a blob nested in a struct
/// field or an enum payload (rule C1, in a scalar lane: SemR decodes no
/// struct or enum with a tensor field).
fn semr_tensor_blob_case(target: Option<trust_ir::TargetInfo>) -> (SemrCase, Vec<BlobWant>) {
    let wasm = target.as_ref().is_some_and(|t| t.pointer_size == 4);
    let w: u32 = if wasm { 32 } else { 64 };
    let of = trust_ir::blob::BlobDigest::of;
    let mut fns: Vec<(String, Vec<Ty>, Vec<Ty>, trust_ir::Block)> = Vec::new();
    let mut args: Vec<Vec<InterpretValue>> = Vec::new();
    let mut wants: Vec<BlobWant> = Vec::new();
    let mut rows: Vec<Vec<u8>> = Vec::new();
    let mut constant = |name: String,
                        elem: &Ty,
                        rank: u32,
                        digest: trust_ir::blob::BlobDigest,
                        dims: &[u64],
                        want: BlobWant| {
        let ty = tensor_ty(elem, rank);
        let mut b = MemBody::new(&[]);
        let r = b.val(blob_const(ty.clone(), digest, dims));
        fns.push((name, vec![], vec![ty], b.ret(vec![r])));
        args.push(vec![]);
        wants.push(want);
    };

    // SHA-256's padding cases, as `u8` vectors.
    for len in [0usize, 1, 55, 56, 63, 64, 65, 119, 120, 128] {
        let data = blob_bytes(len as u64, len);
        constant(
            format!("u8_{len}_bytes"),
            &Ty::U8,
            1,
            of(&data),
            &[len as u64],
            BlobWant::Ok(tensor_val(&Ty::U8, &[len as u64], &blob_residues(&data, 8))),
        );
        rows.push(data);
    }
    // Every integer element type at ranks 0 to 3.
    let elems = [
        Ty::I8,
        Ty::U8,
        Ty::I16,
        Ty::U16,
        Ty::I32,
        Ty::U32,
        Ty::I64,
        Ty::U64,
        Ty::I128,
        Ty::U128,
        Ty::Isize,
        Ty::Usize,
    ];
    let shapes: [&[u64]; 5] = [&[], &[3], &[2, 2], &[2, 0, 3], &[1, 2, 3]];
    for (e, elem) in elems.iter().enumerate() {
        let bits = elem.bit_width_with(w).expect("integer width");
        for (s, dims) in shapes.iter().enumerate() {
            let count: u64 = dims.iter().product();
            let data = blob_bytes(
                1000 + (e * 10 + s) as u64,
                (count * u64::from(bits / 8)) as usize,
            );
            constant(
                format!("{}_rank{}_{s}", semr_ty_str(elem), dims.len()),
                elem,
                dims.len() as u32,
                of(&data),
                dims,
                BlobWant::Ok(tensor_val(elem, dims, &blob_residues(&data, bits))),
            );
            rows.push(data);
        }
    }
    // One row named at two element types: eight bytes as two `i32` and as
    // four `u16`.
    let shared = blob_bytes(2000, 8);
    constant(
        "shared_as_i32".into(),
        &Ty::I32,
        1,
        of(&shared),
        &[2],
        BlobWant::Ok(tensor_val(&Ty::I32, &[2], &blob_residues(&shared, 32))),
    );
    constant(
        "shared_as_u16".into(),
        &Ty::U16,
        2,
        of(&shared),
        &[2, 2],
        BlobWant::Ok(tensor_val(&Ty::U16, &[2, 2], &blob_residues(&shared, 16))),
    );
    rows.push(shared);
    // Sixteen bytes are two `usize` at 64 bits, four at 32.
    let words = blob_bytes(2001, 16);
    constant(
        "usize_pair_over_16_bytes".into(),
        &Ty::Usize,
        1,
        of(&words),
        &[2],
        if wasm {
            BlobWant::TypeError {
                semr: BLOB_COUNT,
                interpreter: "holds 16 bytes",
            }
        } else {
            BlobWant::Ok(tensor_val(&Ty::Usize, &[2], &blob_residues(&words, 64)))
        },
    );
    rows.push(words);

    // The refusals.
    let four = blob_bytes(2002, 4);
    let absent = blob_bytes(2003, 4);
    constant(
        "missing_row".into(),
        &Ty::U8,
        1,
        of(&absent),
        &[4],
        BlobWant::TypeError {
            semr: BLOB_MISSING,
            interpreter: "holds no blob",
        },
    );
    constant(
        "too_many_bytes".into(),
        &Ty::U8,
        1,
        of(&four),
        &[3],
        BlobWant::TypeError {
            semr: BLOB_COUNT,
            interpreter: "holds 4 bytes",
        },
    );
    constant(
        "too_few_bytes".into(),
        &Ty::U8,
        1,
        of(&four),
        &[5],
        BlobWant::TypeError {
            semr: BLOB_COUNT,
            interpreter: "holds 4 bytes",
        },
    );
    constant(
        "rank_other_than_the_type".into(),
        &Ty::U8,
        1,
        of(&four),
        &[2, 2],
        BlobWant::TypeError {
            semr: BLOB_RANK,
            interpreter: "has rank 1",
        },
    );
    // At 64 bits no `u64` extent reaches `2^64`, so the extent is the byte
    // count's refusal there.
    constant(
        "extent_past_usize".into(),
        &Ty::U8,
        1,
        of(&four),
        &[1 << 32],
        if wasm {
            BlobWant::TypeError {
                semr: BLOB_EXTENT,
                interpreter: "does not fit",
            }
        } else {
            BlobWant::TypeError {
                semr: BLOB_COUNT,
                interpreter: "holds 4 bytes",
            }
        },
    );
    constant(
        "count_past_usize".into(),
        &Ty::U8,
        2,
        of(&four),
        &[1 << 32, 1 << 32],
        if wasm {
            BlobWant::TypeError {
                semr: BLOB_EXTENT,
                interpreter: "does not fit",
            }
        } else {
            BlobWant::TypeError {
                semr: BLOB_COUNT,
                interpreter: "holds 4 bytes",
            }
        },
    );
    rows.push(four);
    // A row whose bytes were changed after its digest was recorded.
    let forged = blob_bytes(2004, 4);
    let forged_digest = of(&forged);
    constant(
        "bytes_do_not_hash_to_the_digest".into(),
        &Ty::U8,
        1,
        forged_digest,
        &[4],
        BlobWant::TypeError {
            semr: BLOB_HASH,
            interpreter: "do not hash to it",
        },
    );
    rows.push(forged);

    // A blob as a contraction's right operand: `x · w`.
    let weights = blob_bytes(2005, 12);
    let w_res = blob_residues(&weights, 32);
    for (name, x) in [
        ("dot_with_a_blob", vec![3i128, -1, 7]),
        ("dot_with_a_blob_extents_differ", vec![1, 2, 3, 4]),
    ] {
        let x_ty = tensor_ty(&Ty::I32, 1);
        let mut b = MemBody::new(std::slice::from_ref(&x_ty));
        let k = b.val(blob_const(x_ty.clone(), of(&weights), &[3]));
        let r = b.val(trust_ir::Inst::TensorContract {
            ty: tensor_ty(&Ty::I32, 0),
            lhs: b.param(0),
            rhs: k,
            batch: vec![],
            contract: vec![(0, 0)],
        });
        let want = if x.len() == 3 {
            let dot = x.iter().zip(&w_res).fold(0u128, |acc, (a, w)| {
                acc.wrapping_add((*a as u128).wrapping_mul(*w))
            }) & 0xffff_ffff;
            BlobWant::Ok(tensor_val(&Ty::I32, &[], &[dot]))
        } else {
            BlobWant::Ub(TENSOR_EXTENT_MISMATCH)
        };
        fns.push((
            name.to_string(),
            vec![x_ty],
            vec![tensor_ty(&Ty::I32, 0)],
            b.ret(vec![r]),
        ));
        args.push(vec![tensor_arg(&Ty::I32, &[x.len() as u64], &x)]);
        wants.push(want);
    }
    rows.push(weights);

    // Rule C1 at run time: a blob nested in a struct field or an enum
    // payload has no meaning in either engine, whatever its row holds.
    // SemR's fragment has no struct or enum with a tensor field (its decoder
    // refuses one by name), so the blob sits in a scalar lane: both engines
    // refuse it as misplaced before reading the lane's type.
    let placed = blob_bytes(2006, 4);
    let blob = trust_ir::constant::Constant::TensorBlob {
        digest: of(&placed),
        dims: vec![4],
    };
    let int = trust_ir::constant::Constant::Int;
    for (name, ty, value) in [
        (
            "blob_in_a_struct_field",
            Ty::Struct(trust_ir::value::StructId::new(0)),
            vec![blob.clone(), int(0)],
        ),
        (
            "blob_in_an_enum_payload",
            Ty::Enum(trust_ir::value::EnumId::new(0)),
            vec![int(0), blob.clone()],
        ),
    ] {
        let mut b = MemBody::new(&[]);
        let r = b.val(trust_ir::Inst::Const {
            ty: ty.clone(),
            value: trust_ir::constant::Constant::Aggregate(value),
        });
        fns.push((name.to_string(), vec![], vec![ty], b.ret(vec![r])));
        args.push(vec![]);
        wants.push(BlobWant::TypeError {
            semr: BLOB_MISPLACED,
            interpreter: "misplaced tensor blob constant",
        });
    }
    rows.push(placed);

    let mut module = mem_module(
        "semr_tensor_blob",
        fns.iter()
            .map(|(n, p, r, b)| (n.as_str(), p.clone(), r.clone(), b.clone()))
            .collect(),
    );
    for row in rows {
        module.intern_blob(row);
    }
    module.structs.push(trust_ir::ty::StructDef {
        id: trust_ir::value::StructId::new(0),
        name: "Holder".into(),
        fields: vec![
            trust_ir::ty::FieldDef {
                name: "w".into(),
                ty: Ty::U8,
                offset: None,
            },
            trust_ir::ty::FieldDef {
                name: "n".into(),
                ty: Ty::U8,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    module.enums.push(trust_ir::ty::EnumDef::new(
        trust_ir::value::EnumId::new(0),
        "Wrapped",
        vec![trust_ir::ty::EnumVariant {
            name: "W".into(),
            fields: vec![Ty::U8],
            field_names: vec![],
        }],
    ));
    let forged_row = module
        .blobs
        .iter_mut()
        .find(|row| row.digest == forged_digest)
        .expect("the forged row");
    forged_row.data[0] ^= 1;
    let label = match &target {
        Some(t) => format!("tensor blob {}", t.pointer_size * 8),
        None => "tensor blob reference".to_string(),
    };
    module.target_info = target;
    let runs = module.functions.iter().map(|f| f.id).zip(args).collect();
    (
        SemrCase {
            label,
            module,
            runs,
        },
        wants,
    )
}

/// v70's differential: on both layouts, every blob run's tensor is the hand
/// decode of its row's bytes in the interpreter AND in SemR (`semr_eval` on
/// the module's binary image), a contraction over a blob agrees, its extents
/// mismatch is UB by its normative message in both, and each refusal is a
/// type error in both, SemR's by its own text and the interpreter's by its
/// rule; no run is unsupported on either side. Every element type, rank 0 to
/// 3 and padding length is reached by a successful run, and every refusal by
/// a run.
#[test]
fn semr_tensor_blob_agrees_with_the_interpreter() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    for target in [None, Some(semr_target(32))] {
        let (case, wants) = semr_tensor_blob_case(target);
        let reports = semr_differential(exe, &[case.batch()]);
        assert_eq!(reports.len(), wants.len(), "{}", case.label);
        let mut classes: BTreeMap<String, usize> = BTreeMap::new();
        let mut elements: BTreeSet<String> = BTreeSet::new();
        let mut ranks: BTreeSet<usize> = BTreeSet::new();
        for (report, want) in reports.iter().zip(&wants) {
            let f = &case.module.functions[report.func.0 as usize];
            let what = format!("{}/{}", case.label, f.name);
            assert!(
                !matches!(report.rust, Verdict::Unsupported(_))
                    && !matches!(report.lean, Verdict::Unsupported(_)),
                "{what}: a run is unsupported: {report:?}"
            );
            let class = match want {
                BlobWant::Ok(v) => {
                    assert_eq!(
                        report.rust,
                        Verdict::Ok(vec![v.clone()]),
                        "interpreter {what}"
                    );
                    assert_eq!(report.lean, Verdict::Ok(vec![v.clone()]), "SemR {what}");
                    if let Val::Tensor { elem, dims, .. } = v {
                        elements.insert(format!("{elem}"));
                        ranks.insert(dims.len());
                    }
                    "ok".to_string()
                }
                BlobWant::Ub(m) => {
                    assert_eq!(report.rust, Verdict::Ub((*m).into()), "interpreter {what}");
                    assert_eq!(report.lean, Verdict::Ub((*m).into()), "SemR {what}");
                    (*m).to_string()
                }
                BlobWant::TypeError { semr, interpreter } => {
                    let Verdict::TypeError(rust) = &report.rust else {
                        panic!("interpreter {what}: {report:?}");
                    };
                    let Verdict::TypeError(lean) = &report.lean else {
                        panic!("SemR {what}: {report:?}");
                    };
                    assert!(rust.contains(interpreter), "interpreter {what}: {rust}");
                    assert!(lean.contains(semr), "SemR {what}: {lean}");
                    (*semr).to_string()
                }
            };
            assert_eq!(report.comparison, Comparison::Agree, "{what}");
            *classes.entry(class).or_default() += 1;
        }
        let wasm = case.module.pointer_bits() == 32;
        let mut required = vec![
            "ok",
            TENSOR_EXTENT_MISMATCH,
            BLOB_RANK,
            BLOB_MISSING,
            BLOB_HASH,
            BLOB_COUNT,
            BLOB_MISPLACED,
        ];
        if wasm {
            required.push(BLOB_EXTENT);
        }
        for class in required {
            assert!(
                classes.get(class).is_some_and(|n| *n > 0),
                "{}: no run reaches `{class}`: {classes:?}",
                case.label
            );
        }
        assert_eq!(elements.len(), 12, "{}: {elements:?}", case.label);
        assert_eq!(ranks, BTreeSet::from([0, 1, 2, 3]), "{}", case.label);
        eprintln!("{}: {classes:?}", case.label);
    }
}

/// The Constant axis credits what a run EXECUTED: a blob constant in a block
/// the run never enters earns no `const:TensorBlob`, and the run that takes
/// the other edge does; the gate over the first run alone fails with
/// `TensorBlob` unexercised.
#[test]
fn semr_constant_gate_credits_executed_blobs_only() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let fragment = semr_fragment_rows();
    let constants = semr_const_fragment_rows();
    let weights = blob_bytes(3000, 8);
    let ty = tensor_ty(&Ty::I32, 1);
    let mut mb = ModuleBuilder::new("semr_executed_blob");
    let digest = mb.intern_blob(weights);
    let ft = mb.add_func_type(vec![Ty::Bool, ty.clone()], vec![ty.clone()]);
    let mut fb = mb.function("dead_blob", ft);
    let entry = fb.create_block();
    let live = fb.create_block();
    let dead = fb.create_block();
    let c = fb.add_block_param(entry, Ty::Bool);
    let x = fb.add_block_param(entry, ty.clone());
    fb.switch_to_block(entry);
    fb.condbr(c, live, vec![], dead, vec![]);
    fb.switch_to_block(live);
    fb.ret(vec![x]);
    fb.switch_to_block(dead);
    let k = fb.const_value(
        ty.clone(),
        trust_ir::constant::Constant::TensorBlob {
            digest,
            dims: vec![2],
        },
    );
    fb.ret(vec![k]);
    let f = fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let x = tensor_arg(&Ty::I32, &[2], &[5, -5]);
    let batch = Batch {
        label: "executed blob".into(),
        module: &module,
        runs: vec![
            (f, vec![InterpretValue::bool(true), x.clone()]),
            (f, vec![InterpretValue::bool(false), x]),
        ],
    };
    let executed = semr_executed(exe, &fragment, &batch);
    assert!(
        !executed[0].contains("const:TensorBlob"),
        "{:?}",
        executed[0]
    );
    assert!(
        executed[1].contains("const:TensorBlob"),
        "{:?}",
        executed[1]
    );
    assert!(executed[1].contains("Const"), "{:?}", executed[1]);
    let reports = semr_differential(exe, std::slice::from_ref(&batch));
    assert!(
        reports
            .iter()
            .all(|r| matches!(r.comparison, Comparison::Agree)),
        "{reports:?}"
    );
    let runs: Vec<(BTreeSet<String>, Comparison)> = executed
        .iter()
        .cloned()
        .zip(reports.iter().map(|r| r.comparison.clone()))
        .collect();
    let e = semr_const_parity_gate(&constants, &runs[..1]).unwrap_err();
    assert!(e.contains("\"TensorBlob\""), "{e}");
    assert!(semr_const_parity_gate(&constants, &runs).is_ok());
}

/// A blob module over the v70 wire shapes: two functions naming one row at
/// different element types, a rank-0 tensor and a `usize` tensor (the
/// constant first in each body, so the same bytes under an older header stop
/// at Constant tag 18), with an empty row and a row no constant names.
fn tensor_blob_wire_module(target: Option<trust_ir::TargetInfo>) -> Module {
    let of = trust_ir::blob::BlobDigest::of;
    let pair = vec![1u8, 0x80, 0xff, 0x7f];
    let word = blob_bytes(4000, 8);
    let one = |name: &'static str, ty: Ty, value: trust_ir::Inst| {
        let mut b = MemBody::new(&[]);
        let r = b.val(value);
        (name, vec![], vec![ty], b.ret(vec![r]))
    };
    let mut module = mem_module(
        "semr_tensor_blob_wire",
        vec![
            one(
                "pair_as_i16",
                tensor_ty(&Ty::I16, 1),
                blob_const(tensor_ty(&Ty::I16, 1), of(&pair), &[2]),
            ),
            one(
                "pair_as_u8",
                tensor_ty(&Ty::U8, 2),
                blob_const(tensor_ty(&Ty::U8, 2), of(&pair), &[2, 2]),
            ),
            one(
                "scalar_i32",
                tensor_ty(&Ty::I32, 0),
                blob_const(tensor_ty(&Ty::I32, 0), of(&pair), &[]),
            ),
            one(
                "empty_usize",
                tensor_ty(&Ty::Usize, 1),
                blob_const(tensor_ty(&Ty::Usize, 1), of(&[]), &[0]),
            ),
        ],
    );
    module.intern_blob(pair);
    module.intern_blob(Vec::new());
    module.intern_blob(word);
    module.target_info = target;
    module
}

/// The v70 wire boundary in SemR's decoder: a blob module (and a module
/// whose only v70 content is its table) is written at exactly
/// `TENSOR_BLOB_FORMAT_VERSION`, validates, and decodes in SemR to the module
/// the Rust reader reads, table included; the same bytes under the version
/// before are refused by both decoders, the constant at its tag (Constant tag
/// 18 is read-gated: the Rust reader's `InvalidTag(18)`, SemR's `invalid
/// Constant tag`) and the table as bytes past the module's end; and a header
/// past the newest version is refused by the Rust reader and is
/// `unsupported` (`wire_version`) in SemR, before its payload.
#[test]
fn semr_tensor_blob_wire_boundary_is_explicit() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let v70 = trust_ir::binary::TENSOR_BLOB_FORMAT_VERSION;
    let module = tensor_blob_wire_module(None);
    let mut table_only = Module::new("semr_tensor_blob_table_only");
    table_only.intern_blob(vec![9, 8, 7]);
    let mut blobs = Vec::new();
    for m in [&module, &table_only] {
        let errors = trust_ir_build::validate::validate_module(m);
        assert!(errors.is_empty(), "{} is well-formed: {errors:?}", m.name);
        let blob = trust_ir::binary::serialize_module(m).expect("v70 wire");
        assert_eq!(header_version(&blob), v70, "{}", m.name);
        assert_eq!(&trust_ir::binary::deserialize_module(&blob).unwrap(), m);
        blobs.push(blob);
    }
    let old = relabelled(&blobs[0], v70 - 1);
    let old_table = relabelled(&blobs[1], v70 - 1);
    assert_eq!(
        trust_ir::binary::deserialize_module(&old),
        Err(trust_ir::binary::BinaryError::InvalidTag(18))
    );
    assert!(trust_ir::binary::deserialize_module(&old_table).is_err());
    let future_version = trust_ir::binary::FORMAT_VERSION
        .checked_add(1)
        .expect("wire format has an expressible future version");
    assert!(future_version > v70);
    let future = relabelled(&blobs[0], future_version);
    assert!(trust_ir::binary::deserialize_module(&future).is_err());
    blobs.extend([old, old_table, future]);
    let verdicts = semr_decode(exe, &blobs);
    assert_eq!(verdicts[0]["decoded"], semr_summary_of(&module));
    assert_eq!(verdicts[1]["decoded"], semr_summary_of(&table_only));
    assert_eq!(
        verdicts[2],
        json!({"error": "decode: invalid Constant tag"})
    );
    assert!(
        verdicts[3].get("error").is_some(),
        "the table past a v69 module's end is malformed: {}",
        verdicts[3]
    );
    assert_eq!(verdicts[4], json!({"unsupported": "wire_version"}));
}

/// The decoder differential on the v70 blob wire module (at both layouts):
/// every third proper prefix, one appended byte and every one-byte change,
/// judged as the other decoder differentials judge — a blob Rust accepts SemR
/// must not call malformed (a changed byte of a row's data, or of a digest
/// that keeps the table ascending, decodes in both to the same summary:
/// neither decoder hashes), and a blob Rust refuses SemR must not decode (a
/// digest changed out of ascending order is refused by both).
#[test]
fn semr_decoder_agrees_with_the_binary_reader_on_tensor_blob_constants() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let mut blobs: Vec<(BlobKind, String, Vec<u8>)> = Vec::new();
    for (label, target) in [
        ("tensor blob wire reference", None),
        ("tensor blob wire 32", Some(semr_target(32))),
    ] {
        let module = tensor_blob_wire_module(target);
        let blob = trust_ir::binary::serialize_module(&module).expect("blob wire");
        assert_eq!(
            header_version(&blob),
            trust_ir::binary::TENSOR_BLOB_FORMAT_VERSION,
            "{label}"
        );
        for cut in (0..blob.len()).step_by(3) {
            blobs.push((
                BlobKind::HeaderOrTrailerFault,
                format!("{label} cut {cut}"),
                blob[..cut].to_vec(),
            ));
        }
        let mut longer = blob.clone();
        longer.push(0);
        blobs.push((
            BlobKind::HeaderOrTrailerFault,
            format!("{label} + 0x00"),
            longer,
        ));
        one_byte_mutations(label, &blob, &mut blobs);
        blobs.push((BlobKind::Written, label.to_string(), blob));
    }
    let (rust_ok, equal) = judge_decodes(exe, &blobs, "tensor blob constants");
    assert!(equal >= 2 && rust_ok >= 2);
}

/// NEGATIVE CONTROL for the blob fixture theorems: a helper the executable
/// and the relation share, mutated — SHA-256's rotation by one bit too few,
/// each element's bytes read big-endian, the digest check dropped, the byte
/// count weakened to "at least" — no
/// longer kernel-checks SemR.lean, and every error is in the theorems that
/// pin those values (`sha256_vectors`, `blobVal_reads_and_refuses`).
#[test]
fn semr_tensor_blob_theorems_refuse_mutated_helpers() {
    run_lean_mutants(
        "tensor-blob-theorem-mutants",
        "SemR",
        (
            "SemR.lean",
            Some(&["sha256_vectors", "blobVal_reads_and_refuses"]),
        ),
        &[
            LeanMutant {
                name: "sha256-rotates-one-bit-short",
                file: "SemR.lean",
                from: "def shaRotr (x n : Nat) : Nat := Nat.lor (x >>> n) ((x <<< (32 - n)) % shaM)\n",
                to: "def shaRotr (x n : Nat) : Nat := Nat.lor (x >>> n) ((x <<< (31 - n)) % shaM)\n",
                times: 1,
            },
            LeanMutant {
                name: "tensor-blob-elements-big-endian",
                file: "SemR.lean",
                from: "  | n + 1, bs => leNat (bs.take w) :: leChunks w n (bs.drop w)\n",
                to: "  | n + 1, bs => leNat (bs.take w).reverse :: leChunks w n (bs.drop w)\n",
                times: 1,
            },
            LeanMutant {
                name: "tensor-blob-digest-unchecked",
                file: "SemR.lean",
                from: "    if sha256 bytes != d then tyR",
                to: "    if false then tyR",
                times: 1,
            },
            LeanMutant {
                name: "tensor-blob-byte-count-at-least",
                file: "SemR.lean",
                from: "n * w == bytes.length",
                to: "n * w ≤ bytes.length",
                times: 1,
            },
        ],
    );
}

/// NEGATIVE CONTROL for the blob runs: a helper the executable and the
/// relation share and no fixture theorem pins (the theorems hash one-block
/// messages at 8- and 16-bit elements) — SHA-256's padding for a message
/// whose length word spills into a second block, SHA-256 over every block
/// (cut to the first), the element width at the layout's pointer width (read
/// at 64 bits) — weakened, still kernel-checks, and only
/// the differential against the interpreter sees it: each mutant's
/// `semr_mutant_eval` disagrees with the interpreter on
/// `semr_tensor_blob_case`.
#[test]
fn semr_tensor_blob_differential_refuses_shared_helper_mutants() {
    let Oracle::Ready(_) = semr_oracle() else {
        return;
    };
    let Some(lake) = semr_lake() else {
        return;
    };
    let mutants: [(&str, &str, &str); 3] = [
        (
            "sha256-padding-without-the-spill-block",
            "List.replicate ((119 - msg.length % 64) % 64) 0",
            "List.replicate ((55 - msg.length % 64) % 64) 0",
        ),
        (
            "sha256-hashes-only-the-first-block",
            "  (shaBlocks (p.length / 64) shaH0 p).flatMap (beBytes 4)\n",
            "  (shaBlocks 1 shaH0 p).flatMap (beBytes 4)\n",
        ),
        (
            "tensor-blob-element-width-at-64-bits",
            "    let w := e.bytes m.pointerBits\n    let n := prodL dims\n",
            "    let w := e.bytes 64\n    let n := prodL dims\n",
        ),
    ];
    let cases = [
        semr_tensor_blob_case(None).0,
        semr_tensor_blob_case(Some(semr_target(32))).0,
    ];
    let scratch = SemrScratch::new("tensor-blob-mutants");
    let package = semr_package_files();
    for (name, from, to) in mutants {
        let dir = scratch.path(name);
        fs::create_dir_all(&dir).expect("mutant dir");
        for f in &package {
            fs::copy(semr_dir().join(f), dir.join(f)).unwrap_or_else(|e| panic!("copy {f}: {e}"));
        }
        let path = dir.join("SemR.lean");
        let src = fs::read_to_string(&path).expect("SemR source");
        assert_eq!(
            src.matches(from).count(),
            1,
            "mutant {name}: `{from}` must occur once"
        );
        fs::write(&path, src.replacen(from, to, 1)).expect("write mutant");
        let out = lake_build_command(&lake, &dir, "semr_mutant_eval")
            .output()
            .expect("run lake");
        assert!(
            out.status.success(),
            "mutant {name}: SemR must still build (only the differential can see it):\n{}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        let exe = dir.join(".lake/build/bin/semr_mutant_eval");
        let batches: Vec<Batch<'_>> = cases.iter().map(SemrCase::batch).collect();
        let t = tally(&semr_differential(&exe, &batches));
        assert!(
            !t.mismatches.is_empty(),
            "mutant {name}: the tensor blob differential saw no disagreement"
        );
        eprintln!("mutant {name}: {} disagreement(s)", t.mismatches.len());
        let _ = fs::remove_dir_all(&dir);
    }
}

/// A one-function module whose signature carries `ty` (identity).
fn tensor_signature_module(ty: Ty) -> Module {
    let b = MemBody::new(std::slice::from_ref(&ty));
    mem_module(
        "semr_tensor_signature",
        vec![(
            "tensor_identity",
            vec![ty.clone()],
            vec![ty],
            b.ret_param0(),
        )],
    )
}

/// The tensor's wire spelling has an explicit boundary in SemR's decoder: a
/// tensor module is written at exactly `TENSOR_FORMAT_VERSION` and decodes to
/// the module the Rust reader reads; the same bytes under the version before
/// are malformed in both (Ty tag 41 is not yet a type); a later version is
/// refused before its payload; and an element outside the integers is a
/// NAMED refusal (a float element waits on SemR's float model, PKG-U15),
/// although the Rust reader reads it.
#[test]
fn semr_tensor_wire_boundary_is_explicit() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let (case, _) = semr_tensor_case(None);
    let blob = trust_ir::binary::serialize_module(&case.module).expect("tensor wire");
    assert_eq!(
        header_version(&blob),
        trust_ir::binary::TENSOR_FORMAT_VERSION
    );
    assert_eq!(
        trust_ir::binary::deserialize_module(&blob).unwrap(),
        case.module
    );
    let old = relabelled(&blob, trust_ir::binary::TENSOR_FORMAT_VERSION - 1);
    assert!(trust_ir::binary::deserialize_module(&old).is_err());
    let future = relabelled(
        &blob,
        trust_ir::binary::FORMAT_VERSION
            .checked_add(1)
            .expect("wire format has an expressible future version"),
    );
    assert!(trust_ir::binary::deserialize_module(&future).is_err());
    let float =
        trust_ir::binary::serialize_module(&tensor_signature_module(tensor_ty(&Ty::F32, 2)))
            .expect("a float tensor has a wire spelling");
    let boolean =
        trust_ir::binary::serialize_module(&tensor_signature_module(tensor_ty(&Ty::Bool, 1)))
            .expect("a bool tensor has a wire spelling");
    for refused in [&float, &boolean] {
        assert!(trust_ir::binary::deserialize_module(refused).is_ok());
    }
    let verdicts = semr_decode(exe, &[blob, old, future, float, boolean]);
    assert_eq!(verdicts[0]["decoded"], semr_summary_of(&case.module));
    assert_eq!(
        verdicts[1..],
        [
            json!({"error": "decode: invalid Ty tag"}),
            json!({"unsupported": "wire_version"}),
            json!({"unsupported": "tensor.float_element"}),
            json!({"unsupported": "tensor.element"}),
        ]
    );
}

/// The decoder differential on tensor blobs: every third proper prefix, one
/// appended byte and every one-byte change of the tensor case's modules
/// (both layouts), judged against `deserialize_module` as
/// `semr_decoder_agrees_with_the_binary_reader_on_mutated_blobs` judges.
#[test]
fn semr_decoder_agrees_with_the_binary_reader_on_tensor_blobs() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let modules: Vec<SemrCase> = [None, Some(semr_target(32))]
        .into_iter()
        .map(|t| semr_tensor_case(t).0)
        .collect();
    let mut blobs: Vec<(BlobKind, String, Vec<u8>)> = Vec::new();
    for case in &modules {
        let blob = trust_ir::binary::serialize_module(&case.module).expect("tensor blob");
        let label = &case.label;
        for cut in (0..blob.len()).step_by(3) {
            blobs.push((
                BlobKind::HeaderOrTrailerFault,
                format!("{label} cut {cut}"),
                blob[..cut].to_vec(),
            ));
        }
        let mut longer = blob.clone();
        longer.push(0);
        blobs.push((
            BlobKind::HeaderOrTrailerFault,
            format!("{label} + 0x00"),
            longer,
        ));
        one_byte_mutations(label, &blob, &mut blobs);
        blobs.push((BlobKind::Written, label.clone(), blob));
    }
    let (rust_ok, equal) = judge_decodes(exe, &blobs, "tensor blobs");
    assert!(equal >= modules.len() && rust_ok >= modules.len());
}

/// NEGATIVE CONTROL for the tensor theorem: a contraction that drifts from
/// the loop nest (an accumulation that squares its left factor, a row-major
/// offset that drops its base, a result count checked one too late) no longer
/// kernel-checks `TensorContraction.lean`, and the failure is in the lemmas
/// that state the contraction's elements and its checks.
#[test]
fn semr_tensor_theorem_refuses_mutated_contractions() {
    run_lean_mutants(
        "tensor-theorem-mutants",
        "TensorContraction",
        (
            "TensorContraction.lean",
            Some(&[
                "contractElems_eq_loopNest",
                "evalContract_matmul",
                "tensor_matmul_eq_loopNest",
                "contractElems_matmul",
            ]),
        ),
        &[
            LeanMutant {
                name: "tensor-mac-squares-its-left-factor",
                file: "SemR.lean",
                from: "def macR (w acc x y : Nat) : Nat := (acc + (x * y) % modulus w) % modulus w",
                to: "def macR (w acc x y : Nat) : Nat := (acc + (x * x) % modulus w) % modulus w",
                times: 1,
            },
            LeanMutant {
                name: "tensor-free-axis-drops-its-base",
                file: "SemR.lean",
                from: "    | some t => getN o (base + t)\n",
                to: "    | some t => getN o t\n",
                times: 1,
            },
            LeanMutant {
                name: "tensor-count-check-admits-usize-max-plus-one",
                file: "SemR.lean",
                from: "    else if modulus pointerBits ≤ prodL (contractDims batch contract da db) then\n",
                to: "    else if modulus pointerBits < prodL (contractDims batch contract da db) then\n",
                times: 1,
            },
        ],
    );
}

/// What one MiniRust divergence probe pins: the verdict class both engines
/// reach, the text both UB messages contain (`None` unless UB), and
/// MiniRust's verdict on the same program, which SemR does not reach.
type DivergenceExpect = (&'static str, Option<&'static str>, &'static str);

/// The memory slice's MiniRust divergences (`lean/semr/SemR.lean`'s header
/// lists them), each a program both engines run to the verdict pinned here
/// and MiniRust does not: SemR follows the reference interpreter. Each probe
/// that both engines run to `Ok` sits beside a sibling that differs in one
/// instruction and is UB in both, so an engine that ran every probe to `Ok`
/// fails here.
fn semr_divergence_case() -> (SemrCase, Vec<DivergenceExpect>) {
    use trust_ir::inst::BinOp;
    let mut fns: Vec<(&str, Vec<Ty>, Vec<Ty>, trust_ir::Block)> = Vec::new();
    let mut expect: Vec<DivergenceExpect> = Vec::new();
    let p_i32 = || vec![Ty::I32];
    // 0-1: alignment by allocation order. A two-byte slot of `u8`s accessed
    //      at `u16` is aligned at 1024 and misaligned after a one-byte slot.
    //      MiniRust may place an align-1 slot at any address, so both are UB.
    for (name, behind) in [
        ("alloc_order_aligned", false),
        ("alloc_order_misaligned", true),
    ] {
        let mut b = MemBody::new(&p_i32());
        if behind {
            let _ = b.alloca(Ty::U8, None, None);
        }
        let two = b.konst(Ty::U64, 2);
        let p = b.alloca(Ty::U8, Some(two), None);
        let c = b.konst(Ty::U16, 0x1234);
        b.store(Ty::U16, p, c, false, None);
        let y = b.load(Ty::U16, p, false, None);
        fns.push((name, p_i32(), vec![Ty::U16], b.ret(vec![y])));
        expect.push(if behind {
            (
                "ub",
                Some("Store: pointer address 1025 is not aligned to 2"),
                "UB (an align-1 slot may sit at an odd address)",
            )
        } else {
            ("ok", None, "UB (an align-1 slot may sit at an odd address)")
        });
    }
    // 2-3: an integer loaded from uninitialized bytes. Copied to another slot
    //      it is fine in both engines; MiniRust's typed integer load is UB.
    //      Inspected, it is UB in both.
    for (name, inspect) in [("uninit_int_copied", false), ("uninit_int_inspected", true)] {
        let mut b = MemBody::new(&p_i32());
        let p = b.alloca(Ty::I32, None, None);
        let q = b.alloca(Ty::I32, None, None);
        let y = b.load(Ty::I32, p, false, None);
        b.store(Ty::I32, q, y, false, None);
        if inspect {
            let s = b.val(trust_ir::Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: y,
                rhs: b.param(0),
            });
            fns.push((name, p_i32(), vec![Ty::I32], b.ret(vec![s])));
            expect.push((
                "ub",
                Some("use of an uninitialized value"),
                "UB (at the load)",
            ));
        } else {
            fns.push((name, p_i32(), vec![Ty::I32], b.ret_param0()));
            expect.push(("ok", None, "UB (an integer load of uninitialized bytes)"));
        }
    }
    // 4-7: an `inbounds` GEP past its slot, and from a dead slot: a pointer in
    //      both engines; MiniRust's in-bounds offset is UB. Accessed, UB in
    //      both.
    for (name, dead, access) in [
        ("inbounds_gep_past_the_slot", false, false),
        ("inbounds_gep_past_the_slot_accessed", false, true),
        ("inbounds_gep_dead_slot", true, false),
        ("inbounds_gep_dead_slot_accessed", true, true),
    ] {
        let mut b = MemBody::new(&p_i32());
        let p = b.alloca(Ty::I32, None, None);
        if dead {
            b.dealloc(p);
        }
        let k = b.konst(Ty::I64, if dead { 0 } else { 1000 });
        let q = b.gep_inbounds(Ty::I32, p, vec![k]);
        if access {
            let y = b.load(Ty::I32, q, false, None);
            fns.push((name, p_i32(), vec![Ty::I32], b.ret(vec![y])));
            expect.push((
                "ub",
                Some(if dead {
                    "Load: use after dealloc"
                } else {
                    "is out of bounds for allocation size 4"
                }),
                "UB (at the GEP)",
            ));
        } else {
            fns.push((name, p_i32(), vec![Ty::I32], b.ret_param0()));
            expect.push(("ok", None, "UB (an in-bounds offset out of bounds)"));
        }
    }
    // 8-9: a callee's slot read after it returns (functions 10 and 11): `Return`
    //      frees nothing at level R; MiniRust frees a frame's locals there. A
    //      callee that deallocates its slot first is UB in both.
    for (name, callee) in [
        ("callee_slot_after_return", 10u32),
        ("callee_slot_freed_before_return", 11),
    ] {
        let mut b = MemBody::new(&p_i32());
        let r = b.val(trust_ir::Inst::Call {
            callee: FuncId::new(callee),
            args: vec![b.param(0)],
        });
        let y = b.load(Ty::I32, r, false, None);
        fns.push((name, p_i32(), vec![Ty::I32], b.ret(vec![y])));
        expect.push(if callee == 10 {
            (
                "ok",
                None,
                "UB (the callee's local is dead after its return)",
            )
        } else {
            (
                "ub",
                Some("Load: use after dealloc"),
                "UB (the callee's local is dead)",
            )
        });
    }
    // 10-11: the callees: a slot written with the argument, its address
    //        returned (11 deallocates it first).
    for (name, free) in [("slot_returned", false), ("slot_freed_and_returned", true)] {
        let mut b = MemBody::new(&p_i32());
        let p = b.alloca(Ty::I32, None, None);
        b.store(Ty::I32, p, b.param(0), false, None);
        if free {
            b.dealloc(p);
        }
        fns.push((name, p_i32(), vec![Ty::Ptr], b.ret(vec![p])));
        expect.push(("skip", None, ""));
    }
    // 12-13: a dead, misaligned pointer: both engines name the use after
    //        `Dealloc` (the interpreter checks liveness first), MiniRust the
    //        misalignment (it checks alignment first). Live, both name the
    //        misalignment.
    for (name, dead) in [
        ("dead_and_misaligned", true),
        ("live_and_misaligned", false),
    ] {
        let mut b = MemBody::new(&p_i32());
        let p = b.alloca(Ty::I64, None, None);
        let one = b.konst(Ty::I64, 1);
        let q = b.gep(Ty::I8, p, vec![one]);
        if dead {
            b.dealloc(p);
        }
        let y = b.load(Ty::I32, q, false, None);
        fns.push((name, p_i32(), vec![Ty::I32], b.ret(vec![y])));
        expect.push(if dead {
            (
                "ub",
                Some("Load: use after dealloc"),
                "UB, named as the misalignment",
            )
        } else {
            (
                "ub",
                Some("Load: pointer address 1025 is not aligned to 4"),
                "UB, named as the misalignment",
            )
        });
    }
    let module = mem_module("semr_memory_divergences", fns);
    let runs: Vec<(FuncId, Vec<InterpretValue>)> = module
        .functions
        .iter()
        .zip(&expect)
        .filter(|(_, e)| e.0 != "skip")
        .map(|(f, _)| (f.id, vec![i32_arg(-123_456)]))
        .collect();
    let expect = expect.into_iter().filter(|e| e.0 != "skip").collect();
    (
        SemrCase {
            label: "memory divergences".into(),
            module,
            runs,
        },
        expect,
    )
}

/// RM4c review fix: every place the memory slice's verdict is the
/// interpreter's and not MiniRust's, pinned through both engines — the
/// verdict class, the UB reason, and the value an `Ok` returns — so a
/// divergence cannot move (or vanish into agreement with MiniRust) unseen;
/// `SemR.lean`'s header names each one.
#[test]
fn semr_memory_minirust_divergences_are_pinned() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let (case, expect) = semr_divergence_case();
    let batch = case.batch();
    let reports = semr_differential(exe, std::slice::from_ref(&batch));
    assert_eq!(reports.len(), expect.len());
    let mut failures = Vec::new();
    let mut ok = 0;
    for (r, (class, reason, minirust)) in reports.iter().zip(&expect) {
        let fname = &case.module.functions[r.func.0 as usize].name;
        eprintln!(
            "  {fname}: rust {:?}; semr {:?}; MiniRust: {minirust}",
            r.rust, r.lean
        );
        if r.comparison != Comparison::Agree {
            failures.push(format!("{fname}: {:?}", r.comparison));
            continue;
        }
        if r.rust.class() != *class {
            failures.push(format!("{fname}: {}, expected {class}", r.rust.class()));
        }
        if let Some(reason) = reason {
            for (side, v) in [("rust", &r.rust), ("semr", &r.lean)] {
                match v {
                    Verdict::Ub(m) if m.contains(reason) => {}
                    other => failures.push(format!(
                        "{fname}: {side} {other:?} does not name `{reason}`"
                    )),
                }
            }
        }
        if let Verdict::Ok(vals) = &r.rust {
            ok += 1;
            let want = match fname.as_str() {
                "alloc_order_aligned" => Val::Int {
                    width: 16,
                    raw: 0x1234,
                },
                _ => Val::Int {
                    width: 32,
                    raw: u128::from((-123_456i32) as u32),
                },
            };
            if vals.as_slice() != [want.clone()] {
                failures.push(format!("{fname}: returned {vals:?}, expected {want:?}"));
            }
        }
    }
    assert_eq!(ok, 5, "five probes run to Ok in both engines");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The memory types the generator lays out (`Alloca`, `GEP`) and accesses.
const MEM_LAYOUT_TYS: [Ty; 14] = [
    Ty::I8,
    Ty::U8,
    Ty::I16,
    Ty::U16,
    Ty::I32,
    Ty::U32,
    Ty::I64,
    Ty::U64,
    Ty::I128,
    Ty::U128,
    Ty::Isize,
    Ty::Usize,
    Ty::Bool,
    Ty::Unit,
];

const MEM_ACCESS_TYS: [Ty; 13] = [
    Ty::I8,
    Ty::U8,
    Ty::I16,
    Ty::U16,
    Ty::I32,
    Ty::U32,
    Ty::I64,
    Ty::U64,
    Ty::I128,
    Ty::U128,
    Ty::Isize,
    Ty::Usize,
    Ty::Bool,
];

/// One of `xs`, uniformly.
fn pick_ty(rng: &mut Rng, xs: &[Ty]) -> Ty {
    xs[rng.bounded(xs.len() as u32) as usize].clone()
}

/// A constant of `ty` that the generator's arithmetic and indices draw from:
/// small, occasionally an edge (0, the maximum, the sign bit).
fn mem_const(rng: &mut Rng, ty: &Ty) -> i128 {
    if *ty == Ty::Bool {
        return i128::from(rng.bool());
    }
    let (bits, signed) = match ty {
        Ty::I8 => (8, true),
        Ty::U8 => (8, false),
        Ty::I16 => (16, true),
        Ty::U16 => (16, false),
        Ty::I32 => (32, true),
        Ty::U32 => (32, false),
        Ty::I64 | Ty::Isize => (64, true),
        Ty::U64 | Ty::Usize => (64, false),
        Ty::I128 => (128, true),
        _ => (127, false),
    };
    match rng.bounded(10) {
        0 => 0,
        1 if signed => -1,
        1 => (1i128 << (bits - 1).min(126)) - 1,
        2 if signed => -(1i128 << (bits - 1).min(126)),
        _ => rng.small(),
    }
}

/// One generated memory function: a few slots (some counted, some
/// over-aligned, some zero-sized), then stores, loads, `GEP`s and
/// `Dealloc`s through them in a random order, the arithmetic of what was
/// read, and one returned value. Most accesses go through a pointer at the
/// slot's own element type and an index inside it, so a run often executes to
/// the end; the rest stop at undefined behaviour of every kind the slice has.
fn gen_mem_fn(rng: &mut Rng, ret_ty: Ty) -> (Vec<Ty>, trust_ir::Block) {
    use trust_ir::inst::BinOp;
    type V = trust_ir::value::ValueId;
    let params = vec![Ty::I32, Ty::U8, Ty::I64];
    let mut b = MemBody::new(&params);
    let mut vals: Vec<(V, Ty)> = b.params.clone();
    // A pointer, the element type it was made at, and the elements past it
    // that its slot holds (when known).
    let mut ptrs: Vec<(V, Ty, u32)> = Vec::new();
    let mut bases: Vec<V> = Vec::new();
    let mut stored: Vec<(V, Ty)> = Vec::new();
    let pick_val = |rng: &mut Rng, vals: &Vec<(V, Ty)>, ty: &Ty| {
        let same: Vec<V> = vals
            .iter()
            .filter(|(_, t)| t == ty)
            .map(|(v, _)| *v)
            .collect();
        if same.is_empty() || rng.bounded(5) == 0 {
            None
        } else {
            Some(same[rng.bounded(same.len() as u32) as usize])
        }
    };
    let n_slots = 1 + rng.bounded(3);
    for _ in 0..n_slots {
        let ty = if rng.bounded(4) == 0 {
            pick_ty(rng, &MEM_LAYOUT_TYS)
        } else {
            pick_ty(rng, &MEM_ACCESS_TYS)
        };
        let (count, n) = match rng.bounded(8) {
            0 | 1 => {
                let cty = pick_ty(rng, &[Ty::U64, Ty::I32, Ty::U8, Ty::Usize]);
                let n = match rng.bounded(16) {
                    0 => 0,
                    1 if cty == Ty::I32 => -2,
                    _ => 1 + i128::from(rng.bounded(4)),
                };
                (Some(b.konst(cty, n)), n.max(0) as u32)
            }
            _ => (None, 1),
        };
        let align = match rng.bounded(12) {
            0 => Some(rng.one_of(&[1u64, 2, 4, 8, 16, 32])),
            1 if rng.bounded(4) == 0 => Some(rng.one_of(&[0u64, 3, 6])),
            _ => None,
        };
        let p = b.alloca(ty.clone(), count, align);
        ptrs.push((p, ty, n));
        bases.push(p);
    }
    let n_ops = 4 + rng.bounded(14);
    for _ in 0..n_ops {
        match rng.bounded(20) {
            // store
            0..=5 => {
                let (p, pty, _) = ptrs[rng.bounded(ptrs.len() as u32) as usize].clone();
                let ty = if pty != Ty::Unit && rng.bounded(4) != 0 {
                    pty
                } else {
                    pick_ty(rng, &MEM_ACCESS_TYS)
                };
                let v = match pick_val(rng, &vals, &ty) {
                    Some(v) if rng.bounded(12) != 0 => v,
                    _ => {
                        if rng.bounded(40) == 0 {
                            // the wrong type: a type error on both sides
                            vals[rng.bounded(vals.len() as u32) as usize].0
                        } else {
                            let c = mem_const(rng, &ty);
                            b.konst(ty.clone(), c)
                        }
                    }
                };
                let vol = rng.bounded(8) == 0;
                let align = if rng.bounded(16) == 0 {
                    Some(rng.one_of(&[1u64, 2, 4, 8, 16]))
                } else {
                    None
                };
                b.store(ty.clone(), p, v, vol, align);
                stored.push((p, ty));
            }
            // load (mostly of what was stored)
            6..=11 => {
                let (p, ty) = if !stored.is_empty() && rng.bounded(5) != 0 {
                    let (p, ty) = stored[rng.bounded(stored.len() as u32) as usize].clone();
                    if rng.bounded(5) == 0 {
                        (p, pick_ty(rng, &MEM_ACCESS_TYS))
                    } else {
                        (p, ty)
                    }
                } else {
                    let (p, pty, _) = ptrs[rng.bounded(ptrs.len() as u32) as usize].clone();
                    let ty = if pty != Ty::Unit && rng.bounded(3) != 0 {
                        pty
                    } else {
                        pick_ty(rng, &MEM_ACCESS_TYS)
                    };
                    (p, ty)
                };
                let vol = rng.bounded(8) == 0;
                let align = if rng.bounded(16) == 0 {
                    Some(rng.one_of(&[1u64, 2, 4, 8]))
                } else {
                    None
                };
                let v = b.load(ty.clone(), p, vol, align);
                vals.push((v, ty));
            }
            // gep: mostly an element of the base's own slot
            12..=15 => {
                let (base, bty, n) = ptrs[rng.bounded(ptrs.len() as u32) as usize].clone();
                if rng.bounded(3) != 0 && n > 0 {
                    let ity = pick_ty(rng, &[Ty::I64, Ty::U64, Ty::Usize, Ty::I32]);
                    let i = rng.bounded(n);
                    let idx = b.konst(ity, i128::from(i));
                    let q = b.gep(bty.clone(), base, vec![idx]);
                    ptrs.push((q, bty, n - i));
                } else {
                    let ty = pick_ty(rng, &MEM_LAYOUT_TYS);
                    let n_idx = 1 + rng.bounded(2);
                    let mut idx = Vec::new();
                    for _ in 0..n_idx {
                        let ity = pick_ty(rng, &[Ty::I64, Ty::U64, Ty::I32, Ty::U8, Ty::Usize]);
                        let i = match rng.bounded(16) {
                            0 if matches!(ity, Ty::I64 | Ty::I32) => -1,
                            1 if matches!(ity, Ty::U64 | Ty::Usize) => i128::from(u64::MAX),
                            _ => i128::from(rng.bounded(4)),
                        };
                        idx.push(b.konst(ity, i));
                    }
                    let q = b.gep(ty.clone(), base, idx);
                    ptrs.push((q, ty, 0));
                }
            }
            // dealloc (mostly a slot's base)
            16 => {
                if rng.bounded(3) == 0 {
                    let p = if rng.bounded(4) == 0 {
                        ptrs[rng.bounded(ptrs.len() as u32) as usize].0
                    } else {
                        bases[rng.bounded(bases.len() as u32) as usize]
                    };
                    b.dealloc(p);
                }
            }
            // arithmetic on what was read (poison inspected is UB)
            17 | 18 => {
                let (x, ty) = vals[rng.bounded(vals.len() as u32) as usize].clone();
                if ty != Ty::Bool {
                    let y = match pick_val(rng, &vals, &ty) {
                        Some(y) => y,
                        None => {
                            let c = mem_const(rng, &ty);
                            b.konst(ty.clone(), c)
                        }
                    };
                    let op = rng.one_of(&[BinOp::Add, BinOp::Xor, BinOp::Sub]);
                    let s = b.val(trust_ir::Inst::BinOp {
                        op,
                        ty: ty.clone(),
                        lhs: x,
                        rhs: y,
                    });
                    vals.push((s, ty));
                }
            }
            // a copy (poison moves)
            _ => {
                let (x, ty) = vals[rng.bounded(vals.len() as u32) as usize].clone();
                let c = b.val(trust_ir::Inst::Copy {
                    ty: ty.clone(),
                    operand: x,
                });
                vals.push((c, ty));
            }
        }
    }
    let r = if ret_ty == Ty::Ptr {
        ptrs[rng.bounded(ptrs.len() as u32) as usize].0
    } else {
        // the latest value of the return type (a loaded one, most often)
        match vals.iter().rev().find(|(_, t)| *t == ret_ty) {
            Some((v, _)) => *v,
            None => {
                let c = mem_const(rng, &ret_ty);
                b.konst(ret_ty.clone(), c)
            }
        }
    };
    (params, b.ret(vec![r]))
}

/// The generated memory corpus: `seeds` modules of four functions each.
/// A memory corpus: modules, each with its runs.
type MemCorpus = Vec<(Module, Vec<(FuncId, Vec<InterpretValue>)>)>;

fn mem_corpus(seeds: std::ops::Range<u64>) -> MemCorpus {
    seeds
        .map(|seed| {
            let mut rng = Rng::new(0x4D45_4D00 ^ seed.wrapping_mul(0x9E37_79B9));
            let mut fns = Vec::new();
            for i in 0..4 {
                let ret = pick_ty(
                    &mut rng,
                    &[
                        Ty::I32,
                        Ty::U8,
                        Ty::I64,
                        Ty::U16,
                        Ty::Bool,
                        Ty::Ptr,
                        Ty::U128,
                    ],
                );
                let (params, block) = gen_mem_fn(&mut rng, ret.clone());
                fns.push((["f0", "f1", "f2", "f3"][i], params, vec![ret], block));
            }
            let module = mem_module(&format!("semr_mem_{seed}"), fns);
            let mut arg_rng = Rng::new(seed ^ 0x5A5A);
            let runs = (0..4u32)
                .map(|f| {
                    let args = vec![
                        InterpretValue::int(Ty::I32, i128::from(arg_rng.next_u64() as i32))
                            .expect("i32"),
                        InterpretValue::int(Ty::U8, i128::from(arg_rng.next_u64() as u8))
                            .expect("u8"),
                        InterpretValue::int(Ty::I64, i128::from(arg_rng.next_u64() as i64 % 1000))
                            .expect("i64"),
                    ];
                    (FuncId::new(f), args)
                })
                .collect();
            (module, runs)
        })
        .collect()
}

/// Seeds of the generated memory corpus (four runs each).
const SEMR_MEM_SEEDS: std::ops::Range<u64> = 0..10000;

/// The memory corpus's runs SemR refused by name, per feature, measured
/// 2026-10-29 over the 40,000 runs of `SEMR_MEM_SEEDS` (agreed: 10,440 `ok`,
/// 26,304 `ub`, 2,736 type errors; 0 mismatches): a `Bool` loaded from a byte
/// other than 0 or 1 (`mem.bool_byte`; the interpreter reads it as `true`,
/// MiniRust calls it UB, and SemR takes neither side). The ledger may only
/// go down.
const SEMR_MEM_UNSUPPORTED_LEDGER: &[(&str, usize)] = &[("semr:mem.bool_byte", 520)];

/// RM4c's accept item: 0 disagreements between SemR and the interpreter over
/// the generated memory corpus, UB matched by reason, refusals ratcheted.
#[test]
fn semr_generated_memory_corpus_agrees_with_the_interpreter() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let corpus = mem_corpus(SEMR_MEM_SEEDS);
    let batches: Vec<Batch<'_>> = corpus
        .iter()
        .enumerate()
        .map(|(i, (module, runs))| Batch {
            label: format!("memory seed {i}"),
            module,
            runs: runs.clone(),
        })
        .collect();
    let reports = semr_differential(exe, &batches);
    let mut reasons: BTreeMap<String, usize> = BTreeMap::new();
    for r in &reports {
        if let (Comparison::Agree, Verdict::Ub(m)) = (&r.comparison, &r.rust) {
            let key: String = semr_ub_reason(m)
                .chars()
                .map(|c| if c.is_ascii_digit() { '#' } else { c })
                .collect();
            *reasons.entry(key).or_default() += 1;
        }
    }
    let t = tally(&reports);
    eprintln!(
        "SemR memory corpus: agreed {:?}, refused {:?}",
        t.agreed, t.unsupported
    );
    for (k, n) in &reasons {
        eprintln!("  ub {n:>6}  {k}");
    }
    assert_no_mismatch(&t, "SemR, generated memory corpus");
    let ok = t.agreed.get("ok").copied().unwrap_or(0);
    let ub = t.agreed.get("ub").copied().unwrap_or(0);
    assert!(
        ok > 10_000,
        "only {ok} memory runs executed to Ok in both engines"
    );
    assert!(
        ub > 25_000,
        "only {ub} memory runs reached UB in both engines"
    );
    for reason in [
        "Load: use after dealloc",
        "Store: use after dealloc",
        "Dealloc: allocation is already dead",
        "Dealloc: pointer must reference allocation base",
        "poison at signature boundary",
        "poison at integer use",
    ] {
        assert!(
            reasons.contains_key(reason),
            "no run reached `{reason}`: {reasons:?}"
        );
    }
    for prefix in [
        "Load: access [",
        "Store: access [",
        "Load: pointer address #",
        "Store: pointer address #",
        "Load: reading uninitialized byte",
    ] {
        assert!(
            reasons.keys().any(|k| k.starts_with(prefix)),
            "no run reached `{prefix}…`: {reasons:?}"
        );
    }
    let want: BTreeMap<String, usize> = SEMR_MEM_UNSUPPORTED_LEDGER
        .iter()
        .map(|(k, n)| (k.to_string(), *n))
        .collect();
    assert_eq!(t.unsupported, want, "SemR memory coverage RATCHET");
}

/// The decoder differential on memory modules: every proper prefix, an
/// appended byte and every one-byte change of the memory case's blob and of
/// generated memory modules' (the `Load`/`Store` volatile flag and optional
/// alignment, the `Alloca` count tag, the `GEP` index list and `inbounds`
/// byte among the bytes changed), judged as on the scalar corpus.
#[test]
fn semr_decoder_agrees_with_the_binary_reader_on_memory_blobs() {
    let Oracle::Ready(exe) = semr_oracle() else {
        return;
    };
    let (case, _) = semr_memory_case();
    let mut modules = vec![("memory case".to_string(), case.module.clone())];
    for (i, (m, _)) in mem_corpus(0..3).into_iter().enumerate() {
        modules.push((format!("memory seed {i}"), m));
    }
    let mut blobs: Vec<(BlobKind, String, Vec<u8>)> = Vec::new();
    for (label, module) in &modules {
        let blob = trust_ir::binary::serialize_module(module).expect("memory blob");
        for cut in (0..blob.len()).step_by(3) {
            blobs.push((
                BlobKind::HeaderOrTrailerFault,
                format!("{label} cut {cut}"),
                blob[..cut].to_vec(),
            ));
        }
        let mut longer = blob.clone();
        longer.push(0);
        blobs.push((
            BlobKind::HeaderOrTrailerFault,
            format!("{label} + 0x00"),
            longer,
        ));
        one_byte_mutations(label, &blob, &mut blobs);
        blobs.push((BlobKind::Written, label.clone(), blob));
    }
    let (rust_ok, equal) = judge_decodes(exe, &blobs, "memory blobs");
    assert!(equal >= modules.len() && rust_ok >= modules.len());
}

/// NEGATIVE CONTROL for the memory step: an executable memory piece that
/// drifts from the relation's memory rules (a liveness, bounds or alignment
/// check dropped, an allocation that reuses an id or does not move the bump
/// pointer, a `Dealloc` that leaves the slot live or frees through an
/// interior pointer, a store at the wrong offset, a volatile load that reads
/// poison, a `GEP` that drops the base's offset) no longer kernel-checks, and
/// the failure is in the theorems that tie the two.
#[test]
fn semr_memory_step_refuses_mutated_executables() {
    run_lean_mutants(
        "memory-step-mutants",
        "SemR",
        ("SemR.lean", Some(SEMR_STEP_THEOREMS)),
        &[
            LeanMutant {
                name: "access-skips-the-liveness-check",
                file: "SemR.lean",
                from: "  if al.live then\n    if decide (addrSpace ≤ al.base + o)",
                to: "  if true then\n    if decide (addrSpace ≤ al.base + o)",
                times: 1,
            },
            LeanMutant {
                name: "access-skips-the-bounds-check",
                file: "SemR.lean",
                from: "else if decide (al.size < o + size) then",
                to: "else if false then",
                times: 1,
            },
            LeanMutant {
                name: "access-skips-the-alignment-check",
                file: "SemR.lean",
                from: "else if (al.base + o) % align != 0 then",
                to: "else if false then",
                times: 1,
            },
            LeanMutant {
                name: "alloca-reuses-allocation-zero",
                file: "SemR.lean",
                from: "      node [.ptr k.mem.allocs.length 0]",
                to: "      node [.ptr 0 0]",
                times: 1,
            },
            LeanMutant {
                name: "alloca-does-not-bump",
                file: "SemR.lean",
                from: "                 nextAddr := alignUp k.mem.nextAddr align + max size 1 } }\n      node",
                to: "                 nextAddr := k.mem.nextAddr } }\n      node",
                times: 1,
            },
            LeanMutant {
                name: "dealloc-leaves-the-slot-live",
                file: "SemR.lean",
                from: "bindResults { next k with mem := { k.mem with allocs := setNth k.mem.allocs a { al with live := false } } }",
                to: "bindResults { next k with mem := { k.mem with allocs := setNth k.mem.allocs a { al with live := true } } }",
                times: 1,
            },
            LeanMutant {
                name: "dealloc-frees-through-an-interior-pointer",
                file: "SemR.lean",
                from: "  match o != 0 with\n  | true => ubR \"Dealloc: pointer must reference allocation base\"",
                to: "  match false with\n  | true => ubR \"Dealloc: pointer must reference allocation base\"",
                times: 1,
            },
            LeanMutant {
                name: "store-writes-at-the-base",
                file: "SemR.lean",
                from: "  let a ← accessAt k.mem \"Store\" ao.1 ao.2 size align\n  bindResults { next k with mem := written k.mem ao.1 ao.2 a bs } node []",
                to: "  let a ← accessAt k.mem \"Store\" ao.1 ao.2 size align\n  bindResults { next k with mem := written k.mem ao.1 0 a bs } node []",
                times: 1,
            },
            LeanMutant {
                name: "volatile-load-reads-poison",
                file: "SemR.lean",
                from: "    if vol then ubR s!\"Load: reading uninitialized byte",
                to: "    if false then ubR s!\"Load: reading uninitialized byte",
                times: 1,
            },
            LeanMutant {
                name: "gep-drops-the-base-offset",
                file: "SemR.lean",
                from: "\n    else bindResults (next k) node [.ptr a (o + d)]",
                to: "\n    else bindResults (next k) node [.ptr a d]",
                times: 1,
            },
            LeanMutant {
                name: "gep-skips-target-address-checks",
                file: "SemR.lean",
                from: "    if pointerBits != 64 then",
                to: "    if false then",
                times: 1,
            },
            LeanMutant {
                name: "allocation-skips-target-address-check",
                file: "SemR.lean",
                from: "  else if decide (2 ^ pointerBits < alignUp k.mem.nextAddr align + max size 1) then",
                to: "  else if false then",
                times: 1,
            },
        ],
    );
}

/// NEGATIVE CONTROL for the memory corpus: a memory helper the executable and
/// the relation SHARE (the byte image of an integer, the scaling of a `GEP`
/// index, the rounding of a slot's address, the window a load reads, the
/// positivity of an `Alloca` count, the bytes poison stores; and, from the
/// RM4c review, a pointer's layout, a count wider than `u64`, poison and
/// partial bytes stored at another type, a slot ending at `2^64`, the byte of
/// `true`), mutated, still kernel-checks — the relation moves with it — and
/// only the differential against the interpreter sees it: each mutant's
/// `semr_mutant_eval` disagrees with the interpreter on the memory case or
/// the first generated memory seeds. It shares production's exact I/O driver
/// while the named memory-law controls separately require kernel rejection.
#[test]
fn semr_memory_differential_refuses_shared_helper_mutants() {
    let Oracle::Ready(_) = semr_oracle() else {
        return;
    };
    let Some(lake) = semr_lake() else {
        return;
    };
    let mutants: [(&str, &str, &str, usize); 19] = [
        (
            "integers-stored-big-end-first",
            "  | n + 1, x => .init (x % 256) :: leBytes n (x / 256)",
            "  | n + 1, x => .init ((x / 256 ^ n) % 256) :: leBytes n x",
            1,
        ),
        (
            "gep-ignores-the-element-size",
            "    else gepDelta pointerBits esize vs (d + esize * a)",
            "    else gepDelta pointerBits esize vs (d + a)",
            1,
        ),
        (
            "slot-address-rounds-down",
            "def alignUp (x a : Nat) : Nat := (x + (a - 1)) - (x + (a - 1)) % a",
            "def alignUp (x a : Nat) : Nat := x - x % a",
            1,
        ),
        (
            "load-reads-one-byte-late",
            "  | o, n + 1 => byteAt d o :: readBytes d (o + 1) n",
            "  | o, n + 1 => byteAt d (o + 1) :: readBytes d (o + 2) n",
            1,
        ),
        (
            "alloca-count-zero-allowed",
            "    if a == 0 || (t.signed && isNeg (t.bits pointerBits) a) then ubR \"Alloca: count must be positive\"",
            "    if (t.signed && isNeg (t.bits pointerBits) a) then ubR \"Alloca: count must be positive\"",
            1,
        ),
        (
            "poison-stores-zeros",
            "    else do expectTy pointerBits v ty; pure (uninitBytes size)",
            "    else do expectTy pointerBits v ty; pure (leBytes size 0)",
            1,
        ),
        // RM4c review: the gaps the fresh-seed review found, each now caught by
        // a hand case (45-52 of `semr_memory_case`). A relation-and-executable
        // pair is replaced everywhere it occurs (the last field), so the
        // relation moves with the executable and only the differential sees
        // it.
        (
            "pointer-layout-is-four-bytes",
            "  | .ptr => .ok (pointerBits / 8, pointerBits / 8)",
            "  | .ptr => .ok (4, 4)",
            1,
        ),
        (
            "alloca-count-wider-than-u64-accepted",
            "else if addrSpace ≤ a then ubR s!\"Alloca: count {decStr a} does not fit u64\"",
            "else if false then ubR s!\"Alloca: count {decStr a} does not fit u64\"",
            1,
        ),
        (
            "poison-stored-at-any-type",
            "    else do expectTy pointerBits v ty; pure (uninitBytes size)",
            "    else pure (uninitBytes size)",
            1,
        ),
        (
            "partial-bytes-stored-at-any-type",
            "      expectTy pointerBits v ty\n      if bs.length == size",
            "      if bs.length == size",
            1,
        ),
        (
            "slot-may-end-at-2-64",
            "decide (addrSpace ≤ alignUp k.mem.nextAddr align + max size 1)",
            "decide (addrSpace < alignUp k.mem.nextAddr align + max size 1)",
            5,
        ),
        (
            "bool-true-stored-as-two",
            "  | .bool b => .ok [.init (b2n b)]",
            "  | .bool b => .ok [.init (2 * b2n b)]",
            1,
        ),
        (
            "pointer-sized-integer-bytes-ignore-target",
            "| .isize | .usize => pointerBits / 8",
            "| .isize | .usize => 8",
            1,
        ),
        (
            "integer-encoding-ignores-target",
            "  | .int t a => .ok (leBytes (t.bytes pointerBits) a)",
            "  | .int t a => .ok (leBytes (t.bytes 64) a)",
            1,
        ),
        (
            "count-sign-ignores-target",
            "if a == 0 || (t.signed && isNeg (t.bits pointerBits) a) then",
            "if a == 0 || (t.signed && isNeg (t.bits 64) a) then",
            1,
        ),
        (
            "gep-sign-ignores-target",
            "if t.signed && isNeg (t.bits pointerBits) a then ubR s!\"GEP: negative index",
            "if t.signed && isNeg (t.bits 64) a then ubR s!\"GEP: negative index",
            1,
        ),
        (
            "allocation-target-end-off-by-one",
            "decide (2 ^ pointerBits < alignUp k.mem.nextAddr align + max size 1)",
            "decide (2 ^ pointerBits ≤ alignUp k.mem.nextAddr align + max size 1)",
            4,
        ),
        (
            "count-limited-to-target-width",
            "else if addrSpace ≤ a then ubR s!\"Alloca: count",
            "else if 2 ^ pointerBits ≤ a then ubR s!\"Alloca: count",
            1,
        ),
        (
            "index-limited-to-target-width",
            "else if addrSpace ≤ a then ubR s!\"GEP: index",
            "else if 2 ^ pointerBits ≤ a then ubR s!\"GEP: index",
            1,
        ),
    ];
    let (case, _) = semr_memory_case();
    let (target32, _) = semr_target_memory_case(32);
    let (target64, _) = semr_target_memory_case(64);
    let corpus = mem_corpus(0..200);
    let scratch = SemrScratch::new("memory-mutants");
    let package = semr_package_files();
    for (name, from, to, times) in mutants {
        let dir = scratch.path(name);
        fs::create_dir_all(&dir).expect("mutant dir");
        for f in &package {
            fs::copy(semr_dir().join(f), dir.join(f)).unwrap_or_else(|e| panic!("copy {f}: {e}"));
        }
        let path = dir.join("SemR.lean");
        let src = fs::read_to_string(&path).expect("SemR source");
        assert_eq!(
            src.matches(from).count(),
            times,
            "mutant {name}: `{from}` must occur {times} time(s)"
        );
        fs::write(&path, src.replace(from, to)).expect("write mutant");
        let out = lake_build_command(&lake, &dir, "semr_mutant_eval")
            .output()
            .expect("run lake");
        assert!(
            out.status.success(),
            "mutant {name}: SemR must still build (only the differential can see it):\n{}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        let exe = dir.join(".lake/build/bin/semr_mutant_eval");
        let mut batches = vec![case.batch(), target32.batch(), target64.batch()];
        batches.extend(corpus.iter().enumerate().map(|(i, (module, runs))| Batch {
            label: format!("memory seed {i}"),
            module,
            runs: runs.clone(),
        }));
        let t = tally(&semr_differential(&exe, &batches));
        assert!(
            !t.mismatches.is_empty(),
            "mutant {name}: the memory differential saw no disagreement"
        );
        eprintln!("mutant {name}: {} disagreement(s)", t.mismatches.len());
        let _ = fs::remove_dir_all(&dir);
    }
}

/// SHA-256 of `lean/semr/SemRMemory.lean` (the memory slice's laws and its
/// MiniRust byte representation). Clean's `semr_reference.rs` pins its fixture
/// copy's digest to the same value.
const SEMR_MEMORY_SHA256: &str = "76ae6a87c7140e2afde71a18bb5a7e7597b58370c0af48989e5ee59cf8992577";

/// The memory laws' source is the one Clean re-checks (no `lake` needed).
#[test]
fn semr_memory_laws_source_is_pinned() {
    let path = semr_dir().join("SemRMemory.lean");
    let bytes = fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    assert_eq!(
        sha256_hex(&bytes),
        SEMR_MEMORY_SHA256,
        "lean/semr/SemRMemory.lean changed: update SEMR_MEMORY_SHA256 here and Clean's fixture \
         copy and its pin in crates/clean-olean/tests/semr_reference.rs together"
    );
}

/// The kernel builds the memory laws (Lean 4.30; `lake build SemRMemory`):
/// load after store, disjoint stores, use after `StorageDead`, and the
/// MiniRust byte representation of every integer type.
#[test]
fn semr_memory_laws_kernel_check() {
    let Some(lake) = semr_lake() else {
        return;
    };
    let dir = semr_dir();
    let out = lake_build_command(&lake, &dir, "SemRMemory")
        .output()
        .unwrap_or_else(|e| panic!("cannot run {}: {e}", lake.display()));
    assert!(
        out.status.success(),
        "`lake build SemRMemory` failed in {}:\n{}\n{}",
        dir.display(),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}

/// NEGATIVE CONTROL for the memory laws: a byte or encoding helper the
/// executable and the relation share (so `step_sound`/`step_complete` move
/// with it), mutated — integers stored big end first, a store that skips a
/// byte, a load one byte late, the wrong little-endian weight, a `Bool` byte
/// `1` read as `false`, a written prefix padded with zeros, and (RM4c review)
/// an alignment of 0 accepted, a slot's address rounded down — no longer
/// kernel-checks against the laws (`SemRMemory.lean`), and SemR itself still
/// builds: every error is in the laws' file.
#[test]
fn semr_memory_laws_refuse_mutated_helpers() {
    run_lean_mutants(
        "memory-law-mutants",
        "SemRMemory",
        ("SemRMemory.lean", None),
        &[
            LeanMutant {
                name: "integers-stored-big-end-first",
                file: "SemR.lean",
                from: "  | n + 1, x => .init (x % 256) :: leBytes n (x / 256)",
                to: "  | n + 1, x => .init ((x / 256 ^ n) % 256) :: leBytes n x",
                times: 1,
            },
            LeanMutant {
                name: "store-skips-a-byte",
                file: "SemR.lean",
                from: "  | d, o, b :: bs => writeBytes (setByte d o b) (o + 1) bs",
                to: "  | d, o, b :: bs => writeBytes (setByte d o b) (o + 2) bs",
                times: 1,
            },
            LeanMutant {
                name: "load-reads-one-byte-late",
                file: "SemR.lean",
                from: "  | o, n + 1 => byteAt d o :: readBytes d (o + 1) n",
                to: "  | o, n + 1 => byteAt d (o + 1) :: readBytes d (o + 2) n",
                times: 1,
            },
            LeanMutant {
                name: "little-endian-weights-255",
                file: "SemR.lean",
                from: "  | .init b :: bs => b + 256 * fromLE bs",
                to: "  | .init b :: bs => b + 255 * fromLE bs",
                times: 1,
            },
            LeanMutant {
                name: "bool-byte-one-is-false",
                file: "SemR.lean",
                from: "    | [.init 1] => .ok (.bool true)",
                to: "    | [.init 1] => .ok (.bool false)",
                times: 1,
            },
            LeanMutant {
                name: "set-byte-pads-with-zeros",
                file: "SemR.lean",
                from: "  | [], n + 1, b => .uninit :: setByte [] n b",
                to: "  | [], n + 1, b => .init 0 :: setByte [] n b",
                times: 1,
            },
            // RM4c review: the MiniRust tie-ins. An alignment of 0 accepted
            // breaks `isPow2_minirust` (MiniRust's `Align::from_bytes` refuses
            // it); a slot address rounded down breaks `le_alignUp`, so
            // `alloc_fresh` (the slot would overlap the one before it).
            LeanMutant {
                name: "alignment-zero-accepted",
                file: "SemR.lean",
                from: "def isPow2 (a : Nat) : Bool := a != 0 && Nat.land a (a - 1) == 0",
                to: "def isPow2 (a : Nat) : Bool := Nat.land a (a - 1) == 0",
                times: 1,
            },
            LeanMutant {
                name: "slot-address-rounds-down",
                file: "SemR.lean",
                from: "def alignUp (x a : Nat) : Nat := (x + (a - 1)) - (x + (a - 1)) % a",
                to: "def alignUp (x a : Nat) : Nat := x - x % a",
                times: 1,
            },
        ],
    );
}

/// The memory module whose wire image Clean's `SemRCheck` runs in the kernel
/// (`memBlob`): a slot written and read back (`fn 0`), a load after its
/// `StorageDead` (`fn 1`), a load one element past the slot (`fn 2`), a
/// misaligned load (`fn 3`), and byte 1 of a stored `u32` (`fn 4`).
fn semr_memory_check_module() -> Module {
    let (case, _) = semr_memory_case();
    let keep = [
        "roundtrip",
        "load_after_dealloc",
        "past_the_slot",
        "misaligned",
        "byte_one",
    ];
    let mut fns = Vec::new();
    for name in keep {
        let f = case
            .module
            .functions
            .iter()
            .find(|f| f.name == name)
            .expect("a memory case function");
        let ft = &case.module.func_types[f.ty.0 as usize];
        fns.push((
            name,
            ft.params.clone(),
            ft.returns.clone(),
            f.blocks[0].clone(),
        ));
    }
    mem_module("semr_memory_check", fns)
}

/// `memBlob` in Clean's `crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/semr/SemRCheck.lean`,
/// byte for byte: the wire image `serialize_module` writes for
/// [`semr_memory_check_module`].
#[rustfmt::skip]
const SEMR_MEMORY_CHECK_BLOB: &[u8] = &[
    84, 82, 85, 83, 84, 95, 73, 82, 38, 0, 0, 0, 6, 17, 115, 101, 109, 114, 95, 109, 101, 109, 111,
    114, 121, 95, 99, 104, 101, 99, 107, 9, 114, 111, 117, 110, 100, 116, 114, 105, 112, 18, 108,
    111, 97, 100, 95, 97, 102, 116, 101, 114, 95, 100, 101, 97, 108, 108, 111, 99, 13, 112, 97, 115,
    116, 95, 116, 104, 101, 95, 115, 108, 111, 116, 10, 109, 105, 115, 97, 108, 105, 103, 110, 101,
    100, 8, 98, 121, 116, 101, 95, 111, 110, 101, 0, 5, 1, 2, 1, 2, 0, 1, 2, 1, 2, 0, 1, 2, 1, 2, 0,
    1, 2, 1, 2, 0, 1, 7, 1, 5, 0, 0, 0, 0, 0, 0, 0, 5, 0, 1, 0, 0, 1, 0, 1, 0, 2, 4, 8, 2, 0, 0, 1,
    1, 0, 0, 0, 0, 7, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 6, 2, 1, 0, 0, 1, 2, 0, 0, 0, 0, 20, 1, 2, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 5, 8, 2, 0, 0, 1, 1, 0, 0, 0,
    0, 7, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 39, 1, 0, 0, 0, 0, 0, 6, 2, 1, 0, 0, 1, 2, 0, 0, 0, 0, 20,
    1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 2, 0, 1, 0, 1, 0, 2, 5, 8, 2, 0, 0, 1,
    1, 0, 0, 0, 0, 25, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 9, 2,
    1, 1, 2, 0, 1, 3, 0, 0, 0, 0, 6, 2, 3, 0, 0, 1, 4, 0, 0, 0, 0, 20, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 3, 4, 3, 0, 1, 0, 1, 0, 2, 5, 8, 3, 0, 0, 1, 1, 0, 0, 0, 0, 25, 3, 0, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 9, 0, 1, 1, 2, 0, 1, 3, 0, 0, 0, 0,
    6, 2, 3, 0, 0, 1, 4, 0, 0, 0, 0, 20, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 5, 4,
    0, 1, 0, 1, 0, 7, 6, 8, 7, 0, 0, 1, 1, 0, 0, 0, 0, 7, 7, 1, 0, 0, 0, 0, 0, 0, 0, 0, 25, 3, 0, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 9, 5, 1, 1, 2, 0, 1, 3, 0, 0, 0,
    0, 6, 5, 3, 0, 0, 1, 4, 0, 0, 0, 0, 20, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0,
];

#[test]
fn semr_memory_check_blob_is_pinned() {
    let blob = trust_ir::binary::serialize_module(&semr_memory_check_module()).expect("blob");
    let lean = blob
        .iter()
        .map(|b| b.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    assert_eq!(
        blob.as_slice(),
        SEMR_MEMORY_CHECK_BLOB,
        "the memory check module's wire image changed; Clean's SemRCheck.memBlob is [{lean}]"
    );
}

/// Every admitted ICmp lane family at positive counts beyond the hardware
/// profiles, plus all four scalar Bool pairs. The oracle is required here:
/// an unavailable Lean engine cannot count as a parity pass.
#[test]
fn icmp_bool_and_general_vector_counts_agree_across_engines() {
    use trust_ir::Constant;
    use trust_ir::inst::ICmpOp;

    fn expected(op: ICmpOp, bits: u32, lhs: u128, rhs: u128) -> bool {
        let signed = |value: u128| {
            if value & (1u128 << (bits - 1)) == 0 {
                value as i128
            } else {
                value as i128 - (1i128 << bits)
            }
        };
        match op {
            ICmpOp::Eq => lhs == rhs,
            ICmpOp::Ne => lhs != rhs,
            ICmpOp::Ult => lhs < rhs,
            ICmpOp::Ule => lhs <= rhs,
            ICmpOp::Ugt => lhs > rhs,
            ICmpOp::Uge => lhs >= rhs,
            ICmpOp::Slt => signed(lhs) < signed(rhs),
            ICmpOp::Sle => signed(lhs) <= signed(rhs),
            ICmpOp::Sgt => signed(lhs) > signed(rhs),
            ICmpOp::Sge => signed(lhs) >= signed(rhs),
        }
    }
    const OPS: [ICmpOp; 10] = [
        ICmpOp::Eq,
        ICmpOp::Ne,
        ICmpOp::Ult,
        ICmpOp::Ule,
        ICmpOp::Ugt,
        ICmpOp::Uge,
        ICmpOp::Slt,
        ICmpOp::Sle,
        ICmpOp::Sgt,
        ICmpOp::Sge,
    ];
    let mut mb = ModuleBuilder::new("icmp_bool_and_general_counts");
    let mut cases = Vec::new();
    let scalar_sig = mb.add_func_type(vec![Ty::Bool, Ty::Bool], vec![Ty::Bool]);
    for op in OPS {
        let mut fb = mb.function(format!("scalar_{op}"), scalar_sig);
        let entry = fb.create_block();
        let lhs = fb.add_block_param(entry, Ty::Bool);
        let rhs = fb.add_block_param(entry, Ty::Bool);
        fb.switch_to_block(entry);
        let result = fb.icmp(op, Ty::Bool, lhs, rhs);
        fb.ret(vec![result]);
        let function = fb.build();
        for a in [false, true] {
            for b in [false, true] {
                cases.push((
                    function,
                    vec![InterpretValue::bool(a), InterpretValue::bool(b)],
                    Verdict::Ok(vec![Val::Bool(expected(
                        op,
                        1,
                        u128::from(a),
                        u128::from(b),
                    ))]),
                ));
            }
        }
    }
    for (elem, bits) in [
        (Ty::Bool, 1),
        (Ty::I8, 8),
        (Ty::U8, 8),
        (Ty::I16, 16),
        (Ty::U16, 16),
        (Ty::I32, 32),
        (Ty::U32, 32),
        (Ty::I64, 64),
        (Ty::U64, 64),
    ] {
        let lane = |raw| {
            if elem == Ty::Bool {
                Constant::Bool(raw != 0)
            } else {
                Constant::Int(common::x86_cell_lane_value(&elem, bits, raw))
            }
        };
        for count in [1u32, 2, 3, 5, 8, 16, 17] {
            let ty = Ty::Vector(Box::new(elem.clone()), count);
            let mask = Ty::Vector(Box::new(Ty::Bool), count);
            let signature = mb.add_func_type(vec![], vec![mask]);
            let edges = [0, 1u128 << (bits - 1), (1u128 << bits) - 1, 1];
            let left: Vec<_> = (0..count as usize).map(|i| edges[i % 4]).collect();
            let other: Vec<_> = (0..count as usize).map(|i| edges[(i + 1) % 4]).collect();
            for op in OPS {
                for (phase, right) in [&left, &other].into_iter().enumerate() {
                    let mut fb =
                        mb.function(format!("vector_{elem}_{count}_{phase}_{op}"), signature);
                    let entry = fb.create_block();
                    fb.switch_to_block(entry);
                    // The oracle's entry grammar accepts scalar arguments. Encode
                    // vector inputs as IR constants, as the codec comparison suite does.
                    let lhs = fb.const_value(
                        ty.clone(),
                        Constant::Vector(left.iter().map(|v| lane(*v)).collect()),
                    );
                    let rhs = fb.const_value(
                        ty.clone(),
                        Constant::Vector(right.iter().map(|v| lane(*v)).collect()),
                    );
                    let result = fb.icmp(op, ty.clone(), lhs, rhs);
                    fb.ret(vec![result]);
                    let function = fb.build();
                    let want = left
                        .iter()
                        .zip(right)
                        .map(|(a, b)| Val::Bool(expected(op, bits, *a, *b)))
                        .collect();
                    cases.push((function, vec![], Verdict::Ok(vec![Val::Vector(want)])));
                }
            }
        }
    }
    let module = mb.build().expect("well-formed ICmp corpus");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(cases.len(), 1300);
    for (function, args, want) in &cases {
        assert_eq!(
            &canonical_verdict(run_rust(&module, *function, args)),
            want,
            "{function:?}: {args:?}"
        );
    }
    let Oracle::Ready(exe) = oracle() else {
        panic!("ICmp parity requires the Lean oracle")
    };
    let runs = cases
        .into_iter()
        .map(|(function, args, _)| (function, args))
        .collect();
    let reports = differential(
        exe,
        &[Batch {
            label: "Bool and generic vector ICmp".into(),
            module: &module,
            runs,
        }],
    );
    assert_eq!(reports.len(), 1300);
    let result = tally(&reports);
    assert_no_mismatch(&result, "Bool and generic vector ICmp");
    assert!(result.unsupported.is_empty(), "{:?}", result.unsupported);
    assert_eq!(result.vacuous, 0);
    assert_eq!(result.agreed.get("ok"), Some(&1300));
}
