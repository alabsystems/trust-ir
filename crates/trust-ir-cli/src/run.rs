// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `trust-ir run` — execute a (multi-module) TrustIr image under the reference
//! interpreter (`trust_ir::interpret`) and print the entry function's return
//! value(s).
//!
//! The reference interpreter executes exactly ONE `Module`, resolving calls by
//! `FuncId` inside it, so a program emitted one-module-per-function
//! ("emit-each") must first be LINKED into a single executable image. The
//! linker is the library merge, [`trust_ir_build::merge_into`] under
//! [`MergePolicy::EXECUTION_IMAGE`] (roadmap WS4.11), applied to each input in
//! turn:
//!
//!   * functions and globals are keyed by LINK-TIME SYMBOL; a definition
//!     resolves a bodyless declaration, and of two declarations the earlier
//!     stands (`DuplicateDecl::FirstStands`, this linker's pre-WS4.11 rule:
//!     a declaration adds nothing to an existing entry) — either way the two
//!     must agree on signature and calling convention; duplicate definitions
//!     dedup only when FULLY identical after the remap, and any other
//!     duplicate is an error naming the first differing field (`conflicting
//!     definitions of @f: body_gate differs`) — input order never picks a
//!     codegen license;
//!   * every per-module table reference (`TyId`, `FuncTyId`, `StructId`,
//!     `EnumId`, `RecordId`, `ClosureTyId`, `PredId`, `UnivId`, `GlobalId`,
//!     `FuncId`, `ImportId`, file indices) is remapped by the merge's
//!     exhaustive walk; equal types are one id, and a nominal type is unified
//!     only with a structurally identical one, never by name;
//!   * the linked image carries NO PROOF CLAIMS — it is an execution
//!     artifact, not a verification artifact. Obligations, certificates,
//!     diagnostics, spec modules and imports are not carried over, and
//!     neither is anything that claims one: `Function.summary` (a `proved`
//!     summary with nothing behind it is `InvalidFunctionSummary`), every
//!     `ProofAnnotation::ProofRef` (function- and node-level; each would
//!     dangle as `ProofRefUnresolved`) and every call-site `ProofContext`
//!     (each would dangle as `ProofContextUnknownObligation`). The stripped
//!     counts are printed. Claim-style annotations, `body_gate` and
//!     `display_path` are still copied. Proof claims are re-earned by
//!     `trust-ir validate --link`, never by this runner. (A contract-only
//!     declaration — bodyless, non-external linkage, valid only because it
//!     carries a summary — keeps the claim-free EMPTY summary instead, so the
//!     strip never makes a valid input `EmptyFunction`.)
//!
//! The runner's one link policy of its own is the 64-bit word pun between a
//! declaration and its definition (`respell_word_punned_declarations`).
//!
//! Before linking, every `Module.imports` row of every input is
//! AUTHENTICATED (default ON): each input is hashed once
//! ([`trust_ir::imports::HashedModule`]), a row's recorded digest must equal
//! the digest of one linked input, and that input must pass
//! [`trust_ir::Module::verify_import_hashed`] (name, producer, target). A row
//! that no input matches is refused, naming the inputs and their digests.
//! `--unauthenticated-imports` skips the check and reports every row
//! UNCHECKED (execution only; never agreement).
//!
//! With `--validate` the image is validated TWICE: as linked (the artifact
//! verdict, a user error when refused) and again after the interpreter
//! lowering below (a refusal there is an `internal:` defect of this tool,
//! [`crate::EXIT_INTERNAL`]). The second pass is what keeps the image the
//! interpreter actually executes validated.
//!
//! Functions that remain bodyless after linking are true externs. A small,
//! name-classified set is synthesized as executable builtin bodies in plain
//! TrustIr (so the interpreter itself is untouched):
//!
//!   * Rust allocator shims `__rust_alloc` / `__rust_alloc_zeroed` /
//!     `__rust_realloc` / `__rust_dealloc` mapped onto `HeapAlloc`/`Dealloc`
//!     over the interpreter's own memory model, plus the C `memcpy` /
//!     `memmove` / `memset` / `memcmp` byte loops;
//!   * `core::intrinsics` compute leaves the frontend declares but does not
//!     define: `ctpop`, `ctlz(_nonzero)`, `cttz(_nonzero)`,
//!     `unchecked_funnel_shl` — synthesized as branch-free bit ladders;
//!   * everything else becomes a TRAP STUB: a body whose single block lives
//!     in the reserved id range starting at [`TRAP_BLOCK_BASE`] and executes
//!     `Unreachable`. When the interpreter reports an error in that range the
//!     CLI maps the block id back to the extern's name — a pure program
//!     reaching one is a finding (panic path taken, or emitted IR diverging
//!     from the native binary).
//!
//! The entry points of a pinned trusted runtime — the handle runtimes
//! (`trust_ir_build::TRUSTED_HANDLE_RUNTIMES`) and the reference-counting
//! runtimes (`trust_ir_build::TRUSTED_RC_RUNTIMES`) — are NEVER synthesized:
//! a body would make the image DEFINE a pinned symbol, which the validator
//! refuses (`HandleEntryPointDefinedLocally` / `RcEntryPointDefinedLocally`),
//! and a trap stub would misreport a trusted-runtime call as a finding. They
//! stay bodyless; only their `entry` block id is moved into the reserved range
//! starting at [`RUNTIME_ENTRY_BLOCK_BASE`] (a declaration's entry is never
//! read by the validator), which is how an entry point named by `--entry` is
//! recognised. A call into one is served ONLY by an installed host model:
//!
//!   * `--host none` (the default): the interpreter's `UnsupportedCall`
//!     naming the declaration (WS2.12), which the CLI turns into a named
//!     refusal — the run fails closed, never a trap;
//!   * `--host pinned` (WS2.13): `trust_ir_build::PinnedHandleHost`, the
//!     reference model of both pinned tables, is installed. A run it served
//!     is HOST-ASSISTED (`InterpretOutcome::host_calls > 0`, reported on
//!     stderr) — evidence about the model's reading of the trusted runtime,
//!     `TRUST.md` items 9 and 13, never in-format execution evidence. The
//!     model serves a declaration only under the EXACT pinned signature; any
//!     other declaration of a pinned symbol is refused by name as unserved.

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use trust_ir::ImportVerificationError;
use trust_ir::constant::Constant;
use trust_ir::imports::HashedModule;
use trust_ir::inst::{AllocOrigin, BinOp, CastOp, ICmpOp, Inst, UnOp};
use trust_ir::interpret::InterpretErrorCode;
use trust_ir::interpret::{
    InterpretError, InterpretOptions, InterpretOutcome, InterpretValue, InterpretValueKind,
    Interpreter,
};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::ImportId;
use trust_ir::value::{
    BlockId, FreshIds, FuncId, GlobalId, IdRun, IdSpaceExhausted, TypedId, ValueId,
};
use trust_ir::{Block, Function, Global, Linkage, Module};
use trust_ir_build::PinnedHandleHost;
use trust_ir_build::{MergePolicy, merge_into};

use crate::{EXIT_INTERNAL, EXIT_IO, EXIT_OK, EXIT_USER, Format, decode_module, read_input};

/// First block id of the reserved trap-stub range. A synthesized trap stub's
/// single block gets id `TRAP_BLOCK_BASE + k`; an interpreter error located in
/// that range is mapped back to stub `k`'s extern name for the diagnostic.
/// Real producer blocks are small dense indices, far below this.
const TRAP_BLOCK_BASE: u32 = 0xF000_0000;

/// First block id of the reserved trusted-runtime range. A pinned handle
/// runtime entry point stays BODYLESS; its `entry` is set to
/// `RUNTIME_ENTRY_BLOCK_BASE + k`, so the interpreter's missing-block error on
/// entering it is mapped back to entry point `k`'s symbol. Disjoint from the
/// trap range, and far above any producer block index.
const RUNTIME_ENTRY_BLOCK_BASE: u32 = 0xE000_0000;

/// Host stack for the interpreter thread. `execute_function_inner` recurses on
/// the Rust stack per interpreted call frame, so deep IR recursion (Ackermann,
/// Collatz chains) needs more than the default main-thread allowance.
const RUN_STACK_BYTES: usize = 512 * 1024 * 1024;

// ---------------------------------------------------------------------------
// Input collection
// ---------------------------------------------------------------------------

/// Expand the argument list into concrete module paths. A directory expands
/// to its `*.trust_ir` files in sorted order; files pass through unchanged.
fn collect_module_paths(paths: &[PathBuf]) -> Result<Vec<PathBuf>, String> {
    let mut out = Vec::new();
    for path in paths {
        if path.is_dir() {
            let mut entries: Vec<PathBuf> = fs::read_dir(path)
                .map_err(|e| format!("read dir {}: {e}", path.display()))?
                .filter_map(|entry| entry.ok().map(|e| e.path()))
                .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("trust_ir"))
                .collect();
            entries.sort();
            if entries.is_empty() {
                return Err(format!(
                    "{}: directory contains no .trust_ir modules",
                    path.display()
                ));
            }
            out.extend(entries);
        } else {
            out.push(path.clone());
        }
    }
    if out.is_empty() {
        return Err("no input modules".to_string());
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Linker: merge N modules into one executable image
// ---------------------------------------------------------------------------

/// The id of table slot `index` (the next slot, when `index` is the table's
/// length), by the one table-id rule ([`trust_ir::value::table_id`]): a table
/// longer than its `u32` id space can name is refused by name — a truncating
/// `as u32` would alias two slots. Only the message is the CLI's.
fn next_table_id<I: TypedId>(index: usize) -> Result<I, String> {
    trust_ir::value::table_id(index).map_err(|refusal| {
        format!(
            "the image's {} table exceeds the u32 id space ({index} entries): {refusal}",
            refusal.space
        )
    })
}

/// The proof claims the linker dropped, counted per INPUT function / node
/// (a declaration and its definition each count). The image is an execution
/// artifact: the obligations these claims name are not carried over, so each
/// would be a dangling or unbacked claim in the image.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct StrippedClaims {
    /// `Function.summary` rows.
    summaries: usize,
    /// `ProofAnnotation::ProofRef`s, function- and node-level.
    proof_refs: usize,
    /// Call-site `ProofContext`s.
    proof_contexts: usize,
}

/// The 64-bit machine-word ABI class: a `Ptr` and a pointer-width integer
/// occupy the same integer register, so a producer may spell either.
fn is_word_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Ptr | Ty::U64 | Ty::I64 | Ty::Usize | Ty::Isize)
}

/// The runner's ONE link policy beyond the library merge: a bodyless
/// declaration whose signature differs from the symbol's canonical signature
/// (the first DEFINITION's, else the first declaration's) only by spelling a
/// 64-bit machine word differently (`Ptr` / `U64` / `I64` / `Usize` /
/// `Isize`) is respelled to the canonical lanes, so the library merge sees
/// one signature.
///
/// This arises when the frontend coarsens a closure-env pointer to a 64-bit
/// integer on one side (a `dyn` vtable shim declares `call_once` as
/// `(u64, u64)` while its body is `(ptr, u64)` — same registers). It is
/// tolerated ONLY for a declaration, never between two definitions; the
/// definition's signature wins. A call site that spells the args the
/// declaration's way lives in the shim, which is dead in a monomorphized
/// program; were one reachable, the interpreter's strict per-argument type
/// check would surface it honestly rather than silently mis-execute. Lanes
/// that are not both words must be structurally equal across the two modules
/// (`ty_structurally_eq_across`), or nothing is respelled and the merge
/// refuses the `ty` conflict by name.
fn respell_word_punned_declarations(
    modules: &[(String, Module)],
) -> Result<Vec<(String, std::borrow::Cow<'_, Module>)>, String> {
    // name -> (module index, function index) of the canonical signature.
    let mut canonical: HashMap<&str, (usize, usize)> = HashMap::new();
    for bodied_pass in [true, false] {
        for (mi, (_, module)) in modules.iter().enumerate() {
            for (fi, func) in module.functions.iter().enumerate() {
                if func.blocks.is_empty() != bodied_pass {
                    canonical.entry(func.name.as_str()).or_insert((mi, fi));
                }
            }
        }
    }
    modules
        .iter()
        .enumerate()
        .map(|(mi, (label, module))| {
            let mut respelled: Option<Module> = None;
            for (fi, func) in module.functions.iter().enumerate() {
                if !func.blocks.is_empty() {
                    continue;
                }
                let (cmi, cfi) = canonical[func.name.as_str()];
                if (cmi, cfi) == (mi, fi) {
                    continue;
                }
                let canon_module = &modules[cmi].1;
                let canon = &canon_module.functions[cfi];
                let (Some(decl_sig), Some(canon_sig)) =
                    (module.func_type(func.ty), canon_module.func_type(canon.ty))
                else {
                    continue;
                };
                let lanes_agree = |a: &[Ty], b: &[Ty]| {
                    a.len() == b.len()
                        && a.iter().zip(b).all(|(x, y)| {
                            (is_word_ty(x) && is_word_ty(y))
                                || trust_ir::ty_structurally_eq_across(module, x, canon_module, y)
                        })
                };
                let respell = |a: &[Ty], b: &[Ty]| -> Vec<Ty> {
                    a.iter()
                        .zip(b)
                        .map(|(x, y)| {
                            if is_word_ty(x) && is_word_ty(y) {
                                y.clone()
                            } else {
                                x.clone()
                            }
                        })
                        .collect()
                };
                if decl_sig.abi.is_some() || canon_sig.abi.is_some() {
                    // Byte placement and producer custody stay exact. Word
                    // respelling is only the legacy, unrecorded contract.
                    continue;
                }
                if decl_sig.is_vararg != canon_sig.is_vararg
                    || !lanes_agree(&decl_sig.params, &canon_sig.params)
                    || !lanes_agree(&decl_sig.returns, &canon_sig.returns)
                {
                    continue;
                }
                let sig = FuncTy {
                    abi: None,
                    params: respell(&decl_sig.params, &canon_sig.params),
                    returns: respell(&decl_sig.returns, &canon_sig.returns),
                    is_vararg: decl_sig.is_vararg,
                };
                if sig == *decl_sig {
                    continue;
                }
                let target = respelled.get_or_insert_with(|| module.clone());
                let ty = target
                    .intern_func_type(sig)
                    .map_err(|exhausted| format!("link {label}: {exhausted}"))?;
                target.functions[fi].ty = ty;
            }
            let module = match respelled {
                Some(owned) => std::borrow::Cow::Owned(owned),
                None => std::borrow::Cow::Borrowed(module),
            };
            Ok((label.clone(), module))
        })
        .collect()
}

/// Link the given `(label, module)` pairs into one executable image, and
/// report the proof claims it stripped (the image carries none).
///
/// Every module is merged into the image by the library merge
/// ([`trust_ir_build::merge_into`] under
/// [`MergePolicy::EXECUTION_IMAGE`]): functions and globals keyed by
/// link-time symbol, a definition resolving a declaration, the earlier of two
/// declarations standing, identical duplicate definitions deduped and any
/// other duplicate refused naming the differing field, nominal types unified
/// only when structurally identical, and every proof claim stripped. The only policy of the runner's own is
/// [`respell_word_punned_declarations`].
fn link_modules(modules: &[(String, Module)]) -> Result<(Module, StrippedClaims), String> {
    let mut image = Module::new("linked");
    let mut stripped = StrippedClaims::default();
    for (label, module) in respell_word_punned_declarations(modules)? {
        let remap = merge_into(&mut image, &module, &MergePolicy::EXECUTION_IMAGE)
            .map_err(|error| format!("link {label}: {error}"))?;
        let counts = remap.stripped();
        stripped.summaries += counts.summaries;
        stripped.proof_refs += counts.proof_refs;
        stripped.proof_contexts += counts.proof_contexts;
    }
    Ok((image, stripped))
}

// ---------------------------------------------------------------------------
// Bool-compare legalization
// ---------------------------------------------------------------------------

/// The format allows `ICmp` over `Bool` and `Ptr` operands (the
/// `trust-ir-build` validator whitelists both, and rustc's MIR `x == false` /
/// pointer comparisons lower to exactly that), but the reference
/// interpreter's integer comparator only accepts integer payloads — a known
/// interpreter-vs-validator gap. Rather than touching the interpreter, the
/// runner legalizes both shapes into forms it executes natively:
///
/// Bool compares become `Select` chains (bool order: `false < true`; the
/// signed forms treat `true` as the all-ones `-1`, so they are the unsigned
/// forms with the roles swapped):
///
///   eq  -> a ? b : !b        ne  -> a ? !b : b
///   ult -> a ? false : b     ule -> a ? b : true
///   ugt -> a ? !b : false    uge -> a ? true : !b
///   slt = ugt, sle = uge, sgt = ult, sge = ule
///
/// Ptr compares become `PtrToInt` on both operands followed by the same
/// compare over `u64` (the interpreter's deterministic allocation addresses
/// make this exact, including null).
///
/// Returns the number of rewritten compares.
///
/// Fresh SSA ids come from the one fresh-id rule
/// ([`Function::fresh_value_ids`]), all of a function's at once, before the
/// function is touched: a function whose compares need more ids than remain
/// is REFUSED by name, unchanged ([`LoweringRefusal`]), never wrapped onto an
/// id it already defines. A function with nothing to legalize needs no id and
/// is never refused.
fn legalize_icmp(module: &mut Module) -> Result<u64, LoweringRefusal> {
    let mut rewritten = 0;
    for func in &mut module.functions {
        // How many fresh ids this function's rewrites need, by the same
        // classification the rewrite below uses.
        let mut needed = 0_u32;
        for node in func.blocks.iter().flat_map(|block| &block.body) {
            if let Some(ids) = icmp_legalization_ids(node) {
                needed = needed
                    .checked_add(ids)
                    .ok_or_else(|| LoweringRefusal::value_ids(&func.name))?;
            }
        }
        if needed == 0 {
            continue;
        }
        let mut run = func
            .fresh_value_ids()
            .take_run(needed)
            .map_err(|exhausted| LoweringRefusal::new(&func.name, exhausted))?;
        let name = func.name.clone();
        let mut fresh = || run.take().ok_or_else(|| LoweringRefusal::value_ids(&name));
        for block in &mut func.blocks {
            let body = std::mem::take(&mut block.body);
            let mut new_body = Vec::with_capacity(body.len());
            for node in body {
                // The same classification the id count read.
                if icmp_legalization_ids(&node).is_none() {
                    new_body.push(node);
                    continue;
                }
                let Inst::ICmp {
                    op,
                    ref ty,
                    lhs,
                    rhs,
                } = node.inst
                else {
                    new_body.push(node);
                    continue;
                };
                let is_ptr = *ty == Ty::Ptr;
                let [result] = node.results.as_slice() else {
                    new_body.push(node);
                    continue;
                };
                let result = *result;
                let span = node.span;
                let mut emit = |inst: Inst, result: ValueId| {
                    let mut aux = InstrNode::new(inst);
                    aux.results.push(result);
                    aux.span = span;
                    new_body.push(aux);
                };
                if is_ptr {
                    let lhs_addr = fresh()?;
                    emit(
                        Inst::Cast {
                            op: CastOp::PtrToInt,
                            src_ty: Ty::Ptr,
                            dst_ty: Ty::U64,
                            operand: lhs,
                        },
                        lhs_addr,
                    );
                    let rhs_addr = fresh()?;
                    emit(
                        Inst::Cast {
                            op: CastOp::PtrToInt,
                            src_ty: Ty::Ptr,
                            dst_ty: Ty::U64,
                            operand: rhs,
                        },
                        rhs_addr,
                    );
                    emit(
                        Inst::ICmp {
                            op,
                            ty: Ty::U64,
                            lhs: lhs_addr,
                            rhs: rhs_addr,
                        },
                        result,
                    );
                    rewritten += 1;
                    continue;
                }
                let k_false = fresh()?;
                emit(
                    Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(false),
                    },
                    k_false,
                );
                let k_true = fresh()?;
                emit(
                    Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(true),
                    },
                    k_true,
                );
                let not_rhs = fresh()?;
                emit(
                    Inst::Select {
                        ty: Ty::Bool,
                        cond: rhs,
                        then_val: k_false,
                        else_val: k_true,
                    },
                    not_rhs,
                );
                let (then_val, else_val) = match op {
                    ICmpOp::Eq => (rhs, not_rhs),
                    ICmpOp::Ne => (not_rhs, rhs),
                    ICmpOp::Ult | ICmpOp::Sgt => (k_false, rhs),
                    ICmpOp::Ule | ICmpOp::Sge => (rhs, k_true),
                    ICmpOp::Ugt | ICmpOp::Slt => (not_rhs, k_false),
                    ICmpOp::Uge | ICmpOp::Sle => (k_true, not_rhs),
                };
                emit(
                    Inst::Select {
                        ty: Ty::Bool,
                        cond: lhs,
                        then_val,
                        else_val,
                    },
                    result,
                );
                rewritten += 1;
            }
            block.body = new_body;
        }
    }
    Ok(rewritten)
}

/// How many fresh value ids [`legalize_icmp`] needs to rewrite `node`, or
/// `None` when it leaves `node` alone: a `ptr` compare takes two (`ptrtoint`
/// of each operand), a `bool` compare three (`false`, `true`, `!rhs`). The
/// ONE classification both the id count and the rewrite read.
fn icmp_legalization_ids(node: &InstrNode) -> Option<u32> {
    let Inst::ICmp { ty, .. } = &node.inst else {
        return None;
    };
    if node.results.len() != 1 {
        return None;
    }
    match ty {
        Ty::Ptr => Some(2),
        Ty::Bool => Some(3),
        _ => None,
    }
}

/// The runner could not lower a function for the interpreter: it needs a
/// fresh id and none is left. A limitation of `trust-ir run` on valid IR
/// (one function with ids up to `u32::MAX`), not a format rule.
#[derive(Debug, Clone, PartialEq, Eq)]
struct LoweringRefusal {
    function: String,
    exhausted: IdSpaceExhausted,
}

impl LoweringRefusal {
    fn new(function: &str, exhausted: IdSpaceExhausted) -> Self {
        Self {
            function: function.to_string(),
            exhausted,
        }
    }

    fn value_ids(function: &str) -> Self {
        Self::new(function, IdSpaceExhausted::of::<ValueId>())
    }
}

impl std::fmt::Display for LoweringRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "cannot lower @{} for the interpreter: {}",
            self.function, self.exhausted
        )
    }
}

// ---------------------------------------------------------------------------
// SymbolAddr / vtable devirtualization glue
// ---------------------------------------------------------------------------

/// Make `Constant::SymbolAddr` images executable under the interpreter.
///
/// A trait-object vtable is a constant global whose function slots are
/// `SymbolAddr` link-time relocations, and a `dyn` call loads a `ptr` from the
/// vtable and `call_indirect`s through it. The interpreter has no relocation
/// or in-memory function-pointer story, so the runner lowers the whole
/// pattern at the IR level:
///
/// 1. every function whose address is taken gets a one-byte ANCHOR global
///    (`__fnaddr.<name>`) — its deterministic allocation address stands in
///    for the function's address;
/// 2. `SymbolAddr` slots inside global initializers are zeroed (the slot's
///    tuple field is retyped `ptr` -> `u64`, same 8-byte layout) and a
///    synthesized `@__trust_ir_run_init` — called first by the entry — stores
///    each anchor's real address into the slot at startup;
/// 3. `Const ptr SymbolAddr` instructions become `GlobalAddr` of the anchor
///    (or of the named data global);
/// 4. every `call_indirect` whose callee is a plain `ptr` becomes an
///    address-compare ladder over the anchored functions with the call's
///    exact signature: `ptrtoint` the callee, compare against each anchor's
///    address, and dispatch to the matching direct `Call`; a miss traps with
///    a named stub. Fn-typed (`FnDef`) indirect calls are left untouched.
///
/// Returns `true` if the image was changed.
fn devirtualize_symbol_addrs(
    module: &mut Module,
    entry: &str,
    traps: &mut TrapBlocks,
) -> Result<bool, String> {
    let has_symbol_addr = module
        .globals
        .iter()
        .any(|global| {
            global
                .initializer
                .as_ref()
                .is_some_and(constant_mentions_symbol_addr)
        })
        || module.functions.iter().any(|func| {
            func.blocks.iter().any(|block| {
                block.body.iter().any(|node| {
                    matches!(&node.inst, Inst::Const { value, .. } if constant_mentions_symbol_addr(value))
                })
            })
        });
    if !has_symbol_addr {
        return Ok(false);
    }

    let func_by_name: HashMap<String, FuncId> = module
        .functions
        .iter()
        .map(|func| (func.name.clone(), func.id))
        .collect();
    let global_by_name: HashMap<String, GlobalId> = module
        .globals
        .iter()
        .enumerate()
        .map(|(index, global)| Ok((global.name.clone(), next_table_id(index)?)))
        .collect::<Result<_, String>>()?;

    // Function name -> (function, anchor global). Anchors are created on
    // demand and double as the address key for the dispatch ladders.
    let mut anchors: HashMap<String, (FuncId, GlobalId)> = HashMap::new();
    let mut anchor_for =
        |module: &mut Module, name: &str| -> Result<Option<(FuncId, GlobalId)>, String> {
            if let Some(entry) = anchors.get(name) {
                return Ok(Some(*entry));
            }
            let Some(func) = func_by_name.get(name).copied() else {
                return Ok(None);
            };
            let global = next_table_id(module.globals.len())?;
            module.globals.push(Global {
                name: format!("__fnaddr.{name}"),
                ty: Ty::U8,
                mutable: false,
                initializer: Some(Constant::Int(0)),
                linkage: Linkage::Internal,
                tls: None,
                align: None,
                section: None,
                visibility: Default::default(),
                retained: false,
            });
            anchors.insert(name.to_string(), (func, global));
            Ok(Some((func, global)))
        };

    // -- 1+2: global initializers -------------------------------------------
    // `(global, byte offset, address-source global)` startup patches.
    let mut patches: Vec<(GlobalId, u64, GlobalId)> = Vec::new();
    for index in 0..module.globals.len() {
        let Some(init) = module.globals[index].initializer.clone() else {
            continue;
        };
        if !constant_mentions_symbol_addr(&init) {
            continue;
        }
        let ty = module.globals[index].ty.clone();
        let (Ty::Tuple(fields), Constant::Aggregate(values)) = (&ty, &init) else {
            eprintln!(
                "note: global @{} carries SymbolAddr in an unsupported shape; leaving as-is",
                module.globals[index].name
            );
            continue;
        };
        if fields.len() != values.len() {
            return Err(format!(
                "global @{}: tuple arity {} != initializer arity {}",
                module.globals[index].name,
                fields.len(),
                values.len()
            ));
        }
        // Any tuple of scalar/pointer fields is patchable: compute the real
        // C-style field byte offsets (matching the interpreter's tuple
        // layout) rather than assuming every field is 8 bytes. This covers
        // both the flat all-pointer vtable and a `&str`-shaped `(ptr, u8×8)`
        // (a data-pointer field followed by the length spread as bytes).
        let Some(offsets) = tuple_field_offsets(fields) else {
            eprintln!(
                "note: global @{} carries SymbolAddr in a non-scalar tuple; leaving as-is",
                module.globals[index].name
            );
            continue;
        };
        // Every SymbolAddr field must be pointer-sized (8 bytes) so the
        // ptr->u64 retype preserves layout; refuse otherwise.
        let ptr_sized = fields.iter().zip(values.iter()).all(|(field, value)| {
            !matches!(value, Constant::SymbolAddr { .. })
                || scalar_size_align(field).map(|(size, _)| size) == Some(8)
        });
        if !ptr_sized {
            eprintln!(
                "note: global @{} has a non-8-byte SymbolAddr field; leaving as-is",
                module.globals[index].name
            );
            continue;
        }
        let mut new_fields = fields.clone();
        let mut new_values = values.clone();
        for (slot, (field, value)) in new_fields.iter_mut().zip(new_values.iter_mut()).enumerate() {
            let Constant::SymbolAddr { symbol, addend } = value else {
                continue;
            };
            if *addend != 0 {
                return Err(format!(
                    "global @{}: SymbolAddr with nonzero addend {} is not supported",
                    module.globals[index].name, addend
                ));
            }
            let symbol = symbol.clone();
            let source = if let Some((_, anchor)) = anchor_for(module, &symbol)? {
                anchor
            } else if let Some(target) = global_by_name.get(&symbol) {
                *target
            } else {
                return Err(format!(
                    "global @{}: SymbolAddr target {symbol} is not defined in the image",
                    module.globals[index].name
                ));
            };
            patches.push((next_table_id(index)?, offsets[slot], source));
            *value = Constant::Int(0);
            *field = Ty::U64;
        }
        let global = &mut module.globals[index];
        global.ty = Ty::Tuple(new_fields);
        global.initializer = Some(Constant::Aggregate(new_values));
    }

    // -- 3: Const-instruction SymbolAddr ------------------------------------
    for func_index in 0..module.functions.len() {
        for block_index in 0..module.functions[func_index].blocks.len() {
            for node_index in 0..module.functions[func_index].blocks[block_index].body.len() {
                let inst = &module.functions[func_index].blocks[block_index].body[node_index].inst;
                let Inst::Const {
                    ty: Ty::Ptr,
                    value: Constant::SymbolAddr { symbol, addend },
                } = inst
                else {
                    continue;
                };
                if *addend != 0 {
                    return Err(format!(
                        "const SymbolAddr with nonzero addend {addend} is not supported"
                    ));
                }
                let symbol = symbol.clone();
                let source = if let Some((_, anchor)) = anchor_for(module, &symbol)? {
                    anchor
                } else if let Some(target) = global_by_name.get(&symbol) {
                    *target
                } else {
                    return Err(format!(
                        "const SymbolAddr target {symbol} is not defined in the image"
                    ));
                };
                module.functions[func_index].blocks[block_index].body[node_index].inst =
                    Inst::GlobalAddr { global: source };
            }
        }
    }

    // -- 4: dispatch ladders for ptr-typed call_indirect ---------------------
    let anchored: Vec<(FuncId, GlobalId)> = anchors.values().copied().collect();
    if !anchored.is_empty() {
        for func_index in 0..module.functions.len() {
            devirtualize_calls_in_function(module, func_index, &anchored, traps)
                .map_err(|refusal| refusal.to_string())?;
        }
    }

    // -- 2b: the startup patcher, called first by the entry ------------------
    if !patches.is_empty() {
        let init_sig = module
            .intern_func_type(FuncTy {
                abi: None,
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
            })
            .map_err(|exhausted| exhausted.to_string())?;
        let init_id = next_table_id(module.functions.len())?;
        let mut init = Function::new(init_id, "__trust_ir_run_init", init_sig, BlockId::new(0));
        init.blocks = startup_patcher_body(&patches).map_err(|exhausted| {
            LoweringRefusal::new("__trust_ir_run_init", exhausted).to_string()
        })?;
        module.functions.push(init);

        let Some(entry_func) = module
            .functions
            .iter_mut()
            .find(|func| func.name == entry && !func.blocks.is_empty())
        else {
            return Err(format!(
                "SymbolAddr patching requires entry @{entry}, which has no body"
            ));
        };
        let entry_block = entry_func.entry;
        let Some(first) = entry_func.block_mut(entry_block) else {
            return Err(format!("entry @{entry} is missing its entry block"));
        };
        first.body.insert(
            0,
            InstrNode::new(Inst::Call {
                callee: init_id,
                args: Vec::new(),
            }),
        );
        eprintln!(
            "devirtualized {} SymbolAddr slot(s) across {} anchored function(s)",
            patches.len(),
            anchors.len()
        );
    }
    Ok(true)
}

/// The body of the synthesized startup patcher: store each anchor's real
/// address into its zeroed slot, then return.
fn startup_patcher_body(
    patches: &[(GlobalId, u64, GlobalId)],
) -> Result<Vec<Block>, IdSpaceExhausted> {
    let mut bb = BodyBuilder::new();
    let block = bb.add_block()?;
    bb.switch_to(block);
    for (target, offset, source) in patches {
        let base = bb.push(Inst::GlobalAddr { global: *target })?;
        let off = bb.const_int(Ty::I64, i128::from(*offset))?;
        let slot = bb.push(Inst::GEP {
            pointee_ty: Ty::U8,
            base,
            indices: vec![off],
            inbounds: false,
        })?;
        let addr = bb.push(Inst::GlobalAddr { global: *source })?;
        bb.push_void(Inst::Store {
            ty: Ty::Ptr,
            ptr: slot,
            value: addr,
            volatile: false,
            align: None,
        });
    }
    bb.ret(Vec::new());
    Ok(bb.blocks)
}

/// Does this constant (recursively) contain a `SymbolAddr`? Walked by the
/// crate's own child enumeration, so every carrier — a `Splat`'s one element
/// included — is visited, and a new variant cannot be missed by a wildcard.
fn constant_mentions_symbol_addr(constant: &Constant) -> bool {
    constant
        .try_visit_constants(|node| {
            if matches!(node, Constant::SymbolAddr { .. }) {
                std::ops::ControlFlow::Break(())
            } else {
                std::ops::ControlFlow::Continue(())
            }
        })
        .is_break()
}

/// Rewrite every `CallIndirect` in `module.functions[func_index]` whose
/// callee is a plain `Ty::Ptr` value into an anchor-address dispatch ladder
/// over the anchored functions with the call's signature.
///
/// Fresh ids come from the one fresh-id rule, taken per rewritten call site
/// before the site is touched: values one past the highest the function
/// defines, and continuation/ladder blocks one past its highest block id AND
/// below [`RUNTIME_ENTRY_BLOCK_BASE`] (a user block id is never minted into a
/// reserved range). The dispatch-miss block is taken from the trap range
/// (`traps`). A site that needs more ids than remain refuses the run by name.
fn devirtualize_calls_in_function(
    module: &mut Module,
    func_index: usize,
    anchored: &[(FuncId, GlobalId)],
    traps: &mut TrapBlocks,
) -> Result<(), LoweringRefusal> {
    // Value types are computed once up front: rewrites never introduce new
    // ptr-typed callees, and split-off continuations keep the original result
    // ids (as block params), so the map stays valid across rewrites.
    let value_tys: HashMap<ValueId, Ty> = {
        let func = &module.functions[func_index];
        func.typed_values(module)
            .into_iter()
            .map(|metadata| (metadata.value, metadata.ty))
            .collect()
    };

    let name = module.functions[func_index].name.clone();
    // Cursors only: nothing is refused until a rewrite takes an id.
    let mut block_ids = module.functions[func_index].fresh_block_ids();
    let mut value_ids = module.functions[func_index].fresh_value_ids();

    let mut block_index = 0;
    while block_index < module.functions[func_index].blocks.len() {
        // Find the first ptr-callee indirect call in this block, if any.
        let found = {
            let block = &module.functions[func_index].blocks[block_index];
            block.body.iter().position(|node| {
                matches!(
                    &node.inst,
                    Inst::CallIndirect { callee, .. }
                        if value_tys.get(callee) == Some(&Ty::Ptr)
                )
            })
        };
        let Some(node_index) = found else {
            block_index += 1;
            continue;
        };
        let (callee, sig, args, results) = {
            let node = &module.functions[func_index].blocks[block_index].body[node_index];
            let Inst::CallIndirect {
                callee, sig, args, ..
            } = &node.inst
            else {
                unreachable!("position() matched a CallIndirect");
            };
            (*callee, *sig, args.clone(), node.results.clone())
        };
        let Some(ret_tys) = module.func_type(sig).map(|ft| ft.returns.clone()) else {
            block_index += 1;
            continue;
        };
        if ret_tys.len() != results.len() {
            block_index += 1;
            continue;
        }
        let candidates: Vec<(FuncId, GlobalId)> = anchored
            .iter()
            .copied()
            .filter(|(func, _)| {
                module
                    .function_by_id(*func)
                    .is_some_and(|candidate| candidate.ty == sig)
            })
            .collect();
        if candidates.is_empty() {
            // No anchored target can inhabit this signature; leave the call
            // alone (the interpreter reports it honestly if reached).
            block_index += 1;
            continue;
        }

        // Every id this site needs, taken before the function is touched: one
        // continuation block, a call block per candidate and a chain block per
        // candidate but the last (2n blocks); the `ptrtoint` of the callee,
        // and per candidate its call results plus three compare values.
        let refuse = |exhausted| LoweringRefusal::new(&name, exhausted);
        let candidate_count = u32::try_from(candidates.len())
            .map_err(|_| refuse(IdSpaceExhausted::of::<BlockId>()))?;
        let block_count = candidate_count
            .checked_mul(2)
            .ok_or_else(|| refuse(IdSpaceExhausted::of::<BlockId>()))?;
        let per_candidate = u32::try_from(results.len())
            .ok()
            .and_then(|count| count.checked_add(3))
            .ok_or_else(|| refuse(IdSpaceExhausted::of::<ValueId>()))?;
        let value_count = candidate_count
            .checked_mul(per_candidate)
            .and_then(|count| count.checked_add(1))
            .ok_or_else(|| refuse(IdSpaceExhausted::of::<ValueId>()))?;
        let mut site_blocks = block_ids
            .take_run_below(block_count, RUNTIME_ENTRY_BLOCK_BASE)
            .map_err(refuse)?;
        let mut site_values = value_ids.take_run(value_count).map_err(refuse)?;
        let miss_id = traps
            .take(format!(
                "<indirect-call dispatch miss in @{name} (functy.{})>",
                sig.index()
            ))
            .map_err(refuse)?;
        let mut take_block = || {
            site_blocks
                .take()
                .ok_or_else(|| refuse(IdSpaceExhausted::of::<BlockId>()))
        };

        // Split: `post` moves into the continuation block, whose params are
        // the original call results.
        let post: Vec<InstrNode> = {
            let block = &mut module.functions[func_index].blocks[block_index];
            let post = block.body.split_off(node_index + 1);
            block.body.pop();
            post
        };
        let cont_id = take_block()?;
        let mut cont = Block::new(cont_id);
        cont.params = results
            .iter()
            .copied()
            .zip(ret_tys.iter().cloned())
            .collect();
        cont.body = post;

        let mut miss = Block::new(miss_id);
        miss.body.push(InstrNode::new(Inst::Unreachable));

        // Emit the compare ladder. The first test lives in the split block;
        // later tests get their own chain blocks.
        let mut new_blocks: Vec<Block> = Vec::new();
        let mut take_value = || {
            site_values
                .take()
                .ok_or_else(|| refuse(IdSpaceExhausted::of::<ValueId>()))
        };
        let addr = take_value()?;
        {
            let mut node = InstrNode::new(Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::U64,
                operand: callee,
            });
            node.results.push(addr);
            module.functions[func_index].blocks[block_index]
                .body
                .push(node);
        }
        let mut chain: Option<Block> = None;
        for (position, (target, anchor)) in candidates.iter().enumerate() {
            let is_last = position + 1 == candidates.len();

            // The direct-call block for this candidate.
            let call_id = take_block()?;
            let mut call_block = Block::new(call_id);
            let mut call_results = Vec::with_capacity(results.len());
            let mut call_node = InstrNode::new(Inst::Call {
                callee: *target,
                args: args.clone(),
            });
            for _ in &results {
                let value = take_value()?;
                call_node.results.push(value);
                call_results.push(value);
            }
            call_block.body.push(call_node);
            call_block.body.push(InstrNode::new(Inst::Br {
                target: cont_id,
                args: call_results,
            }));

            let else_target = if is_last {
                miss_id
            } else {
                let id = take_block()?;
                new_blocks.push(Block::new(id));
                id
            };

            // The compare itself, in the current chain position.
            let anchor_ptr = take_value()?;
            let anchor_addr = take_value()?;
            let matches_target = take_value()?;
            let emit_into = |body: &mut Vec<InstrNode>| {
                let mut node = InstrNode::new(Inst::GlobalAddr { global: *anchor });
                node.results.push(anchor_ptr);
                body.push(node);
                let mut node = InstrNode::new(Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty: Ty::Ptr,
                    dst_ty: Ty::U64,
                    operand: anchor_ptr,
                });
                node.results.push(anchor_addr);
                body.push(node);
                let mut node = InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::U64,
                    lhs: addr,
                    rhs: anchor_addr,
                });
                node.results.push(matches_target);
                body.push(node);
                body.push(InstrNode::new(Inst::CondBr {
                    cond: matches_target,
                    then_target: call_id,
                    then_args: Vec::new(),
                    else_target,
                    else_args: Vec::new(),
                }));
            };
            match chain.take() {
                None => emit_into(&mut module.functions[func_index].blocks[block_index].body),
                Some(mut block) => {
                    emit_into(&mut block.body);
                    new_blocks.push(block);
                }
            }
            if !is_last {
                // The freshly created else block becomes the next chain link.
                let pending = new_blocks
                    .iter()
                    .position(|block| block.id == else_target)
                    .expect("chain block was just pushed");
                chain = Some(new_blocks.remove(pending));
            }
            new_blocks.push(call_block);
        }

        let func = &mut module.functions[func_index];
        func.blocks.push(cont);
        func.blocks.push(miss);
        func.blocks.extend(new_blocks);
        block_index += 1;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Builtin synthesis for bodyless externs
// ---------------------------------------------------------------------------

/// What a bodyless extern is synthesized as.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BuiltinKind {
    /// `__rust_alloc(size, align) -> ptr`
    Alloc,
    /// `__rust_alloc_zeroed(size, align) -> ptr`
    AllocZeroed,
    /// `__rust_dealloc(ptr, size, align)`
    Dealloc,
    /// `__rust_realloc(ptr, old_size, align, new_size) -> ptr`
    Realloc,
    /// Unit-returning no-ops: the `__rust_no_alloc_shim_is_unstable_v2` probe
    /// and the check/hint intrinsic family (`assert_inhabited`,
    /// `assert_zero_valid`, `assert_mem_uninitialized_valid`, `assume`,
    /// `cold_path`) — compile-time checks and optimizer hints with no runtime
    /// effect.
    NoOp,
    /// `core::intrinsics::is_val_statically_known<T>(x) -> bool`: always
    /// `false` at runtime (the same answer the native harness shims).
    ConstFalse,
    Memcpy,
    Memmove,
    Memset,
    Memcmp,
    /// `core::intrinsics::ctpop<uN>(x) -> u32`
    Ctpop,
    /// `core::intrinsics::ctlz{,_nonzero}<uN>(x) -> u32`
    Ctlz,
    /// `core::intrinsics::cttz{,_nonzero}<uN>(x) -> u32`
    Cttz,
    /// `core::intrinsics::unchecked_funnel_shl<uN>(a, b, shift: u32) -> uN`
    FunnelShl,
    /// `core::intrinsics::exact_div<T>(a, b) -> a / b` for a signed or
    /// unsigned integer `T`. UB if `b == 0` or the division is inexact; the
    /// synthesized body just emits the (signed or unsigned) `BinOp` division,
    /// matching the native harness's `a/b` shim.
    ExactDiv,
    /// `CCRandomGenerateBytes(bytes: ptr, count: u64) -> i32`: the macOS
    /// libSystem RNG seed source (`RandomState` entropy). Fills the output
    /// buffer with DETERMINISTIC bytes (zeros) and returns `kCCSuccess` (0).
    /// The battery programs that reach it are provably seed-independent
    /// (commutative value sums, key-based gets over pre-sorted probes), so a
    /// constant fill yields the native value.
    RandomBytes,
    /// Anything else: a stub that traps with the extern's name.
    Trap,
}

impl BuiltinKind {
    fn classify(name: &str) -> BuiltinKind {
        // Exact C symbol names.
        match name {
            "memcpy" => return BuiltinKind::Memcpy,
            "memmove" => return BuiltinKind::Memmove,
            "memset" => return BuiltinKind::Memset,
            "memcmp" => return BuiltinKind::Memcmp,
            _ => {}
        }
        // macOS libSystem RNG seed source (may carry a leading underscore in
        // the object symbol). Deterministic fill; see `BuiltinKind::RandomBytes`.
        if name.contains("CCRandomGenerateBytes") {
            return BuiltinKind::RandomBytes;
        }
        // Rust allocator shims (mangled `_RNv..___rustc..___rust_alloc` etc.).
        // The error handler must be checked before the `___rust_alloc` prefix.
        if name.contains("___rust_alloc_error_handler") {
            return BuiltinKind::Trap;
        }
        if name.contains("___rust_alloc_zeroed") {
            return BuiltinKind::AllocZeroed;
        }
        if name.contains("___rust_realloc") {
            return BuiltinKind::Realloc;
        }
        if name.contains("___rust_alloc") {
            return BuiltinKind::Alloc;
        }
        if name.contains("___rust_dealloc") {
            return BuiltinKind::Dealloc;
        }
        if name.contains("___rust_no_alloc_shim_is_unstable") {
            return BuiltinKind::NoOp;
        }
        match v0_intrinsic_name(name).as_deref() {
            Some("ctpop") => BuiltinKind::Ctpop,
            Some("ctlz") | Some("ctlz_nonzero") => BuiltinKind::Ctlz,
            Some("cttz") | Some("cttz_nonzero") => BuiltinKind::Cttz,
            Some("unchecked_funnel_shl") => BuiltinKind::FunnelShl,
            Some("exact_div") => BuiltinKind::ExactDiv,
            // `compare_bytes(a, b, n) -> i32` has memcmp semantics exactly.
            Some("compare_bytes") => BuiltinKind::Memcmp,
            // Check/hint intrinsics: compile-time assertions (the frontend
            // already discharged them) and optimizer hints — runtime no-ops.
            Some("assert_inhabited")
            | Some("assert_zero_valid")
            | Some("assert_mem_uninitialized_valid")
            | Some("assume")
            | Some("cold_path") => BuiltinKind::NoOp,
            Some("is_val_statically_known") => BuiltinKind::ConstFalse,
            _ => BuiltinKind::Trap,
        }
    }
}

/// Extract the length-prefixed identifier following `10intrinsics` in a Rust
/// v0-mangled `core::intrinsics::<name>` symbol, e.g.
/// `_RINvNtC..4core10intrinsics5ctpopyE..` -> `Some("ctpop")`.
///
/// `None` when the name carries no well-formed identifier there — no
/// `10intrinsics`, no decimal length, or a length the rest of the name does
/// not hold (a length is DATA from the extern's name, so no offset is ever
/// computed from it: the tail is sliced by the length alone). The caller
/// classifies `None` as a trap stub, like any unknown extern.
fn v0_intrinsic_name(name: &str) -> Option<String> {
    let (_, rest) = name.split_once("10intrinsics")?;
    let digit_end = rest
        .find(|c: char| !c.is_ascii_digit())
        .unwrap_or(rest.len());
    let (digits, tail) = rest.split_at_checked(digit_end)?;
    let len: usize = digits.parse().ok()?;
    tail.get(..len).map(str::to_string)
}

/// Name of the reserved trap-stub block range in refusals.
const TRAP_RANGE: &str = "trap-block range";

/// Name of the reserved trusted-runtime entry range in refusals.
const RUNTIME_ENTRY_RANGE: &str = "trusted-runtime entry range";

/// The last id of the trusted-runtime entry range: the ranges are
/// `[RUNTIME_ENTRY_BLOCK_BASE, TRAP_BLOCK_BASE)` and `[TRAP_BLOCK_BASE,
/// u32::MAX]`, disjoint by construction.
const RUNTIME_ENTRY_BLOCK_LAST: u32 = TRAP_BLOCK_BASE - 1;

/// A reserved block-id range and the name each id taken from it stands for:
/// `names[k]` owns `first + k` BY CONSTRUCTION — an id is taken from the
/// bounded run, then its name is pushed, and a used-up range is refused by
/// name, never overflowing into the neighbouring range.
struct ReservedBlocks {
    ids: IdRun<BlockId>,
    names: Vec<String>,
    space: &'static str,
}

impl ReservedBlocks {
    fn span(first: u32, last: u32, space: &'static str) -> Result<Self, String> {
        let ids = IdRun::span(first, last)
            .ok_or_else(|| format!("internal: the {space} [{first:#x}, {last:#x}] is empty"))?;
        Ok(Self {
            ids,
            names: Vec::new(),
            space,
        })
    }

    fn take(&mut self, name: String) -> Result<BlockId, IdSpaceExhausted> {
        let id = self
            .ids
            .take()
            .ok_or(IdSpaceExhausted { space: self.space })?;
        self.names.push(name);
        Ok(id)
    }
}

/// The trap-stub range `[TRAP_BLOCK_BASE, u32::MAX]`, shared by dispatch-miss
/// blocks (devirtualization) and extern stubs (synthesis).
type TrapBlocks = ReservedBlocks;

fn trap_blocks() -> Result<TrapBlocks, String> {
    ReservedBlocks::span(TRAP_BLOCK_BASE, u32::MAX, TRAP_RANGE)
}

/// Refuse, by name, a DEFINED function any of whose block ids — or its
/// `entry` — lies in the runner's reserved range `[RUNTIME_ENTRY_BLOCK_BASE,
/// u32::MAX]`, where synthesized trap stubs and trusted-runtime entries live.
/// Such a user block could share an id with a synthesized one and a reached
/// reserved id could not be attributed. A limitation of `trust-ir run` on a
/// valid module, not a format rule.
fn refuse_reserved_block_ids(module: &Module) -> Result<(), String> {
    for func in module
        .functions
        .iter()
        .filter(|func| !func.blocks.is_empty())
    {
        let offending = func
            .block_ids()
            .chain(std::iter::once(func.entry))
            .find(|id| id.index() >= RUNTIME_ENTRY_BLOCK_BASE);
        if let Some(id) = offending {
            return Err(format!(
                "cannot run @{}: block id {} ({:#x}) lies in the runner's reserved block-id range \
                 [{RUNTIME_ENTRY_BLOCK_BASE:#x}, {:#x}] (trap stubs and trusted-runtime entry \
                 points); this is a limitation of `trust-ir run`, not a format rule",
                func.name,
                id.index(),
                id.index(),
                u32::MAX
            ));
        }
    }
    Ok(())
}

/// Report of what synthesis attached to the linked image.
struct SynthesisReport {
    /// Trap names; index `k` owns block id `TRAP_BLOCK_BASE + k`. Holds both
    /// extern stub names and `<indirect-call dispatch miss …>` entries.
    traps: Vec<String>,
    /// (name, builtin) pairs for the executable builtins.
    builtins: Vec<(String, &'static str)>,
    /// How many bodyless externs became trap STUB functions (a subset of
    /// `traps`, which also carries dispatch-miss blocks).
    stub_count: usize,
    /// Pinned trusted-runtime entry points left BODYLESS; index `k` owns the
    /// entry block id `RUNTIME_ENTRY_BLOCK_BASE + k`.
    runtime_entries: Vec<String>,
}

impl SynthesisReport {
    /// Resolve an interpreter error block id back to a trap-stub name.
    fn trap_name(&self, block: BlockId) -> Option<&str> {
        let index = usize::try_from(block.index().checked_sub(TRAP_BLOCK_BASE)?).ok()?;
        self.traps.get(index).map(String::as_str)
    }

    /// Resolve an interpreter error block id back to a pinned trusted-runtime
    /// entry point the program entered (it has no body in the image).
    fn runtime_entry_name(&self, block: BlockId) -> Option<&str> {
        if block.index() > RUNTIME_ENTRY_BLOCK_LAST {
            return None;
        }
        let index = usize::try_from(block.index().checked_sub(RUNTIME_ENTRY_BLOCK_BASE)?).ok()?;
        self.runtime_entries.get(index).map(String::as_str)
    }

    /// Whether `name` is a pinned trusted-runtime entry point this synthesis
    /// left bodyless.
    fn is_runtime_entry(&self, name: &str) -> bool {
        self.runtime_entries.iter().any(|entry| entry == name)
    }
}

/// Is `name` the link-time symbol of an entry point of a pinned trusted
/// runtime — a handle runtime (`trust_ir_build::TRUSTED_HANDLE_RUNTIMES`) or
/// a reference-counting runtime (`trust_ir_build::TRUSTED_RC_RUNTIMES`)? Such
/// a symbol must stay bodyless in the image: the validator refuses a local
/// definition of it (`HandleEntryPointDefinedLocally` /
/// `RcEntryPointDefinedLocally`, so a trap stub would fail the post-lowering
/// validation as this tool's own defect), and the runtime is part of the
/// trusted base, not something this runner may stand in for.
fn is_pinned_runtime_entry(name: &str) -> bool {
    trust_ir_build::TRUSTED_HANDLE_RUNTIMES
        .iter()
        .flat_map(|pin| pin.entry_points.iter())
        .any(|entry| entry.symbol == name)
        || trust_ir_build::rc_entry_for_symbol(name).is_some()
}

/// Small function-body assembler for synthesized builtins.
///
/// Ids come from the one fresh-id rule: values from `0`, blocks from `0`
/// and below [`RUNTIME_ENTRY_BLOCK_BASE`] (a synthesized body never takes a
/// reserved id). Every minting method is total and refuses — never wraps —
/// once its space is used up.
struct BodyBuilder {
    blocks: Vec<Block>,
    cur: usize,
    values: FreshIds<ValueId>,
    block_ids: FreshIds<BlockId>,
}

impl BodyBuilder {
    fn new() -> Self {
        Self {
            blocks: Vec::new(),
            cur: 0,
            values: FreshIds::new(),
            block_ids: FreshIds::new(),
        }
    }

    fn add_block(&mut self) -> Result<BlockId, IdSpaceExhausted> {
        let exhausted = IdSpaceExhausted::of::<BlockId>();
        let id = self
            .block_ids
            .take_run_below(1, RUNTIME_ENTRY_BLOCK_BASE)?
            .take()
            .ok_or(exhausted)?;
        self.blocks.push(Block::new(id));
        Ok(id)
    }

    fn switch_to(&mut self, block: BlockId) {
        self.cur = block.as_usize();
    }

    fn fresh(&mut self) -> Result<ValueId, IdSpaceExhausted> {
        self.values.take()
    }

    fn param(&mut self, block: BlockId, ty: Ty) -> Result<ValueId, IdSpaceExhausted> {
        let value = self.fresh()?;
        self.blocks[block.as_usize()].params.push((value, ty));
        Ok(value)
    }

    fn push_void(&mut self, inst: Inst) {
        self.blocks[self.cur].body.push(InstrNode::new(inst));
    }

    fn push(&mut self, inst: Inst) -> Result<ValueId, IdSpaceExhausted> {
        let value = self.fresh()?;
        let mut node = InstrNode::new(inst);
        node.results.push(value);
        self.blocks[self.cur].body.push(node);
        Ok(value)
    }

    fn const_int(&mut self, ty: Ty, value: i128) -> Result<ValueId, IdSpaceExhausted> {
        self.push(Inst::Const {
            ty,
            value: Constant::Int(value),
        })
    }

    fn binop(
        &mut self,
        op: BinOp,
        ty: Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) -> Result<ValueId, IdSpaceExhausted> {
        self.push(Inst::BinOp { op, ty, lhs, rhs })
    }

    fn icmp(
        &mut self,
        op: ICmpOp,
        ty: Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) -> Result<ValueId, IdSpaceExhausted> {
        self.push(Inst::ICmp { op, ty, lhs, rhs })
    }

    fn br(&mut self, target: BlockId, args: Vec<ValueId>) {
        self.push_void(Inst::Br { target, args });
    }

    fn cond_br(&mut self, cond: ValueId, then_target: BlockId, else_target: BlockId) {
        self.push_void(Inst::CondBr {
            cond,
            then_target,
            then_args: Vec::new(),
            else_target,
            else_args: Vec::new(),
        });
    }

    fn ret(&mut self, values: Vec<ValueId>) {
        self.push_void(Inst::Return { values });
    }

    /// Byte-granular heap allocation of `count` bytes, 16-aligned. The static
    /// 16-byte alignment stands in for the runtime `align` argument of the
    /// Rust allocator ABI; it covers every scalar the interpreter can store.
    fn heap_alloc_bytes(&mut self, count: ValueId) -> Result<ValueId, IdSpaceExhausted> {
        self.push(Inst::HeapAlloc {
            ty: Ty::U8,
            count: Some(count),
            align: Some(16),
            origin: AllocOrigin::RustHeap,
        })
    }

    fn gep_u8(&mut self, base: ValueId, index: ValueId) -> Result<ValueId, IdSpaceExhausted> {
        self.push(Inst::GEP {
            pointee_ty: Ty::U8,
            base,
            indices: vec![index],
            inbounds: false,
        })
    }

    fn load_u8(&mut self, ptr: ValueId) -> Result<ValueId, IdSpaceExhausted> {
        self.push(Inst::Load {
            ty: Ty::U8,
            ptr,
            volatile: false,
            align: None,
        })
    }

    fn store_u8(&mut self, ptr: ValueId, value: ValueId) {
        self.push_void(Inst::Store {
            ty: Ty::U8,
            ptr,
            value,
            volatile: false,
            align: None,
        });
    }

    /// Width-adjust an integer value between integer types (bit-level:
    /// `Trunc` down, `ZExt` up, pass-through when equal). `Unfit` when either
    /// type is not an integer.
    fn adjust_int(&mut self, value: ValueId, from: &Ty, to: &Ty) -> Result<ValueId, BodyRefusal> {
        if from == to {
            return Ok(value);
        }
        let from_bits = int_bits(from).ok_or(BodyRefusal::Unfit)?;
        let to_bits = int_bits(to).ok_or(BodyRefusal::Unfit)?;
        let op = match to_bits.cmp(&from_bits) {
            std::cmp::Ordering::Less => CastOp::Trunc,
            std::cmp::Ordering::Greater => CastOp::ZExt,
            std::cmp::Ordering::Equal => CastOp::Bitcast,
        };
        Ok(self.push(Inst::Cast {
            op,
            src_ty: from.clone(),
            dst_ty: to.clone(),
            operand: value,
        })?)
    }
}

/// Why a builtin body was not built: its declared signature does not fit the
/// builtin's shape (the extern becomes a trap stub), or an id space ran out
/// (the run is refused by name).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BodyRefusal {
    Unfit,
    Exhausted(IdSpaceExhausted),
}

impl From<IdSpaceExhausted> for BodyRefusal {
    fn from(exhausted: IdSpaceExhausted) -> Self {
        Self::Exhausted(exhausted)
    }
}

/// Bit width of an integer type under the 64-bit target this runner pins.
fn int_bits(ty: &Ty) -> Option<u32> {
    match ty {
        Ty::I8 | Ty::U8 => Some(8),
        Ty::I16 | Ty::U16 => Some(16),
        Ty::I32 | Ty::U32 => Some(32),
        Ty::I64 | Ty::U64 | Ty::Isize | Ty::Usize => Some(64),
        Ty::I128 | Ty::U128 => Some(128),
        _ => None,
    }
}

/// Whether an integer type is signed under the 64-bit target this runner pins.
fn int_is_signed(ty: &Ty) -> Option<bool> {
    match ty {
        Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128 | Ty::Isize => Some(true),
        Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 | Ty::Usize => Some(false),
        _ => None,
    }
}

/// `(byte size, byte alignment)` of a scalar/pointer type under the 64-bit
/// little-endian target this runner pins — matching the interpreter's own
/// `byte_size`/`byte_align`. `None` for a non-scalar (which the tuple
/// field-offset computation refuses rather than guessing a layout).
fn scalar_size_align(ty: &Ty) -> Option<(u64, u64)> {
    match ty {
        Ty::Bool | Ty::I8 | Ty::U8 => Some((1, 1)),
        Ty::I16 | Ty::U16 | Ty::F16 => Some((2, 2)),
        Ty::I32 | Ty::U32 | Ty::F32 | Ty::Char => Some((4, 4)),
        Ty::I64 | Ty::U64 | Ty::F64 | Ty::Isize | Ty::Usize | Ty::Ptr => Some((8, 8)),
        Ty::I128 | Ty::U128 => Some((16, 16)),
        _ => None,
    }
}

/// C-style byte offsets of each field of a scalar/pointer tuple, matching the
/// interpreter's `aggregate_layout` (each field aligned up to its natural
/// alignment; no reordering). `None` if any field is not a scalar/pointer, so
/// the caller falls back to leaving the initializer as-is.
fn tuple_field_offsets(fields: &[Ty]) -> Option<Vec<u64>> {
    let mut offset: u64 = 0;
    let mut offsets = Vec::with_capacity(fields.len());
    for field in fields {
        let (size, align) = scalar_size_align(field)?;
        offset = offset.div_ceil(align) * align;
        offsets.push(offset);
        offset = offset.checked_add(size)?;
    }
    Some(offsets)
}

/// Synthesize bodies for every function that is still bodyless after linking.
/// Returns the trap table (continuing `traps` from earlier passes) and the
/// builtin census. An extern whose signature does not fit its classified
/// builtin falls back to a trap stub (with a note on stderr). Refused by name
/// only when an id space runs out: a reserved range, or a synthesized body's
/// own ids.
fn synthesize_builtins(
    module: &mut Module,
    mut traps: TrapBlocks,
) -> Result<SynthesisReport, LoweringRefusal> {
    let mut runtime_entries = ReservedBlocks::span(
        RUNTIME_ENTRY_BLOCK_BASE,
        RUNTIME_ENTRY_BLOCK_LAST,
        RUNTIME_ENTRY_RANGE,
    )
    .map_err(|_| {
        LoweringRefusal::new(
            "<runtime entries>",
            IdSpaceExhausted {
                space: RUNTIME_ENTRY_RANGE,
            },
        )
    })?;
    let mut builtins = Vec::new();
    let mut stub_count = 0;
    for index in 0..module.functions.len() {
        if !module.functions[index].blocks.is_empty() {
            continue;
        }
        let name = module.functions[index].name.clone();
        if is_pinned_runtime_entry(&name) {
            // NEVER synthesized (module docs): stays a bodyless declaration.
            // Only its entry id moves into the reserved range, so reaching it
            // is reported by name; the validator ignores a declaration's entry.
            let entry = runtime_entries
                .take(name.clone())
                .map_err(|exhausted| LoweringRefusal::new(&name, exhausted))?;
            module.functions[index].entry = entry;
            continue;
        }
        let Some(sig) = module.func_type(module.functions[index].ty).cloned() else {
            // Dangling signature: leave bodyless; the interpreter reports it
            // if the function is ever called.
            continue;
        };
        let kind = BuiltinKind::classify(&name);
        let body = match kind {
            BuiltinKind::Trap => None,
            _ => build_builtin_body(kind, &sig)
                .map_err(|exhausted| LoweringRefusal::new(&name, exhausted))?,
        };
        match body {
            Some((entry, blocks)) => {
                let label = builtin_label(kind);
                builtins.push((name, label));
                let func = &mut module.functions[index];
                func.entry = entry;
                func.blocks = blocks;
            }
            None => {
                if kind != BuiltinKind::Trap {
                    eprintln!(
                        "note: extern @{name} matched builtin {:?} but its signature {} does \
                         not fit; using a trap stub",
                        kind,
                        render_sig(&sig)
                    );
                }
                let refuse = |exhausted| LoweringRefusal::new(&name, exhausted);
                let param_count = u32::try_from(sig.params.len())
                    .map_err(|_| refuse(IdSpaceExhausted::of::<ValueId>()))?;
                let mut param_ids = FreshIds::<ValueId>::new()
                    .take_run(param_count)
                    .map_err(refuse)?;
                let block_id = traps.take(name.clone()).map_err(refuse)?;
                let mut block = Block::new(block_id);
                for ty in &sig.params {
                    let value = param_ids
                        .take()
                        .ok_or_else(|| refuse(IdSpaceExhausted::of::<ValueId>()))?;
                    block.params.push((value, ty.clone()));
                }
                block.body.push(InstrNode::new(Inst::Unreachable));
                let func = &mut module.functions[index];
                func.entry = block_id;
                func.blocks = vec![block];
                stub_count += 1;
            }
        }
    }
    Ok(SynthesisReport {
        traps: traps.names,
        builtins,
        stub_count,
        runtime_entries: runtime_entries.names,
    })
}

fn builtin_label(kind: BuiltinKind) -> &'static str {
    match kind {
        BuiltinKind::Alloc => "__rust_alloc",
        BuiltinKind::AllocZeroed => "__rust_alloc_zeroed",
        BuiltinKind::Dealloc => "__rust_dealloc",
        BuiltinKind::Realloc => "__rust_realloc",
        BuiltinKind::NoOp => "no-op",
        BuiltinKind::ConstFalse => "const-false",
        BuiltinKind::Memcpy => "memcpy",
        BuiltinKind::Memmove => "memmove",
        BuiltinKind::Memset => "memset",
        BuiltinKind::Memcmp => "memcmp",
        BuiltinKind::Ctpop => "ctpop",
        BuiltinKind::Ctlz => "ctlz",
        BuiltinKind::Cttz => "cttz",
        BuiltinKind::FunnelShl => "funnel_shl",
        BuiltinKind::ExactDiv => "exact_div",
        BuiltinKind::RandomBytes => "CCRandomGenerateBytes",
        BuiltinKind::Trap => "trap",
    }
}

fn render_sig(sig: &FuncTy) -> String {
    let params: Vec<String> = sig.params.iter().map(|ty| ty.to_string()).collect();
    let returns: Vec<String> = sig.returns.iter().map(|ty| ty.to_string()).collect();
    format!("({}) -> ({})", params.join(", "), returns.join(", "))
}

/// Build the block list for one builtin against its declared signature.
/// Returns `Ok(None)` when the signature does not fit the builtin's shape, and
/// refuses only when a synthesized body's own id space runs out.
fn build_builtin_body(
    kind: BuiltinKind,
    sig: &FuncTy,
) -> Result<Option<(BlockId, Vec<Block>)>, IdSpaceExhausted> {
    match emit_builtin_body(kind, sig) {
        Ok(body) => Ok(Some(body)),
        Err(BodyRefusal::Unfit) => Ok(None),
        Err(BodyRefusal::Exhausted(exhausted)) => Err(exhausted),
    }
}

/// [`build_builtin_body`]'s emitter: `Unfit` for a signature that does not fit.
fn emit_builtin_body(
    kind: BuiltinKind,
    sig: &FuncTy,
) -> Result<(BlockId, Vec<Block>), BodyRefusal> {
    use BodyRefusal::Unfit;
    let mut bb = BodyBuilder::new();
    match kind {
        BuiltinKind::Trap => Err(Unfit),
        BuiltinKind::NoOp => {
            if !sig.returns.is_empty() {
                return Err(Unfit);
            }
            let entry = bb.add_block()?;
            for ty in &sig.params {
                bb.param(entry, ty.clone())?;
            }
            bb.switch_to(entry);
            bb.ret(Vec::new());
            Ok((entry, bb.blocks))
        }
        BuiltinKind::ConstFalse => {
            if sig.returns.as_slice() != [Ty::Bool] {
                return Err(Unfit);
            }
            let entry = bb.add_block()?;
            for ty in &sig.params {
                bb.param(entry, ty.clone())?;
            }
            bb.switch_to(entry);
            let result = bb.push(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(false),
            })?;
            bb.ret(vec![result]);
            Ok((entry, bb.blocks))
        }
        BuiltinKind::Ctpop | BuiltinKind::Ctlz | BuiltinKind::Cttz => {
            let [param_ty] = sig.params.as_slice() else {
                return Err(Unfit);
            };
            let [ret_ty] = sig.returns.as_slice() else {
                return Err(Unfit);
            };
            let bits = int_bits(param_ty).ok_or(Unfit)?;
            int_bits(ret_ty).ok_or(Unfit)?;
            let param_ty = param_ty.clone();
            let ret_ty = ret_ty.clone();
            let entry = bb.add_block()?;
            let x = bb.param(entry, param_ty.clone())?;
            bb.switch_to(entry);
            let counted = match kind {
                BuiltinKind::Ctpop => bb.push(Inst::UnOp {
                    op: UnOp::CtPop,
                    ty: param_ty.clone(),
                    operand: x,
                })?,
                BuiltinKind::Ctlz => {
                    // Smear the leading one downward, then count the ones:
                    // ctlz(x) = bits - ctpop(smear(x)); handles x == 0.
                    let mut smeared = x;
                    let mut shift = 1u32;
                    while shift < bits {
                        let amount = bb.const_int(param_ty.clone(), i128::from(shift))?;
                        let shifted = bb.binop(BinOp::LShr, param_ty.clone(), smeared, amount)?;
                        smeared = bb.binop(BinOp::Or, param_ty.clone(), smeared, shifted)?;
                        shift *= 2;
                    }
                    let pop = bb.push(Inst::UnOp {
                        op: UnOp::CtPop,
                        ty: param_ty.clone(),
                        operand: smeared,
                    })?;
                    let width = bb.const_int(param_ty.clone(), i128::from(bits))?;
                    bb.binop(BinOp::Sub, param_ty.clone(), width, pop)?
                }
                BuiltinKind::Cttz => {
                    // cttz(x) = ctpop((x - 1) & !x); handles x == 0 (wraps to
                    // all-ones & all-ones = all-ones, ctpop = bits).
                    let one = bb.const_int(param_ty.clone(), 1)?;
                    let minus_one = bb.binop(BinOp::Sub, param_ty.clone(), x, one)?;
                    let inverted = bb.push(Inst::UnOp {
                        op: UnOp::Not,
                        ty: param_ty.clone(),
                        operand: x,
                    })?;
                    let mask = bb.binop(BinOp::And, param_ty.clone(), minus_one, inverted)?;
                    bb.push(Inst::UnOp {
                        op: UnOp::CtPop,
                        ty: param_ty.clone(),
                        operand: mask,
                    })?
                }
                _ => return Err(Unfit),
            };
            let result = bb.adjust_int(counted, &param_ty, &ret_ty)?;
            bb.ret(vec![result]);
            Ok((entry, bb.blocks))
        }
        BuiltinKind::FunnelShl => {
            let [a_ty, b_ty, c_ty] = sig.params.as_slice() else {
                return Err(Unfit);
            };
            let [ret_ty] = sig.returns.as_slice() else {
                return Err(Unfit);
            };
            if a_ty != b_ty {
                return Err(Unfit);
            }
            let bits = int_bits(a_ty).ok_or(Unfit)?;
            int_bits(c_ty).ok_or(Unfit)?;
            int_bits(ret_ty).ok_or(Unfit)?;
            let word = a_ty.clone();
            let entry = bb.add_block()?;
            let a = bb.param(entry, word.clone())?;
            let b = bb.param(entry, word.clone())?;
            let c = bb.param(entry, c_ty.clone())?;
            bb.switch_to(entry);
            // fshl(a, b, c): sh = c & (bits-1);
            // result = (a << sh) | ((b >> 1) >> ((bits-1) - sh)).
            // Branch-free and shift-in-range for every c (sh == 0 included).
            let c_word = bb.adjust_int(c, c_ty, &word)?;
            let mask = bb.const_int(word.clone(), i128::from(bits - 1))?;
            let sh = bb.binop(BinOp::And, word.clone(), c_word, mask)?;
            let hi = bb.binop(BinOp::Shl, word.clone(), a, sh)?;
            let one = bb.const_int(word.clone(), 1)?;
            let b_half = bb.binop(BinOp::LShr, word.clone(), b, one)?;
            let inv = bb.binop(BinOp::Sub, word.clone(), mask, sh)?;
            let lo = bb.binop(BinOp::LShr, word.clone(), b_half, inv)?;
            let combined = bb.binop(BinOp::Or, word.clone(), hi, lo)?;
            let result = bb.adjust_int(combined, &word, ret_ty)?;
            bb.ret(vec![result]);
            Ok((entry, bb.blocks))
        }
        BuiltinKind::ExactDiv => {
            let [a_ty, b_ty] = sig.params.as_slice() else {
                return Err(Unfit);
            };
            let [ret_ty] = sig.returns.as_slice() else {
                return Err(Unfit);
            };
            if a_ty != b_ty || a_ty != ret_ty {
                return Err(Unfit);
            }
            let signed = int_is_signed(a_ty).ok_or(Unfit)?;
            let word = a_ty.clone();
            let entry = bb.add_block()?;
            let a = bb.param(entry, word.clone())?;
            let b = bb.param(entry, word.clone())?;
            bb.switch_to(entry);
            // exact_div is precondition-guarded (b != 0, a % b == 0) at the
            // Rust level; the runtime value is just the quotient.
            let op = if signed { BinOp::SDiv } else { BinOp::UDiv };
            let quotient = bb.binop(op, word.clone(), a, b)?;
            bb.ret(vec![quotient]);
            Ok((entry, bb.blocks))
        }
        BuiltinKind::Alloc => {
            let [size_ty, _align_ty] = sig.params.as_slice() else {
                return Err(Unfit);
            };
            if sig.returns.as_slice() != [Ty::Ptr] {
                return Err(Unfit);
            }
            int_bits(size_ty).ok_or(Unfit)?;
            let entry = bb.add_block()?;
            let size = bb.param(entry, size_ty.clone())?;
            bb.param(entry, sig.params[1].clone())?;
            bb.switch_to(entry);
            let ptr = bb.heap_alloc_bytes(size)?;
            bb.ret(vec![ptr]);
            Ok((entry, bb.blocks))
        }
        BuiltinKind::AllocZeroed => {
            let [size_ty, _align_ty] = sig.params.as_slice() else {
                return Err(Unfit);
            };
            if sig.returns.as_slice() != [Ty::Ptr] {
                return Err(Unfit);
            }
            int_bits(size_ty).ok_or(Unfit)?;
            let size_ty = size_ty.clone();
            let entry = bb.add_block()?;
            let loop_head = bb.add_block()?;
            let loop_body = bb.add_block()?;
            let exit = bb.add_block()?;
            let size = bb.param(entry, size_ty.clone())?;
            bb.param(entry, sig.params[1].clone())?;
            let i = bb.param(loop_head, size_ty.clone())?;
            bb.switch_to(entry);
            let ptr = bb.heap_alloc_bytes(size)?;
            let zero = bb.const_int(size_ty.clone(), 0)?;
            bb.br(loop_head, vec![zero]);
            bb.switch_to(loop_head);
            let in_range = bb.icmp(ICmpOp::Ult, size_ty.clone(), i, size)?;
            bb.cond_br(in_range, loop_body, exit);
            bb.switch_to(loop_body);
            let slot = bb.gep_u8(ptr, i)?;
            let zero_byte = bb.const_int(Ty::U8, 0)?;
            bb.store_u8(slot, zero_byte);
            let one = bb.const_int(size_ty.clone(), 1)?;
            let next = bb.binop(BinOp::Add, size_ty.clone(), i, one)?;
            bb.br(loop_head, vec![next]);
            bb.switch_to(exit);
            bb.ret(vec![ptr]);
            Ok((entry, bb.blocks))
        }
        BuiltinKind::Dealloc => {
            let [Ty::Ptr, size_ty, align_ty] = sig.params.as_slice() else {
                return Err(Unfit);
            };
            if !sig.returns.is_empty() {
                return Err(Unfit);
            }
            let (size_ty, align_ty) = (size_ty.clone(), align_ty.clone());
            let entry = bb.add_block()?;
            let ptr = bb.param(entry, Ty::Ptr)?;
            bb.param(entry, size_ty)?;
            bb.param(entry, align_ty)?;
            bb.switch_to(entry);
            bb.push_void(Inst::Dealloc { ptr });
            bb.ret(Vec::new());
            Ok((entry, bb.blocks))
        }
        BuiltinKind::Realloc => {
            let [Ty::Ptr, old_ty, align_ty, new_ty] = sig.params.as_slice() else {
                return Err(Unfit);
            };
            if sig.returns.as_slice() != [Ty::Ptr] || old_ty != new_ty {
                return Err(Unfit);
            }
            int_bits(old_ty).ok_or(Unfit)?;
            let size_ty = old_ty.clone();
            let align_ty = align_ty.clone();
            let entry = bb.add_block()?;
            let loop_head = bb.add_block()?;
            let loop_body = bb.add_block()?;
            let exit = bb.add_block()?;
            let old_ptr = bb.param(entry, Ty::Ptr)?;
            let old_size = bb.param(entry, size_ty.clone())?;
            bb.param(entry, align_ty)?;
            let new_size = bb.param(entry, size_ty.clone())?;
            let i = bb.param(loop_head, size_ty.clone())?;
            bb.switch_to(entry);
            let new_ptr = bb.heap_alloc_bytes(new_size)?;
            let shrinking = bb.icmp(ICmpOp::Ult, size_ty.clone(), old_size, new_size)?;
            let copy_len = bb.push(Inst::Select {
                ty: size_ty.clone(),
                cond: shrinking,
                then_val: old_size,
                else_val: new_size,
            })?;
            let zero = bb.const_int(size_ty.clone(), 0)?;
            bb.br(loop_head, vec![zero]);
            bb.switch_to(loop_head);
            let in_range = bb.icmp(ICmpOp::Ult, size_ty.clone(), i, copy_len)?;
            bb.cond_br(in_range, loop_body, exit);
            bb.switch_to(loop_body);
            let src = bb.gep_u8(old_ptr, i)?;
            let byte = bb.load_u8(src)?;
            let dst = bb.gep_u8(new_ptr, i)?;
            bb.store_u8(dst, byte);
            let one = bb.const_int(size_ty.clone(), 1)?;
            let next = bb.binop(BinOp::Add, size_ty.clone(), i, one)?;
            bb.br(loop_head, vec![next]);
            bb.switch_to(exit);
            bb.push_void(Inst::Dealloc { ptr: old_ptr });
            bb.ret(vec![new_ptr]);
            Ok((entry, bb.blocks))
        }
        BuiltinKind::Memcpy | BuiltinKind::Memmove => {
            let [Ty::Ptr, Ty::Ptr, len_ty] = sig.params.as_slice() else {
                return Err(Unfit);
            };
            let returns_dst = match sig.returns.as_slice() {
                [] => false,
                [Ty::Ptr] => true,
                _ => return Err(Unfit),
            };
            int_bits(len_ty).ok_or(Unfit)?;
            let len_ty = len_ty.clone();
            let entry = bb.add_block()?;
            let dst = bb.param(entry, Ty::Ptr)?;
            let src = bb.param(entry, Ty::Ptr)?;
            let len = bb.param(entry, len_ty.clone())?;
            let finish = |bb: &mut BodyBuilder, dst| {
                if returns_dst {
                    bb.ret(vec![dst]);
                } else {
                    bb.ret(Vec::new());
                }
            };
            if kind == BuiltinKind::Memcpy {
                // Forward byte loop (the regions must not overlap, per the
                // memcpy contract).
                let loop_head = bb.add_block()?;
                let loop_body = bb.add_block()?;
                let exit = bb.add_block()?;
                let i = bb.param(loop_head, len_ty.clone())?;
                bb.switch_to(entry);
                let zero = bb.const_int(len_ty.clone(), 0)?;
                bb.br(loop_head, vec![zero]);
                bb.switch_to(loop_head);
                let in_range = bb.icmp(ICmpOp::Ult, len_ty.clone(), i, len)?;
                bb.cond_br(in_range, loop_body, exit);
                bb.switch_to(loop_body);
                let from = bb.gep_u8(src, i)?;
                let byte = bb.load_u8(from)?;
                let to = bb.gep_u8(dst, i)?;
                bb.store_u8(to, byte);
                let one = bb.const_int(len_ty.clone(), 1)?;
                let next = bb.binop(BinOp::Add, len_ty.clone(), i, one)?;
                bb.br(loop_head, vec![next]);
                bb.switch_to(exit);
                finish(&mut bb, dst);
            } else {
                // Overlap-safe: bounce through a temporary buffer. The
                // temporary needs `len > 0` (a zero-byte allocation is
                // rejected by the interpreter), so branch around it.
                let empty_exit = bb.add_block()?;
                let copy_in = bb.add_block()?;
                let in_head = bb.add_block()?;
                let in_body = bb.add_block()?;
                let out_start = bb.add_block()?;
                let out_head = bb.add_block()?;
                let out_body = bb.add_block()?;
                let done = bb.add_block()?;
                let i = bb.param(in_head, len_ty.clone())?;
                let j = bb.param(out_head, len_ty.clone())?;
                bb.switch_to(entry);
                let zero = bb.const_int(len_ty.clone(), 0)?;
                let is_empty = bb.icmp(ICmpOp::Eq, len_ty.clone(), len, zero)?;
                bb.cond_br(is_empty, empty_exit, copy_in);
                bb.switch_to(empty_exit);
                finish(&mut bb, dst);
                bb.switch_to(copy_in);
                let tmp = bb.heap_alloc_bytes(len)?;
                let zero_in = bb.const_int(len_ty.clone(), 0)?;
                bb.br(in_head, vec![zero_in]);
                bb.switch_to(in_head);
                let in_range = bb.icmp(ICmpOp::Ult, len_ty.clone(), i, len)?;
                bb.cond_br(in_range, in_body, out_start);
                bb.switch_to(in_body);
                let from = bb.gep_u8(src, i)?;
                let byte = bb.load_u8(from)?;
                let to = bb.gep_u8(tmp, i)?;
                bb.store_u8(to, byte);
                let one = bb.const_int(len_ty.clone(), 1)?;
                let next = bb.binop(BinOp::Add, len_ty.clone(), i, one)?;
                bb.br(in_head, vec![next]);
                bb.switch_to(out_start);
                let zero_out = bb.const_int(len_ty.clone(), 0)?;
                bb.br(out_head, vec![zero_out]);
                bb.switch_to(out_head);
                let out_range = bb.icmp(ICmpOp::Ult, len_ty.clone(), j, len)?;
                bb.cond_br(out_range, out_body, done);
                bb.switch_to(out_body);
                let from = bb.gep_u8(tmp, j)?;
                let byte = bb.load_u8(from)?;
                let to = bb.gep_u8(dst, j)?;
                bb.store_u8(to, byte);
                let one = bb.const_int(len_ty.clone(), 1)?;
                let next = bb.binop(BinOp::Add, len_ty.clone(), j, one)?;
                bb.br(out_head, vec![next]);
                bb.switch_to(done);
                bb.push_void(Inst::Dealloc { ptr: tmp });
                finish(&mut bb, dst);
            }
            Ok((entry, bb.blocks))
        }
        BuiltinKind::Memset => {
            let [Ty::Ptr, fill_ty, len_ty] = sig.params.as_slice() else {
                return Err(Unfit);
            };
            let returns_dst = match sig.returns.as_slice() {
                [] => false,
                [Ty::Ptr] => true,
                _ => return Err(Unfit),
            };
            int_bits(fill_ty).ok_or(Unfit)?;
            int_bits(len_ty).ok_or(Unfit)?;
            let (fill_ty, len_ty) = (fill_ty.clone(), len_ty.clone());
            let entry = bb.add_block()?;
            let loop_head = bb.add_block()?;
            let loop_body = bb.add_block()?;
            let exit = bb.add_block()?;
            let dst = bb.param(entry, Ty::Ptr)?;
            let fill = bb.param(entry, fill_ty.clone())?;
            let len = bb.param(entry, len_ty.clone())?;
            let i = bb.param(loop_head, len_ty.clone())?;
            bb.switch_to(entry);
            let byte = bb.adjust_int(fill, &fill_ty, &Ty::U8)?;
            let zero = bb.const_int(len_ty.clone(), 0)?;
            bb.br(loop_head, vec![zero]);
            bb.switch_to(loop_head);
            let in_range = bb.icmp(ICmpOp::Ult, len_ty.clone(), i, len)?;
            bb.cond_br(in_range, loop_body, exit);
            bb.switch_to(loop_body);
            let slot = bb.gep_u8(dst, i)?;
            bb.store_u8(slot, byte);
            let one = bb.const_int(len_ty.clone(), 1)?;
            let next = bb.binop(BinOp::Add, len_ty.clone(), i, one)?;
            bb.br(loop_head, vec![next]);
            bb.switch_to(exit);
            if returns_dst {
                bb.ret(vec![dst]);
            } else {
                bb.ret(Vec::new());
            }
            Ok((entry, bb.blocks))
        }
        BuiltinKind::RandomBytes => {
            // CCRandomGenerateBytes(bytes: ptr, count: len_ty) -> ret_ty:
            // deterministically zero-fill `count` bytes at `bytes`, then
            // return kCCSuccess (0). Same byte loop shape as `memset`.
            let [Ty::Ptr, len_ty] = sig.params.as_slice() else {
                return Err(Unfit);
            };
            let [ret_ty] = sig.returns.as_slice() else {
                return Err(Unfit);
            };
            int_bits(len_ty).ok_or(Unfit)?;
            int_bits(ret_ty).ok_or(Unfit)?;
            let (len_ty, ret_ty) = (len_ty.clone(), ret_ty.clone());
            let entry = bb.add_block()?;
            let loop_head = bb.add_block()?;
            let loop_body = bb.add_block()?;
            let exit = bb.add_block()?;
            let dst = bb.param(entry, Ty::Ptr)?;
            let len = bb.param(entry, len_ty.clone())?;
            let i = bb.param(loop_head, len_ty.clone())?;
            bb.switch_to(entry);
            let zero = bb.const_int(len_ty.clone(), 0)?;
            bb.br(loop_head, vec![zero]);
            bb.switch_to(loop_head);
            let in_range = bb.icmp(ICmpOp::Ult, len_ty.clone(), i, len)?;
            bb.cond_br(in_range, loop_body, exit);
            bb.switch_to(loop_body);
            let slot = bb.gep_u8(dst, i)?;
            let zero_byte = bb.const_int(Ty::U8, 0)?;
            bb.store_u8(slot, zero_byte);
            let one = bb.const_int(len_ty.clone(), 1)?;
            let next = bb.binop(BinOp::Add, len_ty.clone(), i, one)?;
            bb.br(loop_head, vec![next]);
            bb.switch_to(exit);
            let success = bb.const_int(ret_ty, 0)?;
            bb.ret(vec![success]);
            Ok((entry, bb.blocks))
        }
        BuiltinKind::Memcmp => {
            let [Ty::Ptr, Ty::Ptr, len_ty] = sig.params.as_slice() else {
                return Err(Unfit);
            };
            let [ret_ty] = sig.returns.as_slice() else {
                return Err(Unfit);
            };
            int_bits(len_ty).ok_or(Unfit)?;
            int_bits(ret_ty).ok_or(Unfit)?;
            let (len_ty, ret_ty) = (len_ty.clone(), ret_ty.clone());
            let entry = bb.add_block()?;
            let loop_head = bb.add_block()?;
            let loop_body = bb.add_block()?;
            let advance = bb.add_block()?;
            let differ = bb.add_block()?;
            let equal = bb.add_block()?;
            let lhs = bb.param(entry, Ty::Ptr)?;
            let rhs = bb.param(entry, Ty::Ptr)?;
            let len = bb.param(entry, len_ty.clone())?;
            let i = bb.param(loop_head, len_ty.clone())?;
            let byte_l = bb.param(differ, Ty::U8)?;
            let byte_r = bb.param(differ, Ty::U8)?;
            bb.switch_to(entry);
            let zero = bb.const_int(len_ty.clone(), 0)?;
            bb.br(loop_head, vec![zero]);
            bb.switch_to(loop_head);
            let in_range = bb.icmp(ICmpOp::Ult, len_ty.clone(), i, len)?;
            bb.cond_br(in_range, loop_body, equal);
            bb.switch_to(loop_body);
            let lp = bb.gep_u8(lhs, i)?;
            let lv = bb.load_u8(lp)?;
            let rp = bb.gep_u8(rhs, i)?;
            let rv = bb.load_u8(rp)?;
            let same = bb.icmp(ICmpOp::Eq, Ty::U8, lv, rv)?;
            bb.push_void(Inst::CondBr {
                cond: same,
                then_target: advance,
                then_args: Vec::new(),
                else_target: differ,
                else_args: vec![lv, rv],
            });
            bb.switch_to(advance);
            let one = bb.const_int(len_ty.clone(), 1)?;
            let next = bb.binop(BinOp::Add, len_ty.clone(), i, one)?;
            bb.br(loop_head, vec![next]);
            bb.switch_to(differ);
            let below = bb.icmp(ICmpOp::Ult, Ty::U8, byte_l, byte_r)?;
            let minus_one = bb.const_int(ret_ty.clone(), -1)?;
            let plus_one = bb.const_int(ret_ty.clone(), 1)?;
            let verdict = bb.push(Inst::Select {
                ty: ret_ty.clone(),
                cond: below,
                then_val: minus_one,
                else_val: plus_one,
            })?;
            bb.ret(vec![verdict]);
            bb.switch_to(equal);
            let same_result = bb.const_int(ret_ty.clone(), 0)?;
            bb.ret(vec![same_result]);
            Ok((entry, bb.blocks))
        }
    }
}

// ---------------------------------------------------------------------------
// Execution
// ---------------------------------------------------------------------------

fn render_return(value: &InterpretValue) -> String {
    match &value.kind {
        InterpretValueKind::Int(int) => {
            if int.signed {
                int.as_signed().to_string()
            } else {
                int.as_unsigned().to_string()
            }
        }
        InterpretValueKind::Bool(b) => u8::from(*b).to_string(),
        InterpretValueKind::FloatBits(bits) => match value.ty {
            // WS2.15: an `F16` return is its binary16 pattern in the low 16
            // bits; render the value it denotes (before this it fell to the
            // `f64` arm and printed a tiny binary64 subnormal).
            Ty::F16 => format!("{:?}", trust_ir::interpret::f16_bits_to_f64(*bits as u16)),
            Ty::F32 => format!("{:?}", f32::from_bits(*bits as u32)),
            _ => format!("{:?}", f64::from_bits(*bits)),
        },
        InterpretValueKind::NullPtr => "null".to_string(),
        InterpretValueKind::Ptr(ptr) => {
            format!("ptr(alloc {}, offset {})", ptr.allocation, ptr.offset)
        }
        InterpretValueKind::Unit => "()".to_string(),
        // A runtime handle is opaque: its id names a row of the run's host
        // state, nothing else. It has no in-format value to print.
        InterpretValueKind::Handle { id } => format!("handle(#{id}, {})", value.ty),
        // A tensor (PKG-U13a): its type, its extents, then its elements in
        // row-major order. A zero-extent contraction is one uniform node of
        // any count, so a long tensor prints its first elements and its count.
        InterpretValueKind::Tensor { dims, elems } => {
            const SHOWN: usize = 64;
            let mut shown: Vec<String> = elems.iter().take(SHOWN).map(render_return).collect();
            if elems.len() > SHOWN as u64 {
                shown.push(format!("... ({} elements)", elems.len()));
            }
            format!("{} dims {dims:?} [{}]", value.ty, shown.join(", "))
        }
        other => format!("{other:?}"),
    }
}

/// Which host model `run` installs in the reference interpreter (`--host`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum HostChoice {
    /// No host: every bodyless declaration is refused (fail-closed).
    #[default]
    None,
    /// `trust_ir_build::PinnedHandleHost`, the reference model of the pinned
    /// handle and RC runtimes (WS2.13). Host-assisted execution.
    Pinned,
}

/// The named refusal for entering a pinned trusted-runtime entry point the
/// reference interpreter did not serve (module docs): with no host, nothing
/// serves it; with the pinned host, the declaration is not the exact pinned
/// one (the validator refuses such a module; `run` without `--validate`
/// reaches it).
fn unhosted_runtime_entry(name: &str, host: HostChoice) -> String {
    match host {
        HostChoice::None => format!(
            "reached trusted-runtime entry point @{name} — the reference interpreter has no host \
             implementation (TRUST.md items 9 and 13; `run` installs no host model unless \
             `--host pinned` selects the reference model)"
        ),
        HostChoice::Pinned => format!(
            "reached trusted-runtime entry point @{name}, which the pinned reference host model \
             does not serve: its declaration does not carry the exact pinned signature and \
             calling convention (`trust-ir handles`; `--validate` refuses such a module by name)"
        ),
    }
}

fn report_interpret_error(error: &InterpretError, synthesis: &SynthesisReport, host: HostChoice) {
    // A pinned trusted-runtime entry point is bodyless in the image; unless
    // an installed host model served it, calling it is the interpreter's
    // `UnsupportedCall` naming the declaration (WS2.12). Named refusal,
    // fail-closed. Only a name the synthesis pass recorded as a pinned entry
    // point gets it; any other unhosted callee keeps the raw diagnostic.
    if let Some(name) = error
        .unhosted_callee()
        .filter(|name| synthesis.is_runtime_entry(name))
    {
        eprintln!("error: {}", unhosted_runtime_entry(name, host));
        return;
    }
    // Belt and braces: an interpreter that entered the declaration instead
    // would report its missing block at the reserved entry id.
    if error.code == InterpretErrorCode::MissingBlock
        && let Some(name) = error
            .block
            .and_then(|block| synthesis.runtime_entry_name(block))
    {
        eprintln!("error: {}", unhosted_runtime_entry(name, host));
        return;
    }
    if let Some(name) = error.block.and_then(|block| synthesis.trap_name(block)) {
        eprintln!(
            "trap: reached extern builtin stub @{name} — the program called a bodyless \
             extern. For a pure battery program this is a FINDING: either a panic path \
             was taken or the emitted IR diverges from the native binary."
        );
        return;
    }
    eprintln!("interpreter error: {error}");
}

/// The `run` flags that shape the pipeline (everything but the inputs, the
/// entry and its arguments).
#[derive(Debug, Clone, Copy)]
pub(crate) struct RunOptions {
    pub(crate) fuel: u64,
    pub(crate) max_call_depth: u64,
    /// Validate the image as linked AND after lowering.
    pub(crate) validate: bool,
    /// Authenticate every import row against the linked inputs (default ON;
    /// `--unauthenticated-imports` turns it off).
    pub(crate) authenticate_imports: bool,
    /// The host model installed in the interpreter (`--host`).
    pub(crate) host: HostChoice,
}

/// Authenticate every `Module.imports` row of every input against the linked
/// inputs themselves (module docs). Each input is hashed ONCE
/// ([`HashedModule`]); a row binds to the first input whose computed
/// `stable_digest` equals its recorded digest, and that input must then pass
/// [`Module::verify_import_hashed`] (C2–C6: algorithm, name, producer,
/// target). Returns the number of rows authenticated, or the refusal text.
///
/// Identity is the `trust_ir.module.v2` domain today; once the
/// `ModuleImport.scheme` discriminator lands (WS4.10) the match must hash
/// each input under each row's scheme.
fn authenticate_imports(modules: &[(String, Module)]) -> Result<usize, String> {
    // Nothing to authenticate: hash nothing. Hashing runs the binary writer,
    // which has no carrier for some VALID content (a WS4.19
    // `ScopeData.inlined_at` chain link, a completeness claim; before v51
    // also an `Inst::MakeAggregate` ahead of its wire tag) and panics on
    // it — a module carrying such content but no import rows must
    // still run. When there ARE rows, every input is a candidate, so an input
    // without a wire identity is refused by name rather than by panic.
    if modules.iter().all(|(_, module)| module.imports.is_empty()) {
        return Ok(0);
    }
    for (label, module) in modules {
        if let Some(blocker) = trust_ir_build::wire_identity_blocker(module) {
            return Err(format!(
                "{label}: has no wire identity to authenticate import rows against: {blocker}; \
                 pass --unauthenticated-imports (the image then carries no proof claims either way)"
            ));
        }
    }
    let hashed: Vec<HashedModule<'_>> = modules
        .iter()
        .map(|(_, module)| HashedModule::new(module))
        .collect();
    let mut rows = 0;
    for (label, module) in modules {
        for (index, import) in module.imports.iter().enumerate() {
            let id: ImportId = next_table_id(index)?;
            let Some(candidate) = hashed.iter().find(|h| h.digest() == import.digest) else {
                // C2 before "no match": a non-SHA-256 record can match no
                // input by construction, and its own refusal is the precise one
                // (`verify_import_hashed` checks the algorithm before the
                // digest, so any candidate yields it). `hashed` holds `module`.
                if let Err(error @ ImportVerificationError::UnsupportedDigestAlgorithm { .. }) =
                    module.verify_import_hashed(id, &hashed[0])
                {
                    return Err(format!(
                        "{label}: import.{index} {:?}: {error}",
                        import.name
                    ));
                }
                let inputs: Vec<String> = hashed
                    .iter()
                    .map(|h| format!("{}={}", h.module().name, h.digest()))
                    .collect();
                return Err(format!(
                    "{label}: import.{index} {:?} pins digest {}, which matches no linked input \
                     (inputs: {}); link the exact dependency artifact, or pass \
                     --unauthenticated-imports (the image then carries no proof claims either way)",
                    import.name,
                    import.digest,
                    inputs.join(", ")
                ));
            };
            module
                .verify_import_hashed(id, candidate)
                .map_err(|error| format!("{label}: import.{index} {:?}: {error}", import.name))?;
            rows += 1;
        }
    }
    Ok(rows)
}

/// Print a validator refusal list in the `  [i] <Debug>` shape the harnesses
/// parse.
fn print_validation_errors(errors: &[trust_ir_build::validate::ValidationError]) {
    for (i, error) in errors.iter().enumerate() {
        eprintln!("  [{i}] {error:?}");
    }
}

pub(crate) fn cmd_run(
    paths: &[PathBuf],
    fmt: Option<Format>,
    entry: &str,
    entry_args: &[String],
    options: RunOptions,
) -> u8 {
    // 1. Load every module.
    let module_paths = match collect_module_paths(paths) {
        Ok(paths) => paths,
        Err(message) => {
            eprintln!("error: {message}");
            return EXIT_USER;
        }
    };
    let mut modules = Vec::with_capacity(module_paths.len());
    for path in &module_paths {
        let module = match load_one(path, fmt) {
            Ok(module) => module,
            Err((code, message)) => {
                eprintln!("error: {message}");
                return code;
            }
        };
        modules.push((path.display().to_string(), module));
    }

    // 2. Authenticate every import row against the inputs (default ON). The
    //    runner binds by NAME below, so without this a root pinning one
    //    dependency would silently run against another.
    let import_rows: usize = modules.iter().map(|(_, m)| m.imports.len()).sum();
    if options.authenticate_imports {
        match authenticate_imports(&modules) {
            Ok(rows) if rows > 0 => eprintln!(
                "imports: {rows} row(s) authenticated against the linked inputs by digest"
            ),
            Ok(_) => {}
            Err(message) => {
                eprintln!("error: {message}");
                return EXIT_USER;
            }
        }
    } else if import_rows > 0 {
        eprintln!(
            "imports: {import_rows} row(s) UNCHECKED (execution only; this is not agreement)"
        );
    }

    // 3. Link into one executable image. It carries no proof claims.
    let (mut image, stripped) = match link_modules(&modules) {
        Ok(linked) => linked,
        Err(message) => {
            eprintln!("error: {message}");
            return EXIT_USER;
        }
    };
    drop(modules);
    eprintln!(
        "stripped {} summaries / {} ProofRefs / {} call proof contexts (an execution image \
         carries no proof claims; re-earn them with `trust-ir validate --link`)",
        stripped.summaries, stripped.proof_refs, stripped.proof_contexts
    );

    // 4. The artifact verdict: validate the image AS LINKED, before any
    //    interpreter lowering touches it. Its refusals are user errors.
    if options.validate {
        let report = trust_ir_build::validate::validate_module_report(&image);
        let errors = report.errors();
        if !errors.is_empty() {
            eprintln!(
                "validation of linked image failed (as linked; {} errors):",
                errors.len()
            );
            print_validation_errors(errors);
            return EXIT_USER;
        }
        eprintln!("linked image is well-formed (as linked)");
    }

    // 5. Devirtualize SymbolAddr vtables (dyn dispatch), legalize bool/ptr
    //    compares (interpreter-vs-validator gap; see the pass docs), then
    //    synthesize builtins / trap stubs for remaining externs. The trap
    //    table is shared: dispatch-miss blocks and extern stubs both map an
    //    error block id back to a name.
    //    Every fresh id these passes mint comes from the one fresh-id rule,
    //    and every synthesized block id from a bounded reserved range; a
    //    defined function that already uses a reserved id is refused first,
    //    so no user block can share an id with a synthesized one.
    if let Err(message) = refuse_reserved_block_ids(&image) {
        eprintln!("error: {message}");
        return EXIT_USER;
    }
    let mut traps = match trap_blocks() {
        Ok(traps) => traps,
        Err(message) => {
            eprintln!("{message}");
            return EXIT_INTERNAL;
        }
    };
    if let Err(message) = devirtualize_symbol_addrs(&mut image, entry, &mut traps) {
        eprintln!("error: {message}");
        return EXIT_USER;
    }
    let legalized = match legalize_icmp(&mut image) {
        Ok(legalized) => legalized,
        Err(refusal) => {
            eprintln!("error: {refusal}");
            return EXIT_USER;
        }
    };
    if legalized > 0 {
        eprintln!("legalized {legalized} bool/ptr icmp(s)");
    }
    let synthesis = match synthesize_builtins(&mut image, traps) {
        Ok(synthesis) => synthesis,
        Err(refusal) => {
            eprintln!("error: {refusal}");
            return EXIT_USER;
        }
    };
    let defined = image.functions.len()
        - synthesis.stub_count
        - synthesis.builtins.len()
        - synthesis.runtime_entries.len();
    eprintln!(
        "linked {} module(s): {} function(s) ({} defined, {} builtin, {} trap stub(s), {} \
         trusted-runtime entry point(s)), {} global(s)",
        module_paths.len(),
        image.functions.len(),
        defined,
        synthesis.builtins.len(),
        synthesis.stub_count,
        synthesis.runtime_entries.len(),
        image.globals.len()
    );
    if !synthesis.builtins.is_empty() {
        let listed: Vec<String> = synthesis
            .builtins
            .iter()
            .map(|(name, label)| format!("{label} <- @{name}"))
            .collect();
        eprintln!("builtins: {}", listed.join(", "));
    }

    // 6. The image the interpreter actually executes is validated too. The
    //    input already passed step 4, so a refusal here is this tool's own
    //    lowering defect, never a verdict about the input.
    if options.validate {
        let errors = lowered_image_errors(&image);
        if !errors.is_empty() {
            eprintln!(
                "internal: CLI interpreter lowering produced an invalid image ({} errors):",
                errors.len()
            );
            print_validation_errors(&errors);
            return EXIT_INTERNAL;
        }
        eprintln!("lowered image is well-formed");
    }

    // 7. Resolve the entry point.
    let Some(func) = image.function_by_name(entry) else {
        eprintln!("error: no function named @{entry} in the linked image");
        return EXIT_USER;
    };
    let func_id = func.id;
    if func.blocks.is_empty() {
        // A pinned trusted-runtime entry point named as the entry is the same
        // named refusal as reaching one from a call — unless a host model is
        // installed, in which case the interpreter executes the declaration
        // as a host call (WS2.12) and the model decides.
        let hosted_runtime_entry =
            options.host != HostChoice::None && synthesis.runtime_entry_name(func.entry).is_some();
        if !hosted_runtime_entry {
            if synthesis.runtime_entry_name(func.entry).is_some() {
                eprintln!("error: {}", unhosted_runtime_entry(entry, options.host));
            } else {
                eprintln!("error: entry @{entry} has no body in any input module");
            }
            return EXIT_USER;
        }
    }
    let args = match image.func_type(func.ty) {
        Some(sig) => match parse_entry_args(sig, entry_args) {
            Ok(args) => args,
            Err(message) => {
                eprintln!("error: entry @{entry} {}: {message}", render_sig(sig));
                return EXIT_USER;
            }
        },
        None => {
            eprintln!("error: entry @{entry} references an undefined signature");
            return EXIT_USER;
        }
    };

    // 8. Execute on a dedicated big-stack thread (the interpreter recurses on
    //    the host stack per interpreted call).
    let interpret_options = InterpretOptions {
        fuel: options.fuel,
        max_call_depth: options.max_call_depth,
        ..InterpretOptions::default()
    };
    let worker = std::thread::Builder::new()
        .name("trust-ir-run".to_string())
        .stack_size(RUN_STACK_BYTES)
        .spawn(move || -> Result<InterpretOutcome, InterpretError> {
            let pinned = PinnedHandleHost::new();
            let mut interpreter = Interpreter::with_module(&image).with_options(interpret_options);
            if options.host == HostChoice::Pinned {
                interpreter = interpreter.with_host(&pinned);
            }
            interpreter.execute_func(func_id, args)
        });
    let worker = match worker {
        Ok(handle) => handle,
        Err(error) => {
            eprintln!("error: spawn interpreter thread: {error}");
            return EXIT_IO;
        }
    };
    match worker.join() {
        Ok(Ok(outcome)) => {
            for value in &outcome.returns {
                println!("{}", render_return(value));
            }
            eprintln!("executed {} step(s)", outcome.steps);
            if outcome.host_calls > 0 {
                // Counted by the interpreter, not the host. A consumer must
                // not present this run as in-format execution evidence.
                eprintln!(
                    "host-assisted: {} call(s) served by the pinned reference host model \
                     (a trusted model of the runtime, TRUST.md items 9 and 13; this run is not \
                     in-format execution evidence)",
                    outcome.host_calls
                );
            }
            EXIT_OK
        }
        Ok(Err(error)) => {
            report_interpret_error(&error, &synthesis, options.host);
            EXIT_USER
        }
        Err(_) => {
            eprintln!("error: interpreter thread panicked");
            EXIT_IO
        }
    }
}

/// The post-lowering verdict (`run --validate` step 6): the validator's
/// errors on the image the interpreter executes.
fn lowered_image_errors(image: &Module) -> Vec<trust_ir_build::validate::ValidationError> {
    trust_ir_build::validate::validate_module_report(image)
        .errors()
        .to_vec()
}

/// Parse the `--arg` values against the entry signature (`run --arg`).
///
/// Fail-closed at every step: the arity must match EXACTLY, every param type
/// must be one this front can spell (integers, `bool`, `f32`/`f64`), and every
/// integer is range-checked for its width and signedness before it becomes an
/// [`InterpretValue`] — `InterpretValue::int` itself MASKS to the width, so a
/// value that does not fit would otherwise wrap silently.
fn parse_entry_args(sig: &FuncTy, raw: &[String]) -> Result<Vec<InterpretValue>, String> {
    // Types first: an entry whose params this front cannot spell is refused
    // whatever was supplied, naming the first such param.
    for (index, ty) in sig.params.iter().enumerate() {
        if !is_scalar_entry_param(ty) {
            return Err(format!(
                "param {} has type {ty}; only scalar entry arguments are supported \
                 (integers, bool, f32, f64)",
                index + 1
            ));
        }
    }
    if sig.is_vararg {
        return Err("a variadic entry cannot be run".to_string());
    }
    if raw.len() != sig.params.len() {
        return Err(format!(
            "takes {} parameter(s) but {} --arg value(s) were supplied",
            sig.params.len(),
            raw.len()
        ));
    }
    sig.params
        .iter()
        .zip(raw)
        .enumerate()
        .map(|(index, (ty, text))| {
            parse_entry_arg(ty, text)
                .map_err(|message| format!("param {} ({ty}) --arg {text:?}: {message}", index + 1))
        })
        .collect()
}

/// Integer shape `(bits, signed)` of an entry param, or `None`. Mirrors the
/// interpreter's 64-bit model of the pointer-width integers. `char` is NOT an
/// integer here: its valid range is a Unicode-scalar claim, not a width.
fn entry_int_shape(ty: &Ty) -> Option<(u32, bool)> {
    Some(match ty {
        Ty::I8 => (8, true),
        Ty::I16 => (16, true),
        Ty::I32 => (32, true),
        Ty::I64 | Ty::Isize => (64, true),
        Ty::I128 => (128, true),
        Ty::U8 => (8, false),
        Ty::U16 => (16, false),
        Ty::U32 => (32, false),
        Ty::U64 | Ty::Usize => (64, false),
        Ty::U128 => (128, false),
        _ => return None,
    })
}

fn is_scalar_entry_param(ty: &Ty) -> bool {
    entry_int_shape(ty).is_some() || matches!(ty, Ty::Bool | Ty::F32 | Ty::F64)
}

fn parse_entry_arg(ty: &Ty, text: &str) -> Result<InterpretValue, String> {
    if let Some((bits, signed)) = entry_int_shape(ty) {
        let value = parse_entry_int(text, ty, bits, signed)?;
        return InterpretValue::int(ty.clone(), value).map_err(|error| error.to_string());
    }
    match ty {
        Ty::Bool => match text {
            "true" => Ok(InterpretValue::bool(true)),
            "false" => Ok(InterpretValue::bool(false)),
            _ => Err("expected `true` or `false`".to_string()),
        },
        Ty::F32 => {
            let value: f32 = text
                .parse()
                .map_err(|_| "expected an f32 literal".to_string())?;
            check_float_range(text, value.is_infinite(), value == 0.0, "f32")?;
            Ok(InterpretValue {
                ty: Ty::F32,
                kind: InterpretValueKind::FloatBits(u64::from(value.to_bits())),
            })
        }
        Ty::F64 => {
            let value: f64 = text
                .parse()
                .map_err(|_| "expected an f64 literal".to_string())?;
            check_float_range(text, value.is_infinite(), value == 0.0, "f64")?;
            Ok(InterpretValue {
                ty: Ty::F64,
                kind: InterpretValueKind::FloatBits(value.to_bits()),
            })
        }
        other => Err(format!("unsupported param type {other}")),
    }
}

/// Refuse a float literal the parse silently moved out of its magnitude: a
/// FINITE spelling that rounds to infinity (`1e39` at `f32`), or a NONZERO
/// spelling that rounds all the way to zero (`1e-50` at `f32`). Both would
/// otherwise run the entry on a value the caller never wrote — the float
/// counterpart of the integer range check. Ordinary rounding (including to a
/// subnormal) is not a range error; `inf` / `infinity` / `nan` spellings pass.
fn check_float_range(
    text: &str,
    is_infinite: bool,
    is_zero: bool,
    ty_name: &str,
) -> Result<(), String> {
    let unsigned = text.trim_start_matches(['+', '-']).to_ascii_lowercase();
    if is_infinite && unsigned != "inf" && unsigned != "infinity" {
        return Err(format!(
            "out of range for {ty_name}: the literal overflows to infinity"
        ));
    }
    let mantissa = unsigned.split('e').next().unwrap_or("");
    if is_zero && mantissa.bytes().any(|b| (b'1'..=b'9').contains(&b)) {
        return Err(format!(
            "out of range for {ty_name}: the nonzero literal underflows to zero"
        ));
    }
    Ok(())
}

/// Parse a decimal or `0x`-hex integer (optionally `-`-prefixed) and check it
/// fits `bits` at the given signedness. Returns the value as the `i128` whose
/// low `bits` are the two's-complement image `InterpretValue::int` stores
/// (for `u128` above `i128::MAX` that is the wrapped bit pattern).
fn parse_entry_int(text: &str, ty: &Ty, bits: u32, signed: bool) -> Result<i128, String> {
    let (min_magnitude_neg, max_pos): (u128, u128) = if signed {
        let half = 1u128 << (bits - 1);
        (half, half - 1)
    } else {
        (
            0,
            if bits == 128 {
                u128::MAX
            } else {
                (1u128 << bits) - 1
            },
        )
    };
    let out_of_range = || {
        let range = if signed {
            format!("-{min_magnitude_neg}..={max_pos}")
        } else {
            format!("0..={max_pos}")
        };
        // Name the PARAM's type: `isize`/`usize` run at 64 bits here, and the
        // message must not relabel them as `i64`/`u64`.
        format!("out of range for {ty}: {range}")
    };
    let (negative, body) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text),
    };
    let (radix, digits) = match body.strip_prefix("0x").or_else(|| body.strip_prefix("0X")) {
        Some(hex) => (16, hex),
        None => (10, body),
    };
    // `from_str_radix` accepts a leading `+`; a sign after our own `-` or
    // after `0x` is not an integer spelling this front admits.
    let malformed = || "expected a decimal or 0x-hex integer".to_string();
    if digits.is_empty() || digits.starts_with(['+', '-']) {
        return Err(malformed());
    }
    let magnitude = u128::from_str_radix(digits, radix).map_err(|error| {
        if *error.kind() == std::num::IntErrorKind::PosOverflow {
            out_of_range()
        } else {
            malformed()
        }
    })?;
    if negative {
        if magnitude > min_magnitude_neg {
            return Err(out_of_range());
        }
        // `magnitude <= 2^127` here, so the wrapping negation is exact.
        Ok((magnitude as i128).wrapping_neg())
    } else {
        if magnitude > max_pos {
            return Err(out_of_range());
        }
        // For `u128` above `i128::MAX` this is the wrapped bit pattern, which
        // is exactly the image `InterpretValue::int` stores.
        Ok(magnitude as i128)
    }
}

/// Load one module file: explicit `--format` wins, otherwise the name and the
/// content's magic decide ([`Format::resolve`], matching the rest of the CLI).
fn load_one(path: &Path, fmt: Option<Format>) -> Result<Module, (u8, String)> {
    let bytes = read_input(path).map_err(|e| (EXIT_IO, format!("read {}: {e}", path.display())))?;
    let format = Format::resolve(fmt, path, &bytes).map_err(|message| (EXIT_USER, message))?;
    decode_module(format, &bytes)
        .map_err(|message| (EXIT_IO, format!("{}: {message}", path.display())))
}

#[cfg(test)]
#[path = "../../trust-ir-conformance/tests/generate/signature_abi.rs"]
mod signature_abi_fixture;

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::proof::ProofAnnotation;
    use trust_ir::value::{FuncTyId, PredId, SourceSpan, TyId, UnivId};
    use trust_ir::{Pred, ScopeData, Space, Universe};

    /// r11 item 1, FAILING-FIRST (the surface is unchanged): a length prefix
    /// no offset can hold. The old parser computed `digits.len() + len` and
    /// panicked in debug (it wrapped to an empty range and answered `None` in
    /// release only by accident). The one parse rule never adds to the
    /// length: the tail is sliced by it. Mutation check: restoring the add
    /// panics here.
    #[test]
    fn v0_intrinsic_name_refuses_a_length_no_offset_can_hold() {
        let too_long = "_RNvNtCsbu97CrmFxuv_4core10intrinsics18446744073709551615x";
        assert_eq!(v0_intrinsic_name(too_long), None);
        assert_eq!(BuiltinKind::classify(too_long), BuiltinKind::Trap);
        // Controls: a length the name does not hold, and the exact length.
        assert_eq!(v0_intrinsic_name("_RNvNtC_4core10intrinsics99x"), None);
        assert_eq!(
            v0_intrinsic_name("_RNvNtC_4core10intrinsics5ctpop"),
            Some("ctpop".to_string())
        );
        assert_eq!(v0_intrinsic_name("_RNvNtC_4core10intrinsicsx"), None);
    }

    /// One `bool` compare in a function defining `ValueId(u32::MAX)`.
    fn icmp_at_value_id_max(with_compare: bool) -> Module {
        let mut module = Module::new("r11_icmp");
        let signature = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::Bool, Ty::Bool],
                returns: vec![Ty::Bool],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "f", signature, BlockId::new(0));
        let mut body = Vec::new();
        if with_compare {
            body.push(
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::Bool,
                    lhs: ValueId::new(u32::MAX),
                    rhs: ValueId::new(0),
                })
                .with_result(ValueId::new(1)),
            );
        }
        let returned = if with_compare { 1 } else { 0 };
        body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(returned)],
        }));
        function.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![
                (ValueId::new(u32::MAX), Ty::Bool),
                (ValueId::new(0), Ty::Bool),
            ],
            body,
        }];
        module.functions.push(function);
        module
    }

    /// r11 item 2 (port of probe P2, evidence kind ii): before r11 the seed
    /// `index() + 1` panicked in debug, and in release wrapped past
    /// `u32::MAX` to 0, so fresh ids were computed as if the `u32::MAX`
    /// definition did not exist. Now the function is refused by name and
    /// left UNCHANGED (its ids are taken as one run before it is touched).
    /// Mutation check: re-seeding with `saturating_add(1)` mints `u32::MAX`
    /// again (a duplicate definition) instead of refusing.
    #[test]
    fn legalize_icmp_refuses_when_no_fresh_value_id_exists() {
        let mut module = icmp_at_value_id_max(true);
        let before = module.clone();
        assert_eq!(
            legalize_icmp(&mut module),
            Err(LoweringRefusal::value_ids("f"))
        );
        assert_eq!(module, before, "the function is untouched");
    }

    /// Laziness: the same function with no compare needs no id.
    #[test]
    fn legalize_icmp_leaves_a_max_id_function_without_bool_compares_alone() {
        let mut module = icmp_at_value_id_max(false);
        let before = module.clone();
        assert_eq!(legalize_icmp(&mut module), Ok(0));
        assert_eq!(module, before);
    }

    /// `target: () -> ()` (anchored at global 0) and `caller(ptr)` whose
    /// entry `call_indirect`s its parameter, plus an unreachable `extra`
    /// block.
    fn devirt_module(param: u32, extra: Option<u32>) -> (Module, Vec<(FuncId, GlobalId)>) {
        let mut module = Module::new("r11_devirt");
        let unit = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let takes_ptr = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::Ptr],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut target = Function::new(FuncId::new(0), "target", unit, BlockId::new(0));
        target.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return { values: vec![] })],
        }];
        let mut caller = Function::new(FuncId::new(1), "caller", takes_ptr, BlockId::new(0));
        caller.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![(ValueId::new(param), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::CallIndirect {
                    callee: ValueId::new(param),
                    sig: unit,
                    args: vec![],
                    calling_conv: Default::default(),
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }];
        if let Some(extra) = extra {
            caller.blocks.push(Block {
                id: BlockId::new(extra),
                params: vec![],
                body: vec![InstrNode::new(Inst::Unreachable)],
            });
        }
        module.functions.push(target);
        module.functions.push(caller);
        (module, vec![(FuncId::new(0), GlobalId::new(0))])
    }

    /// r11 sibling j/o (port of probes P3/P4, evidence kind ii): before r11 a
    /// block at `u32::MAX` made the ladder mint `u32::MAX` AGAIN
    /// (`saturating_add`) — a duplicate block id, measured
    /// `[0, u32::MAX, u32::MAX, 0xF000_0000, 0]` — and a block at the first
    /// trap id duplicated the miss block. Ladder blocks now come from a run
    /// below `RUNTIME_ENTRY_BLOCK_BASE` and the miss block from the trap
    /// range: every id is unique, and a function with no room below the
    /// reserved ranges is refused by name. (`cmd_run` refuses a user block
    /// INSIDE a reserved range at the input boundary before this pass runs.)
    #[test]
    fn devirtualize_never_mints_a_duplicate_block() {
        let (mut module, anchored) = devirt_module(0, Some(7));
        let mut traps = trap_blocks().expect("trap range");
        devirtualize_calls_in_function(&mut module, 1, &anchored, &mut traps)
            .expect("room for the ladder");
        let mut ids: Vec<u32> = module.functions[1]
            .block_ids()
            .map(BlockId::index)
            .collect();
        assert_eq!(ids, vec![0, 7, 8, TRAP_BLOCK_BASE, 9]);
        ids.sort_unstable();
        ids.dedup();
        assert_eq!(ids.len(), 5, "unique block ids");
        assert_eq!(traps.names.len(), 1);

        let (mut crowded, anchored) = devirt_module(0, Some(RUNTIME_ENTRY_BLOCK_BASE - 1));
        let before = crowded.clone();
        let mut traps = trap_blocks().expect("trap range");
        assert_eq!(
            devirtualize_calls_in_function(&mut crowded, 1, &anchored, &mut traps),
            Err(LoweringRefusal::new(
                "caller",
                IdSpaceExhausted::of::<BlockId>()
            ))
        );
        assert_eq!(crowded, before, "the site is untouched");
    }

    /// r11 sibling j (port of probe P4, evidence kind ii): a callee at
    /// `ValueId(u32::MAX)` has no fresh value for the ladder; before r11 the
    /// seed panicked in debug and wrapped to ids 0.. in release (duplicates
    /// of `%0`-style ids). Refused by name, site untouched. Mutation check:
    /// seeding with `index() + 1` panics here.
    #[test]
    fn devirtualize_refuses_value_id_exhaustion() {
        let (mut module, anchored) = devirt_module(u32::MAX, None);
        let before = module.clone();
        let mut traps = trap_blocks().expect("trap range");
        assert_eq!(
            devirtualize_calls_in_function(&mut module, 1, &anchored, &mut traps),
            Err(LoweringRefusal::value_ids("caller"))
        );
        assert_eq!(module, before);
    }

    /// The two reserved ranges are disjoint by construction and each is
    /// refused by name when used up, never overflowing into its neighbour.
    #[test]
    fn runtime_and_trap_ranges_never_overlap() {
        let mut traps = trap_blocks().expect("trap range");
        assert_eq!(traps.take("a".into()), Ok(BlockId::new(TRAP_BLOCK_BASE)));
        let mut runtime = ReservedBlocks::span(
            RUNTIME_ENTRY_BLOCK_BASE,
            RUNTIME_ENTRY_BLOCK_LAST,
            RUNTIME_ENTRY_RANGE,
        )
        .expect("runtime range");
        assert_eq!(
            runtime.ids.remaining(),
            TRAP_BLOCK_BASE - RUNTIME_ENTRY_BLOCK_BASE
        );
        assert_eq!(
            runtime.take("r".into()),
            Ok(BlockId::new(RUNTIME_ENTRY_BLOCK_BASE))
        );
        // The last two ids of each range, then the refusal.
        let mut tail = ReservedBlocks::span(u32::MAX - 1, u32::MAX, TRAP_RANGE).expect("tail");
        assert_eq!(tail.take("x".into()), Ok(BlockId::new(u32::MAX - 1)));
        assert_eq!(tail.take("y".into()), Ok(BlockId::new(u32::MAX)));
        assert_eq!(
            tail.take("z".into()),
            Err(IdSpaceExhausted { space: TRAP_RANGE })
        );
        assert_eq!(tail.names, vec!["x".to_string(), "y".to_string()]);
        let mut runtime_tail = ReservedBlocks::span(
            RUNTIME_ENTRY_BLOCK_LAST,
            RUNTIME_ENTRY_BLOCK_LAST,
            RUNTIME_ENTRY_RANGE,
        )
        .expect("one id");
        assert_eq!(
            runtime_tail.take("last".into()),
            Ok(BlockId::new(TRAP_BLOCK_BASE - 1))
        );
        assert_eq!(
            runtime_tail.take("next".into()),
            Err(IdSpaceExhausted {
                space: RUNTIME_ENTRY_RANGE
            })
        );
        // The report never reads a trap id as a runtime entry, or back.
        let report = SynthesisReport {
            traps: vec!["t".into()],
            builtins: vec![],
            stub_count: 1,
            runtime_entries: vec!["r".into()],
        };
        assert_eq!(report.trap_name(BlockId::new(TRAP_BLOCK_BASE)), Some("t"));
        assert_eq!(
            report.runtime_entry_name(BlockId::new(TRAP_BLOCK_BASE)),
            None
        );
        assert_eq!(
            report.runtime_entry_name(BlockId::new(RUNTIME_ENTRY_BLOCK_BASE)),
            Some("r")
        );
        assert_eq!(
            report.trap_name(BlockId::new(RUNTIME_ENTRY_BLOCK_BASE)),
            None
        );
    }

    /// Review 2026-09-23: a `SymbolAddr` inside a `Splat` (a uniform address
    /// table such as `[&HOOK; 4]`, whose only spelling is a splat under
    /// SPEC_RATIFICATIONS §3.1) is seen by the devirtualizer's scan, like one
    /// inside any other carrier. It used to fall through a `_ => false` arm.
    #[test]
    fn symbol_addr_scan_sees_every_constant_carrier() {
        let hook = Constant::symbol_addr("hook");
        for carrier in [
            Constant::splat(hook.clone(), 4),
            Constant::Splat {
                elem: Box::new(Constant::Aggregate(vec![Constant::Int(0), hook.clone()])),
                len: 1 << 40,
            },
            Constant::Array(vec![Constant::Int(1), hook.clone()]),
            Constant::Record(vec![("f".into(), hook.clone())]),
            hook.clone(),
        ] {
            assert!(constant_mentions_symbol_addr(&carrier), "{carrier:?}");
        }
        assert!(!constant_mentions_symbol_addr(&Constant::splat(
            Constant::Int(0),
            4
        )));
    }

    /// WS2.15: an `F16` return renders the binary16 VALUE, not the `f64`
    /// reinterpretation of its 16-bit pattern.
    #[test]
    fn render_return_reads_an_f16_pattern_at_binary16() {
        let value = InterpretValue {
            ty: Ty::F16,
            kind: InterpretValueKind::FloatBits(0x4380),
        };
        assert_eq!(render_return(&value), "3.75");
        let f32_value = InterpretValue {
            ty: Ty::F32,
            kind: InterpretValueKind::FloatBits(u64::from(3.75f32.to_bits())),
        };
        assert_eq!(render_return(&f32_value), "3.75");
    }

    fn test_global(name: &str, ty: Ty) -> Global {
        Global {
            name: name.to_string(),
            ty,
            mutable: false,
            initializer: None,
            linkage: Linkage::External,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        }
    }

    fn refined_array_module(name: &str, global_name: &str) -> Module {
        let mut module = Module::new(name);
        let universe = module
            .intern_universe(Universe::range(10, 20).expect("canonical range"))
            .expect("Module::intern_universe: test fixture")
            .expect("universe interns");
        let member = module
            .intern_pred(Pred::InUniverse(universe, Space::Member))
            .expect("Module::intern_pred: test fixture")
            .expect("membership predicate interns");
        let nonzero = module
            .intern_pred(Pred::NonZero)
            .expect("Module::intern_pred: test fixture")
            .expect("nonzero predicate interns");
        let both = module
            .intern_pred(Pred::Conj(vec![member, nonzero]))
            .expect("Module::intern_pred: test fixture")
            .expect("conjunction interns");
        let base = module
            .add_type(Ty::I32)
            .expect("Module::add_type: test fixture");
        let refined = module
            .add_type(Ty::Refine(base, both))
            .expect("Module::add_type: test fixture");
        module
            .globals
            .push(test_global(global_name, Ty::Array(refined, 4)));
        module
    }

    /// The linker rebuilds each `Function` field by field, so a field added to
    /// `Function` does NOT break this build — it silently arrives as
    /// `Function::new`'s default. Only a test can hold that line.
    ///
    /// For `body_gate` the drop would be a SOUNDNESS event, not cosmetic:
    /// `Ungated` means "a codegen consumer MUST refuse this body", while the
    /// default `None` means "no licensing claim", which a consumer may permit.
    /// Losing it in a merge launders a below-tier body into the permitted
    /// state without anyone stating so.
    #[test]
    fn linking_preserves_the_codegen_license_and_display_path() {
        use trust_ir::BodyGate;

        let build = |name: &str, gate: BodyGate| {
            let mut module = Module::new(name);
            let ft = module
                .add_func_type(FuncTy {
                    abi: None,
                    params: vec![],
                    returns: vec![],
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut func = Function::new(FuncId::new(0), name, ft, BlockId::new(0));
            func.body_gate = Some(gate);
            func.display_path = Some(format!("crate::{name}"));
            let mut block = Block::new(BlockId::new(0));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(block);
            module
                .try_add_function(func)
                .expect("Module::try_add_function: test fixture");
            (name.to_string(), module)
        };

        let modules = vec![
            build("ungated_fn", BodyGate::Ungated),
            build(
                "gated_fn",
                BodyGate::Gated {
                    authority: "clean-kernel-tv".to_string(),
                    evidence: None,
                },
            ),
            // v61 evidence (review): the license survives the link, its
            // evidence does not — the image carries no proof rows for it to
            // cite, and the remap may renumber the ids its digest hashes.
            build(
                "evidenced_fn",
                BodyGate::Gated {
                    authority: "clean-kernel-tv".to_string(),
                    evidence: Some(trust_ir::GateEvidence {
                        obligation: trust_ir::ProofId::new(0),
                        body_digest: trust_ir::proof::ProofDigest::sha256([7; 32]),
                    }),
                },
            ),
        ];
        let linked = link_modules(&modules).expect("modules link").0;

        let by_name = |n: &str| {
            linked
                .functions
                .iter()
                .find(|f| f.name == n)
                .unwrap_or_else(|| panic!("{n} survived the link"))
        };
        assert_eq!(
            by_name("ungated_fn").body_gate,
            Some(BodyGate::Ungated),
            "an Ungated body must NOT be laundered into the permitted `None` state by a merge"
        );
        assert_eq!(
            by_name("gated_fn").body_gate,
            Some(BodyGate::Gated {
                authority: "clean-kernel-tv".to_string(),
                evidence: None,
            }),
            "the gating authority must survive the link"
        );
        assert_eq!(
            by_name("gated_fn").display_path.as_deref(),
            Some("crate::gated_fn")
        );
        assert_eq!(
            by_name("evidenced_fn").body_gate,
            Some(BodyGate::gated("clean-kernel-tv")),
            "the license's authority survives the link and its evidence is dropped"
        );
    }

    #[test]
    fn linker_remaps_refinement_tables_deterministically_and_roundtrips() {
        let modules = vec![
            ("a".to_string(), refined_array_module("a", "ga")),
            ("b".to_string(), refined_array_module("b", "gb")),
        ];
        let linked = link_modules(&modules).expect("refined modules link").0;
        let linked_again = link_modules(&modules).expect("repeat link succeeds").0;
        assert_eq!(linked, linked_again, "linking must be deterministic");
        assert_eq!(linked.universes.len(), 1, "equal universes are shared");
        assert_eq!(linked.predicates.len(), 3, "equal predicates are shared");
        // Positional tables are appended whole (the library merge keeps each
        // input's own rows, so a merge into an empty image is the identity);
        // every REFERENCE to an equal row points at the first one.
        assert_eq!(linked.types.len(), 4, "each input's rows are appended");
        assert_eq!(linked.globals[0].ty, linked.globals[1].ty);

        let Ty::Array(refined, 4) = linked.globals[0].ty else {
            panic!("linked global did not preserve the nested refined array")
        };
        let Ty::Refine(base, pred) = linked.types[refined.as_usize()] else {
            panic!("array element did not remap to a refinement")
        };
        assert_eq!(linked.types[base.as_usize()], Ty::I32);
        assert_eq!(
            linked.predicates[pred.as_usize()],
            Pred::Conj(vec![PredId::new(0), PredId::new(1)])
        );

        let bytes =
            trust_ir::binary::serialize_module(&linked).expect("serialize_module: test fixture");
        let roundtrip = trust_ir::binary::deserialize_module(&bytes).expect("linked image decodes");
        assert_eq!(
            roundtrip, linked,
            "refinement tables survive binary round-trip"
        );
        let report = trust_ir_build::validate::validate_module_report(&roundtrip);
        let errors = report.errors();
        assert!(
            errors.is_empty(),
            "linked refinement image must validate: {errors:?}"
        );
    }

    /// Amendment D (§20): a module dropping `Owned` through its glue. The
    /// glue is function 0, defined or (in a module that only uses it)
    /// declared; function 1 drops through its pointer parameter.
    fn drop_glue_module(name: &str, glue: &str, defined: bool) -> Module {
        let mut module = Module::new(name);
        let owned = Ty::Struct(module.add_struct(trust_ir::StructDef {
            id: trust_ir::StructId::new(0),
            name: "Owned".into(),
            fields: vec![trust_ir::FieldDef {
                name: "data".into(),
                ty: Ty::Ptr,
                offset: None,
            }],
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        }));
        let sig = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::Ptr],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut glue_fn = Function::new(FuncId::new(0), glue, sig, BlockId::new(0));
        if defined {
            let mut block = Block::new(BlockId::new(0));
            block.params.push((ValueId::new(0), Ty::Ptr));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            glue_fn.blocks.push(block);
        }
        module.functions.push(glue_fn);
        let mut user = Function::new(FuncId::new(1), format!("user_{name}"), sig, BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params.push((ValueId::new(0), Ty::Ptr));
        block.body.push(InstrNode::new(Inst::Drop {
            ty: owned.clone(),
            ptr: ValueId::new(0),
        }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        user.blocks.push(block);
        module.functions.push(user);
        module
            .set_drop_glue(owned, FuncId::new(0))
            .expect("one row");
        module
    }

    #[test]
    fn run_links_drop_glue_tables() {
        // The table is CARRIED through the link (dropping it would turn
        // every resolved drop back into an unresolved one): both modules'
        // rows remap to the one merged glue and the one merged `Owned`,
        // and the identical rows collapse to one.
        let modules = vec![
            ("a".to_string(), drop_glue_module("a", "drop_owned", true)),
            ("b".to_string(), drop_glue_module("b", "drop_owned", false)),
        ];
        let linked = link_modules(&modules).expect("drop-glue modules link").0;
        let glue = linked
            .functions
            .iter()
            .find(|f| f.name == "drop_owned")
            .expect("the glue is linked")
            .id;
        assert_eq!(
            linked.drop_glue,
            vec![trust_ir::DropGlueEntry {
                glue,
                ty: Ty::Struct(trust_ir::StructId::new(0)),
            }]
        );
        let bytes =
            trust_ir::binary::serialize_module(&linked).expect("serialize_module: test fixture");
        let back = trust_ir::binary::deserialize_module(&bytes).expect("linked image decodes");
        assert_eq!(back, linked, "the table survives the binary round trip");
        let report = trust_ir_build::validate::validate_module_report(&linked);
        assert!(report.errors().is_empty(), "{:?}", report.errors());
        assert!(
            report.unresolved_drops().is_empty(),
            "every linked drop resolves"
        );
    }

    #[test]
    fn run_refuses_two_modules_stating_different_glue_for_one_type() {
        let modules = vec![
            ("a".to_string(), drop_glue_module("a", "drop_owned", true)),
            (
                "b".to_string(),
                drop_glue_module("b", "drop_owned_too", true),
            ),
        ];
        let error = link_modules(&modules).expect_err("two glues for one type");
        assert!(error.contains("drop_glue row"), "{error}");
        assert!(error.contains("already has drop glue"), "{error}");
    }

    #[test]
    fn linker_preserves_debug_metadata_and_remaps_scope_files() {
        let mut prefix = Module::new("prefix");
        prefix
            .intern_file("src/prefix.rs")
            .expect("Module::intern_file: test fixture");

        let mut source = Module::new("source");
        let source_file = source
            .intern_file("src/source.rs")
            .expect("Module::intern_file: test fixture");
        let signature = source
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "identity", signature, BlockId::new(0));
        function.value_names = Some(vec![(ValueId::new(7), "input".to_string())]);
        function.scopes = Some(vec![ScopeData {
            parent: None,
            span: Some(SourceSpan {
                file: source_file,
                line: 1,
                col: 0,
            }),
            inlined_at: None,
        }]);
        let mut entry = Block::new(BlockId::new(0));
        entry.params.push((ValueId::new(7), Ty::I32));
        entry.body.push(
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(7)],
            })
            .with_span(SourceSpan {
                file: source_file,
                line: 2,
                col: 4,
            })
            .with_scope(0),
        );
        function.blocks.push(entry);
        source
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");

        let linked = link_modules(&[
            ("prefix".to_string(), prefix),
            ("source".to_string(), source),
        ])
        .expect("debug-bearing modules link")
        .0;
        assert_eq!(
            linked.files,
            vec!["src/prefix.rs".to_string(), "src/source.rs".to_string()]
        );
        let function = &linked.functions[0];
        assert_eq!(
            function.value_names.as_deref(),
            Some(&[(ValueId::new(7), "input".to_string())][..])
        );
        assert_eq!(function.scopes.as_ref().unwrap()[0].span.unwrap().file, 1);
        assert_eq!(function.blocks[0].body[0].span.unwrap().file, 1);
        assert_eq!(function.blocks[0].body[0].scope, Some(0));

        let errors = trust_ir_build::validate_module(&linked);
        assert!(
            errors.is_empty(),
            "linked debug metadata must remain referentially valid: {errors:#?}"
        );
    }

    #[test]
    fn linker_rejects_dangling_refinement_table_ids() {
        let mut bad_base = Module::new("bad-base");
        let pred = bad_base
            .intern_pred(Pred::NonZero)
            .expect("Module::intern_pred: test fixture")
            .expect("predicate interns");
        bad_base
            .globals
            .push(test_global("bad_base", Ty::Refine(TyId::new(99), pred)));
        let err = link_modules(&[("bad-base".to_string(), bad_base)])
            .expect_err("dangling base must fail closed");
        assert!(
            err.contains("dangling id 99 in the types table"),
            "unexpected error: {err}"
        );

        let mut bad_universe = Module::new("bad-universe");
        bad_universe
            .predicates
            .push(Pred::InUniverse(UnivId::new(99), Space::Member));
        let err = link_modules(&[("bad-universe".to_string(), bad_universe)])
            .expect_err("unused dangling universe must fail closed");
        assert!(
            err.contains("dangling id 99 in the universes table"),
            "unexpected error: {err}"
        );

        let mut bad_pred = Module::new("bad-pred");
        let base = bad_pred
            .add_type(Ty::I32)
            .expect("Module::add_type: test fixture");
        bad_pred
            .globals
            .push(test_global("bad_pred", Ty::Refine(base, PredId::new(99))));
        let err = link_modules(&[("bad-pred".to_string(), bad_pred)])
            .expect_err("dangling predicate must fail closed");
        assert!(
            err.contains("dangling id 99 in the predicates table"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn linker_rejects_refinement_whose_base_is_refined() {
        let mut module = Module::new("nested-refine");
        let pred = module
            .intern_pred(Pred::NonZero)
            .expect("Module::intern_pred: test fixture")
            .expect("predicate interns");
        let base = module
            .add_type(Ty::I32)
            .expect("Module::add_type: test fixture");
        let inner = module
            .add_type(Ty::Refine(base, pred))
            .expect("Module::add_type: test fixture");
        module
            .globals
            .push(test_global("nested", Ty::Refine(inner, pred)));
        let err = link_modules(&[("nested-refine".to_string(), module)])
            .expect_err("Refine-on-Refine must fail closed");
        assert!(
            err.contains(
                "types row 1 cannot be merged: a refinement's base is itself a refinement"
            ),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn v0_intrinsic_name_extracts_length_prefixed_ident() {
        assert_eq!(
            v0_intrinsic_name("_RINvNtCsbu97CrmFxuv_4core10intrinsics5ctpopyECs_7fc_bits"),
            Some("ctpop".to_string())
        );
        assert_eq!(
            v0_intrinsic_name(
                "_RINvNtCsbu97CrmFxuv_4core10intrinsics20unchecked_funnel_shlyECs_8fc_float"
            ),
            Some("unchecked_funnel_shl".to_string())
        );
        assert_eq!(
            v0_intrinsic_name("_RNvNtCsbu97CrmFxuv_4core10intrinsics15caller_locationCs_8fc"),
            Some("caller_location".to_string())
        );
        assert_eq!(
            v0_intrinsic_name("_RNvCsoF1AqU8Qvp_7___rustc17rust_begin_unwind"),
            None
        );
    }

    #[test]
    fn classify_matches_the_battery_externs() {
        use BuiltinKind::*;
        assert_eq!(
            BuiltinKind::classify("_RNvCsoF1AqU8Qvp_7___rustc12___rust_alloc"),
            Alloc
        );
        assert_eq!(
            BuiltinKind::classify("_RNvCsoF1AqU8Qvp_7___rustc19___rust_alloc_zeroed"),
            AllocZeroed
        );
        assert_eq!(
            BuiltinKind::classify("_RNvCsoF1AqU8Qvp_7___rustc14___rust_dealloc"),
            Dealloc
        );
        assert_eq!(
            BuiltinKind::classify("_RNvCsoF1AqU8Qvp_7___rustc26___rust_alloc_error_handler"),
            Trap
        );
        assert_eq!(
            BuiltinKind::classify(
                "_RNvCsoF1AqU8Qvp_7___rustc35___rust_no_alloc_shim_is_unstable_v2"
            ),
            NoOp
        );
        assert_eq!(
            BuiltinKind::classify(
                "_RINvNtCsbu97CrmFxuv_4core10intrinsics12ctlz_nonzeroyECs_7fc_bits"
            ),
            Ctlz
        );
        // The check/hint no-op family: the 16-char length prefix must not
        // swallow the trailing generic-args mangling (`Acj3_E…`).
        assert_eq!(
            BuiltinKind::classify(
                "_RINvNtCsbu97CrmFxuv_4core10intrinsics16assert_inhabitedAcj3_ECs_9fc_strops"
            ),
            NoOp
        );
        assert_eq!(
            BuiltinKind::classify(
                "_RINvNtCsbu97CrmFxuv_4core10intrinsics23is_val_statically_knownyECs_6fc_fmt"
            ),
            ConstFalse
        );
        assert_eq!(
            BuiltinKind::classify("_RNvNtCsbu97CrmFxuv_4core10intrinsics9cold_pathCs_6fc_fmt"),
            NoOp
        );
        assert_eq!(
            BuiltinKind::classify("_RNvCsoF1AqU8Qvp_7___rustc17rust_begin_unwind"),
            Trap
        );
        assert_eq!(BuiltinKind::classify("memmove"), Memmove);
        // The macOS RNG seed source, with and without the leading underscore
        // the object symbol may carry.
        assert_eq!(BuiltinKind::classify("CCRandomGenerateBytes"), RandomBytes);
        assert_eq!(BuiltinKind::classify("_CCRandomGenerateBytes"), RandomBytes);
        // `compare_bytes` is memcmp; `exact_div` is its own division builtin.
        assert_eq!(
            BuiltinKind::classify(
                "_RNvNtCsbu97CrmFxuv_4core10intrinsics13compare_bytesCs_12fc_sortdedup"
            ),
            Memcmp
        );
        assert_eq!(
            BuiltinKind::classify(
                "_RINvNtCsbu97CrmFxuv_4core10intrinsics9exact_divjECs_11fc_strbuild"
            ),
            ExactDiv
        );
    }

    /// `exact_div(a, b)` lowers to an unsigned `UDiv` (`u64`) or signed
    /// `SDiv` (`i64`) per its lane, and its body executes to `a / b`.
    #[test]
    fn exact_div_body_divides_by_lane_signedness() {
        for (word, dividend, divisor, expected) in [
            (Ty::U64, 84_i128, 4, 21_i128),
            (Ty::I64, -84_i128, 4, -21_i128),
        ] {
            let sig = FuncTy {
                abi: None,
                params: vec![word.clone(), word.clone()],
                returns: vec![word.clone()],
                is_vararg: false,
            };
            let (entry, blocks) = build_builtin_body(BuiltinKind::ExactDiv, &sig)
                .expect("fresh ids")
                .expect("exact_div body builds");
            let mut module = Module::new("exact_div_test");
            let ft = FuncTyId::new(0);
            module.func_types.push(sig);
            let mut func = Function::new(FuncId::new(0), "exact_div", ft, entry);
            func.blocks = blocks;
            module.functions.push(func);

            let a = InterpretValue::int(word.clone(), dividend).unwrap();
            let b = InterpretValue::int(word.clone(), divisor).unwrap();
            let outcome = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [a, b])
                .expect("exact_div executes");
            let got = outcome.returns[0].as_int().unwrap();
            let got = if int_is_signed(&word).unwrap() {
                got.as_signed()
            } else {
                got.as_unsigned() as i128
            };
            assert_eq!(got, expected, "exact_div {word} lane");
        }
    }

    /// `compare_bytes(a, b, n)` returns the sign of the first differing byte
    /// (memcmp semantics), 0 when the prefixes are equal.
    #[test]
    fn compare_bytes_body_has_memcmp_semantics() {
        let sig = FuncTy {
            abi: None,
            params: vec![Ty::Ptr, Ty::Ptr, Ty::U64],
            returns: vec![Ty::I32],
            is_vararg: false,
        };
        let (entry, blocks) = build_builtin_body(BuiltinKind::Memcmp, &sig)
            .expect("fresh ids")
            .expect("compare_bytes body builds");
        // Two 3-byte buffers written into interpreter memory, compared.
        let mut module = Module::new("compare_bytes_test");
        let cmp_ft = FuncTyId::new(0);
        module.func_types.push(sig);
        let harness_ft = FuncTyId::new(1);
        module.func_types.push(FuncTy {
            abi: None,
            params: Vec::new(),
            returns: vec![Ty::I32],
            is_vararg: false,
        });

        let mut cmp = Function::new(FuncId::new(0), "compare_bytes", cmp_ft, entry);
        cmp.blocks = blocks;

        // harness(): a=[1,2,3], b=[1,2,4] -> compare_bytes returns -1.
        let mut bb = BodyBuilder::new();
        let hb = bb.add_block().expect("fresh id");
        bb.switch_to(hb);
        let three = bb.const_int(Ty::U64, 3).expect("fresh id");
        let a = bb.heap_alloc_bytes(three).expect("fresh id");
        let b = bb.heap_alloc_bytes(three).expect("fresh id");
        for (i, (av, bv)) in [(1, 1), (2, 2), (3, 4)].into_iter().enumerate() {
            let off = bb.const_int(Ty::U64, i as i128).expect("fresh id");
            let ap = bb.gep_u8(a, off).expect("fresh id");
            let abyte = bb.const_int(Ty::U8, av).expect("fresh id");
            bb.store_u8(ap, abyte);
            let bp = bb.gep_u8(b, off).expect("fresh id");
            let bbyte = bb.const_int(Ty::U8, bv).expect("fresh id");
            bb.store_u8(bp, bbyte);
        }
        let n = bb.const_int(Ty::U64, 3).expect("fresh id");
        let res = bb
            .push(Inst::Call {
                callee: FuncId::new(0),
                args: vec![a, b, n],
            })
            .expect("fresh id");
        bb.ret(vec![res]);
        let mut harness = Function::new(FuncId::new(1), "harness", harness_ft, hb);
        harness.blocks = bb.blocks;

        module.functions.push(cmp);
        module.functions.push(harness);

        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(1), [])
            .expect("compare_bytes harness executes");
        assert_eq!(outcome.returns[0].as_int().unwrap().as_signed(), -1);
    }

    /// `CCRandomGenerateBytes(bytes, count)` zero-fills the buffer and
    /// returns `kCCSuccess` (0). A harness pre-seeds the buffer with `0xFF`s,
    /// calls the builtin, then reads a byte back to prove it was overwritten.
    #[test]
    fn random_bytes_body_zero_fills_and_returns_success() {
        let sig = FuncTy {
            abi: None,
            params: vec![Ty::Ptr, Ty::U64],
            returns: vec![Ty::I32],
            is_vararg: false,
        };
        let (entry, blocks) = build_builtin_body(BuiltinKind::RandomBytes, &sig)
            .expect("fresh ids")
            .expect("random_bytes body builds");
        let mut module = Module::new("random_bytes_test");
        let rng_ft = FuncTyId::new(0);
        module.func_types.push(sig);
        let harness_ft = FuncTyId::new(1);
        module.func_types.push(FuncTy {
            abi: None,
            params: Vec::new(),
            // (return code, first output byte)
            returns: vec![Ty::I32, Ty::U8],
            is_vararg: false,
        });

        let mut rng = Function::new(FuncId::new(0), "random_bytes", rng_ft, entry);
        rng.blocks = blocks;

        // harness(): buf=[0xFF; 4]; rc = random_bytes(buf, 4); return (rc, buf[0]).
        let mut bb = BodyBuilder::new();
        let hb = bb.add_block().expect("fresh id");
        bb.switch_to(hb);
        let four = bb.const_int(Ty::U64, 4).expect("fresh id");
        let buf = bb.heap_alloc_bytes(four).expect("fresh id");
        for i in 0..4i128 {
            let off = bb.const_int(Ty::U64, i).expect("fresh id");
            let slot = bb.gep_u8(buf, off).expect("fresh id");
            let ff = bb.const_int(Ty::U8, 0xFF).expect("fresh id");
            bb.store_u8(slot, ff);
        }
        let count = bb.const_int(Ty::U64, 4).expect("fresh id");
        let rc = bb
            .push(Inst::Call {
                callee: FuncId::new(0),
                args: vec![buf, count],
            })
            .expect("fresh id");
        let zero_off = bb.const_int(Ty::U64, 0).expect("fresh id");
        let first_slot = bb.gep_u8(buf, zero_off).expect("fresh id");
        let first = bb.load_u8(first_slot).expect("fresh id");
        bb.ret(vec![rc, first]);
        let mut harness = Function::new(FuncId::new(1), "harness", harness_ft, hb);
        harness.blocks = bb.blocks;

        module.functions.push(rng);
        module.functions.push(harness);

        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(1), [])
            .expect("random_bytes harness executes");
        assert_eq!(
            outcome.returns[0].as_int().unwrap().as_signed(),
            0,
            "kCCSuccess"
        );
        assert_eq!(
            outcome.returns[1].as_int().unwrap().as_unsigned(),
            0,
            "buffer byte was overwritten to zero"
        );
    }

    #[test]
    fn tuple_field_offsets_match_c_layout() {
        // (ptr, u8×8): a &str-shaped tuple — ptr at 0, bytes at 8..16.
        let str_shape = [
            Ty::Ptr,
            Ty::U8,
            Ty::U8,
            Ty::U8,
            Ty::U8,
            Ty::U8,
            Ty::U8,
            Ty::U8,
            Ty::U8,
        ];
        assert_eq!(
            tuple_field_offsets(&str_shape),
            Some(vec![0, 8, 9, 10, 11, 12, 13, 14, 15])
        );
        // (u8, ptr): the pointer field is aligned up to offset 8.
        assert_eq!(tuple_field_offsets(&[Ty::U8, Ty::Ptr]), Some(vec![0, 8]));
        // A non-scalar field aborts the computation.
        assert_eq!(tuple_field_offsets(&[Ty::Ptr, Ty::Tuple(vec![])]), None);
    }

    #[test]
    fn word_class_is_pointer_and_pointer_width_ints() {
        for word in [Ty::Ptr, Ty::U64, Ty::I64, Ty::Usize, Ty::Isize] {
            assert!(is_word_ty(&word), "{word:?} is a machine word");
        }
        for not_word in [Ty::U32, Ty::F64, Ty::Bool] {
            assert!(!is_word_ty(&not_word), "{not_word:?} is not a machine word");
        }
    }

    /// One module with a bodyless declaration `f(u64, u64) -> ()` calling
    /// nothing, or a definition `f(ptr, u64) -> ()`.
    fn word_pun_module(name: &str, first: Ty, bodied: bool) -> Module {
        let mut module = Module::new(name);
        let ft = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![first, Ty::U64],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, BlockId::new(0));
        if bodied {
            let mut block = Block::new(BlockId::new(0));
            block.params = vec![(ValueId::new(0), Ty::Ptr), (ValueId::new(1), Ty::U64)];
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(block);
        } else {
            func.linkage = Linkage::External;
        }
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        module
    }

    /// The runner's own link policy: a declaration that spells a 64-bit word
    /// lane differently from the definition is respelled to the definition's
    /// signature, in either input order; two DEFINITIONS that pun are still a
    /// conflict the library merge refuses by name.
    #[test]
    fn a_word_punned_declaration_resolves_against_its_definition() {
        for order in [[false, true], [true, false]] {
            let modules: Vec<(String, Module)> = order
                .iter()
                .enumerate()
                .map(|(i, &bodied)| {
                    let first = if bodied { Ty::Ptr } else { Ty::U64 };
                    (
                        format!("m{i}"),
                        word_pun_module(&format!("m{i}"), first, bodied),
                    )
                })
                .collect();
            let (image, _) = link_modules(&modules).expect("the word pun links");
            assert_eq!(image.functions.len(), 1);
            let f = &image.functions[0];
            assert!(!f.blocks.is_empty(), "the definition wins");
            assert_eq!(
                image.func_types[f.ty.as_usize()].params,
                vec![Ty::Ptr, Ty::U64]
            );
        }
        let both = vec![
            ("a".to_string(), word_pun_module("a", Ty::Ptr, true)),
            ("b".to_string(), word_pun_module("b", Ty::U64, true)),
        ];
        let err = link_modules(&both).expect_err("two punning definitions conflict");
        assert!(
            err.contains("conflicting definitions of @f: ty differs"),
            "unexpected error: {err}"
        );
    }

    /// A one-module program over the pinned `Nat` runtime: the whole row of pinned
    /// declarations (bodyless, `External`, C) and `program` calling
    /// `from_u64`.
    fn nat_runtime_module() -> Module {
        let pin = &trust_ir_build::TRUSTED_HANDLE_RUNTIMES[0];
        let target = trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        };
        let mut mb = trust_ir_build::ModuleBuilder::new_with_target_info("nat", target);
        let decls = mb
            .declare_handle_runtime(pin)
            .expect("pinned declarations on an empty module");
        let from_u64 = decls.entry("from_u64").expect("pinned role");
        let nullary = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("program", nullary);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let seven = fb.uconst(Ty::U64, 7);
        fb.call(from_u64, vec![seven]);
        fb.ret(vec![]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// WS4.6 item 4: synthesis never gives a pinned trusted-runtime entry
    /// point a body. They stay bodyless, their entry ids move into the
    /// reserved range, and the report maps each id back to its symbol.
    #[test]
    fn synthesis_leaves_pinned_runtime_entry_points_bodyless_and_named() {
        let (mut image, _) =
            link_modules(&[("nat".to_string(), nat_runtime_module())]).expect("links");
        let report =
            synthesize_builtins(&mut image, trap_blocks().expect("trap range")).expect("fresh ids");
        assert_eq!(report.stub_count, 0);
        assert!(report.builtins.is_empty());
        // The whole pinned row is declared, so every one of its entry points
        // is collected (derived: WS3.2 widened the row from five roles).
        assert_eq!(
            report.runtime_entries.len(),
            trust_ir_build::TRUSTED_HANDLE_RUNTIMES[0]
                .entry_points
                .len()
        );
        for (k, name) in report.runtime_entries.iter().enumerate() {
            assert!(is_pinned_runtime_entry(name));
            let func = image.function_by_name(name).expect("declared");
            assert!(func.blocks.is_empty(), "@{name} must stay bodyless");
            assert_eq!(func.entry.index(), RUNTIME_ENTRY_BLOCK_BASE + k as u32);
            assert_eq!(report.runtime_entry_name(func.entry), Some(name.as_str()));
            assert_eq!(report.trap_name(func.entry), None);
        }
        assert!(!is_pinned_runtime_entry("program"));
        assert!(
            lowered_image_errors(&image).is_empty(),
            "the lowered image validates: {:?}",
            lowered_image_errors(&image)
        );
    }

    /// WS4.6 item 3, mutation control for the POST-lowering pass: the old
    /// lowering (a trap stub for every bodyless extern, pinned ones included)
    /// is exactly what that pass must catch — one
    /// `HandleEntryPointDefinedLocally` per pinned entry point (the whole row:
    /// derived, since WS3.2 widened it from five roles), and nothing else.
    /// This is the verdict `cmd_run` turns into `internal:` / `EXIT_INTERNAL`.
    #[test]
    fn post_lowering_pass_refuses_stubbed_pinned_entry_points() {
        let (mut image, _) =
            link_modules(&[("nat".to_string(), nat_runtime_module())]).expect("links");
        for func in &mut image.functions {
            if func.blocks.is_empty() {
                let block_id = BlockId::new(TRAP_BLOCK_BASE);
                let mut block = Block::new(block_id);
                let sig = image.func_types[func.ty.as_usize()].clone();
                for (value, ty) in (0u32..).zip(&sig.params) {
                    block.params.push((ValueId::new(value), ty.clone()));
                }
                block.body.push(InstrNode::new(Inst::Unreachable));
                func.entry = block_id;
                func.blocks = vec![block];
            }
        }
        let errors = lowered_image_errors(&image);
        let defined_locally = errors
            .iter()
            .filter(|error| format!("{error:?}").starts_with("HandleEntryPointDefinedLocally"))
            .count();
        let pinned = trust_ir_build::TRUSTED_HANDLE_RUNTIMES[0]
            .entry_points
            .len();
        assert_eq!(defined_locally, pinned, "{errors:?}");
        assert_eq!(errors.len(), pinned, "{errors:?}");
        assert_eq!(EXIT_INTERNAL, 3);
    }

    /// WS4.6 item 2: the linker strips `summary`, every `ProofRef` and every
    /// call `ProofContext`, keeps claim-style annotations, and counts what it
    /// stripped per input function / node.
    #[test]
    fn linker_strips_proof_claims_and_keeps_claim_style_annotations() {
        use trust_ir::FunctionSummary;
        use trust_ir::proof::ProofContext;
        use trust_ir::value::ProofId;

        let mut module = Module::new("claims");
        let ty = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ty, BlockId::new(0));
        func.proofs = vec![
            ProofAnnotation::Pure,
            ProofAnnotation::ProofRef(ProofId::new(3)),
        ];
        func.summary = Some(FunctionSummary::new().proved());
        let mut block = Block::new(BlockId::new(0));
        let mut node = InstrNode::new(Inst::Return { values: vec![] });
        node.proofs = vec![
            ProofAnnotation::NoPanic,
            ProofAnnotation::ProofRef(ProofId::new(4)),
        ];
        node.proof_context = Some(ProofContext {
            assumes: vec![ProofId::new(4)],
            establishes: vec![],
        });
        block.body.push(node);
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let (image, stripped) = link_modules(&[("claims".to_string(), module)]).expect("links");
        assert_eq!(
            stripped,
            StrippedClaims {
                summaries: 1,
                proof_refs: 2,
                proof_contexts: 1,
            }
        );
        let f = &image.functions[0];
        assert_eq!(f.summary, None);
        assert_eq!(f.proofs, vec![ProofAnnotation::Pure]);
        let node = &f.blocks[0].body[0];
        assert_eq!(node.proofs, vec![ProofAnnotation::NoPanic]);
        assert_eq!(node.proof_context, None);
    }

    fn typed_signature_module(name: &str, symbol: &str, revision: Option<&str>) -> Module {
        let mut module = signature_abi_fixture::module().expect("typed ABI fixture IDs fit");
        module.name = name.into();
        if let Some(revision) = revision {
            module.func_types[0].abi.as_mut().unwrap().frontend.revision = revision.into();
        } else {
            module.func_types[0].abi = None;
        }
        module
            .try_add_function(Function::new(
                FuncId::new(0),
                symbol,
                FuncTyId::new(0),
                BlockId::new(0),
            ))
            .expect("one function fits");
        module
    }

    #[test]
    fn linker_preserves_typed_signature_identity_and_refuses_declaration_drift() {
        let a = typed_signature_module("a", "a", Some("revision-a"));
        let b = typed_signature_module("b", "b", Some("revision-b"));
        let c = typed_signature_module("c", "c", Some("revision-a"));
        let (image, _) = link_modules(&[("a".into(), a.clone()), ("b".into(), b), ("c".into(), c)])
            .expect("distinct symbols link");
        assert_eq!(image.functions[0].ty, image.functions[2].ty);
        assert_ne!(image.functions[0].ty, image.functions[1].ty);
        for (index, revision) in [(0, "revision-a"), (1, "revision-b"), (2, "revision-a")] {
            let signature = image.func_type(image.functions[index].ty).unwrap();
            assert_eq!(signature.abi.as_ref().unwrap().frontend.revision, revision);
        }
        for revision in [Some("revision-b"), None] {
            let drift = typed_signature_module("drift", "a", revision);
            assert!(link_modules(&[("a".into(), a.clone()), ("drift".into(), drift)]).is_err());
        }
    }

    #[test]
    fn typed_signature_declarations_never_undergo_legacy_word_respelling() {
        for (canonical_revision, declaration_revision) in [
            (Some("revision-a"), Some("revision-a")),
            (Some("revision-a"), None),
            (None, Some("revision-a")),
        ] {
            let canonical = typed_signature_module("canonical", "f", canonical_revision);
            let mut declaration = typed_signature_module("declaration", "f", declaration_revision);
            declaration.func_types[0].params[0] = Ty::U64;
            let before = declaration.func_types.clone();
            let inputs = [
                ("canonical".into(), canonical),
                ("declaration".into(), declaration),
            ];
            let respelled = respell_word_punned_declarations(&inputs).expect("inspect signatures");
            assert_eq!(
                respelled[1].1.func_types, before,
                "typed declarations keep their exact descriptor and pointer roles: {canonical_revision:?}, {declaration_revision:?}",
            );
            assert!(link_modules(&inputs).is_err());
        }
    }

    #[test]
    fn unrecorded_signature_declarations_keep_legacy_word_respelling() {
        let canonical = typed_signature_module("canonical", "f", None);
        let mut declaration = typed_signature_module("declaration", "f", None);
        declaration.func_types[0].params[0] = Ty::U64;
        let inputs = [
            ("canonical".into(), canonical),
            ("declaration".into(), declaration),
        ];
        let respelled = respell_word_punned_declarations(&inputs).expect("legacy word lanes agree");
        let declaration = &respelled[1].1;
        let signature = declaration.func_type(declaration.functions[0].ty).unwrap();
        assert_eq!(signature.params[0], Ty::Ptr);
        assert_eq!(signature.abi, None);
        assert!(link_modules(&inputs).is_ok());
    }
}
