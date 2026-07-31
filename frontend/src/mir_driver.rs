// trust_ir_mir — STAGE1-HOSTED MIR -> trust-ir whole-program driver.
//
// The real path to lowering ALL functions of a crate (clean-kernel) WITHOUT the
// absent nightly-2026-04-20 toolchain that trust-cg's MIR codegen backend pins.
//
// KEY INSIGHT: the STAGE1 Trust compiler (rustc 1.96.0-dev) IS a full rustc with
// rustc_private — its sysroot ships librustc_monomorphize / rustc_middle /
// rustc_codegen_ssa / rustc_interface, and `tcx.collect_and_partition_mono_items(())`,
// `tcx.instance_mir(...)`, `MonoItem` are all available. So we HOST the MIR
// lowering on stage1 rather than the absent nightly backend.
//
// Unlike `trust_ir_frontend` (which hooks `after_expansion` for THIR, because
// MIR-build steals THIR), this hooks `after_analysis(tcx)`: at that point MIR is
// already built and available, and we do NOT need THIR. The existing THIR driver
// (trust_ir_frontend) is untouched — this is an ADDITIVE sibling binary.
//
// Usage:
//   trust_ir_mir [--mir-coverage] [--mir-lower] <rustc args ... file.rs>
//   --mir-coverage  Phase 1: enumerate every MonoItem::Fn + tally a RANKED
//                   histogram of TerminatorKind / Rvalue / StatementKind
//                   variants + the Ty/Aggregate/Cast shapes that appear. This
//                   is the precise "what MIR constructs must we lower" gap map.
//   --mir-lower     Phase 2 (best-effort): also attempt a MINIMAL lowering of
//                   the simplest functions and report lowered-ok vs failed.
//
// Build against the bootstrap-prepared rustc-private metadata as documented in
// Cargo.toml. At runtime set RUSTC to the matching public stage1 compiler (or
// pass its `--sysroot` explicitly) and provide the private dylib search path.

#![feature(rustc_private)]
#![allow(rustc::default_hash_types)]
#![allow(rustc::potential_query_instability)]

extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use std::collections::BTreeMap;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::mono::MonoItem;
use rustc_middle::mir::{
    AggregateKind, Body, CastKind, Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::ty::{self, Instance, Ty, TyCtxt};

mod mir_lower;
// The SHARED rustc-Span -> trust-ir SourceSpan threading (also compiled into the
// `trust_ir_frontend` lib as `trust_ir_frontend::span_map`). Included as SOURCE
// so this binary stays lib-independent (like `mir_lower`'s layout re-derivation).
mod span_map;

struct MirCallbacks {
    /// Phase 1: enumerate + histogram (always on for this driver).
    coverage: bool,
    /// Phase 2: also attempt the minimal MIR -> trust-ir lowering.
    lower: bool,
    /// When set, restrict the histogram + lowering to mono-items whose def_id is
    /// LOCAL to the crate being compiled (clean-kernel's OWN fns, not the ~25K
    /// monomorphized std/dep generics the collector also pulls in). This is the
    /// actionable "what does the KERNEL's code need lowered" view (whnf/def_eq).
    local_only: bool,
    /// EMIT mode (`--mir-emit <fnsubstr> <outpath>`): instead of (or alongside)
    /// the coverage tally, fully lower the FIRST mono-item fn whose def-path
    /// CONTAINS `fnsubstr`, write its SELF-CONTAINED trust-ir module text to
    /// `outpath`, and report `validate_module`'s error count. `None` unless
    /// `--mir-emit` was passed. This is the VERIFICATION leg: the emitted text is
    /// the exact artifact trust-cg parses + JITs + triple-oracles.
    emit: Option<(String, String)>,
    /// EMIT-CLOSURE mode (`--mir-emit-closure <fnsubstr> <outpath>`): like `--mir-emit`,
    /// but starting from the FIRST mono-item fn matching `fnsubstr`, compute the
    /// call-graph CLOSURE over the crate's OWN fns and lower EVERY member into ONE
    /// shared module, wiring cross-member `Call`s to the in-module body `FuncId`s
    /// (extern decls remain only for the true leaves). This is the MULTI-FUNCTION
    /// verification leg: e.g. `def_eq` composing the REAL in-module whnf +
    /// structural_eq. `None` unless `--mir-emit-closure` was passed.
    emit_closure: Option<(String, String)>,
    /// EMIT-EACH mode (`--mir-emit-each <outdir>`): the LINK+RUN CENSUS leg. For
    /// EVERY mono-item fn (or every LOCAL one when `--mir-local-only` is set),
    /// lower it to its OWN self-contained trust-ir module and write it to
    /// `<outdir>/<sanitized-def-path>.trust_ir`, printing one machine-parseable
    /// manifest line per fn (`EMIT-EACH <name> -> <path> | validate=<n>` or
    /// `EMIT-EACH-FAIL <name> :: <reason>`). This gives per-function attribution
    /// the substring-matching `--mir-emit` cannot (prefix-sharing names like
    /// `is_geq` vs `is_geq_core`). `None` unless `--mir-emit-each` was passed.
    emit_each: Option<String>,
}

impl Callbacks for MirCallbacks {
    // Force LOCAL instantiation of every reachable generic for the whole-program
    // `--mir-emit-each` census. With the default `-Zshare-generics`, an
    // upstream-shared monomorphization (e.g. `RawVecInner::<A>::grow_amortized`,
    // `grow_amortized`'s allocator helpers — provided by a precompiled std/gimli
    // crate) is collected as an EXTERNAL reference, NOT a local `MonoItem`, so
    // `run_mir_emit_each` never lowers it and the whole-program link has undefined
    // std-internal leaves (the very ones a heap-using program calls on its happy
    // path). `share_generics = false` makes the collector instantiate them in THIS
    // crate — the EXACT reachable set, never all of std — so every function on the
    // call graph emits through trust-ir. Scoped to emit-each (the link+run leg); the
    // coverage / single-fn emit / emit-closure modes keep the ambient default.
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        if self.emit_each.is_some() {
            config.opts.unstable_opts.share_generics = Some(false);
        }
    }

    // Hook `after_analysis`: MIR IS built and available here (the THIR steal that
    // forces `trust_ir_frontend` to use `after_expansion` is irrelevant — we read
    // MIR, not THIR). `tcx.collect_and_partition_mono_items(())` runs the
    // monomorphization collector and partitions every reachable MonoItem into
    // codegen units; `tcx.instance_mir(instance.def)` returns the post-transform
    // MIR `Body` for each `MonoItem::Fn(instance)`.
    fn after_analysis(&mut self, _compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        // EMIT mode runs first (and on its own): it lowers ONE named fn and writes
        // its self-contained trust-ir text — the verification artifact. It is
        // additive: the coverage tally only runs when EMIT was not requested, so the
        // existing `--mir-coverage`/`--mir-lower` behavior is unchanged.
        if let Some(outdir) = self.emit_each.clone() {
            run_mir_emit_each(tcx, &outdir, self.local_only);
        } else if let Some((fnsubstr, outpath)) = self.emit_closure.clone() {
            run_mir_emit_closure(tcx, &fnsubstr, &outpath);
        } else if let Some((fnsubstr, outpath)) = self.emit.clone() {
            run_mir_emit(tcx, &fnsubstr, &outpath);
        } else if self.coverage {
            run_mir_coverage(tcx, self.lower, self.local_only);
        }
        Compilation::Stop
    }
}

/// EMIT driver (`--mir-emit <fnsubstr> <outpath>`): find the FIRST `MonoItem::Fn`
/// whose def-path CONTAINS `fnsubstr`, lower it to a SELF-CONTAINED trust-ir module
/// (its lowered local callees included as needed; self-recursion wired in-module;
/// extern callees stay 0-block imports for the round-trip to bind/stub), write the
/// module text to `outpath`, and report `validate_module`'s error count. We print a
/// clear EMIT-OK / EMIT-FAIL line so the build/run log records the verification step.
fn run_mir_emit(tcx: TyCtxt<'_>, fnsubstr: &str, outpath: &str) {
    eprintln!("== trust_ir_mir EMIT: lower the fn matching `{fnsubstr}` -> {outpath} ==");
    let mono = tcx.collect_and_partition_mono_items(());
    for cgu in mono.codegen_units {
        for (mono_item, _data) in cgu.items_in_deterministic_order(tcx) {
            if let MonoItem::Fn(instance) = mono_item {
                let name = tcx.def_path_str(instance.def_id());
                if !name.contains(fnsubstr) {
                    continue;
                }
                // Skip synthetic shims (their def-path can still match a substring);
                // we want the user's real fn body.
                if !matches!(instance.def, ty::InstanceKind::Item(_)) {
                    continue;
                }
                let body: &Body<'_> = tcx.instance_mir(instance.def);
                match mir_lower::lower_module_for_emit(tcx, instance, body) {
                    Ok((module, errs)) => {
                        let text = format!("{module}");
                        if let Err(e) = std::fs::write(outpath, &text) {
                            eprintln!("EMIT-FAIL {name}: write {outpath} failed: {e}");
                            return;
                        }
                        eprintln!(
                            "EMIT-OK {name}: wrote {} bytes to {outpath}; validate_module = {} error(s)",
                            text.len(),
                            errs.len()
                        );
                        if !errs.is_empty() {
                            eprintln!("   first validation error: {:?}", errs.first());
                        }
                        // Span-threading provenance: report per lowered BODY fn
                        // (externs have no blocks) how many instructions carry a
                        // real SourceSpan and which file they point at. The
                        // acceptance gate asserts on these lines.
                        for f in module.functions.iter().filter(|f| !f.blocks.is_empty()) {
                            eprintln!("   {}", span_map::function_span_report(&module, f));
                        }
                        // Round-trip the text back through the parser as a
                        // self-check, so EMIT-OK guarantees parseable output.
                        match trust_ir::parser::parse_module(&text) {
                            Ok(_) => eprintln!("   re-parse: OK (parse_module round-trips)"),
                            Err(e) => eprintln!("   re-parse: FAILED: {e:?}"),
                        }
                        return;
                    }
                    Err(reason) => {
                        eprintln!("EMIT-FAIL {name}: lowering bailed: {reason}");
                        return;
                    }
                }
            }
        }
    }
    eprintln!("EMIT-FAIL: no MonoItem::Fn whose def-path contains `{fnsubstr}` was found");
}

/// EMIT-EACH driver (`--mir-emit-each <outdir>`): the LINK+RUN CENSUS leg. Lower
/// EVERY mono-item fn (or every LOCAL fn when `local_only`) to its OWN
/// self-contained trust-ir module and write it to `<outdir>/<sanitized>.trust_ir`.
/// One manifest line per fn is printed so an external census script can pair each
/// emitted module with its def-path (attribution the substring `--mir-emit` cannot
/// give for prefix-sharing names).
fn run_mir_emit_each<'tcx>(tcx: TyCtxt<'tcx>, outdir: &str, local_only: bool) {
    eprintln!("== trust_ir_mir EMIT-EACH: lower every {}fn -> {outdir}/*.trust_ir ==",
        if local_only { "LOCAL " } else { "" });
    if let Err(e) = std::fs::create_dir_all(outdir) {
        eprintln!("EMIT-EACH-FATAL: cannot create {outdir}: {e}");
        return;
    }
    let mono = tcx.collect_and_partition_mono_items(());
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    let (mut ok, mut fail) = (0usize, 0usize);

    // Seed a WORKLIST with every mono-item Fn instance, then BFS the REFERENCE
    // CLOSURE over `Item` callees the collector legitimately pruned but our
    // non-optimizing / non-inlining lowering still emits as real `call @sym` edges:
    // dead `condbr const false` callees (`if needs_drop::<(i64,i64)>() { .. }`),
    // `mentioned`-not-`used` items (a `Debug::fmt` reached only via dead formatting),
    // and upstream `#[inline]` fns the collector inlined away (`ctrl_slice`). Without
    // this, the whole-program link dangles on symbols that name a real MIR body — the
    // fix is to LOWER that body (never to shim a function that has MIR). `queued`
    // dedups worklist membership (expand each instance once); `seen` dedups emission.
    // See `mir_lower::referenced_item_callees`. Scoped to the whole-program census
    // (`!local_only`); `--mir-local-only` keeps its crate-local-only semantics.
    let mut worklist: Vec<Instance<'_>> = Vec::new();
    let mut queued: std::collections::HashSet<String> = std::collections::HashSet::new();
    for cgu in mono.codegen_units {
        for (mono_item, _data) in cgu.items_in_deterministic_order(tcx) {
            if let MonoItem::Fn(instance) = mono_item {
                let sym = tcx.symbol_name(instance).name.to_string();
                if queued.insert(sym) {
                    worklist.push(instance);
                }
            }
        }
    }
    // UNWIND (panic=unwind) lane EXTRA ROOTS: the panic runtime pieces behind
    // the extern lang-item boundary, which the collector never seeds from a
    // corpus crate. They are ordinary Rust MIR in the (MIR-complete) sysroot —
    // emit them through the pipeline like any other fn:
    //   * the `eh_personality` lang item (std's `rust_eh_personality`) — called
    //     by libunwind through each frame's CIE personality pointer;
    //   * `panic_unwind`'s `__rust_start_panic` (raise) and
    //     `__rust_panic_cleanup` (catch-side payload extraction), referenced by
    //     std::panicking through `extern "Rust"` declarations.
    // Under panic=abort nothing is added (byte-stable census).
    if tcx.sess.panic_strategy().unwinds() {
        let mut push_root = |instance: Instance<'tcx>, what: &str| {
            let sym = tcx.symbol_name(instance).name.to_string();
            if queued.insert(sym.clone()) {
                worklist.push(instance);
                eprintln!("EMIT-EACH EH-ROOT {what} -> {sym}");
            }
        };
        if let Some(did) = tcx.lang_items().eh_personality() {
            push_root(Instance::mono(tcx, did), "eh_personality lang item");
        } else {
            eprintln!("EMIT-EACH EH-ROOT MISSING: no eh_personality lang item");
        }
        // The PANIC HANDLER (`#[panic_handler]` — std's `begin_panic_handler`,
        // link symbol `rust_begin_unwind`): every CORE-family panic
        // (`panic_fmt`, the assert-class `panic_const_*` / `panic_bounds_check`
        // entry points) reaches it ONLY through the `extern "Rust" panic_impl`
        // declaration, which the closure walk cannot cross (a foreign decl has
        // no MIR). Seed the real body so the symbol resolves at whole-program
        // link — the assert-unwind lane's raise path.
        if let Some(did) = tcx.lang_items().panic_impl() {
            push_root(Instance::mono(tcx, did), "panic_impl lang item");
        } else {
            eprintln!("EMIT-EACH EH-ROOT MISSING: no panic_impl lang item");
        }
        // The panic-runtime `#[rustc_std_internal_symbol]` leaves the collector
        // never seeds from a corpus crate — each is referenced only across the
        // `extern "Rust"/"C"` lang-item boundary (a foreign decl with no MIR the
        // reference-closure cannot cross):
        //   * panic_unwind's `__rust_start_panic` (raise) + `__rust_panic_cleanup`
        //     (catch-side payload extraction);
        //   * LANE C — std's `__rust_drop_panic` (called by the panic runtime's
        //     `exception_cleanup` when a Rust exception object is deleted without
        //     being rethrown — `rtabort!`) and `__rust_foreign_exception` (called
        //     from the catch-side `cleanup` on a non-Rust exception class —
        //     `rtabort!`). Both are ordinary std MIR (they abort by design); the
        //     minimal-hook corpora never reach them at runtime (every panic is
        //     caught, no foreign exception is ever raised) but the whole-program
        //     LINK references them from panic_unwind's `exception_cleanup`/`cleanup`
        //     bodies, so their real (aborting) bodies must resolve — emit them
        //     through the pipeline like every other fn rather than shim them.
        for &cnum in tcx.crates(()) {
            let cname = tcx.crate_name(cnum);
            let cname = cname.as_str();
            if cname != "panic_unwind" && cname != "std" {
                continue;
            }
            for (sym, _info) in tcx.exported_non_generic_symbols(cnum) {
                let rustc_middle::middle::exported_symbols::ExportedSymbol::NonGeneric(did) =
                    sym
                else {
                    continue;
                };
                let path = tcx.def_path_str(*did);
                if path.ends_with("__rust_start_panic")
                    || path.ends_with("__rust_panic_cleanup")
                {
                    push_root(Instance::mono(tcx, *did), "panic_unwind runtime");
                } else if path.ends_with("__rust_drop_panic")
                    || path.ends_with("__rust_foreign_exception")
                {
                    push_root(Instance::mono(tcx, *did), "panic runtime cleanup shim");
                }
            }
        }
    }
    let mut closure_pulled = 0usize;
    let mut cursor = 0usize;
    while cursor < worklist.len() {
        let instance = worklist[cursor];
        cursor += 1;
        if local_only && !instance.def_id().is_local() {
            continue;
        }
        // FIX #2a — emit real function bodies (`Item`) AND the four synthetic
        // shim kinds the whole-program link census found REFERENCED-BUT-NEVER-
        // EMITTED: DropGlue (`drop_in_place::<T>` — its absence is the 140KB run
        // leak), ClosureOnceShim, VTableShim, and FnPtrShim. All four have
        // lowerable MIR via `tcx.instance_mir(instance.def)` and, emitted under
        // their `tcx.symbol_name` (FIX #1), resolve the callers that reference
        // them. Other InstanceKinds (Intrinsic / Virtual / CloneShim / NEON /
        // alloc / panicking leaves) have no MIR here and are a separate
        // runtime-provision tranche — left out so their `instance_mir` never ICEs.
        let is_item = matches!(instance.def, ty::InstanceKind::Item(_));
        let is_emittable_shim = matches!(
            instance.def,
            // 1.99: shim variants moved under `InstanceKind::Shim(ShimKind::…)`.
            // COROUTINE FAMILY: `ConstructCoroutineInClosure` is the
            // `<{async closure} as AsyncFnOnce>::async_call_once` body (build_
            // construct_coroutine_by_move_shim): one Coroutine aggregate over the
            // moved closure fields + Return — entirely existing constructs, and
            // callers reference it by `tcx.symbol_name`, so leaving it out was a
            // silent skip that broke the whole-program link of any AsyncFnOnce
            // consumer.
            ty::InstanceKind::Shim(
                ty::ShimKind::DropGlue(..)
                    | ty::ShimKind::ClosureOnce { .. }
                    | ty::ShimKind::VTable(_)
                    | ty::ShimKind::FnPtr(..)
                    | ty::ShimKind::ConstructCoroutineInClosure { .. }
                    // LANE C: the derived `<T as Clone>::clone` shim — its MIR is
                    // synthesized on demand (field-by-field clone) and callers
                    // reference it by `tcx.symbol_name` (e.g. a `Map<I, F>` clone
                    // cloning its closure field), so leaving it out dangled the
                    // shim symbol as a cold-path abort probe.
                    | ty::ShimKind::Clone(..),
            )
        );
        if !is_item && !is_emittable_shim {
            continue;
        }
        // REFERENCE CLOSURE: an `Item` on the worklist may call functions the
        // mono collector pruned. Enqueue each referenced `Item` callee (deduped
        // by `queued`) so its body is lowered too. Guarded by `catch_unwind`
        // because building the classifying `Cx` monomorphizes the callee args
        // and can, for an exotic instance, ICE — a failure here must not abort
        // the census. Skipped under `--mir-local-only` (that mode is scoped to
        // crate-local fns, not the cross-crate whole-program link).
        if (is_item || is_emittable_shim) && !local_only {
            let extra = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let body: &Body<'_> = tcx.instance_mir(instance.def);
                mir_lower::referenced_item_callees(tcx, instance, body)
            }))
            .unwrap_or_else(|_| {
                eprintln!(
                    "EMIT-EACH PULL-PANIC {} (its callees were NOT enqueued)",
                    tcx.def_path_str(instance.def_id())
                );
                Vec::new()
            });
            for callee in extra {
                let csym = tcx.symbol_name(callee).name.to_string();
                if queued.insert(csym) {
                    worklist.push(callee);
                    closure_pulled += 1;
                }
            }
        }
        // Human-readable manifest name (def-path).
        let name = tcx.def_path_str(instance.def_id());
        // Dedup + filename key = the unique v0-mangled SYMBOL, for Items AND
        // shims alike. Keying on the def-path is WRONG: a generic Item has one
        // def-path but MANY monomorphizations (`max_gen::<i64>` and
        // `max_gen::<u32>` both read `max_gen`), and the shim kinds share a
        // def-path across every concrete type (`drop_in_place::<T>` all read
        // `drop_in_place`) — so a def-path key collapses distinct link symbols
        // into one file and leaves the rest UNDEFINED at whole-program link. The
        // symbol is exactly the linker symbol the emitted definition now carries
        // (FIX #1), so this is precisely one module per distinct link symbol.
        let dedup_key = tcx.symbol_name(instance).name.to_string();
        if !seen.insert(dedup_key.clone()) {
            continue;
        }
        let mut sanitized: String = dedup_key
            .chars()
            .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
            .collect();
        // macOS caps a single path component at 255 bytes; a deeply-nested
        // monomorphized shim symbol (e.g. a hashbrown `call_once`) can exceed
        // that. Truncate + append a stable hash of the full key so the FILENAME
        // stays filesystem-friendly and unique. Only the filename is shortened —
        // the module's INTERNAL function symbol is the full v0-mangled name
        // (FIX #1). The gate never fires for short Item def-paths, so their
        // filenames are byte-identical to pre-fix.
        if sanitized.len() > 180 {
            use std::hash::{Hash, Hasher};
            let mut h = std::collections::hash_map::DefaultHasher::new();
            dedup_key.hash(&mut h);
            sanitized = format!("{}__h{:016x}", &sanitized[..180], h.finish());
        }
        let outpath = format!("{outdir}/{sanitized}.trust_ir");
        // FAIL-CLOSED for the shim kinds: a shim body that panics in lowering /
        // MIR synthesis, or bails, or validates non-empty must be REPORTED and
        // SKIPPED — never written as a broken module. Item bodies keep their
        // exact pre-fix behavior (write + report validate=<n>, even if non-zero).
        // Debug aid: dump ANY body's MIR by symbol/name substring
        // (`TRUST_IR_DUMP_MIR=<substr>`), success or failure.
        if let Ok(pat) = std::env::var("TRUST_IR_DUMP_MIR") {
            if !pat.is_empty() && (name.contains(&pat) || dedup_key.contains(&pat)) {
                let body: &Body<'_> = tcx.instance_mir(instance.def);
                let mut buf = Vec::new();
                let _ = rustc_middle::mir::pretty::MirWriter::new(tcx).write_mir_fn(body, &mut buf);
                eprintln!(
                    "==== MIR of {name} [{dedup_key}] ====\n{}\n==== end MIR ====",
                    String::from_utf8_lossy(&buf)
                );
            }
        }
        let lowered = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let body: &Body<'_> = tcx.instance_mir(instance.def);
            mir_lower::lower_module_for_emit(tcx, instance, body)
        }));
        match lowered {
            Ok(Ok((module, errs))) => {
                if is_emittable_shim && !errs.is_empty() {
                    eprintln!(
                        "EMIT-EACH-FAIL {name} :: shim validate={} error(s) (fail-closed, not emitted); first: {:?}",
                        errs.len(),
                        errs.first()
                    );
                    if let Ok(pat) = std::env::var("TRUST_IR_DUMP_FAIL_MIR") {
                        if !pat.is_empty() && name.contains(&pat) {
                            let body: &Body<'_> = tcx.instance_mir(instance.def);
                            let mut buf = Vec::new();
                            let _ = rustc_middle::mir::pretty::MirWriter::new(tcx)
                                .write_mir_fn(body, &mut buf);
                            eprintln!(
                                "==== MIR of {name} (instance {:?}) ====\n{}\n==== module ====\n{module}\n==== end MIR ====",
                                instance.def,
                                String::from_utf8_lossy(&buf)
                            );
                        }
                    }
                    fail += 1;
                    continue;
                }
                let text = format!("{module}");
                if let Err(e) = std::fs::write(&outpath, &text) {
                    eprintln!("EMIT-EACH-FAIL {name} :: write {outpath} failed: {e}");
                    fail += 1;
                    continue;
                }
                eprintln!("EMIT-EACH {name} -> {outpath} | validate={}", errs.len());
                ok += 1;
            }
            Ok(Err(reason)) => {
                eprintln!("EMIT-EACH-FAIL {name} :: {reason}");
                // Debug aid: dump the failing body's MIR when requested
                // (`TRUST_IR_DUMP_FAIL_MIR=<substring of name>`).
                if let Ok(pat) = std::env::var("TRUST_IR_DUMP_FAIL_MIR") {
                    if !pat.is_empty() && name.contains(&pat) {
                        let body: &Body<'_> = tcx.instance_mir(instance.def);
                        let mut buf = Vec::new();
                        let _ = rustc_middle::mir::pretty::MirWriter::new(tcx)
                            .write_mir_fn(body, &mut buf);
                        eprintln!(
                            "==== MIR of {name} ====\n{}\n==== end MIR ====",
                            String::from_utf8_lossy(&buf)
                        );
                    }
                }
                fail += 1;
            }
            Err(_) => {
                eprintln!("EMIT-EACH-FAIL {name} :: lowering PANICKED (fail-closed, not emitted)");
                fail += 1;
            }
        }
    }
    // LANE S — REAL STD-STATIC BYTES: emit the dedicated whole-program `statics`
    // module. Every static REFERENCED by the modules lowered above is DEFINED
    // here once, with its real CTFE initializer bytes (External linkage; nested
    // anonymous allocations interned transitively as Internal `const.allocN`
    // globals) — so the link-time runtime generator no longer zero-inits
    // real-data statics (the unicode property tables, fmt's DECIMAL_PAIRS).
    // Statics whose allocation genuinely cannot be evaluated (true foreign
    // `extern` statics, TLS statics) stay extern declarations and are each
    // reported with a reason. FAIL-CLOSED: a statics module that does not
    // validate is NOT written — the affected symbols then dangle at link
    // (loud), never silently zero-filled.
    let (statics_module, statics_defined, statics_extern) = mir_lower::emit_statics_module(tcx);
    if let Some((module, errs)) = statics_module {
        for d in &statics_defined {
            eprintln!(
                "EMIT-EACH STATIC-DEF {} size={} mutable={}",
                d.symbol, d.size, d.mutable
            );
        }
        for (sym, why) in &statics_extern {
            eprintln!("EMIT-EACH STATIC-EXTERN {sym} :: {why}");
        }
        if !errs.is_empty() {
            eprintln!(
                "EMIT-EACH STATICS-FAIL :: validate={} error(s); first: {:?} (statics module NOT written)",
                errs.len(),
                errs.first()
            );
            fail += 1;
        } else {
            let outpath = format!("{outdir}/statics.trust_ir");
            let text = format!("{module}");
            match std::fs::write(&outpath, &text) {
                Ok(()) => {
                    eprintln!(
                        "EMIT-EACH STATICS: {} defined, {} left extern -> {outpath} | validate=0",
                        statics_defined.len(),
                        statics_extern.len()
                    );
                    ok += 1;
                }
                Err(e) => {
                    eprintln!("EMIT-EACH STATICS-FAIL :: write {outpath} failed: {e}");
                    fail += 1;
                }
            }
        }
    }
    eprintln!(
        "== EMIT-EACH DONE: wrote {ok} module(s), {fail} lowering failure(s); reference-closure pulled {closure_pulled} extra fn(s) beyond the mono set =="
    );
}

/// EMIT-CLOSURE driver (`--mir-emit-closure <fnsubstr> <outpath>`): find the FIRST
/// `MonoItem::Fn` whose def-path CONTAINS `fnsubstr` (the ROOT), compute the
/// call-graph CLOSURE over the crate's OWN fns, lower EVERY member into ONE shared
/// trust-ir module with cross-member `Call`s wired to the in-module body `FuncId`s,
/// write the module text, and report `validate_module`'s error count + which members
/// are IN-MODULE. We print EMIT-CLOSURE-OK / EMIT-CLOSURE-FAIL so the run log records
/// the multi-function verification step.
fn run_mir_emit_closure(tcx: TyCtxt<'_>, fnsubstr: &str, outpath: &str) {
    eprintln!("== trust_ir_mir EMIT-CLOSURE: lower the call-graph closure of `{fnsubstr}` -> {outpath} ==");
    let mono = tcx.collect_and_partition_mono_items(());
    for cgu in mono.codegen_units {
        for (mono_item, _data) in cgu.items_in_deterministic_order(tcx) {
            if let MonoItem::Fn(instance) = mono_item {
                let name = tcx.def_path_str(instance.def_id());
                if !name.contains(fnsubstr) {
                    continue;
                }
                if !matches!(instance.def, ty::InstanceKind::Item(_)) {
                    continue;
                }
                // ADDITIVE root selection: a closure-using fn `foo` and its closure
                // body `foo::{closure#0}` BOTH contain the substring `foo`, and the
                // closure sorts first in the deterministic mono-item order. The
                // INTENDED root is the combinator-USING fn, not the closure body
                // (which is pulled in automatically as a member). Skip a closure
                // def-path here UNLESS the substring explicitly names a closure
                // (`{closure`), so `--mir-emit-closure foo` picks `foo`, while
                // emitting a closure body directly is still possible by asking for it.
                // This only changes WHICH root is chosen; the lowering is unchanged.
                if name.contains("{closure") && !fnsubstr.contains("{closure") {
                    continue;
                }
                let body: &Body<'_> = tcx.instance_mir(instance.def);
                match mir_lower::lower_closure_for_emit(tcx, instance, body) {
                    Ok((mut module, errs, member_syms)) => {
                        // Fixture reproducibility: emit-closure exists solely to produce
                        // self-contained, regeneratable test fixtures, so normalize the
                        // span-provenance file table to basenames — a fixture re-emitted
                        // from any checkout location stays byte-identical. The full local
                        // paths remain on the default lowering path.
                        for f in module.files.iter_mut() {
                            if let Some(base) = std::path::Path::new(f.as_str())
                                .file_name()
                                .and_then(|b| b.to_str())
                            {
                                *f = base.to_string();
                            }
                        }
                        let text = format!("{module}");
                        if let Err(e) = std::fs::write(outpath, &text) {
                            eprintln!("EMIT-CLOSURE-FAIL {name}: write {outpath} failed: {e}");
                            return;
                        }
                        eprintln!(
                            "EMIT-CLOSURE-OK {name}: wrote {} bytes to {outpath}; {} closure member(s); validate_module = {} error(s)",
                            text.len(),
                            member_syms.len(),
                            errs.len()
                        );
                        eprintln!("   IN-MODULE members ({}):", member_syms.len());
                        for s in &member_syms {
                            eprintln!("     @{s}");
                        }
                        if !errs.is_empty() {
                            eprintln!("   first validation error: {:?}", errs.first());
                        }
                        // Span-threading provenance, one line per lowered member
                        // body (externs have no blocks).
                        for f in module.functions.iter().filter(|f| !f.blocks.is_empty()) {
                            eprintln!("   {}", span_map::function_span_report(&module, f));
                        }
                        match trust_ir::parser::parse_module(&text) {
                            Ok(_) => eprintln!("   re-parse: OK (parse_module round-trips)"),
                            Err(e) => eprintln!("   re-parse: FAILED: {e:?}"),
                        }
                        return;
                    }
                    Err(reason) => {
                        eprintln!("EMIT-CLOSURE-FAIL {name}: {reason}");
                        return;
                    }
                }
            }
        }
    }
    eprintln!("EMIT-CLOSURE-FAIL: no MonoItem::Fn whose def-path contains `{fnsubstr}` was found");
}

/// A simple ranked counter keyed by a normalized variant label.
#[derive(Default)]
struct Histogram {
    counts: BTreeMap<String, usize>,
}

impl Histogram {
    fn bump(&mut self, key: impl Into<String>) {
        *self.counts.entry(key.into()).or_insert(0) += 1;
    }
    /// Rows sorted by descending count, ties broken alphabetically.
    fn ranked(&self) -> Vec<(&String, usize)> {
        let mut rows: Vec<(&String, usize)> = self.counts.iter().map(|(k, v)| (k, *v)).collect();
        rows.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
        rows
    }
    fn print(&self, title: &str) {
        let rows = self.ranked();
        let total: usize = rows.iter().map(|(_, c)| *c).sum();
        eprintln!("== {title} (total {total}, {} distinct) ==", rows.len());
        for (k, c) in rows {
            eprintln!("   [{c:>7}] {k}");
        }
    }
}

/// The discriminant NAME of a `TerminatorKind` (no operands), for histogramming.
fn terminator_kind_name(t: &TerminatorKind<'_>) -> &'static str {
    match t {
        TerminatorKind::Goto { .. } => "Goto",
        TerminatorKind::SwitchInt { .. } => "SwitchInt",
        TerminatorKind::UnwindResume => "UnwindResume",
        TerminatorKind::UnwindTerminate(_) => "UnwindTerminate",
        TerminatorKind::Return => "Return",
        TerminatorKind::Unreachable => "Unreachable",
        TerminatorKind::Drop { .. } => "Drop",
        TerminatorKind::Call { .. } => "Call",
        TerminatorKind::TailCall { .. } => "TailCall",
        TerminatorKind::Assert { .. } => "Assert",
        TerminatorKind::Yield { .. } => "Yield",
        TerminatorKind::CoroutineDrop => "CoroutineDrop",
        TerminatorKind::FalseEdge { .. } => "FalseEdge",
        TerminatorKind::FalseUnwind { .. } => "FalseUnwind",
        TerminatorKind::InlineAsm { .. } => "InlineAsm",
    }
}

/// The discriminant NAME of a `StatementKind` (no operands).
fn statement_kind_name(s: &StatementKind<'_>) -> &'static str {
    match s {
        StatementKind::Assign(_) => "Assign",
        StatementKind::FakeRead(_) => "FakeRead",
        StatementKind::SetDiscriminant { .. } => "SetDiscriminant",
        StatementKind::StorageLive(_) => "StorageLive",
        StatementKind::StorageDead(_) => "StorageDead",
        StatementKind::PlaceMention(_) => "PlaceMention",
        StatementKind::AscribeUserType(_, _) => "AscribeUserType",
        StatementKind::Coverage(_) => "Coverage",
        StatementKind::Intrinsic(_) => "Intrinsic",
        StatementKind::ConstEvalCounter => "ConstEvalCounter",
        StatementKind::Nop => "Nop",
        StatementKind::BackwardIncompatibleDropHint { .. } => "BackwardIncompatibleDropHint",
    }
}

/// The discriminant NAME of an `Rvalue` (no operands).
fn rvalue_kind_name(r: &Rvalue<'_>) -> &'static str {
    match r {
        Rvalue::Use(_, _) => "Use",
        Rvalue::Repeat(_, _) => "Repeat",
        Rvalue::Ref(_, _, _) => "Ref",
        Rvalue::ThreadLocalRef(_) => "ThreadLocalRef",
        Rvalue::RawPtr(_, _) => "RawPtr",
        Rvalue::Cast(_, _, _) => "Cast",
        Rvalue::BinaryOp(_, _) => "BinaryOp",
        Rvalue::UnaryOp(_, _) => "UnaryOp",
        Rvalue::Discriminant(_) => "Discriminant",
        Rvalue::Aggregate(_, _) => "Aggregate",
        Rvalue::CopyForDeref(_) => "CopyForDeref",
        Rvalue::WrapUnsafeBinder(_, _) => "WrapUnsafeBinder",
        Rvalue::Reborrow(_, _, _) => "Reborrow",
    }
}

/// A coarse SHAPE label for an `AggregateKind` (which aggregate Rvalues build).
fn aggregate_kind_label(a: &AggregateKind<'_>) -> String {
    match a {
        AggregateKind::Array(_) => "Array".to_string(),
        AggregateKind::Tuple => "Tuple".to_string(),
        AggregateKind::Adt(def_id, _, _, _, _) => {
            // Distinguish struct vs enum vs union by the AdtDef kind; we cannot
            // hold a tcx here, so the caller passes a richer label instead.
            let _ = def_id;
            "Adt".to_string()
        }
        AggregateKind::Closure(_, _) => "Closure".to_string(),
        AggregateKind::Coroutine(_, _) => "Coroutine".to_string(),
        AggregateKind::CoroutineClosure(_, _) => "CoroutineClosure".to_string(),
        AggregateKind::RawPtr(_, _) => "RawPtr".to_string(),
    }
}

/// The discriminant NAME of a `CastKind`.
fn cast_kind_name(c: &CastKind) -> &'static str {
    match c {
        CastKind::PointerExposeProvenance => "PointerExposeProvenance",
        CastKind::PointerWithExposedProvenance => "PointerWithExposedProvenance",
        CastKind::PointerCoercion(_, _) => "PointerCoercion",
        CastKind::IntToInt => "IntToInt",
        CastKind::FloatToInt => "FloatToInt",
        CastKind::FloatToFloat => "FloatToFloat",
        CastKind::IntToFloat => "IntToFloat",
        CastKind::PtrToPtr => "PtrToPtr",
        CastKind::FnPtrToPtr => "FnPtrToPtr",
        CastKind::Transmute => "Transmute",
        CastKind::Subtype => "Subtype",
    }
}

/// A coarse SHAPE label for a `Ty` (which type families appear in Rvalues), kept
/// shallow so the histogram stays a small fixed set of families.
fn ty_shape_label<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> String {
    match ty.kind() {
        ty::Bool => "bool".to_string(),
        ty::Char => "char".to_string(),
        ty::Int(i) => format!("int:{i:?}"),
        ty::Uint(u) => format!("uint:{u:?}"),
        ty::Float(f) => format!("float:{f:?}"),
        ty::Str => "str".to_string(),
        ty::Array(_, _) => "array".to_string(),
        ty::Slice(_) => "slice".to_string(),
        ty::RawPtr(_, _) => "rawptr".to_string(),
        ty::Ref(_, _, _) => "ref".to_string(),
        ty::FnDef(_, _) => "fndef".to_string(),
        ty::FnPtr(_, _) => "fnptr".to_string(),
        ty::Tuple(t) if t.is_empty() => "unit".to_string(),
        ty::Tuple(_) => "tuple".to_string(),
        ty::Adt(adt, _) => {
            let name = tcx.item_name(adt.did());
            let kind = if adt.is_enum() {
                "enum"
            } else if adt.is_union() {
                "union"
            } else {
                "struct"
            };
            format!("adt:{kind}:{name}")
        }
        ty::Closure(_, _) => "closure".to_string(),
        ty::Coroutine(_, _) => "coroutine".to_string(),
        ty::Dynamic(_, _) => "dyn".to_string(),
        ty::Foreign(_) => "foreign".to_string(),
        ty::Never => "never".to_string(),
        ty::Param(_) => "param".to_string(),
        ty::Alias(_, _) => "alias".to_string(),
        _ => format!("other:{:?}", ty.kind()),
    }
}

/// PHASE 1 driver: enumerate every MonoItem::Fn of the crate, get each one's MIR
/// `Body` via `tcx.instance_mir`, and tally the construct histograms. Optionally
/// (Phase 2) also attempt the minimal lowering.
fn run_mir_coverage(tcx: TyCtxt<'_>, do_lower: bool, local_only: bool) {
    eprintln!("== trust_ir_mir: STAGE1-HOSTED MIR -> trust-ir whole-program coverage ==");
    eprintln!(
        "   path: tcx.collect_and_partition_mono_items(()) -> for each CGU, \
         items_in_deterministic_order(tcx) -> MonoItem::Fn(instance) -> \
         tcx.instance_mir(instance.def) (the post-transform MIR Body)"
    );
    if local_only {
        eprintln!("   FILTER: local-only (this crate's OWN fns; excludes monomorphized std/dep generics)");
    }

    let mut total_fns = 0usize;
    let mut total_blocks = 0usize;
    let mut total_statements = 0usize;
    let mut total_terminators = 0usize;
    let mut local_fns = 0usize;
    let mut nonlocal_fns = 0usize;
    let mut shim_fns = 0usize;

    let mut term_hist = Histogram::default();
    let mut stmt_hist = Histogram::default();
    let mut rvalue_hist = Histogram::default();
    let mut aggregate_hist = Histogram::default();
    let mut cast_hist = Histogram::default();
    let mut ty_hist = Histogram::default();
    // Histogram of which mono-item DEF kinds the collector produced.
    let mut instkind_hist = Histogram::default();

    // Dedup instances so a generic instantiated N times is one body visit per
    // distinct (def_id, args) — `instance_mir` is the same body, but each distinct
    // monomorphization is a distinct lowering target, so we visit all of them.
    // The collector already partitions distinct mono-items, so we simply visit
    // each as it comes.
    let mono = tcx.collect_and_partition_mono_items(());

    // Phase 2 tally.
    let mut lower_ok = 0usize;
    let mut lower_failed = 0usize;
    let mut lower_attempted = 0usize;
    let mut lower_bucket: BTreeMap<String, (usize, String)> = BTreeMap::new();
    let mut lowered_ok_names: Vec<String> = Vec::new();
    // PANIC-CLASS OBLIGATIONS: the `Pending` claims the lowering RECORDED (one
    // per lowered rustc MIR `Assert`), summed over every lowered-ok body. This
    // is the number of panic-freedom claims the Rust producer used to drop.
    let mut obligation_tally = mir_lower::ObligationTally::default();
    let mut fns_with_obligations = 0usize;

    for cgu in mono.codegen_units {
        for (mono_item, _item_data) in cgu.items_in_deterministic_order(tcx) {
            if let MonoItem::Fn(instance) = mono_item {
                if local_only && !instance.def_id().is_local() {
                    continue;
                }
                total_fns += 1;
                if instance.def_id().is_local() {
                    local_fns += 1;
                } else {
                    nonlocal_fns += 1;
                }
                // Tally the instance KIND (Item vs the synthetic shims).
                instkind_hist.bump(instance_kind_name(&instance.def));
                if !matches!(instance.def, ty::InstanceKind::Item(_)) {
                    shim_fns += 1;
                }

                // `instance_mir` returns the post-transform MIR Body. For shims
                // this synthesizes the shim body; it never panics for a collected
                // mono-item.
                let body: &Body<'_> = tcx.instance_mir(instance.def);
                total_blocks += body.basic_blocks.len();

                tally_body(
                    tcx,
                    instance,
                    body,
                    &mut total_statements,
                    &mut total_terminators,
                    &mut term_hist,
                    &mut stmt_hist,
                    &mut rvalue_hist,
                    &mut aggregate_hist,
                    &mut cast_hist,
                    &mut ty_hist,
                );

                if do_lower {
                    lower_attempted += 1;
                    let name = tcx.def_path_str(instance.def_id());
                    match mir_lower::try_lower_minimal(tcx, instance, body) {
                        Ok(tally) => {
                            lower_ok += 1;
                            if tally.total > 0 {
                                fns_with_obligations += 1;
                            }
                            obligation_tally.add(tally);
                            // Optional: when `TRUST_IR_MIR_OK_GREP` is set, print
                            // EVERY lowered-ok fn whose path contains the filter
                            // (so the full lowered set — not just the 60-cap sample
                            // — can be searched for whnf/def_eq/etc.). Env-gated,
                            // off by default; never affects the tally.
                            if let Ok(f) = std::env::var("TRUST_IR_MIR_OK_GREP") {
                                if f.is_empty() || name.contains(&f) {
                                    eprintln!("LOWERED_OK {name}");
                                }
                            }
                            if lowered_ok_names.len() < 60 {
                                lowered_ok_names.push(name);
                            }
                        }
                        Err(reason) => {
                            lower_failed += 1;
                            if let Ok(f) = std::env::var("TRUST_IR_MIR_FAIL_GREP") {
                                if f.is_empty() || reason.contains(&f) {
                                    eprintln!("LOWER_FAIL [{name}] :: {reason}");
                                }
                            }
                            let bucket = mir_lower::bucket_reason(&reason);
                            let entry =
                                lower_bucket.entry(bucket).or_insert((0, reason.clone()));
                            entry.0 += 1;
                        }
                    }
                }
            }
        }
    }

    // ---- PHASE 1 RESULT ----
    eprintln!();
    eprintln!("== PHASE 1 RESULT: whole-program MIR construct gap map ==");
    eprintln!(
        "   total mono-item fns      = {total_fns}  (local={local_fns}, nonlocal/extern-monomorphized={nonlocal_fns}, synthetic-shims={shim_fns})"
    );
    eprintln!("   total basic blocks       = {total_blocks}");
    eprintln!("   total statements         = {total_statements}");
    eprintln!("   total terminators        = {total_terminators}");
    if total_fns > 0 {
        eprintln!(
            "   avg blocks/fn            = {:.2}",
            total_blocks as f64 / total_fns as f64
        );
    }
    eprintln!();
    instkind_hist.print("MonoItem InstanceKind histogram (which fn forms the collector produced)");
    eprintln!();
    term_hist.print("RANKED TerminatorKind histogram (the control-flow gap map)");
    eprintln!();
    stmt_hist.print("RANKED StatementKind histogram (the statement gap map)");
    eprintln!();
    rvalue_hist.print("RANKED Rvalue histogram (inside StatementKind::Assign) (the rvalue gap map)");
    eprintln!();
    aggregate_hist.print("AggregateKind shapes (which aggregates Rvalue::Aggregate builds)");
    eprintln!();
    cast_hist.print("CastKind shapes (which casts Rvalue::Cast performs)");
    eprintln!();
    ty_hist.print("Ty SHAPE families appearing in Rvalue assign destinations");

    if do_lower {
        eprintln!();
        eprintln!("== PHASE 2 RESULT: minimal MIR -> trust-ir lowering attempt ==");
        eprintln!(
            "   attempted={lower_attempted}  lowered_ok (validate_module 0 errors)={lower_ok}  failed={lower_failed}"
        );
        if lower_attempted > 0 {
            eprintln!(
                "   lowered_ok / attempted = {lower_ok}/{lower_attempted} = {:.2}%",
                100.0 * lower_ok as f64 / lower_attempted as f64
            );
        }
        if !lowered_ok_names.is_empty() {
            eprintln!("   sample lowered-ok fns ({}): {:?}", lowered_ok_names.len(), lowered_ok_names);
        }
        // PANIC-CLASS OBLIGATIONS recorded from rustc MIR `Assert` terminators.
        // These are STATED, UNDISCHARGED claims (`ProofStatus::Pending`): the
        // frontend records what rustc says must hold, and proves none of it.
        //
        // THE COUNT IS BUILD-CONFIG DEPENDENT — it is a property of the MIR we
        // were handed, NOT a stable property of the program. rustc only inserts
        // the `Assert` terminators this pass records when the corresponding
        // check is enabled: with `-Cdebug-assertions=yes` the reference corpus
        // yields 70 asserts, with `-Cdebug-assertions=no` it yields 7 (every
        // misaligned-ptr / null-ref row and one overflow row disappear). Both
        // are exact — recorded == emitted in each configuration — but a reader
        // must never treat "N panic obligations" as a fact about the source.
        // The banner below therefore prints the panic strategy and the
        // debug-assertions setting alongside the totals.
        eprintln!();
        eprintln!(
            "   PANIC-OBLIGATIONS config: panic={}  debug_assertions={}  \
             (the totals below are a property of THIS MIR, not of the program)",
            if tcx.sess.panic_strategy().unwinds() {
                "unwind"
            } else {
                "abort"
            },
            if tcx.sess.opts.debug_assertions {
                "yes"
            } else {
                "no"
            },
        );
        eprintln!(
            "   PANIC-OBLIGATIONS (Pending, recorded not proved): total={}  bounds_check={}  \
             arithmetic_safety={}  memory_safety={}  panic_freedom={}  other_kind={}  \
             with_source_range={}  with_site={}  fns_with_obligations={}",
            obligation_tally.total,
            obligation_tally.bounds_check,
            obligation_tally.arithmetic_safety,
            obligation_tally.memory_safety,
            obligation_tally.panic_freedom,
            obligation_tally.other_kind,
            obligation_tally.with_range,
            obligation_tally.with_site,
            fns_with_obligations,
        );
        // The four named buckets plus `other_kind` must exhaust `total`. If they
        // ever do not, the banner is lying about the distribution — say so
        // loudly rather than letting a bucket silently vanish.
        let bucketed = obligation_tally.bounds_check
            + obligation_tally.arithmetic_safety
            + obligation_tally.memory_safety
            + obligation_tally.panic_freedom
            + obligation_tally.other_kind;
        if bucketed != obligation_tally.total {
            eprintln!(
                "   PANIC-OBLIGATIONS BANNER BUG: buckets sum to {bucketed} but total={} — \
                 the per-kind breakdown above is incomplete",
                obligation_tally.total,
            );
        }
        if obligation_tally.non_pending > 0 {
            eprintln!(
                "   PANIC-OBLIGATIONS INVARIANT VIOLATED: {} non-Pending row(s) — this frontend \
                 must never mint a discharged/trusted/certified status",
                obligation_tally.non_pending
            );
        }
        // Which rustc AssertKind each recorded row came from (ranked), so the
        // AssertKind -> ObligationKind mapping stays reviewable against the
        // real distribution rather than an assumed one.
        if !obligation_tally.by_check.is_empty() {
            let mut rows: Vec<(&String, &usize)> = obligation_tally.by_check.iter().collect();
            rows.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
            eprintln!("   == PANIC-OBLIGATIONS by rustc AssertKind ==");
            for (slug, count) in rows {
                eprintln!("      [{count:>6}] {slug}");
            }
        }
        // Ranked failure buckets.
        let mut rows: Vec<(&String, &(usize, String))> = lower_bucket.iter().collect();
        rows.sort_by(|a, b| b.1 .0.cmp(&a.1 .0).then(a.0.cmp(b.0)));
        eprintln!();
        eprintln!("   == RANKED Phase-2 failure buckets (the failed_roots-equivalent) ==");
        for (bucket, (count, example)) in rows {
            eprintln!("      [{count:>6}] {bucket}");
            eprintln!("              e.g. {example}");
        }
    }
}

/// The NAME of an `InstanceKind` (Item vs the synthetic shim forms).
fn instance_kind_name(k: &ty::InstanceKind<'_>) -> &'static str {
    match k {
        ty::InstanceKind::Item(_) => "Item",
        ty::InstanceKind::Intrinsic(_) => "Intrinsic",
        ty::InstanceKind::Virtual(_, _) => "Virtual",
        ty::InstanceKind::Shim(ty::ShimKind::VTable(_)) => "VTableShim",
        ty::InstanceKind::Shim(ty::ShimKind::Reify(_, _)) => "ReifyShim",
        ty::InstanceKind::Shim(ty::ShimKind::FnPtr(_, _)) => "FnPtrShim",
        ty::InstanceKind::Shim(ty::ShimKind::ClosureOnce { .. }) => "ClosureOnceShim",
        ty::InstanceKind::Shim(ty::ShimKind::ConstructCoroutineInClosure { .. }) => {
            "ConstructCoroutineInClosureShim"
        }
        ty::InstanceKind::Shim(ty::ShimKind::ThreadLocal(_)) => "ThreadLocalShim",
        ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, _)) => "DropGlue",
        ty::InstanceKind::Shim(ty::ShimKind::Clone(_, _)) => "CloneShim",
        ty::InstanceKind::Shim(ty::ShimKind::FnPtrAddr(_, _)) => "FnPtrAddrShim",
        ty::InstanceKind::Shim(ty::ShimKind::AsyncDropGlue(_, _)) => "AsyncDropGlue",
        ty::InstanceKind::Shim(ty::ShimKind::FutureDropPoll(_, _, _)) => {
            "FutureDropPollShim"
        }
        ty::InstanceKind::Shim(ty::ShimKind::AsyncDropGlueCtor(_, _)) => {
            "AsyncDropGlueCtorShim"
        }
    }
}

/// Walk one MIR `Body` and tally its blocks/statements/terminators into the
/// histograms. Types embedded in Rvalues are monomorphized + region-erased
/// against `instance` so the Ty-shape histogram reflects CONCRETE types.
#[allow(clippy::too_many_arguments)]
fn tally_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    body: &Body<'tcx>,
    total_statements: &mut usize,
    total_terminators: &mut usize,
    term_hist: &mut Histogram,
    stmt_hist: &mut Histogram,
    rvalue_hist: &mut Histogram,
    aggregate_hist: &mut Histogram,
    cast_hist: &mut Histogram,
    ty_hist: &mut Histogram,
) {
    let monomorphize = |ty: Ty<'tcx>| -> Ty<'tcx> {
        instance.instantiate_mir_and_normalize_erasing_regions(
            tcx,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(tcx, ty),
        )
    };

    for bb in body.basic_blocks.iter() {
        *total_statements += bb.statements.len();
        for stmt in &bb.statements {
            stmt_hist.bump(statement_kind_name(&stmt.kind));
            if let StatementKind::Assign(boxed) = &stmt.kind {
                let (place, rvalue) = &**boxed;
                rvalue_hist.bump(rvalue_kind_name(rvalue));

                // The destination place's CONCRETE type — the type family this
                // rvalue produces.
                let place_ty = place.ty(&body.local_decls, tcx).ty;
                // Best-effort monomorphize; a Param survives if the body is a
                // generic shim body (rare for collected mono-items).
                let concrete = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    monomorphize(place_ty)
                }))
                .unwrap_or(place_ty);
                ty_hist.bump(ty_shape_label(tcx, concrete));

                match rvalue {
                    Rvalue::Aggregate(kind, _) => {
                        let label = match &**kind {
                            AggregateKind::Adt(def_id, _, _, _, _) => {
                                let adt = tcx.adt_def(*def_id);
                                let k = if adt.is_enum() {
                                    "enum"
                                } else if adt.is_union() {
                                    "union"
                                } else {
                                    "struct"
                                };
                                format!("Adt:{k}")
                            }
                            other => aggregate_kind_label(other),
                        };
                        aggregate_hist.bump(label);
                    }
                    Rvalue::Cast(cast_kind, _, _) => {
                        cast_hist.bump(cast_kind_name(cast_kind));
                    }
                    _ => {}
                }
            }
        }
        if let Some(term) = &bb.terminator {
            *total_terminators += 1;
            term_hist.bump(terminator_kind_name(&term.kind));
        }
    }
}

fn main() {
    let raw: Vec<String> = std::env::args().collect();
    let mut rustc_args: Vec<String> = Vec::new();
    // Default to coverage mode (Phase 1) — that is this driver's whole purpose.
    let mut coverage = true;
    let mut lower = false;
    let mut local_only = false;
    // EMIT mode: `--mir-emit <fnsubstr> <outpath>` (two following positional args).
    let mut emit: Option<(String, String)> = None;
    // EMIT-CLOSURE mode: `--mir-emit-closure <fnsubstr> <outpath>`.
    let mut emit_closure: Option<(String, String)> = None;
    // EMIT-EACH mode: `--mir-emit-each <outdir>`.
    let mut emit_each: Option<String> = None;
    let mut i = 0;
    while i < raw.len() {
        match raw[i].as_str() {
            "--mir-coverage" => {
                coverage = true;
                i += 1;
            }
            "--mir-lower" => {
                lower = true;
                i += 1;
            }
            "--mir-local-only" => {
                local_only = true;
                i += 1;
            }
            "--no-coverage" => {
                coverage = false;
                i += 1;
            }
            // RUNG 10/11 opt-in: the by-value SMALL-AGGREGATE ABI. Lowers small
            // int/bool-lane struct/tuple pair RETURNS (RUNG 10) AND PARAMS (RUNG 11)
            // by value (one SSA 2-tuple) on lowered bodies + in-module call edges,
            // and pins the `byval`/`sret` ParamAttrs on the remaining by-ref
            // aggregate params / sret return pointer. Default OFF: the landed
            // by-ref/sret convention, byte-identical emits (the trust-cg
            // byte-verbatim golds pin it; the default flip is a coordinated trust-cg
            // rung — see mir_lower.rs "RUNG 10"/"RUNG 11").
            // Set the lowering mode directly before `run_compiler`. Ambient
            // environment must not be able to change the emitted Trust IR.
            "--mir-pair-ret-by-value" => {
                mir_lower::enable_pair_ret_by_value();
                i += 1;
            }
            "--mir-emit" => {
                // Consume the next TWO args: the fn-path substring + the output path.
                let fnsubstr = raw.get(i + 1).cloned().unwrap_or_else(|| {
                    eprintln!("--mir-emit requires <fnsubstr> <outpath>");
                    std::process::exit(2);
                });
                let outpath = raw.get(i + 2).cloned().unwrap_or_else(|| {
                    eprintln!("--mir-emit requires <fnsubstr> <outpath>");
                    std::process::exit(2);
                });
                emit = Some((fnsubstr, outpath));
                i += 3;
            }
            "--mir-emit-closure" => {
                // Consume the next TWO args: the root fn-path substring + output path.
                let fnsubstr = raw.get(i + 1).cloned().unwrap_or_else(|| {
                    eprintln!("--mir-emit-closure requires <fnsubstr> <outpath>");
                    std::process::exit(2);
                });
                let outpath = raw.get(i + 2).cloned().unwrap_or_else(|| {
                    eprintln!("--mir-emit-closure requires <fnsubstr> <outpath>");
                    std::process::exit(2);
                });
                emit_closure = Some((fnsubstr, outpath));
                i += 3;
            }
            "--mir-emit-each" => {
                // Consume the next arg: the output directory.
                let outdir = raw.get(i + 1).cloned().unwrap_or_else(|| {
                    eprintln!("--mir-emit-each requires <outdir>");
                    std::process::exit(2);
                });
                emit_each = Some(outdir);
                i += 2;
            }
            _ => {
                rustc_args.push(raw[i].clone());
                i += 1;
            }
        }
    }

    if let Err(error) = trust_ir_frontend::append_matching_rustc_sysroot(&mut rustc_args) {
        eprintln!("trust_ir_mir: {error}");
        std::process::exit(2);
    }

    let mut cb = MirCallbacks {
        coverage,
        lower,
        local_only,
        emit,
        emit_closure,
        emit_each,
    };
    rustc_driver::run_compiler(&rustc_args, &mut cb);
}
