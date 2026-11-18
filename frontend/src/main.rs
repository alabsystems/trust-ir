// trust_ir_frontend driver — M1.
//
// Usage:
//   trust_ir_frontend <file.rs> [--target-fn NAME]...
//
// Compiles `<file.rs>` with the in-process rustc (the Trust stage1 fork), and
// after analysis, for each function whose name matches a `--target-fn` (default:
// `is_zero`, `is_nonzero`), reads its `tcx.thir_body(def)`, lowers it to trust-ir
// via the M1 THIR->trust-ir pass, validates the emitted module, and prints a
// report. This is the END-TO-END automated path: a real `LocalDefId` from a real
// compile fed through the lowering.
//
// Build with `targo --unverified build --manifest-path frontend/Cargo.toml`
// (Cargo.toml): the installed Trust sysroot resolves rustc_private directly, and
// build.rs bakes an rpath to its `librustc_driver`. At runtime RUSTC defaults to
// `trustc`; set it (or pass `--sysroot`) to name another ABI-matching compiler.

#![feature(rustc_private)]
#![allow(rustc::default_hash_types)]
#![allow(rustc::potential_query_instability)]

#[cfg(any(target_os = "linux", target_os = "macos"))]
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;

use trust_ir_build::validate_module;

struct FrontendCallbacks {
    target_fns: Vec<String>,
    /// M3 mode: drive monomorphization of the generic corpus defs (`id`,
    /// `double`) per instantiation + trait static dispatch (`call_yes`).
    m3: bool,
    /// FIX 1(a) — LAYOUT-PINNING gate. When set, after recovering the target
    /// enum's `EnumLayout` via the SAME `tcx.layout_of` path the lowering uses,
    /// ASSERT it byte-for-byte against the rustc ground-truth the audit
    /// confirmed for the M6 niche `Level` (tag offset/width/encoding, every
    /// variant's Switch value, every field offset). Any divergence prints a
    /// "LAYOUT-PIN MISMATCH" line and `exit(1)`s. This is the guard the
    /// emitted-vs-heap differential alone cannot provide: the differential is
    /// SELF-CONSISTENT (both sides read the same recovered layout), so a
    /// `layout_of` divergence (e.g. perturbing a niche value 3->103) would NOT
    /// be caught by it — but it WILL be caught here.
    assert_layout: bool,
    /// When set (with `--m3`), also emit the focused scalar round-trip module
    /// (`id__i64`/`double__i64`) as trust-ir TEXT to this path, for the
    /// downstream trust-cg JIT cross-check.
    emit_text: Option<String>,
    /// When set (with `--m3`), also emit the M4 call-chain round-trip module
    /// (`quad__i64` + `double__i64`, joined by a real Call edge) as trust-ir
    /// TEXT to this path.
    emit_callchain: Option<String>,
    /// When set (with `--m3`), also emit the M5.1 if/pick round-trip module
    /// (`pick` + `select__i64`, both `if`/join) as trust-ir TEXT to this path.
    emit_if: Option<String>,
    /// When set (with `--m3`), also emit the M5.2 `let` round-trip module
    /// (`poly` + `quad_let` + the `double__i64` it calls) as trust-ir TEXT.
    emit_let: Option<String>,
    /// When set (with `--m3`), also emit the M5.3 scalar-`match` round-trip
    /// module (`classify` + `step` + the `double__i64` it calls) as trust-ir TEXT.
    emit_match: Option<String>,
    /// When set (with `--m3`), also emit the M5.4 recursive-ADT-`match` round-trip
    /// module (`count_succ`, the value-producing `match &Level -> i64` fold + its
    /// `Level` tagged struct) as trust-ir TEXT.
    emit_adt: Option<String>,
    /// When set (with `--m3`), also emit the M5.6 capstone round-trip module
    /// (`Level::is_zero` + `Level::is_nonzero` + the `Level` tagged struct) as
    /// trust-ir TEXT — the REAL clean-kernel bool predicate through MonoCx.
    emit_pred: Option<String>,
    /// When set (with `--m3`), also emit the M5.7c scalar-op round-trip module
    /// (`negate` + `bitops` + `divrem` + `shifts`, all i64) as trust-ir TEXT for
    /// the downstream trust-cg JIT cross-check.
    emit_ops: Option<String>,
    /// When set (with `--m3`), also emit the M5.7d multi-type-param round-trip
    /// module (`fst__i64_i64` + `combine__i64_i64`) as trust-ir TEXT for the
    /// downstream trust-cg JIT cross-check.
    emit_multigen: Option<String>,
    /// When set (with `--m3`), also emit the M5.7b inline-scalar-payload round-trip
    /// module (`eval`, the recursive `match &Val -> i64` expression fold + its
    /// `Val` tagged struct) as trust-ir TEXT for the downstream trust-cg JIT
    /// cross-check.
    emit_eval: Option<String>,
    /// When set (with `--m3`), also emit the M5.7a nested-constructor-pattern
    /// round-trip module (`is_beta_redex`, the `match &Term -> bool` redex detector
    /// + its `Term` tagged struct) as trust-ir TEXT for the downstream trust-cg JIT
    /// cross-check.
    emit_redex: Option<String>,
    /// When set (with `--m3`), also emit the M5.7f enum-variant-construction
    /// round-trip module (the construct-then-fold fns `one_depth`/`two_depth`/
    /// `lit_eval`/`neg_lit` + their `Level`/`Val` tagged structs) as trust-ir TEXT
    /// for a downstream trust-cg JIT cross-check (IF trust-cg JITs HeapAlloc).
    emit_construct: Option<String>,
    /// When set (with `--m3`), also emit the M5.7e aggregate-payload round-trip
    /// module (`sym_sum`, the `match &Sym -> i64` fold over an inline-tuple `Span`
    /// payload + its `Sym` tagged struct) as trust-ir TEXT for the downstream
    /// trust-cg JIT cross-check.
    emit_sym: Option<String>,
    /// COVERAGE mode (`--coverage`). For EVERY fn/assoc-fn `hir_body_owner` in the
    /// input file, ATTEMPT to lower it through the UNIFIED worklist path
    /// (`m3::lower_callchain_instance` at an i64 seed instantiation — this is the
    /// SAME path `--m3`/default use, covering recursion, match incl. nested/OR,
    /// if/let, arith/logic/bitops, enum match+construction, single-type-param
    /// generics) and TALLY: total fns, lowered-ok (validate_module 0 errors), and
    /// bailed (bucketed by the LowerError message prefix). Prints a ranked
    /// histogram of bail reasons. Purely additive: it does not affect any other
    /// mode and emits nothing.
    coverage: bool,
}

impl Callbacks for FrontendCallbacks {
    // Run lowering at `after_expansion`, BEFORE the analysis pass builds MIR and
    // STEALS each function's THIR `Steal<Thir>`. Reading `tcx.thir_body(def)`
    // here triggers typeck + THIR construction on demand and the steal cell is
    // still intact. (Doing this in `after_analysis` panics with "attempted to
    // read from stolen value: Thir" because MIR build already stole it.)
    fn after_expansion(&mut self, _compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        if self.coverage {
            run_coverage(tcx);
            return Compilation::Stop;
        }
        if self.m3 {
            run_m3(
                tcx,
                self.emit_text.as_deref(),
                self.emit_callchain.as_deref(),
                self.emit_if.as_deref(),
                self.emit_let.as_deref(),
                self.emit_match.as_deref(),
                self.emit_adt.as_deref(),
                self.emit_pred.as_deref(),
                self.emit_ops.as_deref(),
                self.emit_multigen.as_deref(),
                self.emit_eval.as_deref(),
                self.emit_redex.as_deref(),
                self.emit_construct.as_deref(),
                self.emit_sym.as_deref(),
            );
            return Compilation::Stop;
        }
        let mut any = false;
        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
                continue;
            }
            let name = tcx.item_name(def_id).to_string();
            if !self.target_fns.iter().any(|t| *t == name) {
                continue;
            }
            any = true;
            eprintln!("== lowering `{name}` (def {local_def_id:?}) ==");
            // M2: lower into an UNBUILT builder so we can append heap-constructing
            // differential runners into the SAME module and test the genuine
            // emitted predicate. We first build a standalone copy to report the
            // predicate's own validate result + block count.
            match trust_ir_frontend::lower_fn_to_module(tcx, local_def_id) {
                Ok((module, enum_model, func_id)) => {
                    let verrs = validate_module(&module);
                    eprintln!(
                        "   enum `{}` ({} variants); emitted {} block(s) on the faithful Box/Arc heap layout (fn(ptr)->bool); validate_module: {} error(s)",
                        enum_model.name,
                        enum_model.variants.len(),
                        module
                            .function_by_id(func_id)
                            .map(|f| f.blocks.len())
                            .unwrap_or(0),
                        verrs.len()
                    );
                    for e in verrs.iter().take(5) {
                        eprintln!("     validate: {e:?}");
                    }
                    // Span-threading provenance: how many of the lowered
                    // predicate's instructions carry a real SourceSpan, and
                    // which debug-info file-table entry they point at. The
                    // acceptance gate asserts on this line.
                    if let Some(f) = module.function_by_id(func_id) {
                        eprintln!(
                            "   {}",
                            trust_ir_frontend::span_map::function_span_report(&module, f)
                        );
                    }
                    // FIX 1(a): pin the recovered layout against rustc ground
                    // truth. `enum_model.layout` is the EXACT `EnumLayout`
                    // `tcx.layout_of` produced — the same one the heap builder
                    // AND the predicate reader consume — so asserting it here
                    // catches any `layout_of` divergence the self-consistent
                    // differential would silently agree with.
                    if self.assert_layout {
                        assert_m6_niche_level_layout(&enum_model);
                    }
                    // FIX 1(b) support: env-gated dump of the lowered predicate
                    // module as trust-ir TEXT, so the niche-`Level` `is_zero`/
                    // `is_nonzero` IR can be embedded VERBATIM into the trust-cg
                    // e2e genuine-rustc-memory cross-check. Off by default (no
                    // effect on RESULT output or --emit byte-identity); writes to
                    // `$AY_EMIT_TARGET_IR_DIR/<fn>.tir` when set.
                    if let Ok(dir) = std::env::var("AY_EMIT_TARGET_IR_DIR") {
                        let path = std::path::Path::new(&dir).join(format!("{name}.tir"));
                        let text = format!("{module}");
                        match std::fs::write(&path, &text) {
                            Ok(()) => eprintln!(
                                "   AY_EMIT_TARGET_IR: wrote {} bytes of `{name}` trust-ir text to {}",
                                text.len(),
                                path.display()
                            ),
                            Err(e) => eprintln!(
                                "   AY_EMIT_TARGET_IR FAILED to write {}: {e}",
                                path.display()
                            ),
                        }
                    }
                }
                Err(e) => {
                    eprintln!("   LOWERING FAILED: {e}");
                    continue;
                }
            }
            // Now re-lower into a builder and run the heap differential against
            // the native oracle (incl. Param) over the shared corpus.
            match trust_ir_frontend::lower_fn_to_builder(tcx, local_def_id) {
                Ok((mb, enum_model, func_id)) => {
                    run_differential_for(&name, mb, func_id, &enum_model)
                }
                Err(e) => eprintln!("   DIFFERENTIAL SKIPPED (re-lower failed): {e}"),
            }
        }
        if !any {
            eprintln!(
                "no target fn matched (looked for {:?}); functions present: {:?}",
                self.target_fns,
                tcx.hir_body_owners()
                    .filter(|d| matches!(
                        tcx.def_kind(d.to_def_id()),
                        DefKind::Fn | DefKind::AssocFn
                    ))
                    .map(|d| tcx.item_name(d.to_def_id()).to_string())
                    .collect::<Vec<_>>()
            );
        }
        Compilation::Stop
    }
}

/// Reduce a `LowerError` message to a stable HISTOGRAM BUCKET prefix. The
/// frontend's bail messages are diagnostic-rich (they often quote the specific
/// def-id / type / variant name), so two bails of the SAME shape would otherwise
/// be distinct buckets. We normalize: take the text up to the first `:` (the bail
/// "category"), strip a leading milestone tag (`M3`/`M4`/`M5.7d`/`FIX 11` ...),
/// drop any parenthesized aside, collapse whitespace, and cap the length. This
/// groups e.g. every "callee ... is not a core::ops Add/Sub/Mul operator" bail
/// and every "unsupported expr ..." bail into one ranked row.
fn bail_bucket(msg: &str) -> String {
    // The Display impl prefixes "trust-ir-frontend lowering error: " — strip it.
    let core = msg
        .strip_prefix("trust-ir-frontend lowering error: ")
        .unwrap_or(msg)
        .trim();
    // Strip a LEADING milestone tag (`M3`/`M4 `/`M5.7d `/`M5.1`/`FIX 11`) so two
    // bails of the same shape reported under different milestones share a bucket.
    let mut head = core;
    for tag in [
        "M5.7d", "M5.7a", "M5.7b", "M5.7c", "M5.7e", "M5.7f", "M5.6", "M5.5", "M5.4", "M5.3",
        "M5.2", "M5.1", "M5", "M6", "M4", "M3", "FIX 11", "FIX 5", "FIX 2", "FIX",
    ] {
        if let Some(rest) = head.strip_prefix(tag) {
            head = rest.trim_start_matches([' ', ':', '-']).trim();
            break;
        }
    }
    // SPECIAL CASE — the single biggest real-code blocker: a Call to a NON-LOCAL
    // (extern, e.g. stdlib/core) fn. The raw message quotes the exact DefId path,
    // so each distinct callee would be its own bucket. Group by the CALLEE's
    // crate+leading module path so the roadmap shows WHICH std surfaces block the
    // most fns (e.g. `core::option`, `alloc::vec`, `core::cmp`, `intrinsics`).
    if head.contains("is not local (extern body)") {
        // message form: "callee DefId(2:10793 ~ core[1efe]::option::{impl#0}::map) is not local..."
        if let Some(start) = head.find('~') {
            let after = &head[start + 1..];
            let path = after.split(')').next().unwrap_or(after).trim();
            // Keep crate + up to two module segments (drop the `[hash]` + tail).
            let cleaned = path.replace(|c: char| c == '[', " ").to_string();
            let crate_name = cleaned.split_whitespace().next().unwrap_or("?");
            // module segments after the crate's `::`
            let segs: Vec<&str> = path.split("::").collect();
            let modpath = if segs.len() >= 3 {
                format!("{}::{}", segs.get(1).copied().unwrap_or(""), segs.get(2).copied().unwrap_or(""))
            } else if segs.len() == 2 {
                segs[1].to_string()
            } else {
                String::new()
            };
            let modpath = modpath.split('{').next().unwrap_or(&modpath).trim_end_matches(':').to_string();
            return format!("extern-callee: {crate_name}::{modpath} (not local)");
        }
        return "extern-callee: <unknown> (not local)".to_string();
    }
    // General case: category = text before the first ':' AFTER the milestone strip.
    let cat = head.split(':').next().unwrap_or(head).trim();
    // Drop a trailing parenthesized aside and collapse whitespace.
    let cat = cat.split('(').next().unwrap_or(cat).trim();
    let collapsed: String = cat.split_whitespace().collect::<Vec<_>>().join(" ");
    // Cap so a long one-liner without a ':' does not become its own bucket forever.
    let mut bucket: String = collapsed.chars().take(70).collect();
    if bucket.is_empty() {
        bucket = "<empty bail message>".to_string();
    }
    bucket
}

/// COVERAGE driver. For EVERY fn/assoc-fn `hir_body_owner` in the compiled input
/// file, attempt to lower it through the UNIFIED worklist path
/// (`m3::lower_callchain_instance` at an i64 seed) — the SAME path `--m3`/default
/// use — catch the `LowerError`, validate the emitted module, and TALLY:
///   total fns, lowered-ok (0 validate errors), bailed (bucketed by message).
/// Prints a per-fn line and a RANKED histogram of bail reasons. Purely additive.
///
/// The i64 seed instantiates every TYPE param to i64 (via the worklist's
/// `args_for_single_type_param`), so a single-type-param generic (`id`/`double`/
/// `select`) lowers at T=i64; a multi-type-param or const-generic fn whose body
/// truly needs a different binding will simply BAIL (and be counted), which is the
/// honest measurement we want. `main` and any zero-arg/diverging fn is attempted
/// too — a bail is data, not a crash (the lowering is FAIL-LOUD, never panics on
/// unsupported THIR).
fn run_coverage(tcx: TyCtxt<'_>) {
    use std::collections::BTreeMap;
    let i64_ty = tcx.types.i64;

    let mut total = 0usize;
    let mut ok = 0usize;
    let mut validate_failed = 0usize;
    let mut bailed = 0usize;
    // Bucket -> (count, one example fn name, one example full message).
    let mut buckets: BTreeMap<String, (usize, String, String)> = BTreeMap::new();
    let mut ok_names: Vec<String> = Vec::new();

    eprintln!("== COVERAGE: attempt to lower EVERY fn/assoc-fn in the input file ==");
    eprintln!(
        "   path: m3::lower_callchain_instance(def, i64 seed) -> worklist -> emit -> \
         validate_module (the unified --m3/default lowering)"
    );

    for local_def_id in tcx.hir_body_owners() {
        let def_id = local_def_id.to_def_id();
        if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        let name = tcx.item_name(def_id).to_string();
        total += 1;

        // Note generic arity for the per-fn line (informational; the i64 seed
        // binds all TYPE params to i64).
        let generics = tcx.generics_of(def_id);
        let (mut n_type, mut n_const) = (0usize, 0usize);
        for p in generics.own_params.iter() {
            match p.kind {
                rustc_middle::ty::GenericParamDefKind::Type { .. } => n_type += 1,
                rustc_middle::ty::GenericParamDefKind::Const { .. } => n_const += 1,
                rustc_middle::ty::GenericParamDefKind::Lifetime => {}
            }
        }
        let gen_tag = if n_type == 0 && n_const == 0 {
            String::new()
        } else {
            format!(" [generic: {n_type} type, {n_const} const]")
        };

        let mut mb = trust_ir_build::ModuleBuilder::new(format!("coverage::{name}"));
        match trust_ir_frontend::m3::lower_callchain_instance(
            tcx,
            &mut mb,
            local_def_id,
            i64_ty,
            "i64",
            0,
        )
        .and_then(|lowered| Ok((lowered, mb.build()?)))
        {
            Ok((lowered, module)) => {
                let verrs = validate_module(&module);
                if verrs.is_empty() {
                    ok += 1;
                    ok_names.push(name.clone());
                    eprintln!(
                        "   [OK]   {name}{gen_tag}: {} fn(s) emitted, 0 validate errors",
                        lowered.len()
                    );
                } else {
                    validate_failed += 1;
                    let bucket = format!("VALIDATE: {} error(s)", verrs.len());
                    let entry = buckets.entry(bucket).or_insert((0, name.clone(), format!("{:?}", verrs.first())));
                    entry.0 += 1;
                    eprintln!(
                        "   [VERR] {name}{gen_tag}: lowered but validate_module: {} error(s) — first: {:?}",
                        verrs.len(),
                        verrs.first()
                    );
                }
            }
            Err(e) => {
                bailed += 1;
                let full = e.to_string();
                let bucket = bail_bucket(&full);
                let entry = buckets.entry(bucket).or_insert((0, name.clone(), full.clone()));
                entry.0 += 1;
                eprintln!("   [BAIL] {name}{gen_tag}: {full}");
            }
        }
    }

    eprintln!();
    eprintln!(
        "== COVERAGE SUMMARY ==  total_fns={total}  lowered_ok={ok}  validate_failed={validate_failed}  bailed={bailed}"
    );
    if total > 0 {
        eprintln!(
            "   lowered_ok / total = {ok}/{total} = {:.1}%",
            100.0 * ok as f64 / total as f64
        );
    }
    if !ok_names.is_empty() {
        eprintln!("   OK fns: {ok_names:?}");
    }

    // Ranked histogram of bail reasons (highest count first; ties alpha).
    let mut rows: Vec<(&String, &(usize, String, String))> = buckets.iter().collect();
    rows.sort_by(|a, b| b.1 .0.cmp(&a.1 .0).then(a.0.cmp(b.0)));
    eprintln!();
    eprintln!("== RANKED BLOCKERS (bail/validate buckets, most-blocking first) ==");
    if rows.is_empty() {
        eprintln!("   (none — every fn lowered OK)");
    }
    for (bucket, (count, ex_name, ex_msg)) in rows {
        eprintln!("   [{count:>3}] {bucket}");
        eprintln!("         e.g. `{ex_name}`: {ex_msg}");
    }
}

/// M3 driver: monomorphization of the generic corpus defs per instantiation +
/// trait static dispatch. Finds the `id`, `double`, `call_yes` defs by name in
/// the compiled corpus, then runs the M3 lowering + differential harness.
fn run_m3(
    tcx: TyCtxt<'_>,
    emit_text: Option<&str>,
    emit_callchain: Option<&str>,
    emit_if: Option<&str>,
    emit_let: Option<&str>,
    emit_match: Option<&str>,
    emit_adt: Option<&str>,
    emit_pred: Option<&str>,
    emit_ops: Option<&str>,
    emit_multigen: Option<&str>,
    emit_eval: Option<&str>,
    emit_redex: Option<&str>,
    emit_construct: Option<&str>,
    emit_sym: Option<&str>,
) {
    use rustc_span::def_id::LocalDefId;
    let find = |want: &str| -> Option<LocalDefId> {
        tcx.hir_body_owners().find(|d| {
            matches!(
                tcx.def_kind(d.to_def_id()),
                DefKind::Fn | DefKind::AssocFn
            ) && tcx.item_name(d.to_def_id()).as_str() == want
        })
    };
    let (id_def, double_def, call_yes_def) =
        match (find("id"), find("double"), find("call_yes")) {
            (Some(a), Some(b), Some(c)) => (a, b, c),
            other => {
                eprintln!(
                    "M3: missing corpus def(s) {:?}; need fn `id`, `double`, `call_yes`. \
                     Present: {:?}",
                    other,
                    tcx.hir_body_owners()
                        .filter(|d| matches!(
                            tcx.def_kind(d.to_def_id()),
                            DefKind::Fn | DefKind::AssocFn
                        ))
                        .map(|d| tcx.item_name(d.to_def_id()).to_string())
                        .collect::<Vec<_>>()
                );
                return;
            }
        };

    if std::env::var("M3_DUMP_THIR").is_ok() {
        let mut dump_list = vec![("id", id_def), ("double", double_def), ("call_yes", call_yes_def)];
        if let Some(q) = find("quad") {
            dump_list.push(("quad", q));
        }
        for nm in ["pick", "max2", "select", "classify", "step", "one", "lit", "neg_lit"] {
            if let Some(d) = find(nm) {
                dump_list.push((nm, d));
            }
        }
        for (lbl, d) in dump_list {
            eprintln!("---- THIR dump: {lbl} ----");
            if let Ok((steal, body)) = tcx.thir_body(d) {
                let thir = steal.borrow();
                eprintln!("body_type = {:?}", thir.body_type);
                eprintln!("params = {:?}", thir.params.iter().map(|p| (p.ty, p.pat.is_some())).collect::<Vec<_>>());
                eprintln!("root expr {body:?} kind = {:?}", thir[body].kind);
                // shallow walk one level
                dump_expr(&thir, body, 0, 6);
            }
        }
    }

    eprintln!("== M3: monomorphization + trait static dispatch ==");
    eprintln!(
        "   API: Instance(def_id+GenericArgs) -> tcx.thir_body(generic) + \
         instantiate_and_normalize_erasing_regions(args) -> concrete trust_ir::Ty; \
         trait dispatch via Instance::try_resolve"
    );
    let call_no_def = find("call_no");
    // NON-constant trait methods (`call_two`/`call_neg`): proof the trait callee
    // body lowers through the unified `lower_expr` + a DERIVED sig, not a constant.
    let call_two_def = find("call_two");
    let call_neg_def = find("call_neg");
    match trust_ir_frontend::m3::run_m3_differential(
        tcx,
        id_def,
        double_def,
        call_yes_def,
        call_no_def,
        call_two_def,
        call_neg_def,
    ) {
        Ok((module, report)) => {
            eprintln!(
                "   instantiations lowered: id::<u32>, id::<i64>, double::<u32>, double::<i64> \
                 (4 distinct concrete Functions) + trait-dispatch callers via the UNIFIED worklist \
                 (call_yes/call_no bool + call_two/call_neg non-constant i64)"
            );
            eprintln!(
                "   emitted module: {} function(s); validate_module: {} error(s)",
                module.functions.len(),
                report.validate_errors
            );
            eprintln!(
                "   DIFFERENTIAL (trust-ir Interpreter vs expected-value oracle): {}/{} MATCH",
                report.n_match(),
                report.n_total()
            );
            for (label, got, oracle, m) in &report.checks {
                eprintln!(
                    "     [{}] {label}: ir={got} oracle={oracle}",
                    if *m { "MATCH" } else { "MISMATCH" }
                );
            }
            if report.all_match() && report.validate_errors == 0 {
                eprintln!("   M3 RESULT: ALL MATCH, 0 validate errors");
            } else {
                eprintln!("   M3 RESULT: FAILURES PRESENT (see above)");
            }
        }
        Err(e) => eprintln!("   M3 LOWERING FAILED: {e}"),
    }

    // Optionally emit the focused scalar round-trip module as trust-ir TEXT for
    // the downstream trust-cg JIT cross-check (frontend monomorphization ->
    // trust-ir text -> trust-cg -> native machine code -> executed).
    if let Some(path) = emit_text {
        match trust_ir_frontend::m3::emit_scalar_roundtrip_module(tcx, id_def, double_def) {
            Ok(module) => {
                let verrs = trust_ir_build::validate_module(&module);
                let text = format!("{module}");
                match std::fs::write(path, &text) {
                    Ok(()) => eprintln!(
                        "   EMIT-TEXT: wrote {} bytes of trust-ir text to {path} \
                         (fns: id__i64, double__i64; validate_module: {} error(s))",
                        text.len(),
                        verrs.len()
                    ),
                    Err(e) => eprintln!("   EMIT-TEXT FAILED to write {path}: {e}"),
                }
            }
            Err(e) => eprintln!("   EMIT-TEXT lowering failed: {e}"),
        }
    }

    // --- M4: monomorphic worklist over a generic CALL CHAIN (`quad`). ---------
    match find("quad") {
        Some(quad_def) => {
            eprintln!("== M4: monomorphic worklist (generic CALL CHAIN: quad calls double) ==");
            eprintln!(
                "   API: collect_worklist (root quad<i64> -> walk THIR -> resolve user-fn \
                 Calls via try_resolve -> dedup by (def_id,args), discovery order = FuncId) \
                 then emit each as a SEPARATE Function joined by a real Call edge"
            );
            match trust_ir_frontend::m3::run_m4_differential(tcx, quad_def) {
                Ok((module, report)) => {
                    eprintln!(
                        "   emitted module: {} function(s) (quad__i64 calls double__i64; \
                         NOT inlined); validate_module: {} error(s)",
                        module.functions.len(),
                        report.validate_errors
                    );
                    eprintln!(
                        "   DIFFERENTIAL (interp on quad__i64 vs native 4x-wrapping oracle): {}/{} MATCH",
                        report.n_match(),
                        report.n_total()
                    );
                    for (label, got, oracle, m) in &report.checks {
                        eprintln!(
                            "     [{}] {label}: ir={got} oracle={oracle}",
                            if *m { "MATCH" } else { "MISMATCH" }
                        );
                    }
                    if report.all_match() && report.validate_errors == 0 {
                        eprintln!("   M4 RESULT: ALL MATCH, 0 validate errors");
                    } else {
                        eprintln!("   M4 RESULT: FAILURES PRESENT (see above)");
                    }
                }
                Err(e) => eprintln!("   M4 LOWERING FAILED: {e}"),
            }

            // Optionally emit the call-chain round-trip module as trust-ir TEXT.
            if let Some(path) = emit_callchain {
                match trust_ir_frontend::m3::emit_callchain_roundtrip_module(tcx, quad_def) {
                    Ok(module) => {
                        let verrs = trust_ir_build::validate_module(&module);
                        let text = format!("{module}");
                        match std::fs::write(path, &text) {
                            Ok(()) => eprintln!(
                                "   EMIT-CALLCHAIN: wrote {} bytes of trust-ir text to {path} \
                                 (fns: quad__i64, double__i64; validate_module: {} error(s))",
                                text.len(),
                                verrs.len()
                            ),
                            Err(e) => eprintln!("   EMIT-CALLCHAIN FAILED to write {path}: {e}"),
                        }
                    }
                    Err(e) => eprintln!("   EMIT-CALLCHAIN lowering failed: {e}"),
                }
            }
        }
        None => eprintln!("== M4: no `quad` def in corpus; skipping call-chain worklist =="),
    }

    // --- M5.1: if/else control flow + multi-param functions. ------------------
    match find("pick") {
        Some(pick_def) => {
            use trust_ir_frontend::m3::M5Case;
            eprintln!("== M5.1: if/else control flow + multi-param functions ==");
            eprintln!(
                "   API: unified `lower_expr` (per-expr ir-ty from THIR) + ExprKind::If \
                 -> CondBr to then/else blocks joining at a block-param; N block-params \
                 (one per fn input) bound positionally; collect_calls descends into branches"
            );
            // Build the case list: pick (always), select (if present, proves `if`
            // under monomorphization at T=i64), max2 (if present, signed `>=`).
            let mut cases: Vec<M5Case> = Vec::new();
            // pick(c,a,b) = if c { a } else { b }.
            cases.push(M5Case {
                label: "pick(true,7,9)".into(),
                def: pick_def,
                args: vec![1, 7, 9],
                oracle: 7,
            });
            cases.push(M5Case {
                label: "pick(false,7,9)".into(),
                def: pick_def,
                args: vec![0, 7, 9],
                oracle: 9,
            });
            let select_def = find("select");
            if let Some(sel) = select_def {
                cases.push(M5Case {
                    label: "select::<i64>(true,7,9)".into(),
                    def: sel,
                    args: vec![1, 7, 9],
                    oracle: 7,
                });
                cases.push(M5Case {
                    label: "select::<i64>(false,7,9)".into(),
                    def: sel,
                    args: vec![0, 7, 9],
                    oracle: 9,
                });
            }
            if let Some(m) = find("max2") {
                cases.push(M5Case {
                    label: "max2(7,9)".into(),
                    def: m,
                    args: vec![7, 9],
                    oracle: 9,
                });
                cases.push(M5Case {
                    label: "max2(9,7)".into(),
                    def: m,
                    args: vec![9, 7],
                    oracle: 9,
                });
                cases.push(M5Case {
                    label: "max2(-3,-3)".into(),
                    def: m,
                    args: vec![-3, -3],
                    oracle: -3,
                });
            }

            match trust_ir_frontend::m3::run_m5_differential(tcx, &cases) {
                Ok((module, report)) => {
                    eprintln!(
                        "   per-case modules emitted (last: {} function(s)); \
                         validate_module across cases: {} error(s)",
                        module.functions.len(),
                        report.validate_errors
                    );
                    eprintln!(
                        "   DIFFERENTIAL (interp on if/multi-param fns vs expected-value oracle): {}/{} MATCH",
                        report.n_match(),
                        report.n_total()
                    );
                    for (label, got, oracle, m) in &report.checks {
                        eprintln!(
                            "     [{}] {label}: ir={got} oracle={oracle}",
                            if *m { "MATCH" } else { "MISMATCH" }
                        );
                    }
                    if report.all_match() && report.validate_errors == 0 {
                        eprintln!("   M5 RESULT: ALL MATCH, 0 validate errors");
                    } else {
                        eprintln!("   M5 RESULT: FAILURES PRESENT (see above)");
                    }
                }
                Err(e) => eprintln!("   M5 LOWERING FAILED: {e}"),
            }

            // Optionally emit the if/pick round-trip module as trust-ir TEXT.
            if let Some(path) = emit_if {
                match trust_ir_frontend::m3::emit_if_roundtrip_module(tcx, pick_def, select_def) {
                    Ok(module) => {
                        let verrs = trust_ir_build::validate_module(&module);
                        let text = format!("{module}");
                        match std::fs::write(path, &text) {
                            Ok(()) => eprintln!(
                                "   EMIT-IF: wrote {} bytes of trust-ir text to {path} \
                                 (fns: pick{}; validate_module: {} error(s))",
                                text.len(),
                                if select_def.is_some() { ", select__i64" } else { "" },
                                verrs.len()
                            ),
                            Err(e) => eprintln!("   EMIT-IF FAILED to write {path}: {e}"),
                        }
                    }
                    Err(e) => eprintln!("   EMIT-IF lowering failed: {e}"),
                }
            }
        }
        None => eprintln!("== M5.1: no `pick` def in corpus; skipping if/multi-param =="),
    }

    // --- M5.2: `let`-bindings (multi-statement blocks). -----------------------
    match (find("poly"), find("quad_let")) {
        (Some(poly_def), Some(quad_let_def)) => {
            use trust_ir_frontend::m3::M5Case;
            eprintln!("== M5.2: `let`-bindings (multi-statement blocks) ==");
            eprintln!(
                "   API: unified `lower_expr` Block arm lowers each `let pat = init` \
                 (binding the var into MonoCx::locals) before peeling to the tail; \
                 VarRef resolves locals THEN params; collect_calls walks let initializers"
            );
            let mut cases: Vec<M5Case> = Vec::new();
            // poly(x) = 3x (sequential lets, value reuse).
            cases.push(M5Case { label: "poly(5)".into(), def: poly_def, args: vec![5], oracle: 15 });
            cases.push(M5Case {
                label: "poly(-3)".into(),
                def: poly_def,
                args: vec![-3],
                oracle: -9,
            });
            // quad_let(x) = 4x (a let feeding a call chain).
            cases.push(M5Case {
                label: "quad_let(7)".into(),
                def: quad_let_def,
                args: vec![7],
                oracle: 28,
            });
            // quad_let(i64::MAX) = 4*MAX wrapping = -4 (i64 wrap), a width witness.
            cases.push(M5Case {
                label: "quad_let(i64::MAX) [wraps]".into(),
                def: quad_let_def,
                args: vec![i64::MAX as i128],
                oracle: (i64::MAX.wrapping_mul(4)) as i128,
            });
            // twice_let::<i64>(x) = 2x (a let UNDER monomorphization), if present.
            if let Some(tl) = find("twice_let") {
                cases.push(M5Case {
                    label: "twice_let::<i64>(5)".into(),
                    def: tl,
                    args: vec![5],
                    oracle: 10,
                });
                cases.push(M5Case {
                    label: "twice_let::<i64>(-9)".into(),
                    def: tl,
                    args: vec![-9],
                    oracle: -18,
                });
            }

            match trust_ir_frontend::m3::run_m5b_differential(tcx, &cases) {
                Ok((module, report)) => {
                    eprintln!(
                        "   per-case modules emitted (last: {} function(s)); \
                         validate_module across cases: {} error(s)",
                        module.functions.len(),
                        report.validate_errors
                    );
                    eprintln!(
                        "   DIFFERENTIAL (interp on let-binding fns vs expected-value oracle): {}/{} MATCH",
                        report.n_match(),
                        report.n_total()
                    );
                    for (label, got, oracle, m) in &report.checks {
                        eprintln!(
                            "     [{}] {label}: ir={got} oracle={oracle}",
                            if *m { "MATCH" } else { "MISMATCH" }
                        );
                    }
                    if report.all_match() && report.validate_errors == 0 {
                        eprintln!("   M5.2 RESULT: ALL MATCH, 0 validate errors");
                    } else {
                        eprintln!("   M5.2 RESULT: FAILURES PRESENT (see above)");
                    }
                }
                Err(e) => eprintln!("   M5.2 LOWERING FAILED: {e}"),
            }

            // Optionally emit the let round-trip module as trust-ir TEXT.
            if let Some(path) = emit_let {
                match trust_ir_frontend::m3::emit_let_roundtrip_module(tcx, poly_def, quad_let_def) {
                    Ok(module) => {
                        let verrs = trust_ir_build::validate_module(&module);
                        let text = format!("{module}");
                        match std::fs::write(path, &text) {
                            Ok(()) => eprintln!(
                                "   EMIT-LET: wrote {} bytes of trust-ir text to {path} \
                                 (fns: poly, quad_let__i64, double__i64; \
                                 validate_module: {} error(s))",
                                text.len(),
                                verrs.len()
                            ),
                            Err(e) => eprintln!("   EMIT-LET FAILED to write {path}: {e}"),
                        }
                    }
                    Err(e) => eprintln!("   EMIT-LET lowering failed: {e}"),
                }
            }
        }
        other => eprintln!(
            "== M5.2: missing `poly`/`quad_let` def(s) {other:?}; skipping let-bindings =="
        ),
    }

    // --- M5.3: `match`-as-VALUE over a scalar (integer) discriminant. ---------
    match find("classify") {
        Some(classify_def) => {
            use trust_ir_frontend::m3::M5Case;
            eprintln!("== M5.3: `match`-as-VALUE over a scalar (integer) discriminant ==");
            eprintln!(
                "   API: unified `lower_expr` ExprKind::Match -> `Switch` on the integer \
                 scrutinee VALUE (NOT a heap tag Load) joining each arm at a block-param; \
                 integer-literal arms become SwitchCases, a `_`/binding catch-all is the \
                 default (a binding binds the scrutinee into MonoCx::locals); \
                 collect_calls walks the scrutinee + each arm body. ADT scrutinee -> M5.4"
            );
            let mut cases: Vec<M5Case> = Vec::new();
            // classify(x): 0->100, 1->200, 7->700, _->999.
            cases.push(M5Case {
                label: "classify(0)".into(),
                def: classify_def,
                args: vec![0],
                oracle: 100,
            });
            cases.push(M5Case {
                label: "classify(1)".into(),
                def: classify_def,
                args: vec![1],
                oracle: 200,
            });
            cases.push(M5Case {
                label: "classify(7)".into(),
                def: classify_def,
                args: vec![7],
                oracle: 700,
            });
            cases.push(M5Case {
                label: "classify(2) [catch-all]".into(),
                def: classify_def,
                args: vec![2],
                oracle: 999,
            });
            cases.push(M5Case {
                label: "classify(-5) [catch-all]".into(),
                def: classify_def,
                args: vec![-5],
                oracle: 999,
            });
            // step(x): 0 -> double(x+1) = 2 ; n -> double(n) = 2x (binding + helper).
            let step_def = find("step");
            if let Some(s) = step_def {
                cases.push(M5Case {
                    label: "step(0) [arm calls double(x+1)]".into(),
                    def: s,
                    args: vec![0],
                    oracle: 2,
                });
                cases.push(M5Case {
                    label: "step(5) [binding n -> double(n)]".into(),
                    def: s,
                    args: vec![5],
                    oracle: 10,
                });
                cases.push(M5Case {
                    label: "step(-4) [binding n -> double(n)]".into(),
                    def: s,
                    args: vec![-4],
                    oracle: -8,
                });
            }
            // sign(x) (audit FIX #4): NEGATIVE + BOUNDARY literal arms. Proves
            // `eval_pat_const_int` decodes a negative literal (`-1`) and the
            // extreme `i64::MIN` correctly (sign-extension), and the catch-all
            // still routes an unlisted value. -1 -> 100, 0 -> 200,
            // i64::MIN -> 300, 5 -> 999.
            if let Some(sd) = find("sign") {
                cases.push(M5Case {
                    label: "sign(-1) [negative literal arm]".into(),
                    def: sd,
                    args: vec![-1],
                    oracle: 100,
                });
                cases.push(M5Case {
                    label: "sign(0)".into(),
                    def: sd,
                    args: vec![0],
                    oracle: 200,
                });
                cases.push(M5Case {
                    label: "sign(i64::MIN) [boundary literal arm]".into(),
                    def: sd,
                    args: vec![i64::MIN as i128],
                    oracle: 300,
                });
                cases.push(M5Case {
                    label: "sign(5) [catch-all]".into(),
                    def: sd,
                    args: vec![5],
                    oracle: 999,
                });
            }

            match trust_ir_frontend::m3::run_m5c_differential(tcx, &cases) {
                Ok((module, report)) => {
                    eprintln!(
                        "   per-case modules emitted (last: {} function(s)); \
                         validate_module across cases: {} error(s)",
                        module.functions.len(),
                        report.validate_errors
                    );
                    eprintln!(
                        "   DIFFERENTIAL (interp on scalar-match fns vs expected-value oracle): {}/{} MATCH",
                        report.n_match(),
                        report.n_total()
                    );
                    for (label, got, oracle, m) in &report.checks {
                        eprintln!(
                            "     [{}] {label}: ir={got} oracle={oracle}",
                            if *m { "MATCH" } else { "MISMATCH" }
                        );
                    }
                    if report.all_match() && report.validate_errors == 0 {
                        eprintln!("   M5.3 RESULT: ALL MATCH, 0 validate errors");
                    } else {
                        eprintln!("   M5.3 RESULT: FAILURES PRESENT (see above)");
                    }
                }
                Err(e) => eprintln!("   M5.3 LOWERING FAILED: {e}"),
            }

            // Optionally emit the scalar-match round-trip module as trust-ir TEXT.
            if let Some(path) = emit_match {
                match trust_ir_frontend::m3::emit_match_roundtrip_module(tcx, classify_def, step_def)
                {
                    Ok(module) => {
                        let verrs = trust_ir_build::validate_module(&module);
                        let text = format!("{module}");
                        match std::fs::write(path, &text) {
                            Ok(()) => eprintln!(
                                "   EMIT-MATCH: wrote {} bytes of trust-ir text to {path} \
                                 (fns: classify{}; validate_module: {} error(s))",
                                text.len(),
                                if step_def.is_some() {
                                    ", step__i64, double__i64"
                                } else {
                                    ""
                                },
                                verrs.len()
                            ),
                            Err(e) => eprintln!("   EMIT-MATCH FAILED to write {path}: {e}"),
                        }
                    }
                    Err(e) => eprintln!("   EMIT-MATCH lowering failed: {e}"),
                }
            }
        }
        None => eprintln!("== M5.3: no `classify` def in corpus; skipping scalar match =="),
    }

    // --- SCALAR DEREF (audit FIX 2): `*r` of a `&i64` is a typed Load. ---------
    match find("deref_add") {
        Some(deref_add_def) => {
            eprintln!("== SCALAR DEREF: `*r` of a `&i64` -> typed Load (audit FIX 2) ==");
            eprintln!(
                "   API: unified `lower_expr` ExprKind::Deref whose RESULT ir-ty is a scalar -> \
                 resolve the place pointer + emit a typed `Load(i64, ptr)` (NOT identity-peel the \
                 pointer typed as i64). Runner alloca+Store+Call deref_add(&x); oracle x + 1."
            );
            match trust_ir_frontend::m3::run_deref_differential(tcx, deref_add_def) {
                Ok((module, report)) => {
                    eprintln!(
                        "   emitted module: {} function(s); validate_module: {} error(s)",
                        module.functions.len(),
                        report.validate_errors
                    );
                    eprintln!(
                        "   DIFFERENTIAL (interp on deref_add over alloca'd i64 inputs vs native \
                         `x + 1` oracle): {}/{} MATCH",
                        report.n_match(),
                        report.n_total()
                    );
                    for (label, got, oracle, m) in &report.checks {
                        eprintln!(
                            "     [{}] {label}: ir={got} oracle={oracle}",
                            if *m { "MATCH" } else { "MISMATCH" }
                        );
                    }
                    if report.all_match() && report.validate_errors == 0 {
                        eprintln!("   SCALAR-DEREF RESULT: ALL MATCH, 0 validate errors");
                    } else {
                        eprintln!("   SCALAR-DEREF RESULT: FAILURES PRESENT (see above)");
                    }
                }
                Err(e) => eprintln!("   SCALAR-DEREF LOWERING FAILED: {e}"),
            }
        }
        None => eprintln!("== SCALAR DEREF: no `deref_add` def in corpus; skipping scalar-deref =="),
    }

    // --- M5.4: `match` over a RECURSIVE ADT (heap-tag), value-returning. -------
    match find("count_succ") {
        Some(count_succ_def) => {
            eprintln!("== M5.4: `match` over a RECURSIVE ADT (heap-tag), value-returning ==");
            eprintln!(
                "   API: unified `lower_expr` ExprKind::Match over an `&Enum` (Ptr) -> Load the \
                 discriminant tag through the tagged-struct heap shape + `Switch` joining each arm \
                 at a block-param; per-arm payload bindings bound to child HEAP POINTERS in \
                 MonoCx::locals (load_field at payload_offset); recursion via the worklist Call \
                 edge (a self-call resolves to the same instance's FuncId). Reuses lib.rs \
                 build_enum_model/load_field/pattern_variants/collect_bindings (the M1/M2 helpers)."
            );
            match trust_ir_frontend::m3::run_m5d_differential(tcx, count_succ_def) {
                Ok((module, report)) => {
                    eprintln!(
                        "   emitted module: {} function(s) (count_succ self-recurses; \
                         `Level` tagged struct registered); validate_module: {} error(s)",
                        module.functions.len(),
                        report.validate_errors
                    );
                    eprintln!(
                        "   DIFFERENTIAL (interp on count_succ over real heap inputs vs native \
                         `Micro::count_succ` oracle, several depths): {}/{} MATCH",
                        report.n_match(),
                        report.n_total()
                    );
                    for (label, got, oracle, m) in &report.checks {
                        eprintln!(
                            "     [{}] {label}: ir={got} oracle={oracle}",
                            if *m { "MATCH" } else { "MISMATCH" }
                        );
                    }
                    if report.all_match() && report.validate_errors == 0 {
                        eprintln!("   M5.4 RESULT: ALL MATCH, 0 validate errors");
                    } else {
                        eprintln!("   M5.4 RESULT: FAILURES PRESENT (see above)");
                    }
                }
                Err(e) => eprintln!("   M5.4 LOWERING FAILED: {e}"),
            }

            // Optionally emit the recursive-ADT-match round-trip module as trust-ir TEXT.
            if let Some(path) = emit_adt {
                match trust_ir_frontend::m3::emit_adt_match_roundtrip_module(tcx, count_succ_def) {
                    Ok(module) => {
                        let verrs = trust_ir_build::validate_module(&module);
                        let text = format!("{module}");
                        match std::fs::write(path, &text) {
                            Ok(()) => eprintln!(
                                "   EMIT-ADT: wrote {} bytes of trust-ir text to {path} \
                                 (fns: count_succ__i64 + `Level` struct; \
                                 validate_module: {} error(s))",
                                text.len(),
                                verrs.len()
                            ),
                            Err(e) => eprintln!("   EMIT-ADT FAILED to write {path}: {e}"),
                        }
                    }
                    Err(e) => eprintln!("   EMIT-ADT lowering failed: {e}"),
                }
            }
        }
        None => eprintln!("== M5.4: no `count_succ` def in corpus; skipping recursive-ADT match =="),
    }

    // --- M5.7b: INLINE-SCALAR enum payload (a tiny expression evaluator). ------
    match find("eval") {
        Some(eval_def) => {
            eprintln!("== M5.7b: INLINE-SCALAR enum payload (`match &Val -> i64`, a tiny expression evaluator) ==");
            eprintln!(
                "   API: a `match &Val` heap-tag match (M5.4) whose `Lit(n)` arm binds an \
                 INLINE-SCALAR payload — a by-ref binding `n` of an i64 field is the ADDRESS of \
                 the inline value (the slot GEP, NO Load); the body's `*n` (the M5.4 scalar-Deref \
                 path) Loads it. `Neg(a)`/`Add(a,b)` bind Box CHILDREN (the unchanged M5.4 \
                 pointer-payload Load(Ptr)) + recurse (`-eval(a)`, `eval(a)+eval(b)`, M5.7c \
                 neg/add). Differential drives the THIR-lowered `eval` over real `Val` heap \
                 graphs (inline `Lit`, Box `Neg`/`Add`) vs native `Val::eval` oracle."
            );
            match trust_ir_frontend::m3::run_m5i_differential(tcx, eval_def) {
                Ok((module, report)) => {
                    eprintln!(
                        "   emitted module: {} function(s) (eval self-recurses; `Val` tagged \
                         struct registered); validate_module: {} error(s)",
                        module.functions.len(),
                        report.validate_errors
                    );
                    eprintln!(
                        "   DIFFERENTIAL (interp on eval over real `Val` heap inputs vs native \
                         `Val::eval` oracle, Lit/Neg/Add nesting): {}/{} MATCH",
                        report.n_match(),
                        report.n_total()
                    );
                    for (label, got, oracle, m) in &report.checks {
                        eprintln!(
                            "     [{}] {label}: ir={got} oracle={oracle}",
                            if *m { "MATCH" } else { "MISMATCH" }
                        );
                    }
                    if report.all_match() && report.validate_errors == 0 {
                        eprintln!("   M5.7b RESULT: ALL MATCH, 0 validate errors");
                    } else {
                        eprintln!("   M5.7b RESULT: FAILURES PRESENT (see above)");
                    }
                }
                Err(e) => eprintln!("   M5.7b LOWERING FAILED: {e}"),
            }

            // Optionally emit the inline-scalar-payload round-trip module as trust-ir TEXT.
            if let Some(path) = emit_eval {
                match trust_ir_frontend::m3::emit_eval_roundtrip_module(tcx, eval_def) {
                    Ok(module) => {
                        let verrs = trust_ir_build::validate_module(&module);
                        let text = format!("{module}");
                        match std::fs::write(path, &text) {
                            Ok(()) => eprintln!(
                                "   EMIT-EVAL: wrote {} bytes of trust-ir text to {path} \
                                 (fns: eval__i64 + `Val` struct; validate_module: {} error(s))",
                                text.len(),
                                verrs.len()
                            ),
                            Err(e) => eprintln!("   EMIT-EVAL FAILED to write {path}: {e}"),
                        }
                    }
                    Err(e) => eprintln!("   EMIT-EVAL lowering failed: {e}"),
                }
            }
        }
        None => eprintln!("== M5.7b: no `eval` def in corpus; skipping inline-scalar payload =="),
    }

    // --- M5.7a: NESTED-CONSTRUCTOR match patterns (the canonical β-redex shape). -
    match find("is_beta_redex") {
        Some(_) => {
            eprintln!("== M5.7a: NESTED-CONSTRUCTOR match patterns (`App(box Lam(_), _)`, the canonical β-redex shape) ==");
            eprintln!(
                "   API: an ADT-match arm with EXACTLY ONE one-level nested constructor field \
                 (e.g. `App`'s field 0 = `box Lam(_)`), the rest trivial, PLUS a catch-all `_`. \
                 The outer Switch routes the outer variant to a CANDIDATE block that loads the \
                 nested field's Box child, reads its inner i32 tag, and `condbr (inner_tag == \
                 <nested-variant discr>) -> arm_block, default` — the nested-fail edge falls \
                 through to the catch-all (Rust first-match). The nested ctor's OWN binder (the \
                 `b` in `Lam(b)`) is bound against the nested child pointer via the SAME \
                 type-classified payload binder (`bind_payload_field`). Deeper / ambiguous \
                 nests still BAIL loud (the refined soundness guard). Differential drives the \
                 THIR-lowered predicate over real `Term` heap graphs vs the native `Term` oracle."
            );
            // Two predicates sharing the `Term` shape: the CORE M5.7a proof
            // (`is_beta_redex`, nested ctor with no inner binding) + the BINDING
            // variant (`redex_body_is_var`, nested ctor binding `b` + a further
            // nested match on the bound child). Each runs its own differential over
            // the SAME Term corpus (mirroring M5.6's is_zero/is_nonzero split).
            let preds = [("is_beta_redex", find("is_beta_redex")), ("redex_body_is_var", find("redex_body_is_var"))];
            let mut total_match = 0usize;
            let mut total_cases = 0usize;
            let mut any_fail = false;
            for (pname, pdef) in preds {
                let Some(pdef) = pdef else {
                    eprintln!("   [{pname}] no def in corpus; skipping");
                    continue;
                };
                match trust_ir_frontend::m3::run_m5j_differential(tcx, pdef, pname) {
                    Ok((module, report)) => {
                        eprintln!(
                            "   [{pname}] emitted module: {} function(s) (`Term` tagged struct \
                             registered); validate_module: {} error(s); DIFFERENTIAL (interp on \
                             {pname} over real `Term` heap graphs vs native `Term::{pname}` \
                             oracle, App(Lam,..)/App(Var,..)/Lam/Var true+false trees): {}/{} MATCH",
                            module.functions.len(),
                            report.validate_errors,
                            report.n_match(),
                            report.n_total()
                        );
                        for (label, got, oracle, m) in &report.checks {
                            eprintln!(
                                "     [{}] {label}: ir={got} oracle={oracle}",
                                if *m { "MATCH" } else { "MISMATCH" }
                            );
                        }
                        total_match += report.n_match();
                        total_cases += report.n_total();
                        if !report.all_match() || report.validate_errors != 0 {
                            any_fail = true;
                        }
                    }
                    Err(e) => {
                        eprintln!("   [{pname}] M5.7a LOWERING FAILED: {e}");
                        any_fail = true;
                    }
                }
            }
            if !any_fail && total_cases > 0 {
                eprintln!(
                    "   M5.7a RESULT: ALL MATCH ({total_match}/{total_cases} across is_beta_redex+redex_body_is_var), \
                     0 validate errors — one-level nested-constructor patterns lower correctly"
                );
            } else {
                eprintln!("   M5.7a RESULT: FAILURES PRESENT (see above)");
            }

            // Optionally emit the nested-pattern round-trip module as trust-ir TEXT.
            if let Some(path) = emit_redex {
                if let Some(redex_def) = find("is_beta_redex") {
                    match trust_ir_frontend::m3::emit_redex_roundtrip_module(tcx, redex_def) {
                        Ok(module) => {
                            let verrs = trust_ir_build::validate_module(&module);
                            let text = format!("{module}");
                            match std::fs::write(path, &text) {
                                Ok(()) => eprintln!(
                                    "   EMIT-REDEX: wrote {} bytes of trust-ir text to {path} \
                                     (fns: is_beta_redex__i64 + `Term` struct; \
                                     validate_module: {} error(s))",
                                    text.len(),
                                    verrs.len()
                                ),
                                Err(e) => eprintln!("   EMIT-REDEX FAILED to write {path}: {e}"),
                            }
                        }
                        Err(e) => eprintln!("   EMIT-REDEX lowering failed: {e}"),
                    }
                }
            }
        }
        None => eprintln!("== M5.7a: no `is_beta_redex` def in corpus; skipping nested-constructor patterns =="),
    }

    // --- M5.7e: TUPLE/AGGREGATE enum payload + sub-field destructuring. ---------
    match find("sym_sum") {
        Some(sym_sum_def) => {
            eprintln!("== M5.7e: TUPLE/AGGREGATE enum payload + sub-field destructuring (`match &Sym -> i64` over an inline-tuple `Span((i64,i64))` payload) ==");
            eprintln!(
                "   API: a `match &Sym` heap-tag match (M5.4) whose `Span((a, b))` arm binds an \
                 INLINE-AGGREGATE (tuple) payload's SUB-fields. The tuple lives inline at the \
                 variant's field slot; each sub-binding GEPs to the aggregate's offset WITHIN the \
                 variant + the sub-field's offset WITHIN the tuple (both from `tcx.layout_of`). A \
                 scalar sub-field binds by ADDRESS (the slot GEP; `*a` Loads it); the `Cons(t)` arm \
                 is the unchanged M5.4 Box-child pointer path; `Nil` is a leaf. The differential \
                 drives the THIR-lowered `sym_sum` over real `Sym` heap graphs (inline-tuple \
                 `Span`, Box `Cons`, leaf `Nil`) vs the native `Sym::sym_sum` oracle. SCOPE: this \
                 is the by-ref AGGREGATE-AS-ENUM-PAYLOAD case; a tuple/struct BY VALUE \
                 (return/standalone) is DEFERRED (bail loud — no struct-by-value ABI)."
            );
            match trust_ir_frontend::m3::run_m5l_differential(tcx, sym_sum_def) {
                Ok((module, report)) => {
                    eprintln!(
                        "   emitted module: {} function(s) (sym_sum self-recurses; `Sym` tagged \
                         struct registered); validate_module: {} error(s)",
                        module.functions.len(),
                        report.validate_errors
                    );
                    eprintln!(
                        "   DIFFERENTIAL (interp on sym_sum over real `Sym` heap inputs vs native \
                         `Sym::sym_sum` oracle, Nil/Span/Cons nesting): {}/{} MATCH",
                        report.n_match(),
                        report.n_total()
                    );
                    for (label, got, oracle, m) in &report.checks {
                        eprintln!(
                            "     [{}] {label}: ir={got} oracle={oracle}",
                            if *m { "MATCH" } else { "MISMATCH" }
                        );
                    }
                    if report.all_match() && report.validate_errors == 0 {
                        eprintln!("   M5.7e RESULT: ALL MATCH, 0 validate errors");
                    } else {
                        eprintln!("   M5.7e RESULT: FAILURES PRESENT (see above)");
                    }
                }
                Err(e) => eprintln!("   M5.7e LOWERING FAILED: {e}"),
            }

            // Optionally emit the aggregate-payload round-trip module as trust-ir TEXT.
            if let Some(path) = emit_sym {
                match trust_ir_frontend::m3::emit_sym_roundtrip_module(tcx, sym_sum_def) {
                    Ok(module) => {
                        let verrs = trust_ir_build::validate_module(&module);
                        let text = format!("{module}");
                        match std::fs::write(path, &text) {
                            Ok(()) => eprintln!(
                                "   EMIT-SYM: wrote {} bytes of trust-ir text to {path} \
                                 (fns: sym_sum__i64 + `Sym` struct; validate_module: {} error(s))",
                                text.len(),
                                verrs.len()
                            ),
                            Err(e) => eprintln!("   EMIT-SYM FAILED to write {path}: {e}"),
                        }
                    }
                    Err(e) => eprintln!("   EMIT-SYM lowering failed: {e}"),
                }
            }
        }
        None => eprintln!("== M5.7e: no `sym_sum` def in corpus; skipping aggregate payload =="),
    }

    // --- FIX 5: DISTINCT-WIDTH aggregate sub-fields (`Pair::Cell((i8, i64))`). --
    match find("pair_sum") {
        Some(pair_sum_def) => {
            eprintln!("== FIX5: NARROW-WIDTH aggregate sub-fields (`match &Pair -> i32` over an inline-tuple `Cell((i32, i32))` payload) ==");
            eprintln!(
                "   API: the M5.7e aggregate-sub-field path, but the tuple is NARROW (i32 + i32, \
                 distinct from the I64 the other builders hard-lock). Each sub-field's `layout_of` \
                 OFFSET (0 and 4 in the tuple, the i32 stride) and its REAL I32 Load/Store WIDTH \
                 must both be right: the heap builder Stores each at I32, and the lowered `pair_sum` \
                 Loads each at I32 — an all-I64 model would MASK a wrong narrow width (an I64 Load \
                 of sub-field 0 would also pull in sub-field 1's bytes). Differential: THIR-lowered \
                 `pair_sum` over real `Pair` heap graphs (narrow `Cell`, Box `Next`, leaf `End`, \
                 incl. i32 boundary + wrapping values) vs the native `Pair::pair_sum` oracle."
            );
            match trust_ir_frontend::m3::run_m5_pair_differential(tcx, pair_sum_def) {
                Ok((module, report)) => {
                    eprintln!(
                        "   emitted module: {} function(s) (pair_sum self-recurses; `Pair` tagged \
                         struct registered); validate_module: {} error(s)",
                        module.functions.len(),
                        report.validate_errors
                    );
                    eprintln!(
                        "   DIFFERENTIAL (interp on pair_sum over real distinct-width `Pair` heap \
                         inputs vs native `Pair::pair_sum` oracle): {}/{} MATCH",
                        report.n_match(),
                        report.n_total()
                    );
                    for (label, got, oracle, m) in &report.checks {
                        eprintln!(
                            "     [{}] {label}: ir={got} oracle={oracle}",
                            if *m { "MATCH" } else { "MISMATCH" }
                        );
                    }
                    if report.all_match() && report.validate_errors == 0 {
                        eprintln!("   FIX5 RESULT: ALL MATCH, 0 validate errors");
                    } else {
                        eprintln!("   FIX5 RESULT: FAILURES PRESENT (see above)");
                    }
                }
                Err(e) => eprintln!("   FIX5 LOWERING FAILED: {e}"),
            }
        }
        None => eprintln!("== FIX5: no `pair_sum` def in corpus; skipping distinct-width aggregate =="),
    }

    // --- M5.7f: ENUM-VARIANT CONSTRUCTION (the DUAL of lower_match_adt). --------
    {
        let one_depth_def = find("one_depth");
        let two_depth_def = find("two_depth");
        let lit_eval_def = find("lit_eval");
        let neg_lit_def = find("neg_lit");
        // FIX 2: niche untagged-variant CONSTRUCTION (`NBox`).
        let nbox_nil_depth_def = find("nbox_nil_depth");
        let nbox_one_depth_def = find("nbox_one_depth");
        let nbox_two_depth_def = find("nbox_two_depth");
        if one_depth_def.is_some()
            || two_depth_def.is_some()
            || lit_eval_def.is_some()
            || neg_lit_def.is_some()
            || nbox_nil_depth_def.is_some()
            || nbox_one_depth_def.is_some()
            || nbox_two_depth_def.is_some()
        {
            eprintln!("== M5.7f: ENUM-VARIANT CONSTRUCTION (`Level::Succ(Box::new(Level::Zero))`, `Val::Lit(5)`, the DUAL of lower_match_adt) ==");
            eprintln!(
                "   API: an `ExprKind::Adt` constructing an ENUM VARIANT lowers to a tagged-struct \
                 heap value: `p = HeapAlloc(<enum struct>)`, `Store(i32 discr, GEP(p,@0))`, then \
                 per field i `Store` the lowered field VALUE at `GEP(p, @8+8i)` — a Box-child \
                 stores the inner POINTER (the inverse of the M5.7b/M5.4 pointer read), an inline \
                 scalar stores the VALUE (inverse of the M5.7b scalar read). `Box::new(inner)` is \
                 peeled to `inner` by the `box_new` DIAGNOSTIC ITEM (def-path identity, not a bare \
                 `new` name). Construct-then-fold differential: each fn BUILDS a closed Level/Val \
                 term then FOLDS it through the EXISTING match path (count_succ/eval) — interp vs \
                 a GENUINE native oracle (one_depth==1, two_depth==2, lit_eval(n)==n, neg_lit(n)==-n)."
            );
            match trust_ir_frontend::m3::run_m5k_differential(
                tcx,
                one_depth_def,
                two_depth_def,
                lit_eval_def,
                neg_lit_def,
                [nbox_nil_depth_def, nbox_one_depth_def, nbox_two_depth_def],
            ) {
                Ok((total_fns, report)) => {
                    eprintln!(
                        "   emitted {} function(s) across per-enum modules (construct-then-fold \
                         roots + folders + `Level`/`Val` tagged structs); validate_module: {} \
                         error(s)",
                        total_fns,
                        report.validate_errors
                    );
                    eprintln!(
                        "   DIFFERENTIAL (interp on construct-then-fold over genuine native \
                         oracles): {}/{} MATCH",
                        report.n_match(),
                        report.n_total()
                    );
                    for (label, got, oracle, m) in &report.checks {
                        eprintln!(
                            "     [{}] {label}: ir={got} oracle={oracle}",
                            if *m { "MATCH" } else { "MISMATCH" }
                        );
                    }
                    if report.all_match() && report.validate_errors == 0 {
                        eprintln!("   M5.7f RESULT: ALL MATCH, 0 validate errors");
                    } else {
                        eprintln!("   M5.7f RESULT: FAILURES PRESENT (see above)");
                    }
                }
                Err(e) => eprintln!("   M5.7f LOWERING FAILED: {e}"),
            }

            // Optionally emit the construction round-trip module as trust-ir TEXT.
            if let Some(path) = emit_construct {
                match two_depth_def {
                    Some(td) => match trust_ir_frontend::m3::emit_construct_roundtrip_module(tcx, td)
                    {
                        Ok(module) => {
                            let verrs = trust_ir_build::validate_module(&module);
                            let text = format!("{module}");
                            match std::fs::write(path, &text) {
                                Ok(()) => eprintln!(
                                    "   EMIT-CONSTRUCT: wrote {} bytes of trust-ir text to {path} \
                                     (`two_depth__i64` builds Succ(Succ(Zero)) inline + folds via \
                                     `count_succ__i64` + `Level` struct; validate_module: {} \
                                     error(s))",
                                    text.len(),
                                    verrs.len()
                                ),
                                Err(e) => eprintln!("   EMIT-CONSTRUCT FAILED to write {path}: {e}"),
                            }
                        }
                        Err(e) => eprintln!("   EMIT-CONSTRUCT lowering failed: {e}"),
                    },
                    None => eprintln!("   EMIT-CONSTRUCT skipped: missing `two_depth` def"),
                }
            }
        } else {
            eprintln!("== M5.7f: no construct-then-fold def in corpus; skipping enum-variant construction ==");
        }
    }

    // --- M5.6 CAPSTONE: REAL clean-kernel `Level::is_zero`/`is_nonzero`. -------
    match find("is_zero") {
        Some(is_zero_def) => {
            eprintln!("== M5.6 CAPSTONE: REAL clean-kernel `Level::is_zero`/`is_nonzero` (bool predicate through MonoCx) ==");
            eprintln!(
                "   API: the ACTUAL M1/M2 leaf (`match &Level` heap-tag dispatch + `&&`/`||` \
                 short-circuit + bool literals + worklist recursion on a `fn(ptr)->bool` \
                 self-call `a.is_zero()` => `Level::is_zero(a)`) lowered through the UNIFIED \
                 `MonoCx::lower_expr`. PARITY differential: drives the MonoCx-lowered predicate \
                 over the SAME model.rs heap corpus + native `Micro::is_zero/is_nonzero` oracle \
                 the M1/M2 21/21 LowerCx differential uses."
            );
            let is_nonzero_def = find("is_nonzero");
            let mut total_match = 0usize;
            let mut total_cases = 0usize;
            let mut total_verrs = 0usize;
            let mut any_fail = false;
            let preds: Vec<(&str, Option<rustc_span::def_id::LocalDefId>)> =
                vec![("is_zero", Some(is_zero_def)), ("is_nonzero", is_nonzero_def)];
            for (pname, pdef) in preds {
                let Some(pdef) = pdef else {
                    eprintln!("   ({pname}: no def in corpus; skipped)");
                    continue;
                };
                match trust_ir_frontend::m3::run_m5f_differential(tcx, pdef, pname) {
                    Ok((module, report)) => {
                        total_match += report.n_match();
                        total_cases += report.n_total();
                        total_verrs += report.validate_errors;
                        eprintln!(
                            "   [{pname}] emitted module: {} function(s) (predicate self-recurses; \
                             `Level` tagged struct registered); validate_module: {} error(s); \
                             DIFFERENTIAL (interp vs native `Micro::{pname}` over the M1/M2 heap \
                             corpus): {}/{} MATCH",
                            module.functions.len(),
                            report.validate_errors,
                            report.n_match(),
                            report.n_total()
                        );
                        for (label, got, oracle, m) in &report.checks {
                            if !m {
                                any_fail = true;
                                eprintln!("     [MISMATCH] {label}: ir={got} oracle={oracle}");
                            }
                        }
                        if report.all_match() && report.validate_errors == 0 {
                            eprintln!("     [{pname}] ALL {} cases MATCH, 0 validate errors", report.n_total());
                        }
                    }
                    Err(e) => {
                        any_fail = true;
                        eprintln!("   [{pname}] M5.6 LOWERING FAILED: {e}");
                    }
                }
            }
            if !any_fail && total_verrs == 0 && total_cases > 0 && total_match == total_cases {
                eprintln!(
                    "   M5.6 RESULT: ALL MATCH ({total_match}/{total_cases} across is_zero+is_nonzero), \
                     0 validate errors — MonoCx subsumes the M1/M2 LowerCx leaf class"
                );
            } else {
                eprintln!("   M5.6 RESULT: FAILURES PRESENT (see above)");
            }

            // Optionally emit the capstone predicate round-trip module as trust-ir TEXT.
            if let Some(path) = emit_pred {
                match trust_ir_frontend::m3::emit_predicate_roundtrip_module(
                    tcx,
                    is_zero_def,
                    is_nonzero_def,
                ) {
                    Ok(module) => {
                        let verrs = trust_ir_build::validate_module(&module);
                        let text = format!("{module}");
                        match std::fs::write(path, &text) {
                            Ok(()) => eprintln!(
                                "   EMIT-PRED: wrote {} bytes of trust-ir text to {path} \
                                 (fns: is_zero{} + `Level` struct; validate_module: {} error(s))",
                                text.len(),
                                if is_nonzero_def.is_some() { ", is_nonzero" } else { "" },
                                verrs.len()
                            ),
                            Err(e) => eprintln!("   EMIT-PRED FAILED to write {path}: {e}"),
                        }
                    }
                    Err(e) => eprintln!("   EMIT-PRED lowering failed: {e}"),
                }
            }
        }
        None => eprintln!("== M5.6: no `is_zero` def in corpus; skipping capstone predicate =="),
    }

    // --- M5.7c: unary ops (`!`/unary `-`) + the rest of the integer binops -----
    match find("negate") {
        Some(negate_def) => {
            use trust_ir_frontend::m3::{M5gCase, M5gOracle};
            eprintln!("== M5.7c: unary operators + integer Div/Rem/BitAnd/BitOr/BitXor/Shl/Shr ==");
            eprintln!(
                "   API: unified `lower_expr` ExprKind::Unary (`UnOp::Neg` -> trust-ir `UnOp::Neg`; \
                 `UnOp::Not` -> integer `UnOp::Not` (bitwise) OR a bool `Select(b,false,true)`) + \
                 `lower_binop` Div/Rem (signed `S*`/unsigned `U*` from the operand ir-ty), \
                 BitAnd/BitOr/BitXor (-> And/Or/Xor), Shl (-> Shl), Shr (-> AShr signed / LShr \
                 unsigned). Differential vs Rust-SEMANTICS expected-value oracles (computed HERE in \
                 the driver with Rust's own operators, mirroring the corpus's DOCUMENTED arithmetic \
                 — NOT hand literals, but also NOT a linked execution of the corpus fn, which is not \
                 feasible: the corpus is compiled THROUGH the frontend (rustc_driver Compilation::Stop \
                 at after_expansion) and never codegen'd to a linkable artifact. See FIX 6): \
                 negate(x)==x.wrapping_neg(), inot(x)==!x, bnot(b)==!b, bitops/divrem/shifts."
            );

            // GENUINE native oracles (computed in Rust, mirroring M4/count_succ).
            let negate_oracle = |x: i64| -> i64 { x.wrapping_neg() };
            let inot_oracle = |x: i64| -> i64 { !x };
            let bnot_oracle = |b: bool| -> bool { !b };
            let bitops_oracle = |a: i64, b: i64| -> i64 { (a & b) | (a ^ b) };
            let divrem_oracle = |a: i64, b: i64| -> i64 { (a / b).wrapping_add(a % b) };
            let shifts_oracle =
                |a: i64, n: i64| -> i64 { (a.wrapping_shl(n as u32)).wrapping_shr(n as u32) };

            let mut cases: Vec<M5gCase> = Vec::new();

            // negate (unary `-`): incl. negatives, 0, and i64::MIN (where -MIN
            // wraps to MIN — the native oracle uses wrapping_neg to match trust-ir).
            for x in [0i64, 7, -7, 123456, -123456, i64::MAX, i64::MIN] {
                cases.push(M5gCase {
                    label: format!("negate({x})"),
                    def: negate_def,
                    args: vec![x as i128],
                    oracle: M5gOracle::Int(negate_oracle(x) as i128),
                });
            }
            // inot (integer bitwise `!`).
            if let Some(d) = find("inot") {
                for x in [0i64, -1, 7, -7, i64::MAX, i64::MIN] {
                    cases.push(M5gCase {
                        label: format!("inot({x})"),
                        def: d,
                        args: vec![x as i128],
                        oracle: M5gOracle::Int(inot_oracle(x) as i128),
                    });
                }
            }
            // bnot (bool `!`) — a BOOL-returning case checked against a bool oracle.
            if let Some(d) = find("bnot") {
                for b in [false, true] {
                    cases.push(M5gCase {
                        label: format!("bnot({b})"),
                        def: d,
                        args: vec![b as i128],
                        oracle: M5gOracle::Bool(bnot_oracle(b)),
                    });
                }
            }
            // bitops (BitAnd/BitXor/BitOr): incl. negatives.
            if let Some(d) = find("bitops") {
                for (a, b) in [(0i64, 0i64), (12, 10), (-1, 5), (-8, -3), (i64::MAX, 1)] {
                    cases.push(M5gCase {
                        label: format!("bitops({a},{b})"),
                        def: d,
                        args: vec![a as i128, b as i128],
                        oracle: M5gOracle::Int(bitops_oracle(a, b) as i128),
                    });
                }
            }
            // divrem (signed Div + Rem): ONLY non-zero divisors (interp traps on 0).
            if let Some(d) = find("divrem") {
                for (a, b) in [(7i64, 2i64), (-7, 2), (7, -2), (-7, -3), (100, 9), (i64::MAX, 3)] {
                    cases.push(M5gCase {
                        label: format!("divrem({a},{b})"),
                        def: d,
                        args: vec![a as i128, b as i128],
                        oracle: M5gOracle::Int(divrem_oracle(a, b) as i128),
                    });
                }
            }
            // shifts (Shl then signed AShr): ONLY 0 <= n < 64 (interp traps OOB).
            if let Some(d) = find("shifts") {
                for (a, n) in [(1i64, 0i64), (1, 3), (-1, 5), (255, 8), (-1024, 4), (i64::MIN, 1)] {
                    cases.push(M5gCase {
                        label: format!("shifts({a},{n})"),
                        def: d,
                        args: vec![a as i128, n as i128],
                        oracle: M5gOracle::Int(shifts_oracle(a, n) as i128),
                    });
                }
            }

            match trust_ir_frontend::m3::run_m5g_differential(tcx, &cases) {
                Ok((module, report)) => {
                    eprintln!(
                        "   per-case modules emitted (last: {} function(s)); \
                         validate_module across cases: {} error(s)",
                        module.functions.len(),
                        report.validate_errors
                    );
                    eprintln!(
                        "   DIFFERENTIAL (interp on unary/binop fns vs Rust-semantics expected-value oracle): {}/{} MATCH",
                        report.n_match(),
                        report.n_total()
                    );
                    for (label, got, oracle, m) in &report.checks {
                        eprintln!(
                            "     [{}] {label}: ir={got} oracle={oracle}",
                            if *m { "MATCH" } else { "MISMATCH" }
                        );
                    }
                    if report.all_match() && report.validate_errors == 0 {
                        eprintln!("   M5.7c RESULT: ALL MATCH, 0 validate errors");
                    } else {
                        eprintln!("   M5.7c RESULT: FAILURES PRESENT (see above)");
                    }
                }
                Err(e) => eprintln!("   M5.7c LOWERING FAILED: {e}"),
            }

            // Optionally emit the scalar-op round-trip module as trust-ir TEXT.
            if let Some(path) = emit_ops {
                match (find("bitops"), find("divrem"), find("shifts")) {
                    (Some(bitops_def), Some(divrem_def), Some(shifts_def)) => {
                        match trust_ir_frontend::m3::emit_ops_roundtrip_module(
                            tcx, negate_def, bitops_def, divrem_def, shifts_def,
                        ) {
                            Ok(module) => {
                                let verrs = trust_ir_build::validate_module(&module);
                                let text = format!("{module}");
                                match std::fs::write(path, &text) {
                                    Ok(()) => eprintln!(
                                        "   EMIT-OPS: wrote {} bytes of trust-ir text to {path} \
                                         (fns: negate__i64, bitops__i64, divrem__i64, shifts__i64; \
                                         validate_module: {} error(s))",
                                        text.len(),
                                        verrs.len()
                                    ),
                                    Err(e) => eprintln!("   EMIT-OPS FAILED to write {path}: {e}"),
                                }
                            }
                            Err(e) => eprintln!("   EMIT-OPS lowering failed: {e}"),
                        }
                    }
                    other => eprintln!(
                        "   EMIT-OPS skipped: missing one of bitops/divrem/shifts defs {other:?}"
                    ),
                }
            }
        }
        None => eprintln!("== M5.7c: no `negate` def in corpus; skipping unary/binop =="),
    }

    // --- M5.7d: MULTI-type-param generic monomorphization ----------------------
    match find("fst") {
        Some(fst_def) => {
            use trust_ir_frontend::m3::{M5gOracle, M5hCase};
            eprintln!("== M5.7d: MULTI-type-param generic monomorphization (positional N-type-param binding) ==");
            eprintln!(
                "   API: `args_for_type_params` binds N type params POSITIONALLY (the i-th type \
                 param -> concretes[i]; arity-checked; const/other non-type generics bail loud) + \
                 `lower_multi_generic_instance` lowers a fn with N type params at a concrete tuple \
                 through the SAME unified `MonoCx::lower_expr`. Each fn is lowered at MULTIPLE \
                 distinct type tuples; per-instantiation IR DIFFERS by type/width. Differential vs \
                 Rust-SEMANTICS expected-value oracles (computed in the driver with Rust operators, \
                 NOT a linked corpus execution — see the M5.7c note / FIX 6): fst(a,_)==a; \
                 combine(a,b,_)==a+b (wrapping at the A width)."
            );

            let u32_ty = tcx.types.u32;
            let i64_ty = tcx.types.i64;

            // Env-gated fail-loud PROBE (off by default; the normal --m3 output is
            // unchanged). With `M5H_PROBE_BAILS=1`, drive the bail paths of
            // `args_for_type_params` / `lower_multi_generic_instance` and print
            // whether each bailed loudly: (1) a const-generic fn, (2) an arity
            // mismatch (too few concretes), (3) an arity mismatch (too many). This
            // is the runnable evidence that the guardrail bails are real.
            if std::env::var("M5H_PROBE_BAILS").is_ok() {
                eprintln!("   PROBE: fail-loud guard checks (M5H_PROBE_BAILS=1)");
                // (1) const-generic -> must bail.
                if let Some(cg) = find("with_const") {
                    match trust_ir_frontend::m3::lower_multi_generic_instance(
                        tcx,
                        &mut trust_ir_build::ModuleBuilder::new("probe::cg".to_string()),
                        cg,
                        &[],
                        "probe",
                    ) {
                        Ok(_) => eprintln!("     PROBE-CONST: UNEXPECTED OK (guard regressed!)"),
                        Err(e) => eprintln!("     PROBE-CONST: bailed: {e}"),
                    }
                } else {
                    eprintln!("     PROBE-CONST: no `with_const` def found");
                }
                // (2) arity mismatch: fst has 2 type params, supply 1 concrete.
                match trust_ir_frontend::m3::lower_multi_generic_instance(
                    tcx,
                    &mut trust_ir_build::ModuleBuilder::new("probe::few".to_string()),
                    fst_def,
                    &[i64_ty],
                    "probe",
                ) {
                    Ok(_) => eprintln!("     PROBE-ARITY-FEW: UNEXPECTED OK (guard regressed!)"),
                    Err(e) => eprintln!("     PROBE-ARITY-FEW: bailed: {e}"),
                }
                // (3) arity mismatch: supply 3 concretes for a 2-type-param fn.
                match trust_ir_frontend::m3::lower_multi_generic_instance(
                    tcx,
                    &mut trust_ir_build::ModuleBuilder::new("probe::many".to_string()),
                    fst_def,
                    &[i64_ty, u32_ty, i64_ty],
                    "probe",
                ) {
                    Ok(_) => eprintln!("     PROBE-ARITY-MANY: UNEXPECTED OK (guard regressed!)"),
                    Err(e) => eprintln!("     PROBE-ARITY-MANY: bailed: {e}"),
                }
            }

            let mut cases: Vec<M5hCase> = Vec::new();

            // fst<i64,u32>(a,_b) -> i64: returns the FIRST arg (i64). _b ignored.
            for (a, b) in [(7i64, 3u32), (-5, 9), (i64::MAX, 1), (i64::MIN, 0)] {
                cases.push(M5hCase {
                    label: format!("fst::<i64,u32>({a},{b})"),
                    def: fst_def,
                    concretes: vec![i64_ty, u32_ty],
                    name_suffix: "i64_u32".into(),
                    args: vec![a as i128, b as i128],
                    oracle: M5gOracle::Int(a as i128),
                });
            }
            // fst<u32,i64>(a,_b) -> u32: SWAPPED tuple — returns a u32 (32-bit).
            // The runner reads the result as the U32 ir-ty (32-bit), so a value
            // > u32::MAX would be truncated; the oracle masks to 32 bits to match.
            for (a, b) in [(7u32, 3i64), (0x8000_0000u32, -9i64), (u32::MAX, 1234i64)] {
                cases.push(M5hCase {
                    label: format!("fst::<u32,i64>({a},{b})"),
                    def: fst_def,
                    concretes: vec![u32_ty, i64_ty],
                    name_suffix: "u32_i64".into(),
                    args: vec![a as i128, b as i128],
                    // result is u32 a, read as a signed i128 of a 32-bit value.
                    oracle: M5gOracle::Int(a as i32 as i128),
                });
            }
            // combine<i64,u32>(a,b,_w) -> i64: a + b at i64 width (wrapping).
            if let Some(combine_def) = find("combine") {
                for (a, b, w) in [(3i64, 4i64, 1u32), (-7, 2, 9), (i64::MAX, 1, 0)] {
                    cases.push(M5hCase {
                        label: format!("combine::<i64,u32>({a},{b},{w})"),
                        def: combine_def,
                        concretes: vec![i64_ty, u32_ty],
                        name_suffix: "i64_u32".into(),
                        args: vec![a as i128, b as i128, w as i128],
                        oracle: M5gOracle::Int(a.wrapping_add(b) as i128),
                    });
                }
                // combine<u32,i64>(a,b,_w) -> u32: a + b at U32 width. The
                // width-DISCRIMINATING witness: 0x8000_0000 + 0x8000_0000 wraps to
                // 0 at 32 bits (it would be 0x1_0000_0000 at i64 width), proving
                // the per-instantiation width is honored — NOT silently i64.
                for (a, b, w) in [
                    (3u32, 4u32, 1i64),
                    (0x8000_0000u32, 0x8000_0000u32, -9i64), // wraps to 0 at U32
                    (u32::MAX, 1u32, 0i64),                  // wraps to 0 at U32
                ] {
                    let sum_u32 = a.wrapping_add(b);
                    cases.push(M5hCase {
                        label: format!("combine::<u32,i64>({a},{b},{w}) [U32 width]"),
                        def: combine_def,
                        concretes: vec![u32_ty, i64_ty],
                        name_suffix: "u32_i64".into(),
                        args: vec![a as i128, b as i128, w as i128],
                        oracle: M5gOracle::Int(sum_u32 as i32 as i128),
                    });
                }
            }

            match trust_ir_frontend::m3::run_m5h_differential(tcx, &cases) {
                Ok((module, report, roots)) => {
                    eprintln!(
                        "   per-case modules emitted (last: {} function(s)); \
                         validate_module across cases: {} error(s)",
                        module.functions.len(),
                        report.validate_errors
                    );
                    // Per-instantiation TYPE witness: prove fst<i64,_> returns a
                    // 64-bit ir-ty and fst<u32,_> a 32-bit one (distinct widths).
                    let mut seen: std::collections::HashSet<String> = Default::default();
                    for r in &roots {
                        if seen.insert(r.name.clone()) {
                            let ptys: Vec<String> =
                                r.param_tys.iter().map(|t| format!("{t}")).collect();
                            eprintln!(
                                "     INSTANCE {} : ({}) -> {} [ret bit-width {:?}]",
                                r.name,
                                ptys.join(","),
                                r.ret_ty,
                                r.ret_ty.bit_width()
                            );
                        }
                    }
                    eprintln!(
                        "   DIFFERENTIAL (interp on multi-generic instances vs Rust-semantics expected-value oracle): {}/{} MATCH",
                        report.n_match(),
                        report.n_total()
                    );
                    for (label, got, oracle, m) in &report.checks {
                        eprintln!(
                            "     [{}] {label}: ir={got} oracle={oracle}",
                            if *m { "MATCH" } else { "MISMATCH" }
                        );
                    }
                    if report.all_match() && report.validate_errors == 0 {
                        eprintln!("   M5.7d RESULT: ALL MATCH, 0 validate errors");
                    } else {
                        eprintln!("   M5.7d RESULT: FAILURES PRESENT (see above)");
                    }
                }
                Err(e) => eprintln!("   M5.7d LOWERING FAILED: {e}"),
            }

            // Optionally emit the multi-generic round-trip module as trust-ir TEXT.
            if let Some(path) = emit_multigen {
                match find("combine") {
                    Some(combine_def) => {
                        match trust_ir_frontend::m3::emit_multigen_roundtrip_module(
                            tcx, fst_def, combine_def,
                        ) {
                            Ok(module) => {
                                let verrs = trust_ir_build::validate_module(&module);
                                let text = format!("{module}");
                                match std::fs::write(path, &text) {
                                    Ok(()) => eprintln!(
                                        "   EMIT-MULTIGEN: wrote {} bytes of trust-ir text to {path} \
                                         (fns: fst__i64_i64, combine__i64_i64; \
                                         validate_module: {} error(s))",
                                        text.len(),
                                        verrs.len()
                                    ),
                                    Err(e) => {
                                        eprintln!("   EMIT-MULTIGEN FAILED to write {path}: {e}")
                                    }
                                }
                            }
                            Err(e) => eprintln!("   EMIT-MULTIGEN lowering failed: {e}"),
                        }
                    }
                    None => eprintln!("   EMIT-MULTIGEN skipped: missing `combine` def"),
                }
            }
        }
        None => eprintln!("== M5.7d: no `fst` def in corpus; skipping multi-type-param =="),
    }
}

/// Shallow recursive THIR dump for diagnosing generic body shapes (gated by
/// M3_DUMP_THIR env). Prints `kind` discriminants down to `depth` levels.
fn dump_expr(thir: &rustc_middle::thir::Thir<'_>, e: rustc_middle::thir::ExprId, indent: usize, depth: usize) {
    use rustc_middle::thir::ExprKind::*;
    let pad = "  ".repeat(indent);
    let k = &thir[e].kind;
    eprintln!("{pad}{e:?}: {} ty={:?}", trust_ir_frontend::expr_kind_name_pub(k), thir[e].ty);
    match k {
        Adt(adt) => eprintln!(
            "{pad}  ADT did={:?} variant={:?} nfields={}",
            adt.adt_def.did(), adt.variant_index, adt.fields.len()
        ),
        Call { ty, .. } => eprintln!("{pad}  CALL callee_ty={ty:?}"),
        _ => {}
    }
    if depth == 0 {
        return;
    }
    let mut kids: Vec<rustc_middle::thir::ExprId> = Vec::new();
    match k {
        Scope { value, .. } => kids.push(*value),
        NeverToAny { source } | PointerCoercion { source, .. } => kids.push(*source),
        Deref { arg } | Borrow { arg, .. } => kids.push(*arg),
        Block { block } => {
            if let Some(x) = thir[*block].expr { kids.push(x); }
        }
        Call { fun, args, .. } => {
            kids.push(*fun);
            kids.extend(args.iter().copied());
        }
        Binary { lhs, rhs, .. } | LogicalOp { lhs, rhs, .. } => {
            kids.push(*lhs);
            kids.push(*rhs);
        }
        If { cond, then, else_opt, .. } => {
            kids.push(*cond);
            kids.push(*then);
            if let Some(e) = else_opt {
                kids.push(*e);
            }
        }
        Field { lhs, .. } => kids.push(*lhs),
        Adt(adt) => {
            for f in adt.fields.iter() {
                kids.push(f.expr);
            }
        }
        _ => {}
    }
    for c in kids {
        dump_expr(thir, c, indent + 1, depth - 1);
    }
}

/// Append heap-constructing runners to the genuine THIR-emitted predicate and
/// differential-test it against the native oracle (incl. Param) over the shared
/// corpus, on the faithful Box/Arc heap layout.
/// FIX 1(a) — THE LAYOUT-PIN. Assert the recovered `EnumLayout` for the M6 niche
/// `Level` matches the EXACT rustc ground truth the final audit confirmed
/// (verified against rustc's niche/layout formula + native execution). The
/// emitted-vs-heap differential is SELF-CONSISTENT — it builds the heap with the
/// SAME `EnumLayout` it reads with, so a `layout_of` divergence (e.g. perturbing
/// a niche value 3->103, or moving a field offset) produces a still-consistent
/// pair and the differential stays 21/21. THIS assertion is the guard that
/// catches such a divergence: it compares the recovered numbers to literals.
///
/// Pinned ground truth (audit-confirmed; see `AY_DUMP_LAYOUT` + rustc source):
///   tag_offset == 0, tag width == I64 (8 bytes), encoding == Niche,
///   Zero=Some(3), Succ=Some(4), Max=Some(5), IMax=Some(6), Param=None (Switch
///   default / untagged), field offsets Zero:[], Succ:[8], Max:[8,16],
///   IMax:[8,16], Param:[0].
///
/// On ANY mismatch: print "LAYOUT-PIN MISMATCH" lines and `exit(1)` so the gate
/// (and `cargo test`) fails hard. On full match: print a "LAYOUT-PIN OK" line.
fn assert_m6_niche_level_layout(enum_model: &trust_ir_frontend::EnumModel) {
    use trust_ir::ty::Ty as IrTy;
    use trust_ir_frontend::LayoutTagEncoding;

    let lay = &enum_model.layout;
    let mut mismatches: Vec<String> = Vec::new();

    if enum_model.name != "Level" {
        eprintln!(
            "   LAYOUT-PIN MISMATCH: expected to pin enum `Level`, got `{}` — \
             refusing to certify an unexpected enum.",
            enum_model.name
        );
        std::process::exit(1);
    }

    // (1) Whole-enum tag read: offset, width, encoding.
    if lay.tag_offset != 0 {
        mismatches.push(format!("tag_offset = {} (expected 0)", lay.tag_offset));
    }
    if lay.tag_ir_ty != IrTy::I64 {
        mismatches.push(format!(
            "tag width = {:?} (expected I64 / 8 bytes)",
            lay.tag_ir_ty
        ));
    }
    // Param (variant index 4) is the niche UNTAGGED variant = Switch default.
    let untagged_ok = matches!(
        lay.tag_encoding,
        LayoutTagEncoding::Niche { untagged_variant } if untagged_variant.as_usize() == 4
    );
    if !untagged_ok {
        mismatches.push(format!(
            "tag_encoding = {:?} (expected Niche {{ untagged_variant: Param=#4 }})",
            lay.tag_encoding
        ));
    }

    // (2) Per-variant Switch values + field offsets, in VariantIdx order
    //     Zero=0, Succ=1, Max=2, IMax=3, Param=4.
    // (name, expected switch_value, expected field offsets)
    let expected: [(&str, Option<i128>, &[i128]); 5] = [
        ("Zero", Some(3), &[]),
        ("Succ", Some(4), &[8]),
        ("Max", Some(5), &[8, 16]),
        ("IMax", Some(6), &[8, 16]),
        ("Param", None, &[0]),
    ];
    if lay.variants.len() != 5 {
        mismatches.push(format!(
            "variant count = {} (expected 5)",
            lay.variants.len()
        ));
    }
    for (idx, (exp_name, exp_sv, exp_offs)) in expected.iter().enumerate() {
        let Some(v) = lay.variants.get(idx) else {
            mismatches.push(format!("variant #{idx} ({exp_name}) MISSING"));
            continue;
        };
        if v.name != *exp_name {
            mismatches.push(format!(
                "variant #{idx} name = `{}` (expected `{exp_name}`)",
                v.name
            ));
        }
        if v.switch_value != *exp_sv {
            mismatches.push(format!(
                "variant `{}` switch_value = {:?} (expected {:?})",
                v.name, v.switch_value, exp_sv
            ));
        }
        if v.field_offsets.as_slice() != *exp_offs {
            mismatches.push(format!(
                "variant `{}` field_offsets = {:?} (expected {:?})",
                v.name, v.field_offsets, exp_offs
            ));
        }
    }

    if mismatches.is_empty() {
        eprintln!(
            "   LAYOUT-PIN OK [Level niche]: tag@0 width=I64 encoding=Niche(untagged=Param#4) \
             Zero=3 Succ=4 Max=5 IMax=6 Param=default; \
             offsets Zero=[] Succ=[8] Max=[8,16] IMax=[8,16] Param=[0] \
             — recovered layout MATCHES rustc ground truth."
        );
    } else {
        eprintln!(
            "   LAYOUT-PIN MISMATCH ({} divergence(s)) for enum `Level` — the recovered \
             `tcx.layout_of` layout does NOT match the audit-confirmed rustc ground truth:",
            mismatches.len()
        );
        for m in &mismatches {
            eprintln!("      - {m}");
        }
        eprintln!(
            "   The emitted-vs-heap differential is self-consistent and would NOT catch this; \
             refusing to certify a divergent layout."
        );
        std::process::exit(1);
    }
}

fn run_differential_for(
    name: &str,
    mb: trust_ir_build::ModuleBuilder,
    func_id: trust_ir::value::FuncId,
    enum_model: &trust_ir_frontend::EnumModel,
) {
    // The oracle covers the MicroLevel/Level recursive shape; need the
    // recursive variants (>=4) plus the is_zero/is_nonzero name.
    //
    // SOUNDNESS (audit FIX 5): an unexpected / oracle-incompatible enum shape must
    // be a LOUD failure, not a quiet skip — silently skipping parity lets a wrong
    // lowering pass unchecked. Print a clear FAIL line and set the process exit
    // code so the run is unambiguously not-OK.
    if enum_model.variants.len() < 4 {
        eprintln!(
            "   PARITY NOT CHECKED — FAIL: enum `{}` has {} variants (< 4); the heap \
             oracle only models the MicroLevel/Level shape, so the differential for `{name}` \
             could NOT be checked. Refusing to silently skip.",
            enum_model.name,
            enum_model.variants.len()
        );
        std::process::exit(1);
    }
    // M6: a faithful-layout diagnostic (env-gated, off by default so the normal
    // RESULT output is unchanged). `AY_DUMP_LAYOUT=1` prints the recovered
    // `EnumLayout` — tag offset/width, Direct vs Niche, and each variant's Switch
    // value + field offsets — which is the evidence that the REAL niche `Level`
    // reads a NICHE (values {3,4,5,6}, Param=default) vs the corpus's Direct tag.
    if std::env::var("AY_DUMP_LAYOUT").is_ok() {
        let lay = &enum_model.layout;
        eprintln!(
            "   LAYOUT[{}]: tag@{} width={:?} encoding={}",
            enum_model.name,
            lay.tag_offset,
            lay.tag_ir_ty,
            if lay.is_niche() { "NICHE" } else { "Direct" }
        );
        for v in &lay.variants {
            eprintln!(
                "      variant {} switch={:?} field_offsets={:?}",
                v.name, v.switch_value, v.field_offsets
            );
        }
    }
    // M6: the heap builders must Store the SAME bytes the lowered predicate Loads
    // — tag WIDTH/offset, per-variant tag value (or none for a niche untagged
    // variant), per-variant field offsets — so pass the FAITHFUL `HeapLayout`
    // derived from the recovered `EnumModel.layout` (from `tcx.layout_of`).
    let heap_layout =
        trust_ir_frontend::model::HeapLayout::from_enum_layout(&enum_model.layout);
    match trust_ir_frontend::model::run_emitted_differential(mb, func_id, name, &heap_layout) {
        Err(fault) => {
            eprintln!(
                "   PARITY NOT CHECKED — FAIL: the module builder refused the differential \
                 module for `{name}`: {fault}"
            );
            std::process::exit(1);
        }
        Ok(Some(r)) => {
            eprintln!(
                "   DIFFERENTIAL (emitted-from-THIR, heap layout, vs native `{name}`): {}/{} match (Param cases: {}/{}); validate_module on combined module: {} error(s){}",
                r.n_match,
                r.n_total,
                r.param_match,
                r.param_total,
                r.validate_errors,
                match &r.first_mismatch {
                    Some(m) => format!(" — first mismatch: {m}"),
                    None => " — ALL MATCH".to_string(),
                }
            );
        }
        // SOUNDNESS (audit FIX B): a missing native oracle must be a LOUD failure
        // matching the <4-variant arm above — a quiet skip lets a wrong lowering
        // pass unchecked, contradicting FIX 5's fail-loud intent.
        Ok(None) => {
            eprintln!(
                "   PARITY NOT CHECKED — FAIL: no native oracle for `{name}`; the differential \
                 could NOT be checked. Refusing to silently skip."
            );
            std::process::exit(1);
        }
    }
}

fn main() {
    // SAFETY: the first native-entry operation, before arguments, files or threads.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    if let Err(error) = unsafe { rustc_data_structures::jobserver::capture_early() } {
        eprintln!("frontend entry: inherited compiler scheduler refused: {error}");
        std::process::exit(75);
    }
    let raw: Vec<String> = std::env::args().collect();
    let mut rustc_args: Vec<String> = Vec::new();
    let mut target_fns: Vec<String> = Vec::new();
    let mut m3 = false;
    let mut coverage = false;
    let mut assert_layout = false;
    let mut emit_text: Option<String> = None;
    let mut emit_callchain: Option<String> = None;
    let mut emit_if: Option<String> = None;
    let mut emit_let: Option<String> = None;
    let mut emit_match: Option<String> = None;
    let mut emit_adt: Option<String> = None;
    let mut emit_pred: Option<String> = None;
    let mut emit_ops: Option<String> = None;
    let mut emit_multigen: Option<String> = None;
    let mut emit_eval: Option<String> = None;
    let mut emit_redex: Option<String> = None;
    let mut emit_construct: Option<String> = None;
    let mut emit_sym: Option<String> = None;
    let mut i = 0;
    while i < raw.len() {
        if raw[i] == "--target-fn" {
            if let Some(n) = raw.get(i + 1) {
                target_fns.push(n.clone());
            }
            i += 2;
        } else if raw[i] == "--m3" {
            m3 = true;
            i += 1;
        } else if raw[i] == "--coverage" {
            coverage = true;
            i += 1;
        } else if raw[i] == "--assert-layout" {
            // FIX 1(a): turn on the layout-pin assertion (default-mode only).
            assert_layout = true;
            i += 1;
        } else if raw[i] == "--emit-text" {
            emit_text = raw.get(i + 1).cloned();
            i += 2;
        } else if raw[i] == "--emit-callchain" {
            emit_callchain = raw.get(i + 1).cloned();
            i += 2;
        } else if raw[i] == "--emit-if" {
            emit_if = raw.get(i + 1).cloned();
            i += 2;
        } else if raw[i] == "--emit-let" {
            emit_let = raw.get(i + 1).cloned();
            i += 2;
        } else if raw[i] == "--emit-match" {
            emit_match = raw.get(i + 1).cloned();
            i += 2;
        } else if raw[i] == "--emit-adt" {
            emit_adt = raw.get(i + 1).cloned();
            i += 2;
        } else if raw[i] == "--emit-pred" {
            emit_pred = raw.get(i + 1).cloned();
            i += 2;
        } else if raw[i] == "--emit-ops" {
            emit_ops = raw.get(i + 1).cloned();
            i += 2;
        } else if raw[i] == "--emit-multigen" {
            emit_multigen = raw.get(i + 1).cloned();
            i += 2;
        } else if raw[i] == "--emit-eval" {
            emit_eval = raw.get(i + 1).cloned();
            i += 2;
        } else if raw[i] == "--emit-redex" {
            emit_redex = raw.get(i + 1).cloned();
            i += 2;
        } else if raw[i] == "--emit-construct" {
            emit_construct = raw.get(i + 1).cloned();
            i += 2;
        } else if raw[i] == "--emit-sym" {
            emit_sym = raw.get(i + 1).cloned();
            i += 2;
        } else {
            rustc_args.push(raw[i].clone());
            i += 1;
        }
    }
    if target_fns.is_empty() {
        target_fns = vec!["is_zero".into(), "is_nonzero".into()];
    }

    if let Err(error) = trust_ir_frontend::append_matching_rustc_sysroot(&mut rustc_args) {
        eprintln!("trust_ir_frontend: {error}");
        std::process::exit(2);
    }

    let mut cb = FrontendCallbacks {
        target_fns,
        m3,
        coverage,
        assert_layout,
        emit_text,
        emit_callchain,
        emit_if,
        emit_let,
        emit_match,
        emit_adt,
        emit_pred,
        emit_ops,
        emit_multigen,
        emit_eval,
        emit_redex,
        emit_construct,
        emit_sym,
    };
    rustc_driver::run_compiler(&rustc_args, &mut cb);
}
