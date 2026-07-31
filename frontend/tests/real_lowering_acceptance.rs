//! FIX 5 — REAL-LOWERING acceptance gate.
//!
//! The `#[cfg(test)]` unit suite in `src/m3.rs` hand-builds the EXPECTED IR with
//! `FunctionBuilder` and never invokes `MonoCx::lower_expr` / the `run_*_differential`
//! harness. So a regression in the ACTUAL THIR -> trust-ir lowering could still pass
//! `cargo test --lib` while silently producing wrong IR — the real lowering was only
//! validated by the `--m3` driver, run by hand.
//!
//! This integration test drives the REAL lowering end-to-end: it spawns the built
//! `trust_ir_frontend` binary (provided to integration tests as
//! `CARGO_BIN_EXE_trust_ir_frontend`) under the stage1 rustc toolchain on the
//! committed `m3_corpus.rs`, in BOTH `--m3` mode and default mode, and asserts on
//! the driver's output:
//!
//!   * process exit status 0,
//!   * an "ALL MATCH" RESULT line for EVERY milestone family
//!     (M3 / M4 / M5 [=M5.1] / M5.2 / M5.3 / SCALAR-DEREF / M5.4 / M5.6),
//!   * "21/21" appears TWICE in default mode (is_zero + is_nonzero), and
//!   * NONE of the failure markers ("MISMATCH", "PARITY NOT CHECKED",
//!     "FAILURES", "LOWERING FAILED") appears in either run.
//!
//! Because the `--m3` driver runs each milestone's `MonoCx::lower_expr` lowering and
//! the trust-ir Interpreter differential, and the default mode runs the genuine
//! emitted-from-THIR predicate against the native heap oracle (and `exit(1)`s on a
//! parity-not-checked condition), these assertions catch a real-lowering regression
//! that the `--lib` suite would miss.
//!
//! TOOLCHAIN: the lowering reads `tcx.thir_body` via `rustc_private`, so it MUST run
//! under the ABI-matching trust stage1 rustc and bootstrap-prepared private
//! `rustc_driver` dylib directory. The test rejects a `RUSTC` whose version does
//! not match the linked driver, then falls back to the checkout's canonical
//! stage1/private-sysroot paths. If that pair cannot be located, the test SKIPS
//! loudly rather than running against a mismatched sysroot.

#![feature(rustc_private)]

use std::path::Path;

mod support;
use support::{artifact_only_driver_command, find_stage1_root};

/// Run the built frontend binary on `corpus_file` with the given extra args under
/// the stage1 toolchain. Returns (exit_success, combined stdout+stderr).
fn run_frontend_on(stage1: &Path, corpus_file: &str, extra_args: &[&str]) -> (bool, String) {
    let bin = env!("CARGO_BIN_EXE_trust_ir_frontend");
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join(corpus_file);
    let mut cmd = artifact_only_driver_command(bin, stage1);
    cmd.arg(&corpus);
    cmd.args(extra_args);

    let out = cmd.output().expect("failed to spawn trust_ir_frontend");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    (out.status.success(), combined)
}

/// `run_frontend_on` against the default `m3_corpus.rs` (back-compat shim).
fn run_frontend(stage1: &Path, extra_args: &[&str]) -> (bool, String) {
    run_frontend_on(stage1, "m3_corpus.rs", extra_args)
}

/// Assert NONE of the failure markers appears in `out`.
fn assert_no_failure_markers(out: &str, mode: &str) {
    for marker in ["MISMATCH", "PARITY NOT CHECKED", "FAILURES", "LOWERING FAILED"] {
        assert!(
            !out.contains(marker),
            "[{mode}] real-lowering regression: output contains forbidden marker {marker:?}.\n\
             ---- full output ----\n{out}"
        );
    }
}

/// Parse the first unsigned integer following `key` on `line`
/// (e.g. `span_field("... spanned=28 ...", "spanned=") == 28`).
fn span_field(line: &str, key: &str) -> u32 {
    let at = line
        .find(key)
        .unwrap_or_else(|| panic!("no `{key}` field in SPAN-PROVENANCE line {line:?}"));
    let digits: String = line[at + key.len()..]
        .chars()
        .take_while(|c| c.is_ascii_digit())
        .collect();
    digits
        .parse()
        .unwrap_or_else(|_| panic!("malformed `{key}` field in SPAN-PROVENANCE line {line:?}"))
}

/// SPAN-THREADING provenance gate: find `fn_name`'s `SPAN-PROVENANCE` line in
/// the driver output and assert the lowered fn's instructions carry REAL source
/// spans:
///   * FULL coverage — `spanned == total > 0` (every emitted `InstrNode` has a
///     span; a partially-spanned body means an emission path lost the thread);
///   * the file-table entry points at `corpus_file` (the file the driver
///     compiled), i.e. the module's debug-info file table is populated;
///   * the covered `lines=a..b` range starts AT the fn's real declaration line
///     in the corpus source (the fn-level span) and stays within a plausible
///     window below it — a wrong line mapping (0-based drift, wrong file)
///     fails here.
fn assert_span_provenance(out: &str, mode: &str, fn_name: &str, corpus_file: &str, decl_needle: &str) {
    let matches: Vec<_> = out
        .lines()
        .filter(|line| {
            if !line.contains("SPAN-PROVENANCE") {
                return false;
            }
            let Some(symbol) = line
                .split_once("fn=")
                .and_then(|(_, rest)| rest.split_whitespace().next())
            else {
                return false;
            };
            // The driver reports the emitted TrustIR symbol. Depending on the
            // rustc source revision that is either the source item name or its
            // full v0-mangled symbol; require an exact item-name suffix in the
            // latter case rather than accepting an arbitrary substring.
            symbol == fn_name || symbol.ends_with(fn_name)
        })
        .collect();
    let line = match matches.as_slice() {
        [line] => *line,
        _ => {
            panic!(
                "[{mode}] expected exactly one SPAN-PROVENANCE line for `{fn_name}`, got {} — \
                 the driver no longer reports unambiguous span threading (or the lowering \
                 emitted a span-less module).\n\
                 ---- full output ----\n{out}",
                matches.len()
            )
        }
    };

    let spanned = span_field(line, "spanned=");
    let total = span_field(line, "total=");
    assert!(
        total > 0,
        "[{mode}] SPAN-PROVENANCE for `{fn_name}` reports an empty function.\n{line}"
    );
    assert_eq!(
        spanned, total,
        "[{mode}] `{fn_name}` is only PARTIALLY spanned ({spanned}/{total}) — an emission \
         path dropped the span thread.\n{line}"
    );

    // The file-table entry must be the corpus file the driver compiled.
    let corpus_name = Path::new(corpus_file)
        .file_name()
        .and_then(|s| s.to_str())
        .expect("corpus_file has a filename");
    assert!(
        line.contains(corpus_name),
        "[{mode}] `{fn_name}`'s spans do not point at {corpus_name:?} — wrong/empty \
         debug-info file table.\n{line}"
    );

    // Plausible line range: `lines=a..b` with `a` AT the fn's declaration line
    // (the fn-level default span) and `b` within a small window below it (every
    // corpus fn here is < 40 lines).
    let min_line = span_field(line, "lines=");
    let max_line = {
        let at = line.find("..").unwrap_or_else(|| {
            panic!("[{mode}] no `lines=a..b` range in SPAN-PROVENANCE line {line:?}")
        });
        let digits: String = line[at + 2..].chars().take_while(|c| c.is_ascii_digit()).collect();
        digits.parse::<u32>().unwrap_or_else(|_| {
            panic!("[{mode}] malformed `lines=a..b` range in SPAN-PROVENANCE line {line:?}")
        })
    };
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join(corpus_file);
    let src = std::fs::read_to_string(&corpus)
        .unwrap_or_else(|e| panic!("[{mode}] cannot read corpus {}: {e}", corpus.display()));
    let decl_line = src
        .lines()
        .position(|l| l.contains(decl_needle))
        .unwrap_or_else(|| {
            panic!("[{mode}] corpus {corpus_file} has no line containing {decl_needle:?}")
        }) as u32
        + 1; // 1-based
    assert!(
        min_line == decl_line,
        "[{mode}] `{fn_name}`'s span range starts at line {min_line}, but its declaration \
         ({decl_needle:?}) is at {corpus_file}:{decl_line} — the line mapping drifted.\n{line}"
    );
    assert!(
        max_line >= min_line && max_line < decl_line + 40,
        "[{mode}] `{fn_name}`'s span range {min_line}..{max_line} is implausible for a fn \
         declared at {corpus_file}:{decl_line}.\n{line}"
    );
}

#[test]
fn real_lowering_m3_and_default_accept() {
    let Some(stage1) = find_stage1_root() else {
        eprintln!(
            "SKIP real_lowering_acceptance: no stage1 rustc toolchain found \
             (set RUSTC=<stage1>/bin/rustc, or place it at \
             $HOME/trust/build/aarch64-apple-darwin/stage1). \
             This test is the REAL-lowering gate; it is being skipped only because \
             the rustc_private toolchain is unavailable."
        );
        return;
    };

    // --- 1) `--m3` mode: every milestone family must report ALL MATCH. ---------
    let (ok_m3, out_m3) = run_frontend(&stage1, &["--m3"]);
    assert!(
        ok_m3,
        "[--m3] driver exited non-zero.\n---- full output ----\n{out_m3}"
    );
    assert_no_failure_markers(&out_m3, "--m3");

    // One "ALL MATCH" RESULT line per milestone family. The driver prints the
    // M5.1 family under the label "M5 RESULT".
    for needle in [
        "M3 RESULT: ALL MATCH",
        "M4 RESULT: ALL MATCH",
        "M5 RESULT: ALL MATCH",
        "M5.2 RESULT: ALL MATCH",
        "M5.3 RESULT: ALL MATCH",
        "SCALAR-DEREF RESULT: ALL MATCH",
        "M5.4 RESULT: ALL MATCH",
        "M5.7b RESULT: ALL MATCH",
        "M5.7a RESULT: ALL MATCH",
        "M5.7e RESULT: ALL MATCH",
        // FIX 5: the NARROW-WIDTH aggregate sub-field differential (`Pair`,
        // `Cell((i32,i32))`) — exercises distinct (I32) Load/Store widths + offsets.
        "FIX5 RESULT: ALL MATCH",
        // FIX 2: the enum-variant CONSTRUCTION family — now incl. the NICHE
        // untagged-variant construction (`NBox::Cons(Box::new(..))`).
        "M5.7f RESULT: ALL MATCH",
        "M5.6 RESULT: ALL MATCH",
    ] {
        assert!(
            out_m3.contains(needle),
            "[--m3] missing expected RESULT line {needle:?}.\n\
             ---- full output ----\n{out_m3}"
        );
    }

    // FIX 2: the niche untagged-variant CONSTRUCTION cases must MATCH. `NBox` is
    // niche-encoded with `Cons(Box<NBox>)` as the UNTAGGED variant (the Switch
    // default); constructing it exercises the `is_niche_untagged` no-tag-store
    // branch, and folding it back through `nbox_depth` confirms it reads back as
    // `Cons`. (A wrong untagged construction — a clobbering synthetic tag — would
    // mis-route the fold and show up as a MISMATCH, already caught by the
    // forbidden-marker check, but assert on the case labels too.)
    for needle in [
        "nbox_nil_depth() builds niche-encoded Nil -> 0",
        "nbox_one_depth() builds untagged Cons(Nil) -> 1",
        "nbox_two_depth() builds untagged Cons(Cons(Nil)) -> 2",
    ] {
        assert!(
            out_m3.contains(&format!("[MATCH] {needle}")),
            "[--m3] missing expected niche untagged-construction MATCH for {needle:?}.\n\
             ---- full output ----\n{out_m3}"
        );
    }

    // --- 2) default mode: the genuine emitted-from-THIR predicate, 21/21 twice. -
    let (ok_def, out_def) = run_frontend(&stage1, &[]);
    assert!(
        ok_def,
        "[default] driver exited non-zero (a PARITY NOT CHECKED fail exits 1).\n\
         ---- full output ----\n{out_def}"
    );
    assert_no_failure_markers(&out_def, "default");
    let n_2121 = out_def.matches("21/21").count();
    assert_eq!(
        n_2121, 2,
        "[default] expected '21/21' to appear exactly twice (is_zero + is_nonzero), \
         saw {n_2121}.\n---- full output ----\n{out_def}"
    );

    // --- 3) span-threading provenance (THIR path): the lowered predicates must
    // carry REAL source spans — full instruction coverage, a file-table entry
    // pointing at m3_corpus.rs, and a line range anchored at each fn's real
    // declaration line. (`emit_worklist` names the instance `{fn}__i64`.)
    assert_span_provenance(&out_def, "default", "is_zero__i64", "m3_corpus.rs", "fn is_zero(");
    assert_span_provenance(
        &out_def,
        "default",
        "is_nonzero__i64",
        "m3_corpus.rs",
        "fn is_nonzero(",
    );
}

/// M6 CAPSTONE gate: the REAL, NICHE-ENCODED clean-kernel `Level` (`Param(Name)`,
/// niche discriminant) — verbatim `is_zero`/`is_nonzero` — must LOWER through the
/// `layout_of`-driven frontend and DIFFERENTIAL-MATCH 21/21 over real heap graphs,
/// AND its recovered `EnumLayout` must MATCH the rustc ground truth (the FIX-1
/// layout-pin).
///
/// HONEST SCOPE: the 21/21 differential is NECESSARY but NOT SUFFICIENT for
/// faithfulness. The differential is SELF-CONSISTENT — the heap builder
/// (`build_heap_value`) and the lowered predicate BOTH consume the SAME
/// `layout_of`-recovered `EnumLayout`, so a `layout_of` divergence (e.g.
/// perturbing a niche value 3->103, or moving a field offset) yields a
/// still-consistent pair and the differential stays 21/21 (proven by
/// perturbation). FAITHFULNESS-TO-RUSTC is what the `--assert-layout` LAYOUT-PIN
/// provides: it compares the recovered numbers to the audit-confirmed rustc
/// literals and `exit(1)`s on any divergence. This test runs BOTH:
///   * `--assert-layout`: the recovered layout MUST print "LAYOUT-PIN OK" and
///     MUST NOT print "LAYOUT-PIN MISMATCH" (the pin against rustc ground truth);
///   * the predicate differential: 21/21 twice over the real niche heap graphs.
#[test]
fn real_lowering_m6_niche_level_accepts() {
    let Some(stage1) = find_stage1_root() else {
        eprintln!(
            "SKIP real_lowering_m6_niche_level: no stage1 rustc toolchain found. \
             This is the M6 niche-Level capstone gate; skipped only because the \
             rustc_private toolchain is unavailable."
        );
        return;
    };

    let (ok, out) = run_frontend_on(
        &stage1,
        "m6_corpus.rs",
        &[
            "--assert-layout",
            "--target-fn",
            "is_zero",
            "--target-fn",
            "is_nonzero",
        ],
    );
    assert!(
        ok,
        "[m6] driver exited non-zero on the niche `Level` (a LAYOUT-PIN MISMATCH \
         exits 1).\n---- full output ----\n{out}"
    );
    assert_no_failure_markers(&out, "m6");
    // FIX 1(a): the LAYOUT-PIN must pass — recovered layout MATCHES rustc ground
    // truth. A MISMATCH would have `exit(1)`'d above, but assert on the markers
    // too so a silent regression (pin not running) is also caught.
    assert!(
        !out.contains("LAYOUT-PIN MISMATCH"),
        "[m6] LAYOUT-PIN MISMATCH: the recovered `tcx.layout_of` layout for the \
         niche `Level` diverged from the audit-confirmed rustc ground truth.\n\
         ---- full output ----\n{out}"
    );
    let n_pin_ok = out.matches("LAYOUT-PIN OK").count();
    assert_eq!(
        n_pin_ok, 2,
        "[m6] expected the LAYOUT-PIN assertion ('LAYOUT-PIN OK') to run+pass \
         once per target fn (is_zero + is_nonzero), saw {n_pin_ok}. The pin is the \
         FIX-1 guard that catches a `layout_of` divergence the self-consistent \
         differential cannot.\n---- full output ----\n{out}"
    );
    // Both predicates must report ALL MATCH (the niche heap differential).
    let n_all_match = out.matches("ALL MATCH").count();
    assert!(
        n_all_match >= 2,
        "[m6] expected an 'ALL MATCH' differential for BOTH is_zero and is_nonzero \
         over the niche `Level`, saw {n_all_match}.\n---- full output ----\n{out}"
    );
    // And specifically 21/21 twice (the same heap corpus the Direct `Level` uses).
    let n_2121 = out.matches("21/21").count();
    assert_eq!(
        n_2121, 2,
        "[m6] expected '21/21' twice (is_zero + is_nonzero over niche `Level`), \
         saw {n_2121}.\n---- full output ----\n{out}"
    );

    // Span-threading provenance over the NICHE corpus too: the same lowering
    // must thread real spans regardless of the enum's discriminant encoding.
    assert_span_provenance(&out, "m6", "is_zero__i64", "m6_corpus.rs", "fn is_zero(");
    assert_span_provenance(&out, "m6", "is_nonzero__i64", "m6_corpus.rs", "fn is_nonzero(");
}

/// MIR-path SPAN-THREADING provenance gate: `trust_ir_mir --mir-emit` over the
/// committed `tests/fixtures/span_corpus.rs` must (a) still EMIT-OK + validate
/// 0 errors + re-parse, (b) report FULL span coverage for the lowered body fn
/// with the file table pointing at the fixture and a line range anchored at the
/// fn's declaration, and (c) write module text whose debug-info file table
/// (`file 0 "..."`) names the fixture — i.e. provenance SURVIVES the text
/// round-trip the downstream JIT consumes.
#[test]
fn mir_emit_threads_spans() {
    let Some(stage1) = find_stage1_root() else {
        eprintln!(
            "SKIP mir_emit_threads_spans: no stage1 rustc toolchain found \
             (set RUSTC=<stage1>/bin/rustc, or place it at \
             $HOME/trust/build/aarch64-apple-darwin/stage1). \
             This is the MIR-path span-threading provenance gate; it is being \
             skipped only because the rustc_private toolchain is unavailable."
        );
        return;
    };

    let bin = env!("CARGO_BIN_EXE_trust_ir_mir");
    let corpus_rel = "tests/fixtures/span_corpus.rs";
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join(corpus_rel);
    let outpath = Path::new(env!("CARGO_TARGET_TMPDIR")).join("span_probe_sz.tir");
    let mut cmd = artifact_only_driver_command(bin, &stage1);
    cmd.arg("--mir-emit");
    cmd.arg("span_probe_sz");
    cmd.arg(&outpath);
    cmd.arg(&corpus);

    let out = cmd.output().expect("failed to spawn trust_ir_mir");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));

    assert!(
        out.status.success(),
        "[mir] trust_ir_mir exited non-zero.\n---- full output ----\n{combined}"
    );
    assert!(
        combined.contains("EMIT-OK"),
        "[mir] no EMIT-OK — the span_probe_sz fixture no longer lowers.\n\
         ---- full output ----\n{combined}"
    );
    assert!(
        combined.contains("validate_module = 0 error(s)"),
        "[mir] the emitted module no longer validates cleanly (a span with a \
         dangling file index is a validate error).\n---- full output ----\n{combined}"
    );
    assert!(
        combined.contains("re-parse: OK"),
        "[mir] the emitted text (now carrying a `file` table) no longer \
         re-parses.\n---- full output ----\n{combined}"
    );

    // (b) full span coverage, right file, plausible lines.
    assert_span_provenance(
        &combined,
        "mir",
        "span_probe_sz",
        corpus_rel,
        "fn span_probe_sz(",
    );

    // (c) the WRITTEN module text carries the debug-info file table.
    let text = std::fs::read_to_string(&outpath)
        .unwrap_or_else(|e| panic!("[mir] cannot read emitted module {}: {e}", outpath.display()));
    assert!(
        text.contains("file 0 ") && text.contains("span_corpus.rs"),
        "[mir] the emitted module text has no `file 0 \"...span_corpus.rs\"` \
         debug-info table entry — provenance does not survive serialization.\n\
         ---- emitted text head ----\n{}",
        &text[..text.len().min(600)]
    );
}

// ===== PANIC-ABORT: size-scaled raw-memory intrinsics (MIR path) =============

/// Find the unique function whose emitted name ends in `suffix`.
fn fn_ending_in<'m>(module: &'m trust_ir::Module, suffix: &str) -> &'m trust_ir::Function {
    let matches: Vec<_> =
        module.functions.iter().filter(|function| function.name.ends_with(suffix)).collect();
    assert_eq!(
        matches.len(),
        1,
        "[mem-intrinsic] expected exactly one function ending in {suffix:?}; got {:?}",
        matches.iter().map(|function| function.name.as_str()).collect::<Vec<_>>()
    );
    matches[0]
}

/// Whether `value` is defined by an integer constant of the requested type and
/// value in `function`.
fn value_is_int_const(
    function: &trust_ir::Function,
    value: trust_ir::ValueId,
    ty: &trust_ir::Ty,
    expected: i128,
) -> bool {
    function.instructions().any(|node| {
        node.results.contains(&value)
            && matches!(
                &node.inst,
                trust_ir::Inst::Const {
                    ty: actual_ty,
                    value: trust_ir::Constant::Int(actual),
                } if actual_ty == ty && *actual == expected
            )
    })
}

/// Whether `value` is the product of two exact integer constants (in either
/// commutative operand order).
fn value_is_const_product(
    function: &trust_ir::Function,
    value: trust_ir::ValueId,
    ty: &trust_ir::Ty,
    first: i128,
    second: i128,
) -> bool {
    function.instructions().any(|node| {
        if !node.results.contains(&value) {
            return false;
        }
        let trust_ir::Inst::BinOp { op: trust_ir::BinOp::Mul, ty: actual_ty, lhs, rhs } =
            &node.inst
        else {
            return false;
        };
        actual_ty == ty
            && ((value_is_int_const(function, *lhs, ty, first)
                && value_is_int_const(function, *rhs, ty, second))
                || (value_is_int_const(function, *lhs, ty, second)
                    && value_is_int_const(function, *rhs, ty, first)))
    })
}

/// Whether `value` is exactly `source * stride` (in either commutative operand
/// order), rather than merely an unrelated multiplication that happens to use
/// the same stride constant.
fn value_is_stride_scaled_from(
    function: &trust_ir::Function,
    value: trust_ir::ValueId,
    source: trust_ir::ValueId,
    ty: &trust_ir::Ty,
    stride: i128,
) -> bool {
    function.instructions().any(|node| {
        if !node.results.contains(&value) {
            return false;
        }
        let trust_ir::Inst::BinOp { op: trust_ir::BinOp::Mul, ty: actual_ty, lhs, rhs } =
            &node.inst
        else {
            return false;
        };
        actual_ty == ty
            && ((*lhs == source && value_is_int_const(function, *rhs, ty, stride))
                || (*rhs == source && value_is_int_const(function, *lhs, ty, stride)))
    })
}

/// Prove that a dynamic signed pointer offset uses the complete sanctioned
/// integer-pointer lane — `ptrtoint(ptr) + count * stride`, then `inttoptr` —
/// and cannot escape as either an allocation-relative GEP or an opaque call.
fn assert_integer_pointer_offset(function: &trust_ir::Function, stride: i128, text: &str) {
    let params = &function.entry_block().expect("offset helper entry block").params;
    assert_eq!(params.len(), 2, "dynamic offset ABI changed.\n---- IR ----\n{text}");
    let (ptr, count) = (params[0].0, params[1].0);

    let ptr_ints: Vec<_> = function
        .instructions()
        .filter_map(|node| match &node.inst {
            trust_ir::Inst::Cast {
                op: trust_ir::CastOp::PtrToInt,
                src_ty: trust_ir::Ty::Ptr,
                dst_ty: trust_ir::Ty::I64,
                operand,
            } if *operand == ptr => node.results.first().copied(),
            _ => None,
        })
        .collect();
    assert_eq!(
        ptr_ints.len(),
        1,
        "dynamic offset must cast its pointer to one i64 address.\n---- IR ----\n{text}"
    );

    let scaled: Vec<_> = function
        .instructions()
        .flat_map(|node| node.results.iter().copied())
        .filter(|value| {
            value_is_stride_scaled_from(function, *value, count, &trust_ir::Ty::I64, stride)
        })
        .collect();
    assert_eq!(
        scaled.len(),
        1,
        "dynamic offset must scale its signed count by exactly {stride}.\n---- IR ----\n{text}"
    );

    let advanced: Vec<_> = function
        .instructions()
        .filter_map(|node| match &node.inst {
            trust_ir::Inst::BinOp {
                op: trust_ir::BinOp::Add,
                ty: trust_ir::Ty::I64,
                lhs,
                rhs,
            } if (*lhs == ptr_ints[0] && *rhs == scaled[0])
                || (*rhs == ptr_ints[0] && *lhs == scaled[0]) =>
            {
                node.results.first().copied()
            }
            _ => None,
        })
        .collect();
    assert_eq!(
        advanced.len(),
        1,
        "dynamic offset must add the scaled byte offset to the pointer address.\n\
         ---- IR ----\n{text}"
    );
    assert!(
        function.instructions().any(|node| {
            matches!(
                &node.inst,
                trust_ir::Inst::Cast {
                    op: trust_ir::CastOp::IntToPtr,
                    src_ty: trust_ir::Ty::I64,
                    dst_ty: trust_ir::Ty::Ptr,
                    operand,
                } if *operand == advanced[0]
            )
        }),
        "dynamic offset must cast the advanced address back to a pointer.\n---- IR ----\n{text}"
    );
    assert!(
        !function.instructions().any(|node| {
            matches!(&node.inst, trust_ir::Inst::Call { .. } | trust_ir::Inst::GEP { .. })
        }),
        "dynamic offset escaped through an opaque call or narrower GEP.\n---- IR ----\n{text}"
    );
}

/// Whether `value` is the required `u8 -> i32` zero-extension of a particular
/// byte constant (the libc `memset` fill operand).
fn value_is_zext_byte_const(
    function: &trust_ir::Function,
    value: trust_ir::ValueId,
    expected: i128,
) -> bool {
    function.instructions().any(|node| {
        if !node.results.contains(&value) {
            return false;
        }
        let trust_ir::Inst::Cast {
            op: trust_ir::CastOp::ZExt,
            src_ty: trust_ir::Ty::U8,
            dst_ty: trust_ir::Ty::I32,
            operand,
        } = &node.inst
        else {
            return false;
        };
        value_is_int_const(function, *operand, &trust_ir::Ty::U8, expected)
    })
}

/// Emit one ZST pointer-offset helper and prove the frontend preserved it as a
/// true pointer-identity operation: no opaque call, byte multiply, or GEP.
fn assert_zst_offset_is_noop(stage1: &Path, bin: &str, corpus: &Path, symbol: &str) {
    let outpath =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("{symbol}_must_be_noop.tir"));
    let _ = std::fs::remove_file(&outpath);
    let mut command = artifact_only_driver_command(bin, stage1);
    command.arg("--mir-emit");
    command.arg(symbol);
    command.arg(&outpath);
    command.arg("-Cpanic=abort");
    command.arg(corpus);
    let out = command.output().expect("failed to spawn trust_ir_mir");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    assert!(
        out.status.success()
            && combined.contains("EMIT-OK")
            && combined.contains("validate_module = 0 error(s)")
            && combined.contains("re-parse: OK"),
        "[zst-offset] {symbol} did not lower and validate.\n---- output ----\n{combined}"
    );
    let text = std::fs::read_to_string(&outpath).unwrap_or_else(|error| {
        panic!("[zst-offset] cannot read emitted module {}: {error}", outpath.display())
    });
    let module = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|error| panic!("[zst-offset] emitted module does not parse: {error:?}"));
    let function = fn_ending_in(&module, symbol);
    assert!(
        !function.instructions().any(|node| {
            matches!(
                &node.inst,
                trust_ir::Inst::Call { .. }
                    | trust_ir::Inst::GEP { .. }
                    | trust_ir::Inst::BinOp { op: trust_ir::BinOp::Mul, .. }
            )
        }),
        "[zst-offset] {symbol} is not a true pointer-identity no-op.\n---- IR ----\n{text}"
    );
}

/// Regression for the panic-abort miscompile fixed in `mir_lower`: an intrinsic
/// element count for `u64` must become a BYTE count (`count * 8`) before the
/// memmove/memset call. The old abort lane emitted a stride-erased intrinsic
/// extern, which trust-cg interpreted as a byte count and silently copied only
/// one eighth of the requested memory.
#[test]
fn mir_panic_abort_scales_wide_copy_and_write_bytes() {
    let Some(stage1) = find_stage1_root() else {
        eprintln!(
            "SKIP mir_panic_abort_scales_wide_copy_and_write_bytes: no ABI-matching \
             stage1 rustc toolchain found. This is the panic-abort wide-memory \
             miscompile gate; it is skipped only because rustc_private is unavailable."
        );
        return;
    };

    let bin = env!("CARGO_BIN_EXE_trust_ir_mir");
    let corpus =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/mem_intrinsic_wide_corpus.rs");
    let outpath = Path::new(env!("CARGO_TARGET_TMPDIR")).join("mem_intrinsic_wide_abort.tir");
    let mut cmd = artifact_only_driver_command(bin, &stage1);
    cmd.arg("--mir-emit-closure");
    cmd.arg("mem_intrinsic_wide");
    cmd.arg(&outpath);
    cmd.arg("-Cpanic=abort");
    cmd.arg(&corpus);

    let out = cmd.output().expect("failed to spawn trust_ir_mir");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    assert!(
        out.status.success() && combined.contains("EMIT-CLOSURE-OK"),
        "[mem-intrinsic] panic-abort fixture did not lower.\n---- output ----\n{combined}"
    );
    assert!(
        combined.contains("validate_module = 0 error(s)") && combined.contains("re-parse: OK"),
        "[mem-intrinsic] emitted module did not validate and round-trip.\n\
         ---- output ----\n{combined}"
    );

    let text = std::fs::read_to_string(&outpath).unwrap_or_else(|error| {
        panic!("[mem-intrinsic] cannot read emitted module {}: {error}", outpath.display())
    });
    let module = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|error| panic!("[mem-intrinsic] emitted module does not parse: {error:?}"));

    let memmove = fn_ending_in(&module, "memmove");
    let memset = fn_ending_in(&module, "memset");
    assert!(memmove.blocks.is_empty() && memset.blocks.is_empty());

    for (body_suffix, callee, label) in [
        ("wide_copy", memmove.id, "copy -> memmove"),
        ("wide_write", memset.id, "write_bytes -> memset"),
    ] {
        let function = fn_ending_in(&module, body_suffix);
        let calls: Vec<_> = function
            .instructions()
            .filter_map(|node| match &node.inst {
                trust_ir::Inst::Call { callee: actual, args } if *actual == callee => Some(args),
                _ => None,
            })
            .collect();
        assert_eq!(
            calls.len(),
            1,
            "[mem-intrinsic] {label} must emit exactly one libc call.\n---- IR ----\n{text}"
        );
        let call_args = calls[0];
        let params = &function
            .entry_block()
            .expect("emitted helper must have an entry block")
            .params;
        match body_suffix {
            "wide_copy" => {
                assert_eq!(params.len(), 3, "wide_copy ABI changed.\n---- IR ----\n{text}");
                assert_eq!(call_args.len(), 3, "memmove ABI changed.\n---- IR ----\n{text}");
                assert_eq!(
                    (call_args[0], call_args[1]),
                    (params[0].0, params[1].0),
                    "[mem-intrinsic] memmove must receive `(dst, src, ...)`, preserving the \
                     Rust helper's parameter identities.\n---- IR ----\n{text}"
                );
                assert!(
                    value_is_stride_scaled_from(
                        function,
                        call_args[2],
                        params[2].0,
                        &trust_ir::Ty::U64,
                        8,
                    ),
                    "[mem-intrinsic] copy did not pass its own `count * 8` to memmove.\n\
                     ---- IR ----\n{text}"
                );
            }
            "wide_write" => {
                assert_eq!(params.len(), 2, "wide_write ABI changed.\n---- IR ----\n{text}");
                assert_eq!(call_args.len(), 3, "memset ABI changed.\n---- IR ----\n{text}");
                assert_eq!(
                    call_args[0], params[0].0,
                    "[mem-intrinsic] memset destination is not the helper's `dst`.\n\
                     ---- IR ----\n{text}"
                );
                assert!(
                    value_is_zext_byte_const(function, call_args[1], 0xa5),
                    "[mem-intrinsic] memset fill is not the helper's exact `0xa5` byte.\n\
                     ---- IR ----\n{text}"
                );
                assert!(
                    value_is_stride_scaled_from(
                        function,
                        call_args[2],
                        params[1].0,
                        &trust_ir::Ty::U64,
                        8,
                    ),
                    "[mem-intrinsic] write_bytes did not pass its own `count * 8` to memset.\n\
                     ---- IR ----\n{text}"
                );
            }
            _ => unreachable!(),
        }
    }

    assert!(
        !module.functions.iter().any(|function| {
            function.blocks.is_empty()
                && function.name.contains("intrinsics")
                && (function.name.contains("copy") || function.name.contains("write_bytes"))
        }),
        "[mem-intrinsic] a stride-erased intrinsic extern survived the inline lowering.\n\
         ---- IR ----\n{text}"
    );
}

/// Stable `ptr::copy*`/raw-pointer copy methods and `write_bytes` wrappers can
/// remain ordinary cross-crate calls in stage1 MIR. They must enter the same
/// size-aware inline lane as direct intrinsics, including the reversed
/// destination/source order of `*mut T::copy_from*`.
#[test]
fn mir_panic_abort_scales_stable_pointer_memory_wrappers() {
    let Some(stage1) = find_stage1_root() else {
        eprintln!(
            "SKIP mir_panic_abort_scales_stable_pointer_memory_wrappers: no ABI-matching \
             stage1 rustc toolchain found."
        );
        return;
    };

    let bin = env!("CARGO_BIN_EXE_trust_ir_mir");
    let corpus =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/mem_intrinsic_wide_corpus.rs");
    let outpath =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join("stable_mem_wrappers_wide_abort.tir");
    let _ = std::fs::remove_file(&outpath);
    let mut cmd = artifact_only_driver_command(bin, &stage1);
    cmd.arg("--mir-emit-closure");
    cmd.arg("stable_mem_wrappers_wide");
    cmd.arg(&outpath);
    cmd.arg("-Cpanic=abort");
    cmd.arg(&corpus);

    let out = cmd.output().expect("failed to spawn trust_ir_mir");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    assert!(
        out.status.success()
            && combined.contains("EMIT-CLOSURE-OK")
            && combined.contains("validate_module = 0 error(s)")
            && combined.contains("re-parse: OK"),
        "[stable-mem] fixture did not lower, validate, and round-trip.\n\
         ---- output ----\n{combined}"
    );

    let text = std::fs::read_to_string(&outpath).unwrap_or_else(|error| {
        panic!("[stable-mem] cannot read emitted module {}: {error}", outpath.display())
    });
    let module = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|error| panic!("[stable-mem] emitted module does not parse: {error:?}"));
    for suffix in [
        "stable_free_copy",
        "stable_free_copy_nonoverlapping",
        "stable_copy_to",
        "stable_copy_to_nonoverlapping",
        "stable_copy_from",
        "stable_copy_from_nonoverlapping",
    ] {
        let function = fn_ending_in(&module, suffix);
        let calls: Vec<_> = function
            .instructions()
            .filter_map(|node| match &node.inst {
                trust_ir::Inst::Call { callee, args }
                    if module.functions.iter().any(|candidate| {
                        candidate.id == *callee
                            && candidate.blocks.is_empty()
                            && candidate.name.ends_with("memmove")
                    }) =>
                {
                    Some(args)
                }
                _ => None,
            })
            .collect();
        assert_eq!(calls.len(), 1, "[stable-mem] {suffix} must call memmove once.\n{text}");
        let params = &function.entry_block().expect("copy helper entry block").params;
        assert_eq!(params.len(), 3, "[stable-mem] {suffix} ABI changed.\n{text}");
        assert_eq!(
            (calls[0][0], calls[0][1]),
            (params[0].0, params[1].0),
            "[stable-mem] {suffix} did not preserve `(dst, src)` identity.\n{text}"
        );
        assert!(
            value_is_stride_scaled_from(
                function,
                calls[0][2],
                params[2].0,
                &trust_ir::Ty::U64,
                8,
            ),
            "[stable-mem] {suffix} did not pass `count * 8`.\n{text}"
        );
    }

    for suffix in ["stable_free_write", "stable_method_write"] {
        let function = fn_ending_in(&module, suffix);
        let calls: Vec<_> = function
            .instructions()
            .filter_map(|node| match &node.inst {
                trust_ir::Inst::Call { callee, args }
                    if module.functions.iter().any(|candidate| {
                        candidate.id == *callee
                            && candidate.blocks.is_empty()
                            && candidate.name.ends_with("memset")
                    }) =>
                {
                    Some(args)
                }
                _ => None,
            })
            .collect();
        assert_eq!(calls.len(), 1, "[stable-mem] {suffix} must call memset once.\n{text}");
        let params = &function.entry_block().expect("write helper entry block").params;
        assert_eq!(params.len(), 2, "[stable-mem] {suffix} ABI changed.\n{text}");
        assert_eq!(calls[0][0], params[0].0, "[stable-mem] wrong write destination.\n{text}");
        assert!(value_is_zext_byte_const(function, calls[0][1], 0xa5));
        assert!(
            value_is_stride_scaled_from(
                function,
                calls[0][2],
                params[1].0,
                &trust_ir::Ty::U64,
                8,
            ),
            "[stable-mem] {suffix} did not pass `count * 8`.\n{text}"
        );
    }

    let bodyless: Vec<_> = module
        .functions
        .iter()
        .filter(|function| function.blocks.is_empty())
        .map(|function| function.name.as_str())
        .collect();
    assert_eq!(bodyless.iter().filter(|name| name.ends_with("memmove")).count(), 6);
    assert_eq!(bodyless.iter().filter(|name| name.ends_with("memset")).count(), 2);
    assert!(
        bodyless
            .iter()
            .all(|name| name.ends_with("memmove") || name.ends_with("memset")),
        "[stable-mem] a stable wrapper escaped as an opaque extern: {bodyless:?}.\n{text}"
    );
}

/// Every stable wrapper over a ZST denotes zero bytes and must disappear
/// without a libc call, opaque wrapper declaration, byte multiply, or GEP.
#[test]
fn mir_panic_abort_stable_zst_memory_wrappers_are_true_noops() {
    let Some(stage1) = find_stage1_root() else {
        eprintln!(
            "SKIP mir_panic_abort_stable_zst_memory_wrappers_are_true_noops: no \
             ABI-matching stage1 rustc toolchain found."
        );
        return;
    };

    let bin = env!("CARGO_BIN_EXE_trust_ir_mir");
    let corpus =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/mem_intrinsic_wide_corpus.rs");
    let outpath =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join("stable_mem_wrappers_zst_abort.tir");
    let _ = std::fs::remove_file(&outpath);
    let mut cmd = artifact_only_driver_command(bin, &stage1);
    cmd.arg("--mir-emit-closure");
    cmd.arg("stable_mem_wrappers_zst");
    cmd.arg(&outpath);
    cmd.arg("-Cpanic=abort");
    cmd.arg(&corpus);

    let out = cmd.output().expect("failed to spawn trust_ir_mir");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    assert!(
        out.status.success()
            && combined.contains("EMIT-CLOSURE-OK")
            && combined.contains("validate_module = 0 error(s)")
            && combined.contains("re-parse: OK"),
        "[stable-mem-zst] fixture did not lower, validate, and round-trip.\n\
         ---- output ----\n{combined}"
    );

    let text = std::fs::read_to_string(&outpath).unwrap_or_else(|error| {
        panic!("[stable-mem-zst] cannot read emitted module {}: {error}", outpath.display())
    });
    let module = trust_ir::parser::parse_module(&text).unwrap_or_else(|error| {
        panic!("[stable-mem-zst] emitted module does not parse: {error:?}")
    });
    let function = fn_ending_in(&module, "stable_mem_wrappers_zst");
    assert!(
        !function.instructions().any(|node| {
            matches!(
                &node.inst,
                trust_ir::Inst::Call { .. }
                    | trust_ir::Inst::GEP { .. }
                    | trust_ir::Inst::BinOp { op: trust_ir::BinOp::Mul, .. }
            )
        }),
        "[stable-mem-zst] wrappers were not true pointer-memory no-ops.\n{text}"
    );
    assert!(
        module.functions.iter().all(|candidate| !candidate.blocks.is_empty()),
        "[stable-mem-zst] an opaque/libc extern survived.\n{text}"
    );
}

/// A zero-sized element count always denotes zero bytes. The frontend must not
/// manufacture an observable foreign call for the ZST `copy`/`write_bytes`
/// forms, even under panic=abort.
#[test]
fn mir_panic_abort_zst_memory_intrinsics_are_true_noops() {
    let Some(stage1) = find_stage1_root() else {
        eprintln!(
            "SKIP mir_panic_abort_zst_memory_intrinsics_are_true_noops: no ABI-matching \
             stage1 rustc toolchain found."
        );
        return;
    };

    let bin = env!("CARGO_BIN_EXE_trust_ir_mir");
    let corpus =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/mem_intrinsic_wide_corpus.rs");
    let outpath = Path::new(env!("CARGO_TARGET_TMPDIR")).join("mem_intrinsic_zst_abort.tir");
    let _ = std::fs::remove_file(&outpath);
    let mut cmd = artifact_only_driver_command(bin, &stage1);
    cmd.arg("--mir-emit-closure");
    cmd.arg("mem_intrinsic_zst");
    cmd.arg(&outpath);
    cmd.arg("-Cpanic=abort");
    cmd.arg(&corpus);

    let out = cmd.output().expect("failed to spawn trust_ir_mir");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    assert!(
        out.status.success()
            && combined.contains("EMIT-CLOSURE-OK")
            && combined.contains("validate_module = 0 error(s)")
            && combined.contains("re-parse: OK"),
        "[mem-intrinsic-zst] fixture did not lower, validate, and round-trip.\n\
         ---- output ----\n{combined}"
    );

    let text = std::fs::read_to_string(&outpath).unwrap_or_else(|error| {
        panic!("[mem-intrinsic-zst] cannot read emitted module {}: {error}", outpath.display())
    });
    let module = trust_ir::parser::parse_module(&text).unwrap_or_else(|error| {
        panic!("[mem-intrinsic-zst] emitted module does not parse: {error:?}")
    });
    for suffix in ["zst_copy", "zst_write"] {
        let function = fn_ending_in(&module, suffix);
        assert!(
            !function
                .instructions()
                .any(|node| matches!(&node.inst, trust_ir::Inst::Call { .. })),
            "[mem-intrinsic-zst] {suffix} retained an observable call.\n---- IR ----\n{text}"
        );
    }
    assert!(
        !module.functions.iter().any(|function| {
            function.name.ends_with("memmove")
                || function.name.ends_with("memset")
                || (function.name.contains("intrinsics")
                    && (function.name.contains("copy")
                        || function.name.contains("write_bytes")))
        }),
        "[mem-intrinsic-zst] a libc or stride-erased intrinsic declaration survived.\n\
         ---- IR ----\n{text}"
    );
}

/// `arith_offset` and its stable `wrapping_offset` wrapper are Rust's wrapping
/// signed pointer arithmetic. TrustIR GEP is deliberately non-negative and
/// allocation-relative, so both forms must use the modular integer-pointer lane
/// without leaving a bodyless intrinsic/wrapper declaration behind.
#[test]
fn mir_arith_offset_uses_wrapping_integer_pointer_lane() {
    let Some(stage1) = find_stage1_root() else {
        eprintln!(
            "SKIP mir_arith_offset_uses_wrapping_integer_pointer_lane: no \
             ABI-matching stage1 rustc toolchain found."
        );
        return;
    };

    let bin = env!("CARGO_BIN_EXE_trust_ir_mir");
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/arith_offset_fail_closed_corpus.rs");
    for symbol in ["wrapping_wide_offset", "stable_wrapping_wide_offset"] {
        let outpath =
            Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("{symbol}_integer_lane.tir"));
        let _ = std::fs::remove_file(&outpath);
        let mut command = artifact_only_driver_command(bin, &stage1);
        command.arg("--mir-emit");
        command.arg(symbol);
        command.arg(&outpath);
        command.arg("-Cpanic=abort");
        command.arg(&corpus);

        let out = command.output().expect("failed to spawn trust_ir_mir");
        let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
        combined.push_str(&String::from_utf8_lossy(&out.stderr));
        assert!(
            out.status.success()
                && combined.contains("EMIT-OK")
                && combined.contains("validate_module = 0 error(s)")
                && combined.contains("re-parse: OK"),
            "[arith-offset] {symbol} did not lower, validate, and round-trip.\n\
             ---- output ----\n{combined}"
        );

        let text = std::fs::read_to_string(&outpath).unwrap_or_else(|error| {
            panic!("[arith-offset] cannot read emitted module {}: {error}", outpath.display())
        });
        let module = trust_ir::parser::parse_module(&text).unwrap_or_else(|error| {
            panic!("[arith-offset] emitted module does not parse: {error:?}")
        });
        let function = fn_ending_in(&module, symbol);
        assert_integer_pointer_offset(function, 8, &text);
        assert!(
            module.functions.iter().all(|candidate| !candidate.blocks.is_empty()),
            "[arith-offset] {symbol} retained a bodyless intrinsic/wrapper declaration.\n\
             ---- IR ----\n{text}"
        );
    }
}

/// The ordinary MIR `BinOp::Offset` path keeps its allocation-relative GEP fast
/// path for a forward constant, while a dynamic signed count uses the complete
/// integer-pointer lane so valid backward in-allocation steps remain expressible.
#[test]
fn mir_binop_offset_admits_forward_and_dynamic_signed() {
    let Some(stage1) = find_stage1_root() else {
        eprintln!(
            "SKIP mir_binop_offset_admits_forward_and_dynamic_signed: no \
             ABI-matching stage1 rustc toolchain found."
        );
        return;
    };

    let bin = env!("CARGO_BIN_EXE_trust_ir_mir");
    let corpus =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/mir_offset_domain_corpus.rs");

    let forward_path =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join("mir_offset_forward_constant.tir");
    let _ = std::fs::remove_file(&forward_path);
    let mut forward = artifact_only_driver_command(bin, &stage1);
    forward.arg("--mir-emit");
    forward.arg("forward_wide_offset");
    forward.arg(&forward_path);
    forward.arg("-Cpanic=abort");
    forward.arg(&corpus);
    let out = forward.output().expect("failed to spawn trust_ir_mir");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    assert!(
        out.status.success()
            && combined.contains("EMIT-OK")
            && combined.contains("validate_module = 0 error(s)")
            && combined.contains("re-parse: OK"),
        "[binop-offset] forward constant did not lower and validate.\n\
         ---- output ----\n{combined}"
    );

    let text = std::fs::read_to_string(&forward_path).unwrap_or_else(|error| {
        panic!("[binop-offset] cannot read emitted module {}: {error}", forward_path.display())
    });
    let module = trust_ir::parser::parse_module(&text).unwrap_or_else(|error| {
        panic!("[binop-offset] emitted forward module does not parse: {error:?}")
    });
    let function = fn_ending_in(&module, "forward_wide_offset");
    let indices: Vec<_> = function
        .instructions()
        .filter_map(|node| match &node.inst {
            trust_ir::Inst::GEP { pointee_ty, indices, .. } if pointee_ty == &trust_ir::Ty::I8 => {
                Some(indices)
            }
            _ => None,
        })
        .collect();
    assert_eq!(
        indices.len(),
        1,
        "[binop-offset] forward `u64` offset must emit exactly one byte GEP.\n\
         ---- IR ----\n{text}"
    );
    assert_eq!(
        indices[0].len(),
        1,
        "[binop-offset] forward byte GEP must have exactly one index.\n---- IR ----\n{text}"
    );
    assert!(
        value_is_const_product(function, indices[0][0], &trust_ir::Ty::I64, 1, 8),
        "[binop-offset] forward `u64` offset was not exactly `1 * 8` bytes.\n\
         ---- IR ----\n{text}"
    );

    let dynamic_path =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join("mir_offset_dynamic_integer_lane.tir");
    let _ = std::fs::remove_file(&dynamic_path);
    let mut dynamic = artifact_only_driver_command(bin, &stage1);
    dynamic.arg("--mir-emit");
    dynamic.arg("dynamic_wide_offset");
    dynamic.arg(&dynamic_path);
    dynamic.arg("-Cpanic=abort");
    dynamic.arg(&corpus);
    let out = dynamic.output().expect("failed to spawn trust_ir_mir");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    assert!(
        out.status.success()
            && combined.contains("EMIT-OK")
            && combined.contains("validate_module = 0 error(s)")
            && combined.contains("re-parse: OK"),
        "[binop-offset] dynamic signed offset did not lower and validate.\n\
         ---- output ----\n{combined}"
    );
    let text = std::fs::read_to_string(&dynamic_path).unwrap_or_else(|error| {
        panic!(
            "[binop-offset] cannot read emitted dynamic module {}: {error}",
            dynamic_path.display()
        )
    });
    let module = trust_ir::parser::parse_module(&text).unwrap_or_else(|error| {
        panic!("[binop-offset] emitted dynamic module does not parse: {error:?}")
    });
    let function = fn_ending_in(&module, "dynamic_wide_offset");
    assert_integer_pointer_offset(function, 8, &text);
    assert_zst_offset_is_noop(&stage1, bin, &corpus, "dynamic_zst_offset");
}

/// Cross-crate MIR may retain `ptr.offset` itself as a core method call. The
/// wrapper must share the direct BinOp domain split: inline a provably-forward
/// constant through GEP and a dynamic signed count through integer-pointer
/// arithmetic, never an opaque core extern whose semantics evade verification.
#[test]
fn mir_raw_ptr_offset_wrapper_inlines_both_domains() {
    let Some(stage1) = find_stage1_root() else {
        eprintln!(
            "SKIP mir_raw_ptr_offset_wrapper_inlines_both_domains: no \
             ABI-matching stage1 rustc toolchain found."
        );
        return;
    };

    let bin = env!("CARGO_BIN_EXE_trust_ir_mir");
    let corpus =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/mir_offset_domain_corpus.rs");

    let forward_path =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join("raw_ptr_wrapper_forward.tir");
    let _ = std::fs::remove_file(&forward_path);
    let mut forward = artifact_only_driver_command(bin, &stage1);
    forward.arg("--mir-emit");
    forward.arg("wrapper_forward_wide_offset");
    forward.arg(&forward_path);
    forward.arg("-Cpanic=abort");
    forward.arg(&corpus);
    let out = forward.output().expect("failed to spawn trust_ir_mir");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    assert!(
        out.status.success()
            && combined.contains("EMIT-OK")
            && combined.contains("validate_module = 0 error(s)")
            && combined.contains("re-parse: OK"),
        "[raw-ptr-offset-wrapper] forward wrapper did not lower and validate.\n\
         ---- output ----\n{combined}"
    );

    let text = std::fs::read_to_string(&forward_path).unwrap_or_else(|error| {
        panic!(
            "[raw-ptr-offset-wrapper] cannot read emitted module {}: {error}",
            forward_path.display()
        )
    });
    let module = trust_ir::parser::parse_module(&text).unwrap_or_else(|error| {
        panic!("[raw-ptr-offset-wrapper] emitted forward module does not parse: {error:?}")
    });
    let function = fn_ending_in(&module, "wrapper_forward_wide_offset");
    assert!(
        !function
            .instructions()
            .any(|node| matches!(&node.inst, trust_ir::Inst::Call { .. })),
        "[raw-ptr-offset-wrapper] admitted wrapper survived as an opaque call.\n\
         ---- IR ----\n{text}"
    );
    let indices: Vec<_> = function
        .instructions()
        .filter_map(|node| match &node.inst {
            trust_ir::Inst::GEP { pointee_ty, indices, .. }
                if pointee_ty == &trust_ir::Ty::I8 =>
            {
                Some(indices)
            }
            _ => None,
        })
        .collect();
    assert_eq!(
        indices.len(),
        1,
        "[raw-ptr-offset-wrapper] forward wrapper must emit one byte GEP.\n\
         ---- IR ----\n{text}"
    );
    assert!(
        indices[0].len() == 1
            && value_is_const_product(function, indices[0][0], &trust_ir::Ty::I64, 1, 8),
        "[raw-ptr-offset-wrapper] wrapper was not exactly `1 * 8` bytes.\n\
         ---- IR ----\n{text}"
    );

    let dynamic_path =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join("raw_ptr_wrapper_dynamic_integer_lane.tir");
    let _ = std::fs::remove_file(&dynamic_path);
    let mut dynamic = artifact_only_driver_command(bin, &stage1);
    dynamic.arg("--mir-emit");
    dynamic.arg("wrapper_dynamic_wide_offset");
    dynamic.arg(&dynamic_path);
    dynamic.arg("-Cpanic=abort");
    dynamic.arg(&corpus);
    let out = dynamic.output().expect("failed to spawn trust_ir_mir");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    assert!(
        out.status.success()
            && combined.contains("EMIT-OK")
            && combined.contains("validate_module = 0 error(s)")
            && combined.contains("re-parse: OK"),
        "[raw-ptr-offset-wrapper] dynamic wrapper did not lower and validate.\n\
         ---- output ----\n{combined}"
    );
    let text = std::fs::read_to_string(&dynamic_path).unwrap_or_else(|error| {
        panic!(
            "[raw-ptr-offset-wrapper] cannot read emitted dynamic module {}: {error}",
            dynamic_path.display()
        )
    });
    let module = trust_ir::parser::parse_module(&text).unwrap_or_else(|error| {
        panic!("[raw-ptr-offset-wrapper] emitted dynamic module does not parse: {error:?}")
    });
    let function = fn_ending_in(&module, "wrapper_dynamic_wide_offset");
    assert_integer_pointer_offset(function, 8, &text);
    assert!(
        module.functions.iter().all(|candidate| !candidate.blocks.is_empty()),
        "[raw-ptr-offset-wrapper] dynamic wrapper retained a bodyless core declaration.\n\
         ---- IR ----\n{text}"
    );
    assert_zst_offset_is_noop(&stage1, bin, &corpus, "wrapper_dynamic_zst_offset");
}

// ============ RUNG 10: by-value SMALL-PAIR return ABI (MIR path) =============

/// The pair-return fixture compiled NATIVELY by the host rustc — the oracle the
/// trust-ir Interpreter differential compares against. Same source the driver
/// lowers, so the differential is genuine (not a re-derived expected table).
#[allow(dead_code)]
mod pair_native {
    include!("fixtures/pair_ret_corpus.rs");
}

/// Find `name`'s (function, signature) in a parsed module.
fn fn_and_sig<'m>(
    module: &'m trust_ir::Module,
    name: &str,
) -> (&'m trust_ir::Function, &'m trust_ir::FuncTy) {
    let f = module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| {
            panic!(
                "[pair] emitted module has no fn named {name:?} (fns: {:?})",
                module.functions.iter().map(|f| &f.name).collect::<Vec<_>>()
            )
        });
    let sig = module
        .func_types
        .get(f.ty.index() as usize)
        .unwrap_or_else(|| panic!("[pair] fn {name:?} has a dangling functy id"));
    (f, sig)
}

/// Run `func` in the trust-ir Interpreter over unsigned-int args and return the
/// single result value.
fn interp_call(
    module: &trust_ir::Module,
    func: trust_ir::FuncId,
    args: &[(trust_ir::Ty, u128)],
) -> trust_ir::interpret::InterpretValue {
    use trust_ir::interpret::{InterpretValue, Interpreter};
    let vals: Vec<InterpretValue> = args
        .iter()
        .map(|(ty, v)| {
            InterpretValue::int(ty.clone(), *v as i128)
                .unwrap_or_else(|e| panic!("[pair] bad interp arg: {e:?}"))
        })
        .collect();
    let outcome = Interpreter::with_module(module)
        .execute_func(func, vals)
        .unwrap_or_else(|e| panic!("[pair] interpreter error: {e:?}"));
    outcome
        .returns
        .first()
        .unwrap_or_else(|| panic!("[pair] fn returned no value"))
        .clone()
}

/// The unsigned integer in lane `i` of an Aggregate return value.
fn agg_lane_uint(v: &trust_ir::interpret::InterpretValue, i: usize) -> u128 {
    use trust_ir::interpret::InterpretValueKind;
    let InterpretValueKind::Aggregate(lanes) = &v.kind else {
        panic!("[pair] expected an Aggregate return value, got {v:?}");
    };
    lanes
        .get(i)
        .and_then(|l| l.as_int())
        .unwrap_or_else(|| panic!("[pair] lane {i} is not an int in {v:?}"))
        .as_unsigned()
}

/// RUNG 10 acceptance gate: under the OPT-IN `--mir-pair-ret-by-value` flag, a
/// fn returning a 2-int-lane struct/tuple must lower BY VALUE on the MIR path —
/// the emitted signature returns ONE 2-tuple with NO leading sret pointer
/// param — validate cleanly, re-parse, carry full spans, and AGREE WITH THE
/// INTERPRETER against the natively-compiled fixture:
///
///   * `mk_pair` / `mk_tuple` / `swap_wide`: the by-value producer side (`ret`
///     of one SSA 2-tuple), lane values checked against the native
///     struct/tuple fields (2-tuples keep source order — empirically rustc
///     does not reorder them);
///   * `mk_rev` (`struct Rev { tag: u8, val: u32 }`, rustc-REORDERED to val@0,
///     tag@4): pins the OFFSET-ORDERED lane contract — the emitted return type
///     is `(u32, u8)` and lane 0 of the interpreted result is the SOURCE
///     `.val`;
///   * `pair_trip`: the caller side (call + whole-aggregate spill + field
///     reads), checked end-to-end over several argument pairs.
#[test]
fn mir_pair_by_value_return_lowers_and_interprets() {
    let Some(stage1) = find_stage1_root() else {
        eprintln!(
            "SKIP mir_pair_by_value_return_lowers_and_interprets: no stage1 rustc \
             toolchain found (set RUSTC=<stage1>/bin/rustc, or place it at \
             $HOME/trust/build/aarch64-apple-darwin/stage1). This is the MIR-path \
             by-value pair-return gate; it is being skipped only because the \
             rustc_private toolchain is unavailable."
        );
        return;
    };

    let bin = env!("CARGO_BIN_EXE_trust_ir_mir");
    let corpus_rel = "tests/fixtures/pair_ret_corpus.rs";
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join(corpus_rel);
    let outpath = Path::new(env!("CARGO_TARGET_TMPDIR")).join("pair_ret_closure.tir");
    // Lower the CALL-GRAPH CLOSURE of `pair_trip` (wires mk_pair / mk_tuple /
    // swap_wide in-module), so both the callee `ret` side and the caller spill
    // side of the by-value pair ABI are in one interpretable module.
    let mut cmd = artifact_only_driver_command(bin, &stage1);
    cmd.arg("--mir-pair-ret-by-value");
    cmd.arg("--mir-emit-closure");
    cmd.arg("pair_trip");
    cmd.arg(&outpath);
    cmd.arg("--crate-type=lib");
    cmd.arg(&corpus);

    let out = cmd.output().expect("failed to spawn trust_ir_mir");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));

    assert!(
        out.status.success(),
        "[pair] trust_ir_mir exited non-zero.\n---- full output ----\n{combined}"
    );
    assert!(
        combined.contains("EMIT-CLOSURE-OK"),
        "[pair] no EMIT-CLOSURE-OK — the pair-return corpus no longer lowers.\n\
         ---- full output ----\n{combined}"
    );
    assert!(
        combined.contains("validate_module = 0 error(s)"),
        "[pair] the emitted module no longer validates cleanly.\n\
         ---- full output ----\n{combined}"
    );
    assert!(
        combined.contains("re-parse: OK"),
        "[pair] the emitted text no longer re-parses.\n---- full output ----\n{combined}"
    );

    // Span threading must cover the NEW by-value return/spill instructions too
    // (spanned == total for both sides of the ABI).
    assert_span_provenance(&combined, "pair", "pair_trip", corpus_rel, "fn pair_trip(");
    assert_span_provenance(&combined, "pair", "mk_pair", corpus_rel, "fn mk_pair(");
    assert_span_provenance(&combined, "pair", "swap_wide", corpus_rel, "fn swap_wide(");

    // Parse the emitted text and pin the BY-VALUE signatures.
    let text = std::fs::read_to_string(&outpath)
        .unwrap_or_else(|e| panic!("[pair] cannot read emitted module {}: {e}", outpath.display()));
    let module = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|e| panic!("[pair] emitted module does not parse: {e:?}"));

    use trust_ir::Ty;
    let (mk_pair_fn, mk_pair_sig) = fn_and_sig(&module, "mk_pair");
    assert_eq!(
        mk_pair_sig.params,
        vec![Ty::U64, Ty::U32],
        "[pair] mk_pair params changed — a leading Ptr here would mean the sret \
         convention leaked back into the small-pair return"
    );
    assert_eq!(
        mk_pair_sig.returns,
        vec![Ty::Tuple(vec![Ty::U64, Ty::U32])],
        "[pair] mk_pair must return ONE by-value (u64, u32) tuple"
    );

    let (mk_tuple_fn, mk_tuple_sig) = fn_and_sig(&module, "mk_tuple");
    assert_eq!(mk_tuple_sig.params, vec![Ty::U64, Ty::U64]);
    assert_eq!(
        mk_tuple_sig.returns,
        vec![Ty::Tuple(vec![Ty::U64, Ty::U64])],
        "[pair] mk_tuple must return ONE by-value (u64, u64) tuple"
    );

    // A mixed-width 2-tuple keeps SOURCE order (rustc lays out u32@0, u64@8).
    let (swap_fn, swap_sig) = fn_and_sig(&module, "swap_wide");
    assert_eq!(swap_sig.params, vec![Ty::U32, Ty::U64]);
    assert_eq!(
        swap_sig.returns,
        vec![Ty::Tuple(vec![Ty::U32, Ty::U64])],
        "[pair] swap_wide's (u32, u64) must emit the (source == offset ordered) \
         (u32, u64) by-value return type"
    );

    // The rustc-REORDERED struct (`Rev { tag: u8, val: u32 }` -> val@0, tag@4):
    // the emitted return type is the OFFSET-ORDERED `(u32, u8)`, NOT the
    // declaration order.
    let (mk_rev_fn, mk_rev_sig) = fn_and_sig(&module, "mk_rev");
    assert_eq!(mk_rev_sig.params, vec![Ty::U8, Ty::U32]);
    assert_eq!(
        mk_rev_sig.returns,
        vec![Ty::Tuple(vec![Ty::U32, Ty::U8])],
        "[pair] mk_rev's reordered struct must emit the offset-ordered (u32, u8) \
         by-value return type"
    );

    let (pair_trip_fn, pair_trip_sig) = fn_and_sig(&module, "pair_trip");
    assert_eq!(pair_trip_sig.returns, vec![Ty::U64]);

    // ---- Interpreter differential vs the natively-compiled fixture. ----------

    // Producer side: mk_pair lanes are (hi@0, lo@8) — declaration order.
    let (x, y) = (600_006u64, 40_961u32);
    let native = pair_native::mk_pair(x, y);
    let got = interp_call(
        &module,
        mk_pair_fn.id,
        &[(Ty::U64, x as u128), (Ty::U32, y as u128)],
    );
    assert_eq!(
        (agg_lane_uint(&got, 0), agg_lane_uint(&got, 1)),
        (native.hi as u128, native.lo as u128),
        "[pair] interpreter vs native mk_pair({x}, {y}) disagree"
    );

    let (a, b) = (123_456_789u64, 987_654_321u64);
    let native_t = pair_native::mk_tuple(a, b);
    let got = interp_call(
        &module,
        mk_tuple_fn.id,
        &[(Ty::U64, a as u128), (Ty::U64, b as u128)],
    );
    assert_eq!(
        (agg_lane_uint(&got, 0), agg_lane_uint(&got, 1)),
        (native_t.0 as u128, native_t.1 as u128),
        "[pair] interpreter vs native mk_tuple({a}, {b}) disagree"
    );

    let (sa, sb) = (7u32, 123_456_789u64);
    let native_s = pair_native::swap_wide(sa, sb);
    let got = interp_call(
        &module,
        swap_fn.id,
        &[(Ty::U32, sa as u128), (Ty::U64, sb as u128)],
    );
    assert_eq!(
        (agg_lane_uint(&got, 0), agg_lane_uint(&got, 1)),
        (native_s.0 as u128, native_s.1 as u128),
        "[pair] interpreter vs native swap_wide({sa}, {sb}) disagree"
    );

    // Offset-order pin: lane 0 of the interpreted `Rev` result is the SOURCE
    // `.val` (the u32 rustc placed at offset 0), lane 1 the source `.tag`.
    let (rt, rv) = (0x91u8, 999_999u32);
    let native_r = pair_native::mk_rev(rt, rv);
    let got = interp_call(
        &module,
        mk_rev_fn.id,
        &[(Ty::U8, rt as u128), (Ty::U32, rv as u128)],
    );
    assert_eq!(
        (agg_lane_uint(&got, 0), agg_lane_uint(&got, 1)),
        (native_r.val as u128, native_r.tag as u128),
        "[pair] interpreter vs native mk_rev({rt}, {rv}) disagree (offset-ordered lanes)"
    );

    // Caller side, end-to-end over several argument pairs.
    for (x, y) in [
        (600_006u64, 40_961u32),
        (1u64, 0u32),
        (0u64, u32::MAX),
        (987_654_321_012u64, 55_555u32),
    ] {
        let native_r = pair_native::pair_trip(x, y);
        let got = interp_call(
            &module,
            pair_trip_fn.id,
            &[(Ty::U64, x as u128), (Ty::U32, y as u128)],
        );
        let got_int = got
            .as_int()
            .unwrap_or_else(|| panic!("[pair] pair_trip returned a non-int: {got:?}"))
            .as_unsigned();
        assert_eq!(
            got_int, native_r as u128,
            "[pair] interpreter vs native pair_trip({x}, {y}) disagree"
        );
    }
}

/// DEFAULT-OFF pin for RUNG 10: WITHOUT `--mir-pair-ret-by-value`, the same
/// pair-returning fixture must keep the LANDED sret convention exactly — a
/// leading hidden `Ptr` param and a void return. This is the in-repo guard for
/// the no-drift default (the trust-cg byte-verbatim fixture golds pin the sret
/// form, including for in-module pair-returning members like derived `Clone`s
/// of 2-byte structs; flipping the default is a coordinated trust-cg rung).
#[test]
fn mir_pair_return_defaults_to_sret_without_flag() {
    let Some(stage1) = find_stage1_root() else {
        eprintln!(
            "SKIP mir_pair_return_defaults_to_sret_without_flag: no stage1 rustc \
             toolchain found. This is the RUNG 10 default-off (no-drift) pin; it \
             is being skipped only because the rustc_private toolchain is \
             unavailable."
        );
        return;
    };

    let bin = env!("CARGO_BIN_EXE_trust_ir_mir");
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/pair_ret_corpus.rs");
    let outpath = Path::new(env!("CARGO_TARGET_TMPDIR")).join("pair_ret_default_sret.tir");
    let mut cmd = artifact_only_driver_command(bin, &stage1);
    cmd.arg("--mir-emit-closure");
    cmd.arg("pair_trip");
    cmd.arg(&outpath);
    cmd.arg("--crate-type=lib");
    cmd.arg(&corpus);
    // The retired ambient switch must be inert: only the explicit driver flag
    // is authorized to change the emitted ABI.
    cmd.env("TRUST_IR_MIR_PAIR_RET", "1");

    let out = cmd.output().expect("failed to spawn trust_ir_mir");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    assert!(
        out.status.success() && combined.contains("EMIT-CLOSURE-OK"),
        "[pair-default] the fixture no longer lowers under the DEFAULT (sret) \
         convention.\n---- full output ----\n{combined}"
    );
    assert!(
        combined.contains("validate_module = 0 error(s)"),
        "[pair-default] the default-convention module no longer validates.\n\
         ---- full output ----\n{combined}"
    );

    let text = std::fs::read_to_string(&outpath)
        .unwrap_or_else(|e| panic!("[pair-default] cannot read {}: {e}", outpath.display()));
    let module = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|e| panic!("[pair-default] emitted module does not parse: {e:?}"));

    use trust_ir::Ty;
    let (_, mk_pair_sig) = fn_and_sig(&module, "mk_pair");
    assert_eq!(
        mk_pair_sig.params,
        vec![Ty::Ptr, Ty::U64, Ty::U32],
        "[pair-default] without the flag, mk_pair must keep the LANDED sret form \
         (leading hidden Ptr param) — the default convention drifted"
    );
    assert_eq!(
        mk_pair_sig.returns,
        Vec::<Ty>::new(),
        "[pair-default] without the flag, mk_pair must return void (sret) — the \
         default convention drifted"
    );
}

// ============ RUNG 11: by-value SMALL-PAIR PARAM ABI (MIR path) ===============

/// The pair-PARAM fixture compiled NATIVELY by the host rustc — the oracle the
/// trust-ir Interpreter differential compares against (same source the driver
/// lowers, so the differential is genuine).
#[allow(dead_code)]
mod pair_param_native {
    include!("fixtures/pair_param_corpus.rs");
}

/// Run `func` in the trust-ir Interpreter over pre-built argument VALUES (so a
/// by-value 2-tuple PARAM can be fed directly) and return the single result value.
fn interp_call_vals(
    module: &trust_ir::Module,
    func: trust_ir::FuncId,
    vals: Vec<trust_ir::interpret::InterpretValue>,
) -> trust_ir::interpret::InterpretValue {
    use trust_ir::interpret::Interpreter;
    let outcome = Interpreter::with_module(module)
        .execute_func(func, vals)
        .unwrap_or_else(|e| panic!("[pair-param] interpreter error: {e:?}"));
    outcome
        .returns
        .first()
        .unwrap_or_else(|| panic!("[pair-param] fn returned no value"))
        .clone()
}

/// A by-value 2-tuple argument value (offset-ordered lanes) for `interp_call_vals`.
fn tuple2(a: (trust_ir::Ty, u128), b: (trust_ir::Ty, u128)) -> trust_ir::interpret::InterpretValue {
    use trust_ir::interpret::{InterpretValue, InterpretValueKind};
    InterpretValue {
        ty: trust_ir::Ty::Tuple(vec![a.0.clone(), b.0.clone()]),
        kind: InterpretValueKind::Aggregate(vec![
            InterpretValue::int(a.0, a.1 as i128).expect("lane a"),
            InterpretValue::int(b.0, b.1 as i128).expect("lane b"),
        ]),
    }
}

/// RUNG 11 acceptance gate (the DUAL of RUNG 10): under the OPT-IN
/// `--mir-pair-ret-by-value` flag, a fn TAKING a 2-int-lane struct/tuple must lower
/// its parameter BY VALUE on the MIR path — the emitted signature takes ONE SSA
/// 2-tuple param with NO leading by-ref `Ptr` — validate cleanly, re-parse, carry
/// full spans, and AGREE WITH THE INTERPRETER against the natively-compiled fixture:
///
///   * `sum_pair` / `sum_tuple`: the callee side (SSA-tuple param + entry spill +
///     field reads), fed a by-value 2-tuple directly (isolated), lanes in source
///     order (rustc does not reorder these);
///   * `take_rev` (`Rev { tag: u8, val: u32 }`, rustc-REORDERED to val@0, tag@4):
///     pins the OFFSET-ORDERED param-lane contract — the accepted param type is
///     `(u32, u8)` and lane 0 fed to the interpreter is the SOURCE `.val`;
///   * `param_trip`: end-to-end (caller by-value arg Load + callee spill), where
///     every pair arg originates from a by-value RETURN (padding zeroed), over
///     several argument pairs;
///   * the RUNG 11 `byval`/`sret` ABI pins: `big_first`'s by-ref aggregate param is
///     `byval`, `mk_big`'s sret return pointer is `sret` (display-comment pins on
///     the emitted text; validate-clean on the built module).
#[test]
fn mir_pair_by_value_param_lowers_and_interprets() {
    let Some(stage1) = find_stage1_root() else {
        eprintln!(
            "SKIP mir_pair_by_value_param_lowers_and_interprets: no stage1 rustc \
             toolchain found (set RUSTC=<stage1>/bin/rustc, or place it at \
             $HOME/trust/build/aarch64-apple-darwin/stage1). This is the MIR-path \
             by-value pair-PARAM gate; it is being skipped only because the \
             rustc_private toolchain is unavailable."
        );
        return;
    };

    let bin = env!("CARGO_BIN_EXE_trust_ir_mir");
    let corpus_rel = "tests/fixtures/pair_param_corpus.rs";
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join(corpus_rel);
    let outpath = Path::new(env!("CARGO_TARGET_TMPDIR")).join("pair_param_closure.tir");
    // Lower the CALL-GRAPH CLOSURE of `param_trip` (wires the producers + consumers
    // in-module), so both the callee spill side and the caller by-value-arg side of
    // the by-value pair PARAM ABI are in one interpretable module.
    let mut cmd = artifact_only_driver_command(bin, &stage1);
    cmd.arg("--mir-pair-ret-by-value");
    cmd.arg("--mir-emit-closure");
    cmd.arg("param_trip");
    cmd.arg(&outpath);
    cmd.arg("--crate-type=lib");
    cmd.arg(&corpus);

    let out = cmd.output().expect("failed to spawn trust_ir_mir");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));

    assert!(
        out.status.success(),
        "[pair-param] trust_ir_mir exited non-zero.\n---- full output ----\n{combined}"
    );
    assert!(
        combined.contains("EMIT-CLOSURE-OK"),
        "[pair-param] no EMIT-CLOSURE-OK — the pair-param corpus no longer lowers.\n\
         ---- full output ----\n{combined}"
    );
    assert!(
        combined.contains("validate_module = 0 error(s)"),
        "[pair-param] the emitted module no longer validates cleanly.\n\
         ---- full output ----\n{combined}"
    );
    assert!(
        combined.contains("re-parse: OK"),
        "[pair-param] the emitted text no longer re-parses.\n---- full output ----\n{combined}"
    );

    // Span threading must cover the NEW by-value pair instructions on BOTH sides of
    // the ABI: the callee entry-spill Store (`sum_pair`/`sum_tuple`/`take_rev`) and
    // the caller whole-aggregate arg Load (`param_trip`) — spanned == total. (The
    // byval-pinned `big_first` emits no NEW instruction — its by-ref lowering is the
    // pre-existing RUNG 3 path, and the pin is a display attr, not an instruction —
    // and a scalar-return by-ref-param fn has no entry-preamble instruction whose
    // span would anchor at the `fn` line, so its coverage is asserted elsewhere.)
    assert_span_provenance(&combined, "pair-param", "sum_pair", corpus_rel, "fn sum_pair(");
    assert_span_provenance(&combined, "pair-param", "sum_tuple", corpus_rel, "fn sum_tuple(");
    assert_span_provenance(&combined, "pair-param", "take_rev", corpus_rel, "fn take_rev(");
    assert_span_provenance(&combined, "pair-param", "param_trip", corpus_rel, "fn param_trip(");

    // Parse the emitted text and pin the BY-VALUE param signatures.
    let text = std::fs::read_to_string(&outpath).unwrap_or_else(|e| {
        panic!("[pair-param] cannot read emitted module {}: {e}", outpath.display())
    });
    let module = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|e| panic!("[pair-param] emitted module does not parse: {e:?}"));

    use trust_ir::Ty;
    let (sum_pair_fn, sum_pair_sig) = fn_and_sig(&module, "sum_pair");
    assert_eq!(
        sum_pair_sig.params,
        vec![Ty::Tuple(vec![Ty::U64, Ty::U32])],
        "[pair-param] sum_pair must take ONE by-value (u64, u32) tuple param — a \
         leading Ptr here would mean the by-ref convention leaked back in"
    );
    assert_eq!(sum_pair_sig.returns, vec![Ty::U64]);

    let (sum_tuple_fn, sum_tuple_sig) = fn_and_sig(&module, "sum_tuple");
    assert_eq!(
        sum_tuple_sig.params,
        vec![Ty::Tuple(vec![Ty::U64, Ty::U64])],
        "[pair-param] sum_tuple must take ONE by-value (u64, u64) tuple param"
    );

    // The rustc-REORDERED struct param (`Rev { tag: u8, val: u32 }` -> val@0, tag@4):
    // the accepted param type is the OFFSET-ORDERED `(u32, u8)`.
    let (take_rev_fn, take_rev_sig) = fn_and_sig(&module, "take_rev");
    assert_eq!(
        take_rev_sig.params,
        vec![Ty::Tuple(vec![Ty::U32, Ty::U8])],
        "[pair-param] take_rev's reordered struct must be accepted as the \
         offset-ordered (u32, u8) by-value tuple param"
    );

    // The RUNG 11 byval/sret ABI pins on the aggregates that STAY by-ref/sret.
    let (_, big_first_sig) = fn_and_sig(&module, "big_first");
    assert_eq!(
        big_first_sig.params,
        vec![Ty::Ptr],
        "[pair-param] a >16-byte aggregate param must stay by-ref (Ptr)"
    );
    let (_, mk_big_sig) = fn_and_sig(&module, "mk_big");
    assert_eq!(mk_big_sig.params, vec![Ty::Ptr, Ty::U64]);
    assert_eq!(mk_big_sig.returns, Vec::<Ty>::new());
    assert!(
        text.contains("; #param_attrs 0: byval"),
        "[pair-param] the by-ref aggregate param of big_first must be pinned `byval` \
         under the flag.\n---- emitted ----\n{text}"
    );
    assert!(
        text.contains("; #param_attrs 0: sret"),
        "[pair-param] the sret return pointer of mk_big must be pinned `sret` under \
         the flag.\n---- emitted ----\n{text}"
    );

    // ---- Interpreter differential vs the natively-compiled fixture. ----------

    // Callee side, ISOLATED: feed a by-value 2-tuple param directly, source order.
    let (hi, lo) = (0x1122_3344_5566_7788u64, 0x99aa_bbccu32);
    let native = pair_param_native::sum_pair(pair_param_native::Pair { hi, lo });
    let got = interp_call_vals(
        &module,
        sum_pair_fn.id,
        vec![tuple2((Ty::U64, hi as u128), (Ty::U32, lo as u128))],
    );
    assert_eq!(
        got.as_int().map(|i| i.as_unsigned()),
        Some(native as u128),
        "[pair-param] interpreter vs native sum_pair by-value param disagree"
    );

    let (a, b) = (0xdead_beef_0000_1111u64, 0x0f0f_f0f0_1234_5678u64);
    let native_t = pair_param_native::sum_tuple((a, b));
    let got = interp_call_vals(
        &module,
        sum_tuple_fn.id,
        vec![tuple2((Ty::U64, a as u128), (Ty::U64, b as u128))],
    );
    assert_eq!(
        got.as_int().map(|i| i.as_unsigned()),
        Some(native_t as u128),
        "[pair-param] interpreter vs native sum_tuple by-value param disagree"
    );

    // Offset-order pin: lane 0 of the fed tuple is the SOURCE `.val` (the u32 rustc
    // placed at offset 0), lane 1 the source `.tag`.
    let (tag, val) = (0x5eu8, 0x0abc_def0u32);
    let native_r = pair_param_native::take_rev(pair_param_native::Rev { tag, val });
    let got = interp_call_vals(
        &module,
        take_rev_fn.id,
        vec![tuple2((Ty::U32, val as u128), (Ty::U8, tag as u128))],
    );
    assert_eq!(
        got.as_int().map(|i| i.as_unsigned()),
        Some(native_r as u128),
        "[pair-param] interpreter vs native take_rev (offset-ordered by-value param) disagree"
    );

    // End-to-end: caller by-value arg Load + callee spill, over several arg pairs.
    let (param_trip_fn, param_trip_sig) = fn_and_sig(&module, "param_trip");
    assert_eq!(param_trip_sig.params, vec![Ty::U64, Ty::U32]);
    assert_eq!(param_trip_sig.returns, vec![Ty::U64]);
    for (x, y) in [
        (600_006u64, 40_961u32),
        (1u64, 0u32),
        (0u64, u32::MAX),
        (987_654_321_012u64, 55_555u32),
    ] {
        let native_r = pair_param_native::param_trip(x, y);
        let got = interp_call(
            &module,
            param_trip_fn.id,
            &[(Ty::U64, x as u128), (Ty::U32, y as u128)],
        );
        let got_int = got
            .as_int()
            .unwrap_or_else(|| panic!("[pair-param] param_trip returned a non-int: {got:?}"))
            .as_unsigned();
        assert_eq!(
            got_int, native_r as u128,
            "[pair-param] interpreter vs native param_trip({x}, {y}) disagree"
        );
    }
}

/// DEFAULT-OFF pin for RUNG 11: WITHOUT `--mir-pair-ret-by-value`, the same
/// pair-taking fixture must keep the LANDED by-ref convention exactly — every small
/// pair param is a leading `Ptr`, and NO `byval`/`sret` attr comment is emitted.
/// This is the in-repo guard for the no-drift default.
#[test]
fn mir_pair_param_defaults_to_byref_without_flag() {
    let Some(stage1) = find_stage1_root() else {
        eprintln!(
            "SKIP mir_pair_param_defaults_to_byref_without_flag: no stage1 rustc \
             toolchain found. This is the RUNG 11 default-off (no-drift) pin; it is \
             being skipped only because the rustc_private toolchain is unavailable."
        );
        return;
    };

    let bin = env!("CARGO_BIN_EXE_trust_ir_mir");
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/pair_param_corpus.rs");
    let outpath = Path::new(env!("CARGO_TARGET_TMPDIR")).join("pair_param_default_byref.tir");
    let mut cmd = artifact_only_driver_command(bin, &stage1);
    cmd.arg("--mir-emit-closure");
    cmd.arg("param_trip");
    cmd.arg(&outpath);
    cmd.arg("--crate-type=lib");
    cmd.arg(&corpus);
    cmd.env_remove("TRUST_IR_MIR_PAIR_RET");

    let out = cmd.output().expect("failed to spawn trust_ir_mir");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    assert!(
        out.status.success() && combined.contains("EMIT-CLOSURE-OK"),
        "[pair-param-default] the fixture no longer lowers under the DEFAULT (by-ref) \
         convention.\n---- full output ----\n{combined}"
    );
    assert!(
        combined.contains("validate_module = 0 error(s)"),
        "[pair-param-default] the default-convention module no longer validates.\n\
         ---- full output ----\n{combined}"
    );

    let text = std::fs::read_to_string(&outpath)
        .unwrap_or_else(|e| panic!("[pair-param-default] cannot read {}: {e}", outpath.display()));
    let module = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|e| panic!("[pair-param-default] emitted module does not parse: {e:?}"));

    use trust_ir::Ty;
    let (_, sum_pair_sig) = fn_and_sig(&module, "sum_pair");
    assert_eq!(
        sum_pair_sig.params,
        vec![Ty::Ptr],
        "[pair-param-default] without the flag, sum_pair must keep the LANDED by-ref \
         form (a leading `Ptr` param) — the default convention drifted"
    );
    assert!(
        !text.contains("#param_attrs") && !text.contains("#attrs"),
        "[pair-param-default] without the flag, NO byval/sret attr comment may be \
         emitted (byte-drift guard).\n---- emitted ----\n{text}"
    );
}

// ===== CONSTANT-AGGREGATE call arg (R1) + FAT-POINTER Cast/Transmute (R2) =====

/// The R1/R2 fixture compiled NATIVELY by the host rustc — the oracle the
/// trust-ir Interpreter differential compares against.
#[allow(dead_code)]
mod agg_native {
    include!("fixtures/agg_const_cast_corpus.rs");
}

/// Run `func` in the trust-ir Interpreter over one `u64` argument and return the
/// scalar `u64` result.
fn interp_u64(module: &trust_ir::Module, func: trust_ir::FuncId, x: u64) -> u64 {
    let r = interp_call(module, func, &[(trust_ir::Ty::U64, x as u128)]);
    r.as_int()
        .unwrap_or_else(|| panic!("[agg] expected a scalar int return, got {r:?}"))
        .as_unsigned() as u64
}

/// Emit the call-graph closure of `fnname` from the R1/R2 fixture and return the
/// combined driver output plus the parsed module (asserting EMIT-CLOSURE-OK,
/// clean validation, and a text round-trip along the way).
fn emit_agg_closure(stage1: &Path, fnname: &str) -> (String, trust_ir::Module) {
    let bin = env!("CARGO_BIN_EXE_trust_ir_mir");
    let corpus_rel = "tests/fixtures/agg_const_cast_corpus.rs";
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join(corpus_rel);
    let outpath =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("agg_{fnname}.tir"));
    let mut cmd = artifact_only_driver_command(bin, stage1);
    cmd.arg("--mir-emit-closure");
    cmd.arg(fnname);
    cmd.arg(&outpath);
    cmd.arg("--crate-type=lib");
    cmd.arg(&corpus);

    let out = cmd.output().expect("failed to spawn trust_ir_mir");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));

    assert!(
        out.status.success() && combined.contains("EMIT-CLOSURE-OK"),
        "[agg] `{fnname}` no longer lowers.\n---- full output ----\n{combined}"
    );
    assert!(
        combined.contains("validate_module = 0 error(s)"),
        "[agg] `{fnname}` no longer validates cleanly.\n---- full output ----\n{combined}"
    );
    assert!(
        combined.contains("re-parse: OK"),
        "[agg] `{fnname}` emitted text no longer re-parses.\n---- full output ----\n{combined}"
    );

    let text = std::fs::read_to_string(&outpath)
        .unwrap_or_else(|e| panic!("[agg] cannot read emitted module {}: {e}", outpath.display()));
    let module = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|e| panic!("[agg] emitted module does not parse: {e:?}"));
    (text, module)
}

/// R1 + R2 acceptance gate on the MIR path:
///
///   * R1 (`const_agg_trip` / `take_cfg`): a `const` STRUCT passed BY VALUE as a
///     call argument is materialized into a stack slot and passed by ref; the
///     in-module callee reads its fields. The emitted closure must validate,
///     re-parse, and AGREE WITH THE INTERPRETER against the natively-compiled
///     fixture over several arguments — the end-to-end proof that
///     `materialize_const_aggregate`'s byte image + the by-ref call ABI are
///     faithful.
///   * R2 (`fat_cast_probe`): a fat `&[u64]` -> thin `*const u64` reinterpret
///     (lane-0 data-pointer extraction) plus an array->slice Unsize fat-store,
///     lowered INLINE. A fat pointer's runtime address has no Interpreter
///     provenance model, so this leg is the EMIT + VALIDATE + re-parse bar (the
///     same one the MIR span-threading gate uses); the emitted body must contain
///     the inline `load ptr` lane-0 extraction and carry NO residual call.
#[test]
fn mir_const_aggregate_arg_lowers_and_interprets() {
    let Some(stage1) = find_stage1_root() else {
        eprintln!(
            "SKIP mir_const_aggregate_arg_lowers_and_interprets: no stage1 rustc \
             toolchain found (set RUSTC=<stage1>/bin/rustc, or place it at \
             $HOME/trust/build/aarch64-apple-darwin/stage1). This is the MIR-path \
             const-aggregate-arg / fat-cast gate; it is skipped only because the \
             rustc_private toolchain is unavailable."
        );
        return;
    };

    // --- R1: const-aggregate call arg, full interpreter differential. ---
    let (_r1_text, r1) = emit_agg_closure(&stage1, "const_agg_trip");
    let (cfg_fn, _sig) = fn_and_sig(&r1, "const_agg_trip");
    // The XOR fold is bit-exact, so EVERY argument must match the native oracle.
    for x in [0u64, 1, 0xdead_beef, 0xffff_ffff_ffff_ffff, 0x0123_4567_89ab_cdef] {
        let got = interp_u64(&r1, cfg_fn.id, x);
        let want = agg_native::const_agg_trip(x);
        assert_eq!(
            got, want,
            "[agg] R1 differential MISMATCH: const_agg_trip(0x{x:016x}) interp=0x{got:016x} \
             native=0x{want:016x} — the const-aggregate materialization or the by-ref \
             call ABI is not faithful"
        );
    }

    // --- R2: fat-pointer cast, emit + validate + inline-shape check. ---
    let (r2_text, _r2) = emit_agg_closure(&stage1, "fat_cast_probe");
    assert!(
        !r2_text.contains("call @"),
        "[agg] R2 fat_cast_probe should lower the fat->thin cast INLINE (no residual \
         call to a std as_ptr).\n---- emitted ----\n{r2_text}"
    );
    assert!(
        r2_text.contains("load ptr,"),
        "[agg] R2 fat_cast_probe must contain the inline lane-0 data-pointer load \
         (the fat-source cast extraction).\n---- emitted ----\n{r2_text}"
    );
}

/// TrustIR v24 has one canonical spelling for integer constants: values above
/// `i128::MAX` use `Constant::U128`. Exercise the actual MIR lowering so a
/// regression cannot silently spell `u128::MAX` as the negative
/// `Constant::Int(-1)` bit pattern rejected by validation and downstream
/// fail-closed adapters.
#[test]
fn mir_u128_max_uses_canonical_constant() {
    let Some(stage1) = find_stage1_root() else {
        eprintln!(
            "SKIP mir_u128_max_uses_canonical_constant: no stage1 rustc toolchain found. \
             This is the real MIR U128-constant gate; it is skipped only because \
             the rustc_private toolchain is unavailable."
        );
        return;
    };

    let bin = env!("CARGO_BIN_EXE_trust_ir_mir");
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/u128_const_corpus.rs");
    let outpath = Path::new(env!("CARGO_TARGET_TMPDIR")).join("u128_max_const.tir");
    let mut cmd = artifact_only_driver_command(bin, &stage1);
    cmd.arg("--mir-emit-closure");
    cmd.arg("u128_max_const");
    cmd.arg(&outpath);
    cmd.arg("--crate-type=lib");
    cmd.arg(&corpus);

    let out = cmd.output().expect("failed to spawn trust_ir_mir");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    assert!(
        out.status.success() && combined.contains("EMIT-CLOSURE-OK"),
        "[u128-const] fixture no longer lowers.\n---- full output ----\n{combined}"
    );
    assert!(
        combined.contains("validate_module = 0 error(s)"),
        "[u128-const] emitted module is not validation-clean.\n\
         ---- full output ----\n{combined}"
    );

    let text = std::fs::read_to_string(&outpath).unwrap_or_else(|error| {
        panic!(
            "[u128-const] cannot read emitted module {}: {error}",
            outpath.display()
        )
    });
    let module = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|error| panic!("[u128-const] module does not parse: {error:?}"));
    let function = fn_ending_in(&module, "u128_max_const");
    assert!(
        function.instructions().any(|node| matches!(
            &node.inst,
            trust_ir::Inst::Const {
                ty: trust_ir::Ty::U128,
                value: trust_ir::Constant::U128(value),
            } if *value == u128::MAX
        )),
        "[u128-const] u128::MAX was not emitted as canonical Constant::U128.\n\
         ---- emitted ----\n{text}"
    );
    assert!(
        !text.contains("const u128 -1"),
        "[u128-const] legacy negative raw-bit spelling escaped.\n---- emitted ----\n{text}"
    );

    let outcome = trust_ir::interpret::Interpreter::with_module(&module)
        .execute_func(function.id, vec![])
        .unwrap_or_else(|error| panic!("[u128-const] interpreter failed: {error:?}"));
    let got = outcome
        .returns
        .first()
        .and_then(|value| value.as_int())
        .map(|value| value.as_unsigned());
    assert_eq!(got, Some(u128::MAX), "[u128-const] interpreter parity");
}

// ===== PANIC-CLASS PROOF OBLIGATIONS (rustc `Assert` -> `ProofObligation`) ====

/// Emit one probe from `tests/fixtures/panic_obligation_corpus.rs` and return
/// its parsed module plus the driver's combined output. Compiles with debug
/// assertions ON so the overflow/div-by-zero asserts actually exist in MIR.
fn emit_panic_obligation_probe(
    stage1: &Path,
    symbol: &str,
) -> (trust_ir::Module, String) {
    let bin = env!("CARGO_BIN_EXE_trust_ir_mir");
    let corpus =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/panic_obligation_corpus.rs");
    let outpath =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("panic_obligation_{symbol}.tir"));
    let _ = std::fs::remove_file(&outpath);
    let mut cmd = artifact_only_driver_command(bin, stage1);
    cmd.arg("--mir-emit");
    cmd.arg(symbol);
    cmd.arg(&outpath);
    cmd.arg("-Cdebug-assertions=yes");
    cmd.arg(&corpus);

    let out = cmd.output().expect("failed to spawn trust_ir_mir");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    assert!(
        out.status.success() && combined.contains("EMIT-OK"),
        "[panic-obligations] {symbol} did not lower.\n---- full output ----\n{combined}"
    );
    // HARD CONSTRAINT: the emitted module must still validate. `validate_module`
    // checks proof-obligation integrity (duplicate ids, source text ids, source
    // ranges against the file table), so a malformed obligation fails HERE.
    assert!(
        combined.contains("validate_module = 0 error(s)"),
        "[panic-obligations] {symbol}: emitted module no longer validates cleanly.\n\
         ---- full output ----\n{combined}"
    );
    assert!(
        combined.contains("re-parse: OK"),
        "[panic-obligations] {symbol}: emitted text (now carrying `obligation` \
         rows) no longer re-parses.\n---- full output ----\n{combined}"
    );

    let text = std::fs::read_to_string(&outpath).unwrap_or_else(|error| {
        panic!(
            "[panic-obligations] cannot read emitted module {}: {error}",
            outpath.display()
        )
    });
    let module = trust_ir::parser::parse_module(&text).unwrap_or_else(|error| {
        panic!("[panic-obligations] {symbol}: module does not parse: {error:?}")
    });
    (module, text)
}

/// Every obligation of `kind` scoped to the function whose name ends in
/// `suffix`.
fn obligations_for<'m>(
    module: &'m trust_ir::Module,
    suffix: &str,
    kind: trust_ir::ObligationKind,
) -> Vec<&'m trust_ir::ProofObligation> {
    let fid = fn_ending_in(module, suffix).id;
    module
        .proof_obligations
        .iter()
        .filter(|oblig| oblig.kind == kind && oblig.function == Some(fid))
        .collect()
}

/// Shared invariants EVERY obligation this frontend mints must satisfy.
fn assert_obligation_shape(module: &trust_ir::Module, label: &str) {
    assert!(
        !module.proof_obligations.is_empty(),
        "[panic-obligations] {label}: the module records NO obligations — the \
         Assert pre-pass is not wired in"
    );
    let mut seen_ids = std::collections::BTreeSet::new();
    for oblig in &module.proof_obligations {
        // (1) STATUS. The frontend records claims; it discharges nothing.
        // Anything stronger than Pending here is faith-stamping.
        assert_eq!(
            oblig.status,
            trust_ir::ProofStatus::Pending,
            "[panic-obligations] {label}: obligation {} carries {:?}, but the \
             frontend has PROVED nothing — it must be Pending",
            oblig.id.index(),
            oblig.status
        );
        // (2) SCOPE (B4): every row names the function that carries the check,
        // and that function actually exists in the module.
        let fid = oblig.function.unwrap_or_else(|| {
            panic!(
                "[panic-obligations] {label}: obligation {} is unscoped",
                oblig.id.index()
            )
        });
        assert!(
            module.functions.iter().any(|f| f.id == fid),
            "[panic-obligations] {label}: obligation {} is scoped to FuncId {} \
             which is not in the module",
            oblig.id.index(),
            fid.index()
        );
        // (3) IDENTITY + LOCATION. A human must be able to find the check.
        let source = oblig.source.as_ref().unwrap_or_else(|| {
            panic!(
                "[panic-obligations] {label}: obligation {} carries no source identity",
                oblig.id.index()
            )
        });
        assert_eq!(source.source_id, "trust-ir-frontend/mir-assert@1");
        assert!(
            trust_ir::is_valid_proof_obligation_source_text_id(&source.assertion_id),
            "[panic-obligations] {label}: assertion id {:?} is not a valid text id",
            source.assertion_id
        );
        let range = source.range.unwrap_or_else(|| {
            panic!(
                "[panic-obligations] {label}: obligation {} lost its source range",
                oblig.id.index()
            )
        });
        assert!(
            (range.file as usize) < module.files.len(),
            "[panic-obligations] {label}: obligation {} points at file index {} \
             but the module has {} file(s)",
            oblig.id.index(),
            range.file,
            module.files.len()
        );
        assert!(
            range.start_line > 0 && (range.end_line, range.end_col) >= (range.start_line, range.start_col),
            "[panic-obligations] {label}: obligation {} has a degenerate range {range:?}",
            oblig.id.index()
        );
        assert!(
            module.files[range.file as usize].ends_with("panic_obligation_corpus.rs"),
            "[panic-obligations] {label}: obligation {} points at {:?}, not the fixture",
            oblig.id.index(),
            module.files[range.file as usize]
        );
        // (4) The description must be human-usable: it names the check and the
        // function, and says out loud that nothing was proved.
        assert!(
            oblig.description.contains("rustc MIR Assert")
                && oblig.description.contains("NOT PROVED"),
            "[panic-obligations] {label}: unhelpful description {:?}",
            oblig.description
        );
        // (5) Ids are unique (validate_module also enforces this).
        assert!(
            seen_ids.insert(oblig.id.index()),
            "[panic-obligations] {label}: duplicate obligation id {}",
            oblig.id.index()
        );
    }
}

/// PANIC-CLASS OBLIGATION gate: rustc tells the frontend, via
/// `TerminatorKind::Assert`, exactly where a panic-freedom property must hold.
/// The frontend used to lower the control flow faithfully and record NOTHING.
/// This asserts the claims now land as `Pending` `ProofObligation`s with the
/// right KIND, the right COUNT, the right FUNCTION SCOPE, and a real source
/// range — and that no `ProofAnnotation` was minted alongside them (an
/// annotation would CLAIM the property holds, which nothing here established).
#[test]
fn mir_emit_records_panic_class_obligations() {
    let Some(stage1) = find_stage1_root() else {
        eprintln!(
            "SKIP mir_emit_records_panic_class_obligations: no ABI-matching stage1 \
             rustc toolchain found. This is the panic-class proof-obligation gate; \
             it is skipped only because rustc_private is unavailable."
        );
        return;
    };

    // ---- (a) a slice index mints exactly one BoundsCheck. ----
    let (module, text) = emit_panic_obligation_probe(&stage1, "probe_bounds");
    assert_obligation_shape(&module, "probe_bounds");
    let bounds = obligations_for(&module, "probe_bounds", trust_ir::ObligationKind::BoundsCheck);
    assert_eq!(
        bounds.len(),
        1,
        "[panic-obligations] probe_bounds must record exactly one BoundsCheck; got {}.\n\
         ---- emitted ----\n{text}",
        bounds.len()
    );
    assert!(
        bounds[0]
            .source
            .as_ref()
            .is_some_and(|s| s.assertion_id.ends_with("#bounds_check")),
        "[panic-obligations] probe_bounds: assertion id does not name the check: {:?}",
        bounds[0].source
    );
    // A bounds panic is NOT a MemorySafety obligation — MemorySafety routes to
    // borrow-check, which would mis-file a panic-freedom VC.
    assert!(
        !module
            .proof_obligations
            .iter()
            .any(|o| o.kind == trust_ir::ObligationKind::MemorySafety),
        "[panic-obligations] probe_bounds: a bounds check was filed as MemorySafety"
    );
    // The rows survive the TEXT format the downstream consumer reads.
    assert!(
        text.contains("obligation ") && text.contains("bounds_check pending"),
        "[panic-obligations] probe_bounds: no `obligation .. bounds_check pending` \
         row in the emitted text.\n---- emitted ----\n{text}"
    );
    // The obligation is RECORDED, not linked as an established claim: a
    // `ProofRef` to a Pending obligation is rejected by the validator, and a
    // bare `ProofAnnotation` would assert the property holds.
    assert!(
        fn_ending_in(&module, "probe_bounds").proofs.is_empty(),
        "[panic-obligations] probe_bounds: the frontend minted a function-level \
         ProofAnnotation — that CLAIMS the property holds, which nothing proved"
    );

    // ---- (b) a checked add mints exactly one ArithmeticSafety. ----
    let (module, text) = emit_panic_obligation_probe(&stage1, "probe_overflow");
    assert_obligation_shape(&module, "probe_overflow");
    let arith = obligations_for(
        &module,
        "probe_overflow",
        trust_ir::ObligationKind::ArithmeticSafety,
    );
    assert_eq!(
        arith.len(),
        1,
        "[panic-obligations] probe_overflow must record exactly one \
         ArithmeticSafety; got {}.\n---- emitted ----\n{text}",
        arith.len()
    );
    assert!(
        arith[0]
            .source
            .as_ref()
            .is_some_and(|s| s.assertion_id.ends_with("#overflow")),
        "[panic-obligations] probe_overflow: assertion id does not name the check: {:?}",
        arith[0].source
    );
    assert!(
        text.contains("arithmetic_safety pending"),
        "[panic-obligations] probe_overflow: no `arithmetic_safety pending` row in \
         the emitted text.\n---- emitted ----\n{text}"
    );

    // ---- (c) a signed division mints BOTH div-by-zero and overflow, and both
    // route to ArithmeticSafety (the shift/div family must never fall through
    // to the panic-freedom bucket). ----
    let (module, text) = emit_panic_obligation_probe(&stage1, "probe_div_zero");
    assert_obligation_shape(&module, "probe_div_zero");
    let arith = obligations_for(
        &module,
        "probe_div_zero",
        trust_ir::ObligationKind::ArithmeticSafety,
    );
    let slugs: Vec<&str> = arith
        .iter()
        .filter_map(|o| o.source.as_ref())
        .filter_map(|s| s.assertion_id.rsplit('#').next())
        .collect();
    assert!(
        slugs.contains(&"div_by_zero"),
        "[panic-obligations] probe_div_zero: no div-by-zero obligation; slugs={slugs:?}\n\
         ---- emitted ----\n{text}"
    );
    assert!(
        slugs.contains(&"overflow"),
        "[panic-obligations] probe_div_zero: the `i64::MIN / -1` overflow assert \
         was not recorded; slugs={slugs:?}\n---- emitted ----\n{text}"
    );
    assert_eq!(
        arith.len(),
        2,
        "[panic-obligations] probe_div_zero must record exactly two \
         ArithmeticSafety obligations; got {} ({slugs:?})",
        arith.len()
    );
}

/// The obligation rows must survive the wire formats a REAL emitted module
/// crosses, not just the text one the driver writes. This round-trips a genuine
/// frontend module through canonical text and the binary codec. (JSON and
/// MessagePack are guarded byte-golden by the `frontend_panic_obligations`
/// conformance fixture, which does not need a rustc toolchain to run.)
#[test]
fn panic_class_obligations_survive_every_wire_format() {
    let Some(stage1) = find_stage1_root() else {
        eprintln!(
            "SKIP panic_class_obligations_survive_every_wire_format: no ABI-matching \
             stage1 rustc toolchain found."
        );
        return;
    };

    let (module, text) = emit_panic_obligation_probe(&stage1, "probe_div_zero");
    assert!(!module.proof_obligations.is_empty());

    // Text (already parsed once by the helper) — assert idempotence of the
    // Display -> parse -> Display cycle over the obligation rows.
    let reprinted = module.to_string();
    let reparsed = trust_ir::parser::parse_module(&reprinted)
        .expect("[panic-obligations] re-printed module does not parse");
    assert_eq!(
        reparsed.proof_obligations, module.proof_obligations,
        "[panic-obligations] obligations changed across a text round-trip.\n\
         ---- emitted ----\n{text}"
    );

    // Binary.
    let bytes = trust_ir::binary::serialize_module(&module);
    let decoded = trust_ir::binary::deserialize_module(&bytes)
        .expect("[panic-obligations] binary decode failed");
    assert_eq!(
        decoded.proof_obligations, module.proof_obligations,
        "[panic-obligations] obligations did not survive the binary codec"
    );
}
