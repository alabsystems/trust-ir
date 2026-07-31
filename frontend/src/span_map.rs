// span_map — rustc `Span` -> trust-ir `SourceSpan` threading, SHARED by both
// lowering paths:
//   * the THIR path (`MonoCx` in `m3.rs`, compiled into the `trust_ir_frontend`
//     lib/binary via `pub mod span_map;` in `lib.rs`), and
//   * the MIR whole-program path (`lower_with_signature` in `mir_lower.rs`,
//     compiled into the `trust_ir_mir` binary via `#[path] mod span_map;` in
//     `mir_driver.rs` — that binary is deliberately lib-independent, so it
//     includes this SOURCE FILE rather than linking the lib).
//
// The trust-ir side of the contract is the debug-info file table
// (`ModuleBuilder::intern_file`, indexed by `SourceSpan::file`) plus the
// builder's sticky span (`FunctionBuilder::set_span` / `clear_span`), which
// stamps every subsequently-emitted `InstrNode`. `SourceSpan` is a POINT
// (`file`/`line`/`col`), so a rustc byte-range span maps to its LO edge.
//
// TOTALITY (the span-threading item's hard requirement): mapping NEVER panics
// and NEVER bails —
//   * a macro-expansion span degrades to its OUTERMOST CALLSITE
//     (`Span::source_callsite`, the user-visible source position);
//   * a dummy/synthetic span (or a span whose file the pre-pass never saw)
//     maps to `None`, and the caller emits span-less — the IR's back-compat
//     default, never an error.
//
// Author: frontend span threading (integration-frontend-emission)
// License: Apache-2.0

use std::collections::HashMap;

use rustc_middle::mir::Body;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use trust_ir::value::SourceSpan;
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

/// Per-body map from rustc source files to the module's debug-info file table.
///
/// Built by a PRE-PASS over all the spans a body can mention, BEFORE a
/// `FunctionBuilder` is created — `ModuleBuilder::intern_file` needs `&mut`
/// access to the module, which the `FunctionBuilder` holds exclusively while a
/// function is being emitted. After the pre-pass, `to_ir`/`apply` are pure
/// lookups (no module access), so they can run at every emission site.
pub struct SpanMap {
    /// Locally-displayed filename -> `Module.files` index (from `intern_file`,
    /// so the ids are the module's own — idempotent across bodies sharing a
    /// module).
    files: HashMap<String, u32>,
}

impl SpanMap {
    /// PRE-PASS: resolve the source FILE of every span in `spans` and intern
    /// each distinct one into the module's debug-info file table. Dummy spans
    /// are skipped; macro-expansion spans resolve to their outermost callsite's
    /// file. Never fails.
    pub fn build<'tcx>(
        tcx: TyCtxt<'tcx>,
        mb: &mut ModuleBuilder,
        spans: impl IntoIterator<Item = Span>,
    ) -> SpanMap {
        let mut files: HashMap<String, u32> = HashMap::new();
        for span in spans {
            if let Some(name) = file_of(tcx, span) {
                if !files.contains_key(&name) {
                    let idx = mb.intern_file(name.clone());
                    files.insert(name, idx);
                }
            }
        }
        SpanMap { files }
    }

    /// Map a rustc `Span` to a trust-ir `SourceSpan`: the interned file id plus
    /// the 1-based line and column of the span's LO edge. `None` for a dummy
    /// span or a file the pre-pass never saw — the caller degrades to span-less
    /// emission (never a panic, never a bail).
    pub fn to_ir<'tcx>(&self, tcx: TyCtxt<'tcx>, span: Span) -> Option<SourceSpan> {
        // A macro-expansion span degrades to its outermost callsite (the
        // user-visible position); a non-expansion span is returned unchanged.
        let span = span.source_callsite();
        if span.is_dummy() {
            return None;
        }
        let loc = tcx.sess.source_map().lookup_char_pos(span.lo());
        let name = loc.file.name.prefer_local_unconditionally().to_string();
        let file = *self.files.get(&name)?;
        Some(SourceSpan {
            file,
            // `Loc::line` is already 1-based.
            line: u32::try_from(loc.line).unwrap_or(u32::MAX),
            // `Loc::col_display` is 0-based; emit 1-based columns.
            col: u32::try_from(loc.col_display).unwrap_or(u32::MAX - 1) + 1,
        })
    }

    /// Map a rustc `Span` to a trust-ir `ProofObligationSourceRange`: the
    /// interned file id plus BOTH 1-based endpoints. Where `to_ir` collapses a
    /// byte range to its LO edge (a `SourceSpan` is a point), a proof
    /// obligation wants the whole extent — an obligation a human cannot
    /// locate is much less useful than one that highlights the expression.
    ///
    /// TOTALITY, same contract as `to_ir`: never panics, never bails. `None`
    /// for a dummy span, a file the pre-pass never interned, or a degenerate
    /// zero line. The HI endpoint degrades to the LO endpoint whenever it
    /// resolves into a different file or precedes LO (which a multi-file
    /// macro expansion can produce) — so every range this returns already
    /// satisfies `validate_module`'s `InvalidProofObligationSourceRange`
    /// checks, and an invalid range is unconstructible here.
    pub fn to_ir_range<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        span: Span,
    ) -> Option<trust_ir::proof::ProofObligationSourceRange> {
        let span = span.source_callsite();
        if span.is_dummy() {
            return None;
        }
        let source_map = tcx.sess.source_map();
        let lo = source_map.lookup_char_pos(span.lo());
        let lo_name = lo.file.name.prefer_local_unconditionally().to_string();
        let file = *self.files.get(&lo_name)?;
        let start_line = u32::try_from(lo.line).unwrap_or(u32::MAX);
        if start_line == 0 {
            return None;
        }
        let start_col = u32::try_from(lo.col_display).unwrap_or(u32::MAX - 1) + 1;
        // Degenerate default: a point range at the LO edge.
        let mut end_line = start_line;
        let mut end_col = start_col;
        let hi = source_map.lookup_char_pos(span.hi());
        if hi.file.name.prefer_local_unconditionally().to_string() == lo_name {
            let hi_line = u32::try_from(hi.line).unwrap_or(u32::MAX);
            let hi_col = u32::try_from(hi.col_display).unwrap_or(u32::MAX - 1) + 1;
            if hi_line != 0 && (hi_line, hi_col) >= (start_line, start_col) {
                end_line = hi_line;
                end_col = hi_col;
            }
        }
        Some(trust_ir::proof::ProofObligationSourceRange {
            file,
            start_line,
            start_col,
            end_line,
            end_col,
        })
    }

    /// `to_ir` + apply: set the builder's sticky span (or CLEAR it when the
    /// rustc span does not map — so a synthetic statement never inherits an
    /// unrelated predecessor's position). Returns what was applied.
    pub fn apply<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        fb: &mut FunctionBuilder<'_>,
        span: Span,
    ) -> Option<SourceSpan> {
        let ir = self.to_ir(tcx, span);
        set_or_clear(fb, ir);
        ir
    }
}

/// Set or clear the builder's sticky span from an optional `SourceSpan`.
pub fn set_or_clear(fb: &mut FunctionBuilder<'_>, span: Option<SourceSpan>) {
    match span {
        Some(s) => fb.set_span(s),
        None => fb.clear_span(),
    }
}

/// The locally-displayed source-file name a span resolves to (through its
/// outermost callsite), or `None` for a dummy span.
fn file_of<'tcx>(tcx: TyCtxt<'tcx>, span: Span) -> Option<String> {
    let span = span.source_callsite();
    if span.is_dummy() {
        return None;
    }
    let loc = tcx.sess.source_map().lookup_char_pos(span.lo());
    Some(loc.file.name.prefer_local_unconditionally().to_string())
}

/// Every span a MIR body carries: the fn-level `body.span`, plus each
/// statement's and terminator's `SourceInfo` span. The MIR path's pre-pass
/// input (macro-expansion spans are resolved to their callsite file inside
/// `SpanMap::build`).
pub fn mir_body_spans<'tcx>(body: &Body<'tcx>) -> Vec<Span> {
    let mut spans = vec![body.span];
    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            spans.push(stmt.source_info.span);
        }
        if let Some(term) = &bb.terminator {
            spans.push(term.source_info.span);
        }
    }
    spans
}

/// One greppable SPAN-PROVENANCE report line for a function of a built module:
/// how many of its instructions carry a span, which file-table entry they point
/// at, and the covered line range. Printed by BOTH drivers so the acceptance
/// gates can assert that real spans came through:
///
/// `SPAN-PROVENANCE fn=<name> spanned=<n> total=<m> file=<idx>:"<path>" lines=<lo>..<hi>`
///
/// (`file=-` / `lines=-` when no instruction carries a span.)
pub fn function_span_report(module: &trust_ir::Module, func: &trust_ir::Function) -> String {
    let mut total = 0usize;
    let mut spanned = 0usize;
    let mut file: Option<u32> = None;
    let mut min_line = u32::MAX;
    let mut max_line = 0u32;
    for block in &func.blocks {
        for node in &block.body {
            total += 1;
            if let Some(s) = node.span {
                spanned += 1;
                file.get_or_insert(s.file);
                min_line = min_line.min(s.line);
                max_line = max_line.max(s.line);
            }
        }
    }
    let file_str = match file {
        Some(f) => match module.files.get(f as usize) {
            Some(path) => format!("file={f}:{path:?}"),
            None => format!("file={f}:<dangling: not in the module file table>"),
        },
        None => "file=-".to_string(),
    };
    let lines = if spanned > 0 {
        format!("lines={min_line}..{max_line}")
    } else {
        "lines=-".to_string()
    };
    format!(
        "SPAN-PROVENANCE fn={} spanned={spanned} total={total} {file_str} {lines}",
        func.name
    )
}
