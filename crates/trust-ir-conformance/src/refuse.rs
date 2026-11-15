// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The must-refuse corpus runner (KIND 4, 2026-09-24).
//!
//! `tests/fixtures/refuse/` holds a corpus of WIRE ARTIFACTS a conforming
//! consumer must REFUSE: a module that decodes but that a named trust-ir entry
//! point refuses, a module that is well-formed by every trust-ir rule but that
//! a native backend must still refuse (the consumer-relative obligations the
//! format states in prose), and poisoned byte strings the binary reader must
//! refuse. Every row is paired, in `MANIFEST.tsv`, with the trust-ir verdict
//! that names WHY (a `ValidationError` / `BinaryError` / `CompletenessError`
//! variant, the zero-`Trusted` census, or a consumer-relative rule), and with
//! the document where the "consumer MUST" sentence lives.
//!
//! This module is what a CONSUMER calls. It never re-implements the corpus:
//! [`corpus`] reads the checked-in bytes (the wire the consumer will meet in
//! production, not a builder's in-memory module), and [`Report::run`] drives
//! the consumer's own admission function over every row and reports, per row,
//! refused or accepted. A consumer test is a few lines:
//!
//! ```
//! use trust_ir_conformance::refuse::{Report, Row, corpus};
//! // The consumer's own admission: decode + validate + lower, whatever it
//! // does before it would emit code, with STRUCTURAL_LICENSE_AUTHORITY in
//! // its recognized set FOR THIS RUN (see "The runner is reason-blind"
//! // below). This stand-in refuses every artifact and accepts the control.
//! fn admit(row: &Row) -> Result<(), String> {
//!     if row.is_control() {
//!         Ok(())
//!     } else {
//!         Err("refused".to_string())
//!     }
//! }
//! let rows = corpus().expect("the must-refuse corpus loads");
//! let report = Report::run(&rows, admit);
//! if let Err(findings) = report.check(&rows) {
//!     panic!("{findings}");
//! }
//! ```
//!
//! The library is TOTAL (r11 item 7): [`corpus`], [`manifest`] and
//! [`Report::check`] return typed errors, and the CONSUMER'S TEST decides —
//! a panic there is a test failure, not a library contract.
//!
//! Growth fails by NAME: [`Corpus::uncovered`] lists the rows a consumer's
//! test did not dispatch, so a row added here cannot pass a consumer
//! silently. (Different question: [`Report::uncovered`] lists the rows a
//! REPORT has no outcome for.)
//!
//! # The runner is reason-blind, and the control row is what bounds that
//!
//! [`Report::run`] sees `Ok` or `Err`; it never compares the consumer's
//! reason with the manifest's verdict. Every `module` row whose subject is
//! not the codegen license wears
//! `Gated { authority: STRUCTURAL_LICENSE_AUTHORITY }`, so that the license
//! layer is not what refuses it — and that authority is, by design
//! (`trust-ir-build`'s WS1.5 DECIDE 1), in NO consumer's default recognized
//! set. A consumer that runs the corpus under its production recognized set
//! therefore refuses those rows as `UnrecognizedGateAuthority` before their
//! subject is reached (measured at landing under `{clean-kernel-tv}`: most
//! module rows, and for every `Consumer:<rule>` row, the `Trusted` census
//! row, the completeness row and the unbacked-claim row the license was the
//! ONLY refusal), and a refuse-everything admission "passes" the same way.
//! Neither run says anything about the rows' subjects.
//!
//! The `control` row (`refuse/control_licensed_identity`) bounds this
//! mechanically. It is the envelope every module row shares — the identity
//! function under the structural license on the canonical target — with NO
//! subject, and a conforming consumer must ACCEPT it. [`Report::check`]
//! returns `Err` naming it when a control row is refused, and
//! [`Report::controls_refused`] lists it, so a consumer test that asserts on
//! either — that has not recognized [`STRUCTURAL_LICENSE_AUTHORITY`] for the
//! run, or that refuses everything — cannot pass. That rung is the
//! consumer's OWN assertion (test rung): the library no longer panics for
//! it. Recognizing the authority is a TEST-time decision for this run only;
//! it licenses nothing in production.
//!
//! What the control does NOT close: it pins that the shared envelope is
//! accepted, not that each refusal is for that row's subject. A consumer
//! that lowers no `Vector` type at all accepts the control and still refuses
//! `struct_passing_unclassified_vector_by_value` for the wrong reason (its
//! vector, not its `Unclassified` struct-passing policy); only a per-row
//! accepted twin (the row minus its subject) would attribute that, and the
//! corpus carries no twins yet. [`Outcome::Refused`] carries the consumer's
//! own message so its test can add a by-name check where that matters.
//! trust-cg's must-refuse test does, per row and lane, in its
//! `EXPECTED_REASON` table; for this row its entry names `unclassified`.
//!
//! # What the corpus is, and is not
//!
//! * Every `module` / `bytes` row is TEST-rung evidence: the row is executed
//!   by `tests/refuse_corpus.rs` against the trust-ir entry points the
//!   manifest names, and byte-pinned as a golden. A consumer running it gains
//!   evidence about ITS refusal, never proof.
//! * A `none` row is an obligation the corpus CANNOT express as a refusable
//!   artifact (a non-inference rule, a semantics-preservation rule, a
//!   consumer-internal rule). It carries no bytes; it exists so the
//!   enforcement-link gate can hold the document that states the obligation
//!   to say so, with its honest rung, by the same two-way citation every
//!   expressible row has.
//! * The trust-ir verdict names WHY the row is refusable; a consumer's own
//!   error need not spell it. [`Outcome::Refused`] carries the consumer's
//!   message so its test may add a by-name check of its own.
//!
//! # The manifest grammar
//!
//! Tab-separated, `#` comments, one header row naming the columns:
//!
//! ```text
//! row  carrier  verdicts  text_losses  obligation  why
//! ```
//!
//! * `row`: the row id; it names the FEATURE (never a wire version). A
//!   `module` / `bytes` row has a `<row>.tmbc` beside the manifest.
//! * `carrier`: `module` (the bytes decode; the verdicts are about the
//!   module), `bytes` (poisoned wire the reader refuses), `control` (the
//!   bytes decode to a module a conforming consumer must ACCEPT: the
//!   envelope every `module` row shares, with no subject; its `consumer`
//!   verdict is `accepts`), or `none`.
//! * `verdicts`: `;`-separated `<entry-point>=<verdict>` pairs, or `-`.
//!   Verdicts: `accepts`, `Validation:<Variant>`, `Completeness:<Variant>`,
//!   `Binary:<Variant>`, `Census:Trusted`, `Consumer:<rule>`. A row may carry
//!   several verdicts at several entry points — a two-verdict row (accepted
//!   by `validate_module`, refused by the codegen gate) states BOTH, so the
//!   grandfather reading and the refusal are both pinned, never one.
//! * `text_losses`: the exact `TextLossKind` set the canonical text printer
//!   reports for the module (`-` when loss-free). A lossy row is never
//!   offered as text: the text form would launder the refusal.
//! * `obligation`: the repo-rooted file where the "consumer MUST" sentence
//!   lives. That file must cite `refuse/<row>` back (checked by
//!   `scripts/check_enforcement_links.py`, rule R).
//! * `why`: one sentence.

use std::collections::BTreeSet;
use std::fmt;
use std::fs;
use std::ops::Deref;
use std::path::{Path, PathBuf};

use trust_ir::Module;
use trust_ir::binary::{WireVersion, deserialize_module_with_wire_version};

/// The manifest text, compiled in so a consumer always reads the manifest of
/// the pinned revision (the row files are read beside it at run time).
pub const MANIFEST: &str = include_str!("../tests/fixtures/refuse/MANIFEST.tsv");

/// The columns, in order; the header row of the manifest must spell exactly
/// these.
pub const COLUMNS: [&str; 6] = [
    "row",
    "carrier",
    "verdicts",
    "text_losses",
    "obligation",
    "why",
];

/// The gate authority every non-license artifact row wears
/// (`Gated { authority }`), so that the codegen license layer is not what
/// refuses it. It is outside `trust-ir-build`'s
/// `EVIDENCE_BOUND_GATE_AUTHORITIES` and, by design, in no consumer's default
/// recognized set: a consumer running this corpus recognizes it FOR THE RUN
/// (a test-time decision that licenses nothing in production), or every such
/// row is refused as `UnrecognizedGateAuthority` before its subject is
/// reached and the `control` row fails the run by name (module docs).
/// `tests/refuse_corpus.rs` pins the builders' spelling equal to this one.
pub const STRUCTURAL_LICENSE_AUTHORITY: &str = "trust-direct-lane-structural";

/// Directory the row files live in.
#[must_use]
pub fn fixtures_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("refuse")
}

/// What a row carries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Carrier {
    /// `<row>.tmbc` decodes to a module; the verdicts are about that module.
    Module,
    /// `<row>.tmbc` is poisoned wire the binary reader must refuse.
    Bytes,
    /// `<row>.tmbc` decodes to a module a conforming consumer must ACCEPT:
    /// the envelope the `module` rows share, with no subject (module docs).
    Control,
    /// No artifact: an obligation the corpus cannot express, recorded so the
    /// document stating it is held to say so.
    None,
}

/// The verdict a named entry point returns for a row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// The entry point accepts the row (the grandfather / structural reading
    /// of a two-verdict row).
    Accepts,
    /// `trust_ir_build::validate::ValidationError::<variant>`.
    Validation(String),
    /// `trust_ir_build::validate::CompletenessError::<variant>`.
    Completeness(String),
    /// `trust_ir::binary::BinaryError::<variant>`.
    Binary(String),
    /// A module-wide census refuses: today only `Trusted` (the zero-`Trusted`
    /// census, `trust-ir validate --forbid-trusted`).
    Census(String),
    /// No trust-ir variant exists: the module is well-formed by every
    /// trust-ir rule and a conforming native consumer must still refuse it,
    /// for the named rule.
    Consumer(String),
}

impl Verdict {
    /// Parse one verdict token.
    pub fn parse(token: &str) -> Result<Self, String> {
        if token == "accepts" {
            return Ok(Self::Accepts);
        }
        let Some((class, name)) = token.split_once(':') else {
            return Err(format!(
                "verdict `{token}` is neither `accepts` nor `<class>:<name>`"
            ));
        };
        if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
            return Err(format!(
                "verdict `{token}` names `{name}`, not an identifier"
            ));
        }
        let name = name.to_string();
        Ok(match class {
            "Validation" => Self::Validation(name),
            "Completeness" => Self::Completeness(name),
            "Binary" => Self::Binary(name),
            "Census" => Self::Census(name),
            "Consumer" => Self::Consumer(name),
            other => {
                return Err(format!(
                    "verdict class `{other}` is not one of Validation, Completeness, Binary, \
                     Census, Consumer"
                ));
            }
        })
    }

    /// True for every verdict but [`Verdict::Accepts`].
    #[must_use]
    pub fn is_refusal(&self) -> bool {
        !matches!(self, Self::Accepts)
    }

    /// The variant / rule name a refusal names.
    #[must_use]
    pub fn name(&self) -> Option<&str> {
        match self {
            Self::Accepts => None,
            Self::Validation(n)
            | Self::Completeness(n)
            | Self::Binary(n)
            | Self::Census(n)
            | Self::Consumer(n) => Some(n),
        }
    }
}

impl fmt::Display for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Accepts => f.write_str("accepts"),
            Self::Validation(n) => write!(f, "Validation:{n}"),
            Self::Completeness(n) => write!(f, "Completeness:{n}"),
            Self::Binary(n) => write!(f, "Binary:{n}"),
            Self::Census(n) => write!(f, "Census:{n}"),
            Self::Consumer(n) => write!(f, "Consumer:{n}"),
        }
    }
}

/// One `<entry-point>=<verdict>` pair of a manifest row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expectation {
    /// The trust-ir entry point, as the manifest spells it
    /// (`validate_module`, `validate_module_for_codegen`, `deserialize_module`,
    /// `consumer`, ...). `tests/refuse_corpus.rs` owns the closed list.
    pub entry_point: String,
    /// What it returns.
    pub verdict: Verdict,
}

/// One parsed manifest row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ManifestRow {
    /// The row id (the fixture stem).
    pub id: String,
    /// What the row carries.
    pub carrier: Carrier,
    /// Every pinned verdict, in manifest order.
    pub expectations: Vec<Expectation>,
    /// The exact `TextLossKind` names the canonical printer reports.
    pub text_losses: Vec<String>,
    /// The file where the obligation's "consumer MUST" sentence lives.
    pub obligation: String,
    /// One sentence.
    pub why: String,
}

impl ManifestRow {
    /// The refusal verdicts of this row.
    pub fn refusals(&self) -> impl Iterator<Item = &Expectation> + '_ {
        self.expectations.iter().filter(|e| e.verdict.is_refusal())
    }

    /// True iff the row is an artifact a consumer must refuse (a `module` or
    /// `bytes` row). By construction every such row carries at least one
    /// refusal verdict; the manifest parser refuses one that does not.
    #[must_use]
    pub fn must_refuse(&self) -> bool {
        matches!(self.carrier, Carrier::Module | Carrier::Bytes)
    }

    /// True iff the row is a `control` row: an artifact a conforming consumer
    /// must ACCEPT.
    #[must_use]
    pub fn is_control(&self) -> bool {
        matches!(self.carrier, Carrier::Control)
    }

    /// True iff the row has bytes (`module`, `bytes` or `control`): every
    /// such row is one a consumer's test must dispatch.
    #[must_use]
    pub fn has_artifact(&self) -> bool {
        !matches!(self.carrier, Carrier::None)
    }
}

/// A manifest that does not parse. The corpus fails closed on it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ManifestError {
    /// 1-based line.
    pub line: usize,
    /// What is wrong.
    pub message: String,
}

impl fmt::Display for ManifestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "MANIFEST.tsv:{}: {}", self.line, self.message)
    }
}

impl std::error::Error for ManifestError {}

fn ident_ok(id: &str) -> bool {
    !id.is_empty()
        && id
            .chars()
            .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_')
}

/// Parse a manifest text. Refuses (fail closed): a missing or misspelt header,
/// a wrong column count, an unknown carrier, an unparsable verdict, a
/// `module`/`bytes` row with no refusal verdict, a `control` row with no
/// `accepts`, with a `Binary:` verdict, or whose `consumer` verdict is not
/// `accepts`, a `none` row with any verdict or loss, a duplicate id, an id
/// that is not `[a-z0-9_]+`, an obligation that is not a repo-rooted path.
pub fn parse_manifest(text: &str) -> Result<Vec<ManifestRow>, ManifestError> {
    let mut rows = Vec::new();
    let mut seen = BTreeSet::new();
    let mut header_seen = false;
    // Line numbers count from 1. `zip(1..)` is not used: `RangeFrom::next`
    // overflows at its end just as `index + 1` does. A `str` holds fewer than
    // `usize::MAX` lines, so the saturation never engages; it only states that
    // the numbering cannot panic.
    for (index, raw) in text.lines().enumerate() {
        let line = index.saturating_add(1);
        let err = |message: String| ManifestError { line, message };
        if raw.trim().is_empty() || raw.trim_start().starts_with('#') {
            continue;
        }
        let cells: Vec<&str> = raw.split('\t').map(str::trim).collect();
        if !header_seen {
            if cells != COLUMNS {
                return Err(err(format!(
                    "the first non-comment line must be the header `{}`, got `{}`",
                    COLUMNS.join("\\t"),
                    cells.join("\\t")
                )));
            }
            header_seen = true;
            continue;
        }
        let [
            id,
            carrier_cell,
            verdicts_cell,
            losses_cell,
            obligation_cell,
            why_cell,
        ] = cells.as_slice()
        else {
            return Err(err(format!(
                "expected {} tab-separated cells, got {}",
                COLUMNS.len(),
                cells.len()
            )));
        };
        let id = *id;
        if !ident_ok(id) {
            return Err(err(format!("row id `{id}` is not [a-z0-9_]+")));
        }
        if !seen.insert(id.to_string()) {
            return Err(err(format!("row `{id}` is listed twice")));
        }
        let carrier = match *carrier_cell {
            "module" => Carrier::Module,
            "bytes" => Carrier::Bytes,
            "control" => Carrier::Control,
            "none" => Carrier::None,
            other => {
                return Err(err(format!(
                    "carrier `{other}` is not one of module, bytes, control, none"
                )));
            }
        };
        let mut expectations = Vec::new();
        if *verdicts_cell != "-" {
            for pair in verdicts_cell.split(';') {
                let Some((entry_point, verdict)) = pair.split_once('=') else {
                    return Err(err(format!(
                        "verdict `{pair}` is not `<entry-point>=<verdict>`"
                    )));
                };
                if entry_point.is_empty() {
                    return Err(err(format!("verdict `{pair}` names no entry point")));
                }
                let verdict = Verdict::parse(verdict).map_err(err)?;
                expectations.push(Expectation {
                    entry_point: entry_point.to_string(),
                    verdict,
                });
            }
        }
        let text_losses: Vec<String> = if *losses_cell == "-" {
            Vec::new()
        } else {
            losses_cell
                .split(',')
                .map(|s| s.trim().to_string())
                .collect()
        };
        let obligation = obligation_cell.to_string();
        if !obligation.contains('/') || obligation.starts_with('/') || obligation.contains("..") {
            return Err(err(format!(
                "obligation `{obligation}` is not a repo-rooted relative path"
            )));
        }
        let why = why_cell.to_string();
        if why.is_empty() {
            return Err(err("`why` is empty".to_string()));
        }
        match carrier {
            Carrier::None => {
                if !expectations.is_empty() || !text_losses.is_empty() {
                    return Err(err(format!(
                        "a `none` row states no verdict and no loss (row `{id}`); it records an \
                         obligation the corpus cannot express"
                    )));
                }
            }
            Carrier::Control => {
                if !expectations
                    .iter()
                    .any(|e| matches!(e.verdict, Verdict::Accepts))
                {
                    return Err(err(format!(
                        "row `{id}` is a control row but pins no `accepts`: a control is an \
                         artifact a conforming consumer must accept"
                    )));
                }
                if let Some(e) = expectations.iter().find(|e| {
                    matches!(e.verdict, Verdict::Binary(_) | Verdict::Consumer(_))
                        || (e.entry_point == "consumer" && !matches!(e.verdict, Verdict::Accepts))
                }) {
                    return Err(err(format!(
                        "row `{id}` is a control row yet pins `{}={}`: a control decodes, and its \
                         `consumer` verdict is `accepts`",
                        e.entry_point, e.verdict
                    )));
                }
            }
            Carrier::Module | Carrier::Bytes => {
                if !expectations.iter().any(|e| e.verdict.is_refusal()) {
                    return Err(err(format!(
                        "row `{id}` carries an artifact but no refusal verdict: every artifact \
                         row is something a consumer must refuse"
                    )));
                }
                if carrier == Carrier::Bytes
                    && !expectations
                        .iter()
                        .all(|e| matches!(e.verdict, Verdict::Binary(_)))
                {
                    return Err(err(format!(
                        "row `{id}` is poisoned bytes: only `Binary:<variant>` verdicts apply"
                    )));
                }
            }
        }
        rows.push(ManifestRow {
            id: id.to_string(),
            carrier,
            expectations,
            text_losses,
            obligation,
            why,
        });
    }
    if !header_seen {
        return Err(ManifestError {
            line: 1,
            message: "empty manifest".to_string(),
        });
    }
    Ok(rows)
}

/// The compiled-in manifest, parsed.
///
/// # Errors
///
/// [`ManifestError`] when it does not parse: a corpus whose manifest is
/// broken must not run vacuously, and the caller's test decides how to fail.
pub fn manifest() -> Result<Vec<ManifestRow>, ManifestError> {
    parse_manifest(MANIFEST)
}

/// One row with its wire bytes and, for a `module` / `control` row, the
/// decoded module.
#[derive(Debug, Clone)]
pub struct Row {
    /// The manifest entry.
    pub manifest: ManifestRow,
    /// The checked-in bytes of `<row>.tmbc`.
    pub wire: Vec<u8>,
    /// The decoded module, `None` for a `bytes` row.
    pub module: Option<Module>,
    /// The header version the decoder reported, `None` for a `bytes` row.
    pub wire_version: Option<WireVersion>,
}

impl Row {
    /// The row id.
    #[must_use]
    pub fn id(&self) -> &str {
        &self.manifest.id
    }

    /// The decoded module (`None` for poisoned bytes: run your decoder on
    /// [`Self::wire_bytes`] instead).
    #[must_use]
    pub fn module(&self) -> Option<&Module> {
        self.module.as_ref()
    }

    /// The exact bytes a consumer would read from disk.
    #[must_use]
    pub fn wire_bytes(&self) -> &[u8] {
        &self.wire
    }

    /// True iff this is a `control` row: one the consumer must ACCEPT.
    #[must_use]
    pub fn is_control(&self) -> bool {
        self.manifest.is_control()
    }
}

/// Why a row could not be loaded. The corpus fails closed on it.
#[derive(Debug)]
pub enum CorpusError {
    /// The manifest does not parse.
    Manifest(ManifestError),
    /// A `module` / `bytes` row has no file.
    MissingFile { row: String, path: PathBuf },
    /// A `module` / `control` row's bytes do not decode.
    Undecodable { row: String, error: String },
    /// A `none` row has a file (it must not: nothing carries it).
    UnexpectedFile { row: String, path: PathBuf },
    /// The corpus is VACUOUS: it carries no `control` row or no must-refuse
    /// row, so a consumer run over it could pass without refusing anything
    /// (or without the control that makes a refusal attributable).
    Vacuous { controls: usize, must_refuse: usize },
}

impl fmt::Display for CorpusError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Manifest(e) => write!(f, "{e}"),
            Self::MissingFile { row, path } => {
                write!(f, "row `{row}`: missing {}", path.display())
            }
            Self::Undecodable { row, error } => {
                write!(f, "row `{row}`: its bytes do not decode: {error}")
            }
            Self::UnexpectedFile { row, path } => write!(
                f,
                "row `{row}` is a `none` row yet {} exists",
                path.display()
            ),
            Self::Vacuous {
                controls,
                must_refuse,
            } => write!(
                f,
                "the corpus is vacuous: {controls} control row(s) and {must_refuse} must-refuse \
                 row(s); a run needs at least one of each"
            ),
        }
    }
}

impl std::error::Error for CorpusError {}

/// The loaded artifact rows of a must-refuse corpus.
///
/// Minted only by [`corpus`] / [`corpus_from`], which refuse a vacuous
/// corpus; deliberately NOT `Default` — an empty corpus is a vacuous pass, not
/// a corpus. Derefs to the rows, so `Report::run(&rows, ..)`, `rows.iter()`
/// and `rows.len()` read as before.
#[derive(Debug, Clone)]
pub struct Corpus(Vec<Row>);

impl Deref for Corpus {
    type Target = [Row];

    fn deref(&self) -> &[Row] {
        &self.0
    }
}

impl<'a> IntoIterator for &'a Corpus {
    type Item = &'a Row;
    type IntoIter = std::slice::Iter<'a, Row>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl IntoIterator for Corpus {
    type Item = Row;
    type IntoIter = std::vec::IntoIter<Row>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl Corpus {
    /// The artifact rows (`module`, `bytes`, `control`) whose ids are NOT in
    /// `handled`. A consumer test that dispatches rows by name asserts this
    /// is empty, so a row added to the corpus fails that test by name
    /// instead of passing unseen.
    #[must_use]
    pub fn uncovered(&self, handled: &[&str]) -> Vec<&str> {
        self.0
            .iter()
            .map(Row::id)
            .filter(|id| !handled.contains(id))
            .collect()
    }
}

/// Load every artifact row (`module`, `bytes` and `control`) of the manifest
/// in `text` from `dir`. `none` rows are not returned (they carry nothing).
///
/// # Errors
///
/// [`CorpusError`]: the manifest does not parse, a row's file is missing,
/// undecodable or unexpected, or the corpus is VACUOUS (no `control` row or
/// no must-refuse row).
pub fn corpus_from(dir: &Path, text: &str) -> Result<Corpus, CorpusError> {
    let rows = parse_manifest(text).map_err(CorpusError::Manifest)?;
    let mut out = Vec::new();
    for manifest in rows {
        let path = dir.join(format!("{}.tmbc", manifest.id));
        match manifest.carrier {
            Carrier::None => {
                if path.exists() {
                    return Err(CorpusError::UnexpectedFile {
                        row: manifest.id,
                        path,
                    });
                }
                continue;
            }
            Carrier::Module | Carrier::Bytes | Carrier::Control => {}
        }
        let wire = fs::read(&path).map_err(|_| CorpusError::MissingFile {
            row: manifest.id.clone(),
            path: path.clone(),
        })?;
        let (module, wire_version) = match manifest.carrier {
            Carrier::Module | Carrier::Control => {
                let (module, version) =
                    deserialize_module_with_wire_version(&wire).map_err(|e| {
                        CorpusError::Undecodable {
                            row: manifest.id.clone(),
                            error: e.to_string(),
                        }
                    })?;
                (Some(module), Some(version))
            }
            _ => (None, None),
        };
        out.push(Row {
            manifest,
            wire,
            module,
            wire_version,
        });
    }
    let controls = out.iter().filter(|row| row.is_control()).count();
    let must_refuse = out.iter().filter(|row| row.manifest.must_refuse()).count();
    if controls == 0 || must_refuse == 0 {
        return Err(CorpusError::Vacuous {
            controls,
            must_refuse,
        });
    }
    Ok(Corpus(out))
}

/// Every artifact row of the corpus, decoded from the checked-in bytes.
///
/// # Errors
///
/// [`CorpusError`] (fail closed) when a row is missing or does not decode, or
/// the corpus is vacuous: a consumer must never pass over an empty or
/// half-loaded corpus. Its test decides how to fail.
pub fn corpus() -> Result<Corpus, CorpusError> {
    corpus_from(&fixtures_dir(), MANIFEST)
}

/// What a consumer's admission did with one row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// The consumer refused it, with its own message.
    Refused { message: String },
    /// The consumer accepted it. For a must-refuse row this is the finding
    /// the corpus exists to surface; for a `control` row it is required.
    Accepted,
}

/// Per-row outcomes of one consumer run over the corpus.
#[derive(Debug, Clone, Default)]
pub struct Report {
    entries: Vec<(String, Outcome)>,
}

impl Report {
    /// Run `admit` over every row. `admit` is the consumer's OWN admission
    /// (decode + validate + lower, whatever it does before it would emit
    /// code); `Ok(())` means the consumer would proceed with the row.
    pub fn run<E: fmt::Display>(
        rows: &[Row],
        mut admit: impl FnMut(&Row) -> Result<(), E>,
    ) -> Self {
        let mut report = Self::default();
        for row in rows {
            let outcome = match admit(row) {
                Ok(()) => Outcome::Accepted,
                Err(e) => Outcome::Refused {
                    message: e.to_string(),
                },
            };
            report.entries.push((row.id().to_string(), outcome));
        }
        report
    }

    /// Every outcome, in corpus order.
    #[must_use]
    pub fn outcomes(&self) -> &[(String, Outcome)] {
        &self.entries
    }

    /// Ids of the must-refuse rows of `rows` this consumer ACCEPTED: the
    /// finding the corpus exists to surface.
    #[must_use]
    pub fn must_refuse_accepted<'a>(&self, rows: &'a [Row]) -> Vec<&'a str> {
        rows.iter()
            .filter(|row| row.manifest.must_refuse())
            .map(Row::id)
            .filter(|id| self.outcome(id) == Some(&Outcome::Accepted))
            .collect()
    }

    /// Ids of the `control` rows of `rows` this consumer REFUSED. While one
    /// is refused, no refusal in this report is attributable to a row's
    /// subject (module docs: the runner is reason-blind).
    #[must_use]
    pub fn controls_refused<'a>(&self, rows: &'a [Row]) -> Vec<&'a str> {
        rows.iter()
            .filter(|row| row.is_control())
            .map(Row::id)
            .filter(|id| matches!(self.outcome(id), Some(Outcome::Refused { .. })))
            .collect()
    }

    /// The outcome recorded for `id`, if it was dispatched.
    #[must_use]
    pub fn outcome(&self, id: &str) -> Option<&Outcome> {
        self.entries
            .iter()
            .find(|(row, _)| row == id)
            .map(|(_, o)| o)
    }

    /// Ids the consumer ACCEPTED, control rows included (see
    /// [`Self::must_refuse_accepted`] for the finding).
    #[must_use]
    pub fn accepted(&self) -> Vec<&str> {
        self.entries
            .iter()
            .filter(|(_, o)| matches!(o, Outcome::Accepted))
            .map(|(id, _)| id.as_str())
            .collect()
    }

    /// Ids the consumer refused.
    #[must_use]
    pub fn refused(&self) -> Vec<&str> {
        self.entries
            .iter()
            .filter(|(_, o)| matches!(o, Outcome::Refused { .. }))
            .map(|(id, _)| id.as_str())
            .collect()
    }

    /// The consumer's message for a refused row.
    #[must_use]
    pub fn message(&self, id: &str) -> Option<&str> {
        self.entries.iter().find_map(|(row, o)| match o {
            Outcome::Refused { message } if row == id => Some(message.as_str()),
            _ => None,
        })
    }

    /// Rows of `rows` this report has no outcome for.
    #[must_use]
    pub fn uncovered<'a>(&self, rows: &'a [Row]) -> Vec<&'a str> {
        rows.iter()
            .map(Row::id)
            .filter(|id| !self.entries.iter().any(|(row, _)| row == id))
            .collect()
    }

    /// `Ok` iff every must-refuse row of `rows` was refused, every `control`
    /// row was ACCEPTED, and every row was dispatched; otherwise the findings,
    /// naming each offender. The consumer's test calls this once and fails on
    /// `Err` (its own assertion — the library never panics for it).
    ///
    /// # Errors
    ///
    /// [`CorpusFindings`] naming every accepted must-refuse row, refused
    /// control row and undispatched row.
    pub fn check(&self, rows: &[Row]) -> Result<(), CorpusFindings> {
        let findings = CorpusFindings {
            accepted: owned(self.must_refuse_accepted(rows)),
            controls_refused: owned(self.controls_refused(rows)),
            undispatched: owned(self.uncovered(rows)),
        };
        if findings.accepted.is_empty()
            && findings.controls_refused.is_empty()
            && findings.undispatched.is_empty()
        {
            Ok(())
        } else {
            Err(findings)
        }
    }
}

fn owned(ids: Vec<&str>) -> Vec<String> {
    ids.into_iter().map(str::to_string).collect()
}

/// Why a consumer run over the corpus does not pass ([`Report::check`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CorpusFindings {
    /// Must-refuse rows the consumer ACCEPTED.
    pub accepted: Vec<String>,
    /// Control rows the consumer REFUSED.
    pub controls_refused: Vec<String>,
    /// Rows the report has no outcome for.
    pub undispatched: Vec<String>,
}

impl fmt::Display for CorpusFindings {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "must-refuse corpus: {} row(s) ACCEPTED {:?}; {} control row(s) REFUSED {:?}; {} \
             row(s) not dispatched {:?}. Each accepted row is a module or byte string this \
             consumer compiled although trust-ir names it as one to refuse (MANIFEST.tsv says \
             why); disclose it by name in the consumer's own ledger or refuse it — never drop \
             the row here. A refused control row is the envelope every module row shares (the \
             identity function under `{}` on the canonical target) with no subject: while it \
             is refused, no refusal in this report is attributable to a row's subject. \
             Recognize that authority for this run (a test-time decision that licenses nothing \
             in production), or find what else this consumer refuses in it.",
            self.accepted.len(),
            self.accepted,
            self.controls_refused.len(),
            self.controls_refused,
            self.undispatched.len(),
            self.undispatched,
            STRUCTURAL_LICENSE_AUTHORITY
        )
    }
}

impl std::error::Error for CorpusFindings {}

#[cfg(test)]
mod tests {
    use super::*;

    const HEADER: &str = "row\tcarrier\tverdicts\ttext_losses\tobligation\twhy\n";

    fn parse(body: &str) -> Result<Vec<ManifestRow>, ManifestError> {
        parse_manifest(&format!("# c\n{HEADER}{body}"))
    }

    #[test]
    fn a_two_verdict_row_parses_with_both_verdicts() {
        let rows = parse(
            "body_gate_ungated\tmodule\tvalidate_module=accepts;validate_module_for_codegen=Validation:UngatedBodyForCodegen\t-\tcrates/trust-ir/src/lib.rs\tan affirmative no-gate claim\n",
        )
        .unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].carrier, Carrier::Module);
        assert_eq!(rows[0].expectations.len(), 2);
        assert_eq!(rows[0].expectations[0].verdict, Verdict::Accepts);
        assert_eq!(
            rows[0].expectations[1].verdict,
            Verdict::Validation("UngatedBodyForCodegen".into())
        );
        assert!(rows[0].must_refuse());
        assert_eq!(rows[0].refusals().count(), 1);
    }

    #[test]
    fn a_refusal_names_the_one_based_line_it_read() {
        // `# c` is line 1, the header line 2, the bad row line 3.
        let e = parse("x\tmodule\tvalidate_module=accepts\t-\tdocs/a.md\twhy\n").unwrap_err();
        assert_eq!(e.line, 3, "{e}");
        let e = parse_manifest("not the header\n").unwrap_err();
        assert_eq!(e.line, 1, "{e}");
    }

    #[test]
    fn an_artifact_row_without_a_refusal_is_refused() {
        let e = parse("x\tmodule\tvalidate_module=accepts\t-\tdocs/a.md\twhy\n").unwrap_err();
        assert!(e.message.contains("no refusal verdict"), "{e}");
    }

    #[test]
    fn a_control_row_pins_accepts_and_never_a_refusal_at_the_consumer() {
        let ok = parse(
            "c\tcontrol\tvalidate_module=accepts;validate_module_for_codegen:recognizing_clean_kernel_tv=Validation:UnrecognizedGateAuthority;consumer=accepts\t-\tdocs/a.md\twhy\n",
        )
        .unwrap();
        assert!(ok[0].is_control() && ok[0].has_artifact() && !ok[0].must_refuse());
        let e =
            parse("c\tcontrol\tvalidate_module=Validation:Foo\t-\tdocs/a.md\twhy\n").unwrap_err();
        assert!(e.message.contains("pins no `accepts`"), "{e}");
        let e =
            parse("c\tcontrol\tvalidate_module=accepts;consumer=Consumer:r\t-\tdocs/a.md\twhy\n")
                .unwrap_err();
        assert!(
            e.message.contains("its `consumer` verdict is `accepts`"),
            "{e}"
        );
        let e = parse(
            "c\tcontrol\tvalidate_module=accepts;deserialize_module=Binary:InvalidMagic\t-\tdocs/a.md\twhy\n",
        )
        .unwrap_err();
        assert!(e.message.contains("a control decodes"), "{e}");
        assert!(parse("c\tcontrol\t-\t-\tdocs/a.md\twhy\n").is_err());
    }

    #[test]
    fn a_none_row_carries_nothing_and_a_bytes_row_only_binary_verdicts() {
        assert!(parse("x\tnone\t-\t-\tdocs/a.md\twhy\n").is_ok());
        let e = parse("x\tnone\tconsumer=Consumer:r\t-\tdocs/a.md\twhy\n").unwrap_err();
        assert!(e.message.contains("states no verdict"), "{e}");
        let e =
            parse("x\tbytes\tdeserialize_module=Validation:Foo\t-\tdocs/a.md\twhy\n").unwrap_err();
        assert!(e.message.contains("poisoned bytes"), "{e}");
        assert!(
            parse("x\tbytes\tdeserialize_module=Binary:InvalidMagic\t-\tdocs/a.md\twhy\n").is_ok()
        );
    }

    #[test]
    fn the_header_the_id_shape_the_verdict_grammar_and_duplicates_are_checked() {
        assert!(parse_manifest("x\tmodule\t-\t-\ta/b\tw\n").is_err());
        assert!(parse("Bad-Id\tnone\t-\t-\tdocs/a.md\twhy\n").is_err());
        assert!(parse("x\tmodule\tvalidate_module=Refuses:Foo\t-\tdocs/a.md\twhy\n").is_err());
        assert!(parse("x\tmodule\tvalidate_module\t-\tdocs/a.md\twhy\n").is_err());
        assert!(parse("x\tmodule\t=Validation:Foo\t-\tdocs/a.md\twhy\n").is_err());
        assert!(parse("x\tnone\t-\t-\tnot-a-path\twhy\n").is_err());
        assert!(parse("x\tnone\t-\t-\tdocs/a.md\twhy\nx\tnone\t-\t-\tdocs/a.md\twhy\n").is_err());
        assert!(parse("x\tnone\t-\t-\tdocs/a.md\t\n").is_err());
    }

    #[test]
    fn verdict_names_round_trip_through_display() {
        for token in [
            "accepts",
            "Validation:UngatedBodyForCodegen",
            "Completeness:IncompletenessUnclaimed",
            "Binary:InvalidMagic",
            "Census:Trusted",
            "Consumer:struct_passing_unclassified",
        ] {
            assert_eq!(Verdict::parse(token).unwrap().to_string(), token);
        }
    }

    #[test]
    fn the_compiled_in_manifest_parses_and_is_not_empty() {
        let rows = manifest().expect("the compiled-in manifest parses");
        assert!(rows.iter().any(|r| r.carrier == Carrier::Module));
        assert!(rows.iter().any(|r| r.carrier == Carrier::Bytes));
        assert!(rows.iter().any(|r| r.carrier == Carrier::Control));
        assert!(rows.iter().any(|r| r.carrier == Carrier::None));
    }

    /// r11 item 7 (evidence kind ii: the surface is new). On origin/main a
    /// manifest with no artifact row loaded as `Ok(vec![])` — a corpus a
    /// consumer could "pass" by refusing nothing. Now it is a typed refusal,
    /// and so is a corpus with no control row. Mutation check: letting
    /// `corpus_from` accept zero rows turns this red.
    #[test]
    fn a_vacuous_manifest_is_a_typed_error() {
        let dir = fixtures_dir();
        let only_none = format!("{HEADER}x\tnone\t-\t-\tdocs/a.md\twhy\n");
        assert!(matches!(
            corpus_from(&dir, &only_none),
            Err(CorpusError::Vacuous {
                controls: 0,
                must_refuse: 0
            })
        ));
        let rows = parse_manifest(MANIFEST).expect("the compiled-in manifest parses");
        let without_control: String = MANIFEST
            .lines()
            .filter(|line| {
                !rows
                    .iter()
                    .any(|row| row.is_control() && line.starts_with(&format!("{}\t", row.id)))
            })
            .map(|line| format!("{line}\n"))
            .collect();
        assert!(matches!(
            corpus_from(&dir, &without_control),
            Err(CorpusError::Vacuous { controls: 0, .. })
        ));
    }

    /// `Report::check` names every offender and is `Ok` only for a clean
    /// run; its `Display` is the message `assert_every_row_refused` used to
    /// panic with.
    #[test]
    fn check_names_every_offender() {
        let rows = corpus().expect("the must-refuse corpus loads");
        let report = Report::run(&rows[..1], |_| Ok::<(), String>(()));
        let findings = report
            .check(&rows)
            .expect_err("one accepted, the rest undispatched");
        assert_eq!(findings.undispatched.len(), rows.len() - 1);
        assert!(findings.to_string().contains("not dispatched"));
    }

    #[test]
    fn a_report_names_accepted_refused_controls_and_undispatched_rows() {
        let rows = corpus().expect("the must-refuse corpus loads");
        assert!(!rows.is_empty());
        let controls = rows.iter().filter(|r| r.is_control()).count();
        assert!(controls > 0, "the corpus carries a control row");
        // Refuse every artifact, accept the control: green.
        let report = Report::run(&rows, |row| {
            if row.is_control() {
                Ok(())
            } else {
                Err("refused")
            }
        });
        assert_eq!(report.must_refuse_accepted(&rows), Vec::<&str>::new());
        assert_eq!(report.controls_refused(&rows), Vec::<&str>::new());
        assert_eq!(report.accepted().len(), controls);
        assert_eq!(report.refused().len(), rows.len() - controls);
        assert_eq!(report.check(&rows), Ok(()));
        // Refuse EVERYTHING (the reason-blind trap): the control is named.
        let report = Report::run(&rows, |_| Err::<(), _>("unsupported"));
        assert_eq!(report.accepted(), Vec::<&str>::new());
        assert_eq!(report.message(rows[0].id()), Some("unsupported"));
        assert_eq!(report.controls_refused(&rows).len(), controls);
        let text = report
            .check(&rows)
            .expect_err("the control is refused")
            .to_string();
        assert!(
            text.contains("control row(s) REFUSED") && text.contains("control_licensed_identity"),
            "{text}"
        );
        assert!(text.contains(STRUCTURAL_LICENSE_AUTHORITY), "{text}");
        // Accept everything: every must-refuse row is named, no control is.
        let report = Report::run(&rows, |_| Ok::<(), String>(()));
        assert_eq!(report.accepted().len(), rows.len());
        assert_eq!(
            report.must_refuse_accepted(&rows).len(),
            rows.len() - controls
        );
        assert_eq!(report.controls_refused(&rows), Vec::<&str>::new());
        let text = report
            .check(&rows)
            .expect_err("rows were accepted")
            .to_string();
        assert!(
            text.contains("ACCEPTED") && !text.contains("control_licensed_identity"),
            "{text}"
        );
        // A half-run report names what it skipped.
        let report = Report::run(&rows[..1], |_| Err::<(), _>("r"));
        assert_eq!(report.uncovered(&rows).len(), rows.len() - 1);
        let handled: Vec<&str> = rows.iter().map(Row::id).collect();
        assert!(rows.uncovered(&handled).is_empty());
        assert_eq!(rows.uncovered(&[]).len(), rows.len());
    }
}
