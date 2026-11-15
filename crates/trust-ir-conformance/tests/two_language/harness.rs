//! The two-language ratchet harness (roadmap increment WS8.6).
//!
//! This file has no trust-ir dependency on purpose: the conformance area
//! targets (`two_language_b0` .. `two_language_b7`) reach it through
//! `common.rs`, and `trust-ir-cli`'s `two_language_cli` target includes it by
//! `#[path]`, so both crates check their rows against the ONE ledger,
//! `RATCHETS.tsv`, which sits next to this file.
//!
//! What it fixes relative to the archived 2026-09-17 Part B battery
//! (`reports/2026-09-17-two-language-proof-program/partb/tests/common/mod.rs`):
//!
//! * **Verdicts are data, not a grep.** Every row is recorded as
//!   `(id, verdict, detail)` and written by the harness itself to
//!   `$CARGO_TARGET_TMPDIR/two_language/<target>.tsv`. The archived harness
//!   printed `FEATURE` lines and relied on a `^FEATURE` grep, which lost the
//!   first row of every test under `--nocapture` (libtest prints it on the
//!   `test <name> ...` header line).
//! * **A GAP row states its expected OUTCOME.** `feature_gap` takes an
//!   [`Expect`] (the wrong acceptance a gap records, an exact refusal
//!   variant with its payload predicate and follow-ons, or an exact
//!   measurement) and the observed [`Outcome`]. ANY change fails the row: an
//!   acceptance becoming a refusal (the fix, which is the flip) and one
//!   refusal becoming another alike. The archived `feature_gap(id, bool, ..)`
//!   could stay silently GAP after the gap changed shape.
//! * **The ledger is a bijection.** Every row a target emits must appear
//!   exactly once in `RATCHETS.tsv` with the same verdict and that target, and
//!   every ledger row owned by the target must be emitted. Flipping a row
//!   therefore means editing the ledger in the fixing commit.
#![allow(dead_code)]

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;
use std::panic::{AssertUnwindSafe, catch_unwind};

/// The ledger every target checks itself against.
pub const LEDGER: &str = include_str!("RATCHETS.tsv");

// ---------------------------------------------------------------------------
// Verdicts
// ---------------------------------------------------------------------------

/// `Pass` = the format does what the design needs, with a right-reason
/// negative twin. `Gap` = a RATCHET: the gap is present today, in exactly the
/// recorded shape. `RatifiedOut` = a former gap the spec now RATIFIES as the
/// intended behaviour (e.g. the panic=abort unwind projection,
/// `docs/ub-numerics-policy.md` §4): not a defect and not a format capability,
/// so it is in neither the PASS nor the GAP count, but it is still held in its
/// exact recorded shape, so a change of behaviour trips it like a gap. `Fail`
/// = a PASS row that no longer holds, or a GAP / RATIFIED-OUT row whose
/// outcome changed ("ratchet tripped").
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Verdict {
    Pass,
    Gap,
    RatifiedOut,
    Fail,
}

#[allow(unused_imports)]
pub use Verdict::{Fail as FAIL, Gap as GAP, Pass as PASS, RatifiedOut as RATIFIED_OUT};

impl Verdict {
    pub fn token(self) -> &'static str {
        match self {
            Verdict::Pass => "PASS",
            Verdict::Gap => "GAP",
            Verdict::RatifiedOut => "RATIFIED-OUT",
            Verdict::Fail => "FAIL",
        }
    }

    pub fn parse(token: &str) -> Option<Self> {
        match token {
            "PASS" => Some(Verdict::Pass),
            "GAP" => Some(Verdict::Gap),
            "RATIFIED-OUT" => Some(Verdict::RatifiedOut),
            _ => None,
        }
    }
}

/// One emitted row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Row {
    pub id: String,
    pub verdict: Verdict,
    pub detail: String,
}

thread_local! {
    /// The rows of the case running on this thread (`None` outside a case).
    static ROWS: RefCell<Option<Vec<Row>>> = const { RefCell::new(None) };
}

fn one_line(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Record a row. Outside a case (a row emitted from a helper thread, or a
/// harness self-test) the row is recorded nowhere and the caller's return
/// value is all that counts.
pub fn feature(id: &str, verdict: Verdict, detail: &str) {
    let row = Row {
        id: id.split_whitespace().collect::<Vec<_>>().join("_"),
        verdict,
        detail: one_line(detail),
    };
    ROWS.with(|rows| {
        if let Some(rows) = rows.borrow_mut().as_mut() {
            rows.push(row);
        }
    });
}

/// A PASS row: `ok` true records PASS, false records FAIL. Returns `ok` so the
/// call site can `assert!` on it after the row is recorded.
pub fn feature_check(id: &str, ok: bool, detail: &str) -> bool {
    feature(id, if ok { Verdict::Pass } else { Verdict::Fail }, detail);
    ok
}

/// A GAP ratchet: records GAP when `observed` matches `expected` exactly, and
/// FAIL ("ratchet tripped") otherwise. Returns whether it matched.
pub fn feature_gap(id: &str, expected: Expect, observed: Outcome, detail: &str) -> bool {
    held_exactly(id, Verdict::Gap, expected, observed, detail)
}

/// A RATIFIED-OUT row: the recorded behaviour is the one the spec ratified
/// (cite the ratification at the call site). Held exactly like a gap: records
/// RATIFIED-OUT when `observed` matches `expected`, FAIL otherwise.
pub fn feature_ratified(id: &str, expected: Expect, observed: Outcome, detail: &str) -> bool {
    held_exactly(id, Verdict::RatifiedOut, expected, observed, detail)
}

fn held_exactly(
    id: &str,
    verdict: Verdict,
    expected: Expect,
    observed: Outcome,
    detail: &str,
) -> bool {
    match expected.check(&observed) {
        Ok(()) => {
            feature(id, verdict, detail);
            true
        }
        Err(why) => {
            feature(
                id,
                Verdict::Fail,
                &format!(
                    "RATCHET TRIPPED ({why}); expected {expected:?}, observed {observed:?}. \
                     If trust-ir closed this gap, flip the row to PASS with a negative twin and \
                     edit RATCHETS.tsv in the same commit (a ratified behaviour that changed \
                     needs the ratification amended first). {detail}"
                ),
            );
            false
        }
    }
}

// ---------------------------------------------------------------------------
// Outcomes
// ---------------------------------------------------------------------------

/// The leading identifier of a `Debug` rendering: the enum variant name of
/// `ValidationError::Foo { .. }` / `ParseError::Bar(..)`, or the error-code
/// prefix of an interpreter message (`MissingBlock: ...`).
pub fn variant_name(rendered: &str) -> String {
    rendered
        .trim_start_matches('"')
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect()
}

/// One refusal: its variant and its full `Debug` rendering (the payload).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Refusal {
    pub variant: String,
    pub rendered: String,
}

impl Refusal {
    pub fn of<E: Debug>(error: &E) -> Self {
        Self::from_rendered(format!("{error:?}"))
    }

    pub fn from_rendered(rendered: String) -> Self {
        Refusal {
            variant: variant_name(&rendered),
            rendered,
        }
    }
}

/// What a measurement observed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// No refusal: the validator / decoder / entry point accepted.
    Accepted,
    /// Refused, with every refusal in the order reported.
    Refused(Vec<Refusal>),
    /// A measurement that is not an accept/refuse verdict, rendered exactly.
    Measured(String),
}

impl Outcome {
    /// An error list: empty = `Accepted`.
    pub fn of<E: Debug>(errors: &[E]) -> Self {
        if errors.is_empty() {
            Outcome::Accepted
        } else {
            Outcome::Refused(errors.iter().map(Refusal::of).collect())
        }
    }

    /// A `Result`: `Ok` = `Accepted`, `Err(e)` = one refusal.
    pub fn of_result<T, E: Debug>(result: &Result<T, E>) -> Self {
        match result {
            Ok(_) => Outcome::Accepted,
            Err(e) => Outcome::Refused(vec![Refusal::of(e)]),
        }
    }

    /// An interpreter / CLI message (`"Code: message"`): one refusal whose
    /// variant is the leading code.
    pub fn of_message<T>(result: &Result<T, String>) -> Self {
        match result {
            Ok(_) => Outcome::Accepted,
            Err(message) => Outcome::Refused(vec![Refusal::from_rendered(message.clone())]),
        }
    }

    pub fn measured(text: impl Into<String>) -> Self {
        Outcome::Measured(text.into())
    }

    /// Several single-change mutants measured as ONE row: `Accepted` only when
    /// EVERY mutant was accepted, `Refused` (every refusal, in order) only when
    /// EVERY mutant was refused. A MIXED set is a [`Outcome::Measured`] naming
    /// each mutant's outcome, which no expectation can equal: pooling it would
    /// let one mutant start being accepted while another gains a second refusal
    /// of the same variant, leaving the refusal multiset (and so the row)
    /// unchanged although the gap moved.
    pub fn all<I: IntoIterator<Item = Outcome>>(outcomes: I) -> Self {
        let outcomes: Vec<Outcome> = outcomes.into_iter().collect();
        if let Some(measured) = outcomes.iter().find(|o| matches!(o, Outcome::Measured(_))) {
            return measured.clone();
        }
        let accepted = outcomes
            .iter()
            .filter(|o| matches!(o, Outcome::Accepted))
            .count();
        if accepted == outcomes.len() {
            return Outcome::Accepted;
        }
        if accepted > 0 {
            return Outcome::Measured(format!(
                "mixed mutant outcomes (accepted and refused): {outcomes:?}"
            ));
        }
        Outcome::Refused(
            outcomes
                .into_iter()
                .flat_map(|o| match o {
                    Outcome::Refused(r) => r,
                    _ => Vec::new(),
                })
                .collect(),
        )
    }

    /// The facts a gap row rests on besides the primary outcome (the baseline
    /// still validates, the interpreter still returns the wrong value, ...).
    /// Any fact that no longer holds turns the outcome into a measurement that
    /// can never equal the expectation, so the row trips.
    pub fn given(self, facts: &[(&str, bool)]) -> Self {
        let broken: Vec<&str> = facts
            .iter()
            .filter(|(_, ok)| !ok)
            .map(|(name, _)| *name)
            .collect();
        if broken.is_empty() {
            self
        } else {
            Outcome::Measured(format!(
                "fact(s) no longer hold: {broken:?}; primary outcome was {self:?}"
            ))
        }
    }
}

/// The outcome a GAP row records.
pub enum Expect {
    /// The wrong acceptance most GAP rows record (an exact `Ok` / empty list).
    Accepted,
    /// A refusal: exactly one `primary` whose rendering satisfies `payload`,
    /// plus EXACTLY the listed `follow_ons` (a multiset; order-free).
    Refused {
        primary: &'static str,
        payload: Box<dyn Fn(&str) -> bool>,
        payload_text: String,
        follow_ons: Vec<&'static str>,
    },
    /// An exact measurement.
    Measured(String),
}

impl Debug for Expect {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expect::Accepted => write!(f, "Accepted"),
            Expect::Refused {
                primary,
                payload_text,
                follow_ons,
                ..
            } => write!(
                f,
                "Refused({primary} where {payload_text}; follow-ons {follow_ons:?})"
            ),
            Expect::Measured(text) => write!(f, "Measured({text:?})"),
        }
    }
}

impl Expect {
    /// Exactly one refusal of `primary`, any payload, no follow-ons.
    pub fn refused(primary: &'static str) -> Self {
        Expect::Refused {
            primary,
            payload: Box::new(|_| true),
            payload_text: "any payload".to_string(),
            follow_ons: Vec::new(),
        }
    }

    /// Exactly one refusal of `primary` whose `Debug` rendering contains every
    /// `needle`, no follow-ons.
    pub fn refused_with(primary: &'static str, needles: &[&str]) -> Self {
        let owned: Vec<String> = needles.iter().map(|n| (*n).to_string()).collect();
        let payload_text = format!("payload contains {owned:?}");
        Expect::Refused {
            primary,
            payload: Box::new(move |rendered| owned.iter().all(|n| rendered.contains(n.as_str()))),
            payload_text,
            follow_ons: Vec::new(),
        }
    }

    /// Exactly `n` refusals, all of `primary` (one edit that trips the same
    /// rule at `n` sites); at least one rendering contains every `needle`.
    pub fn refused_times(primary: &'static str, n: usize, needles: &[&str]) -> Self {
        let mut expect = Self::refused_with(primary, needles);
        if let Expect::Refused { follow_ons, .. } = &mut expect {
            follow_ons.extend(std::iter::repeat_n(primary, n.saturating_sub(1)));
        }
        expect
    }

    /// Add the refusals one edit legitimately produces beside the primary.
    pub fn with_follow_ons(mut self, extra: &[&'static str]) -> Self {
        if let Expect::Refused { follow_ons, .. } = &mut self {
            follow_ons.extend_from_slice(extra);
        }
        self
    }

    pub fn measured(text: impl Into<String>) -> Self {
        Expect::Measured(text.into())
    }

    /// `Ok` iff `observed` is exactly this expectation.
    pub fn check(&self, observed: &Outcome) -> Result<(), String> {
        match (self, observed) {
            (Expect::Accepted, Outcome::Accepted) => Ok(()),
            (Expect::Measured(want), Outcome::Measured(got)) if want == got => Ok(()),
            (
                Expect::Refused {
                    primary,
                    payload,
                    follow_ons,
                    ..
                },
                Outcome::Refused(refusals),
            ) => {
                let mut want: Vec<&str> = follow_ons.clone();
                want.push(primary);
                want.sort_unstable();
                let mut got: Vec<&str> = refusals.iter().map(|r| r.variant.as_str()).collect();
                got.sort_unstable();
                if want != got {
                    return Err(format!(
                        "refusal variants changed: want {want:?}, got {got:?}"
                    ));
                }
                if refusals
                    .iter()
                    .any(|r| r.variant == *primary && payload(&r.rendered))
                {
                    Ok(())
                } else {
                    Err(format!(
                        "the {primary} refusal no longer carries the recorded payload"
                    ))
                }
            }
            (want, got) => Err(format!("outcome kind changed: want {want:?}, got {got:?}")),
        }
    }
}

// ---------------------------------------------------------------------------
// The ledger
// ---------------------------------------------------------------------------

/// One `RATCHETS.tsv` line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LedgerRow {
    pub id: String,
    pub verdict: String,
    pub column: String,
    pub finding: String,
    pub closing_increment: String,
    pub producer_reachable: String,
    pub target: String,
}

/// Parse the ledger. `#` lines are comments; every other line has exactly
/// seven tab-separated fields. A malformed line is returned as an error.
pub fn parse_ledger(text: &str) -> Result<Vec<LedgerRow>, String> {
    let mut rows = Vec::new();
    for (index, line) in text.lines().enumerate() {
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        let fields: Vec<&str> = line.split('\t').collect();
        let [id, verdict, column, finding, closing, reachable, target] = fields.as_slice() else {
            return Err(format!(
                "RATCHETS.tsv:{}: expected 7 tab-separated fields, got {}",
                index + 1,
                fields.len()
            ));
        };
        rows.push(LedgerRow {
            id: (*id).to_string(),
            verdict: (*verdict).to_string(),
            column: (*column).to_string(),
            finding: (*finding).to_string(),
            closing_increment: (*closing).to_string(),
            producer_reachable: (*reachable).to_string(),
            target: (*target).to_string(),
        });
    }
    Ok(rows)
}

/// The bijection between what `target` emitted and what the ledger assigns to
/// it. Returns every problem found (empty = consistent).
pub fn ledger_problems(ledger: &str, target: &str, emitted: &[Row]) -> Vec<String> {
    let rows = match parse_ledger(ledger) {
        Ok(rows) => rows,
        Err(e) => return vec![e],
    };
    let mut problems = Vec::new();
    let mut by_id: BTreeMap<&str, Vec<&LedgerRow>> = BTreeMap::new();
    for row in &rows {
        by_id.entry(row.id.as_str()).or_default().push(row);
    }
    for (id, lines) in &by_id {
        if lines.len() > 1 {
            problems.push(format!("ledger lists {id} {} times", lines.len()));
        }
    }
    let mut seen: BTreeMap<&str, usize> = BTreeMap::new();
    for row in emitted {
        *seen.entry(row.id.as_str()).or_default() += 1;
    }
    for (id, count) in &seen {
        if *count > 1 {
            problems.push(format!("{target} emitted {id} {count} times"));
        }
    }
    for row in emitted {
        match by_id.get(row.id.as_str()).and_then(|lines| lines.first()) {
            None => problems.push(format!(
                "{target} emitted {} ({}), which RATCHETS.tsv does not list",
                row.id,
                row.verdict.token()
            )),
            Some(line) => {
                if line.target != target {
                    problems.push(format!(
                        "{} is emitted by {target} but the ledger assigns it to {}",
                        row.id, line.target
                    ));
                }
                if row.verdict != Verdict::Fail
                    && Verdict::parse(&line.verdict) != Some(row.verdict)
                {
                    problems.push(format!(
                        "{} emitted {} but the ledger records {}: edit RATCHETS.tsv in the commit that changes the verdict",
                        row.id,
                        row.verdict.token(),
                        line.verdict
                    ));
                }
            }
        }
    }
    let emitted_ids: BTreeSet<&str> = emitted.iter().map(|r| r.id.as_str()).collect();
    for line in rows.iter().filter(|l| l.target == target) {
        if !emitted_ids.contains(line.id.as_str()) {
            problems.push(format!(
                "ledger row {} ({}) is assigned to {target} but was not emitted",
                line.id, line.verdict
            ));
        }
    }
    problems
}

// ---------------------------------------------------------------------------
// The runner
// ---------------------------------------------------------------------------

/// One case of a target: a named function that records rows.
pub type Case = (&'static str, fn());

/// Stack for a case thread: validation and the in-process kernel recurse.
const CASE_STACK_BYTES: usize = 64 * 1024 * 1024;

fn panic_text(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "non-string panic payload".to_string()
    }
}

/// The ledger target token a two-language Cargo test target checks (its
/// `CARGO_CRATE_NAME`): `two_language_bN` -> `bN`, `two_language_field_ratchets`
/// -> `field`, `two_language_cli` -> `cli`. `None` for anything else (the
/// harness self-test target emits no rows).
pub fn target_token(crate_name: &str) -> Option<&str> {
    match crate_name.strip_prefix("two_language_")? {
        "field_ratchets" => Some("field"),
        "harness" | "" => None,
        other => Some(other),
    }
}

/// `None` when the Cargo test target `crate_name` may check `target`'s rows;
/// otherwise why not. The token is bound to the target NAME because the ledger
/// is checked per target, inside the target: if two `[[test]]` entries pointed
/// at the same source file (a copy-paste `path` in the manifest), the file's
/// rows would be checked twice and the other target's rows never, with the
/// gate green.
pub fn target_mismatch(crate_name: &str, target: &str) -> Option<String> {
    match target_token(crate_name) {
        Some(token) if token == target => None,
        token => Some(format!(
            "test target {crate_name} checks ledger target {token:?} but its source calls \
             run_target({target:?}): a [[test]] path points at the wrong file"
        )),
    }
}

/// Run every case of `target` (in parallel, each on its own thread), write the
/// verdict table to `$CARGO_TARGET_TMPDIR/two_language/<target>.tsv`, and
/// panic with the full report if any row failed, any case panicked, the
/// emitted rows and the ledger disagree, or `target` is not the token of the
/// Cargo test target running it ([`target_mismatch`]).
pub fn run_target(target: &str, cases: &[Case]) {
    let results: Vec<(&'static str, Vec<Row>, Option<String>)> = std::thread::scope(|scope| {
        let handles: Vec<_> = cases
            .iter()
            .map(|(name, case)| {
                let case = *case;
                let handle = std::thread::Builder::new()
                    .name((*name).to_string())
                    .stack_size(CASE_STACK_BYTES)
                    .spawn_scoped(scope, move || {
                        ROWS.with(|rows| *rows.borrow_mut() = Some(Vec::new()));
                        let outcome = catch_unwind(AssertUnwindSafe(case));
                        let rows = ROWS
                            .with(|rows| rows.borrow_mut().take())
                            .unwrap_or_default();
                        (rows, outcome.err().map(|p| panic_text(p.as_ref())))
                    })
                    .expect("spawn case thread");
                (*name, handle)
            })
            .collect();
        handles
            .into_iter()
            .map(|(name, handle)| {
                let (rows, panicked) = handle.join().expect("case thread joins");
                (name, rows, panicked)
            })
            .collect()
    });

    let mut emitted = Vec::new();
    let mut problems: Vec<String> = target_mismatch(env!("CARGO_CRATE_NAME"), target)
        .into_iter()
        .collect();
    for (name, rows, panicked) in results {
        for row in &rows {
            if row.verdict == Verdict::Fail {
                problems.push(format!("FAIL {} [{name}]: {}", row.id, row.detail));
            }
        }
        if let Some(why) = panicked {
            problems.push(format!("case {name} panicked: {why}"));
        }
        emitted.extend(rows);
    }
    problems.extend(ledger_problems(LEDGER, target, &emitted));

    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("two_language");
    let table: String = emitted
        .iter()
        .map(|r| {
            format!(
                "{}\t{}\t{}\n",
                r.id,
                r.verdict.token(),
                r.detail.replace('\t', " ")
            )
        })
        .collect();
    let written = std::fs::create_dir_all(&dir)
        .and_then(|()| std::fs::write(dir.join(format!("{target}.tsv")), &table));
    if let Err(e) = written {
        problems.push(format!(
            "could not write the verdict table under {}: {e}",
            dir.display()
        ));
    }

    let pass = emitted
        .iter()
        .filter(|r| r.verdict == Verdict::Pass)
        .count();
    let gap = emitted.iter().filter(|r| r.verdict == Verdict::Gap).count();
    let ratified = emitted
        .iter()
        .filter(|r| r.verdict == Verdict::RatifiedOut)
        .count();
    let fail = emitted
        .iter()
        .filter(|r| r.verdict == Verdict::Fail)
        .count();
    println!(
        "two-language {target}: {} rows = {pass} PASS / {gap} GAP / {ratified} RATIFIED-OUT / {fail} FAIL",
        emitted.len()
    );
    assert!(
        problems.is_empty(),
        "two-language {target}: {} problem(s):\n{}",
        problems.len(),
        problems.join("\n")
    );
}
