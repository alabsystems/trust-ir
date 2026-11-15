//! Mutation self-tests of the two-language harness (roadmap WS8.6): the
//! harness must fail every way a ratchet can silently rot. Each test drives
//! the harness's own functions with synthetic data, so none of them depends on
//! trust-ir's behaviour.

#[path = "harness.rs"]
mod harness;

use harness::{
    Expect, LEDGER, Outcome, Refusal, Row, Verdict, feature_gap, ledger_problems, parse_ledger,
    target_mismatch, target_token, variant_name,
};

/// A stand-in for a validator error type.
#[derive(Debug)]
#[allow(dead_code)]
enum FakeError {
    EmptyFunction,
    CallArgCountMismatch { expected: usize, actual: usize },
    InvalidFunctionSummary { detail: String },
}

#[test]
fn variant_names_are_read_from_debug_renderings() {
    assert_eq!(variant_name("EmptyFunction"), "EmptyFunction");
    assert_eq!(
        variant_name("CallArgCountMismatch { expected: 2, actual: 1 }"),
        "CallArgCountMismatch"
    );
    assert_eq!(variant_name("InvalidTag(38)"), "InvalidTag");
    assert_eq!(variant_name("MissingBlock: bb0 of @f"), "MissingBlock");
}

#[test]
fn an_accepting_gap_holds_and_trips_when_the_refusal_arrives() {
    // The recorded gap: the validator ACCEPTS.
    assert!(feature_gap(
        "selftest.accepts",
        Expect::Accepted,
        Outcome::of::<FakeError>(&[]),
        ""
    ));
    // The fix lands: the same measurement now refuses. The row must fail.
    let fixed = Outcome::of(&[FakeError::EmptyFunction]);
    assert!(!feature_gap(
        "selftest.accepts",
        Expect::Accepted,
        fixed,
        ""
    ));
}

#[test]
fn a_refusing_gap_trips_when_the_refusal_no_longer_occurs() {
    let expect = || Expect::refused("EmptyFunction");
    assert!(feature_gap(
        "selftest.refuses",
        expect(),
        Outcome::of(&[FakeError::EmptyFunction]),
        ""
    ));
    // The refusal no longer occurs.
    assert!(!feature_gap(
        "selftest.refuses",
        expect(),
        Outcome::of::<FakeError>(&[]),
        ""
    ));
}

#[test]
fn a_gap_trips_when_a_different_refusal_variant_arrives() {
    let expect = || Expect::refused("EmptyFunction");
    let other = Outcome::of(&[FakeError::CallArgCountMismatch {
        expected: 2,
        actual: 1,
    }]);
    assert!(!feature_gap("selftest.variant", expect(), other, ""));
    // ... and when an unexpected follow-on joins the recorded one.
    let extra = Outcome::of(&[
        FakeError::EmptyFunction,
        FakeError::CallArgCountMismatch {
            expected: 2,
            actual: 1,
        },
    ]);
    assert!(!feature_gap("selftest.variant", expect(), extra, ""));
    // Listed follow-ons are exact: they must all be present.
    let with_follow_on =
        || Expect::refused("EmptyFunction").with_follow_ons(&["CallArgCountMismatch"]);
    let both = Outcome::of(&[
        FakeError::CallArgCountMismatch {
            expected: 2,
            actual: 1,
        },
        FakeError::EmptyFunction,
    ]);
    assert!(feature_gap("selftest.variant", with_follow_on(), both, ""));
    let primary_only = Outcome::of(&[FakeError::EmptyFunction]);
    assert!(!feature_gap(
        "selftest.variant",
        with_follow_on(),
        primary_only,
        ""
    ));
}

#[test]
fn a_gap_trips_when_the_refusal_payload_changes() {
    let expect = || Expect::refused_with("InvalidFunctionSummary", &["counting rule"]);
    let same = Outcome::of(&[FakeError::InvalidFunctionSummary {
        detail: "the counting rule".into(),
    }]);
    assert!(feature_gap("selftest.payload", expect(), same, ""));
    let other = Outcome::of(&[FakeError::InvalidFunctionSummary {
        detail: "arity".into(),
    }]);
    assert!(!feature_gap("selftest.payload", expect(), other, ""));
}

#[test]
fn a_broken_supporting_fact_trips_the_row() {
    let held = Outcome::Accepted.given(&[("the interpreter still returns -1", true)]);
    assert!(feature_gap("selftest.fact", Expect::Accepted, held, ""));
    let broken = Outcome::Accepted.given(&[("the interpreter still returns -1", false)]);
    assert!(!feature_gap("selftest.fact", Expect::Accepted, broken, ""));
}

#[test]
fn outcome_all_is_accepted_only_when_every_mutant_is() {
    let all_ok = Outcome::all([Outcome::Accepted, Outcome::Accepted]);
    assert_eq!(all_ok, Outcome::Accepted);
    let both_refused = Outcome::all([
        Outcome::Refused(vec![Refusal::from_rendered("EmptyFunction".into())]),
        Outcome::Refused(vec![Refusal::from_rendered("EmptyFunction".into())]),
    ]);
    assert!(matches!(both_refused, Outcome::Refused(r) if r.len() == 2));
    // A mixed set is a measurement, never a pooled refusal (adversarial
    // review: see `outcome_all_never_pools_a_mixed_set_of_mutants`).
    let one_refused = Outcome::all([
        Outcome::Accepted,
        Outcome::Refused(vec![Refusal::from_rendered("EmptyFunction".into())]),
    ]);
    assert!(matches!(one_refused, Outcome::Measured(_)));
}

fn row(id: &str, verdict: Verdict) -> Row {
    Row {
        id: id.to_string(),
        verdict,
        detail: String::new(),
    }
}

const TOY: &str = "# row_id\tverdict\tcolumn\tfinding\tclosing_increment\tproducer_reachable\ttarget\n\
toy.pass\tPASS\tformat\t-\t-\tunknown\ttoy\n\
toy.gap\tGAP\tformat\tF-001\tWS1.1\tunknown\ttoy\n\
toy.v2\tGAP\tv2-decision\t-\tWS8.16\tno\t-\n";

#[test]
fn the_ledger_bijection_holds_for_a_matching_emission() {
    let emitted = [row("toy.pass", Verdict::Pass), row("toy.gap", Verdict::Gap)];
    assert_eq!(ledger_problems(TOY, "toy", &emitted), Vec::<String>::new());
}

#[test]
fn removing_a_row_from_the_ledger_fails_the_bijection() {
    let without_gap: String = TOY
        .lines()
        .filter(|l| !l.starts_with("toy.gap"))
        .map(|l| format!("{l}\n"))
        .collect();
    let emitted = [row("toy.pass", Verdict::Pass), row("toy.gap", Verdict::Gap)];
    let problems = ledger_problems(&without_gap, "toy", &emitted);
    assert!(
        problems
            .iter()
            .any(|p| p.contains("toy.gap") && p.contains("does not list")),
        "{problems:?}"
    );
}

#[test]
fn a_row_the_target_stops_emitting_fails_the_bijection() {
    let emitted = [row("toy.pass", Verdict::Pass)];
    let problems = ledger_problems(TOY, "toy", &emitted);
    assert!(
        problems
            .iter()
            .any(|p| p.contains("toy.gap") && p.contains("not emitted")),
        "{problems:?}"
    );
}

#[test]
fn a_flipped_verdict_without_a_ledger_edit_fails_the_bijection() {
    let emitted = [
        row("toy.pass", Verdict::Pass),
        row("toy.gap", Verdict::Pass),
    ];
    let problems = ledger_problems(TOY, "toy", &emitted);
    assert!(
        problems
            .iter()
            .any(|p| p.contains("toy.gap") && p.contains("edit RATCHETS.tsv")),
        "{problems:?}"
    );
}

#[test]
fn a_duplicate_emission_fails_the_bijection() {
    let emitted = [
        row("toy.pass", Verdict::Pass),
        row("toy.gap", Verdict::Gap),
        row("toy.gap", Verdict::Gap),
    ];
    let problems = ledger_problems(TOY, "toy", &emitted);
    assert!(
        problems
            .iter()
            .any(|p| p.contains("emitted toy.gap 2 times")),
        "{problems:?}"
    );
}

#[test]
fn a_v2_decision_line_can_never_be_emitted() {
    let emitted = [
        row("toy.pass", Verdict::Pass),
        row("toy.gap", Verdict::Gap),
        row("toy.v2", Verdict::Gap),
    ];
    let problems = ledger_problems(TOY, "toy", &emitted);
    assert!(
        problems
            .iter()
            .any(|p| p.contains("toy.v2") && p.contains("assigns it to -")),
        "{problems:?}"
    );
}

/// The real ledger is well-formed: seven fields, known columns / verdicts /
/// targets, unique ids, every GAP row names a finding and a closing increment,
/// and the v2-decision lines are never test rows.
#[test]
fn the_real_ledger_is_well_formed() {
    let rows = parse_ledger(LEDGER).expect("RATCHETS.tsv parses");
    let targets = [
        "b0", "b1", "b2", "b3", "b4", "b5", "b6", "b7", "field", "cli", "-",
    ];
    let mut ids = std::collections::BTreeSet::new();
    for r in &rows {
        assert!(ids.insert(r.id.as_str()), "duplicate ledger id {}", r.id);
        assert!(
            ["PASS", "GAP", "RATIFIED-OUT"].contains(&r.verdict.as_str()),
            "{}: verdict {}",
            r.id,
            r.verdict
        );
        assert!(
            ["format", "producer-reachable", "v2-decision"].contains(&r.column.as_str()),
            "{}: column {}",
            r.id,
            r.column
        );
        assert!(
            ["yes", "no", "unknown"].contains(&r.producer_reachable.as_str()),
            "{}: producer_reachable {}",
            r.id,
            r.producer_reachable
        );
        assert!(
            targets.contains(&r.target.as_str()),
            "{}: target {}",
            r.id,
            r.target
        );
        if r.column == "v2-decision" {
            assert_eq!(
                r.target, "-",
                "{}: a v2-decision line is never a test row",
                r.id
            );
            assert!(
                r.closing_increment.starts_with("WS8."),
                "{}: v2-decision lines point at the WS8 decision gates",
                r.id
            );
        } else {
            assert_ne!(
                r.target, "-",
                "{}: a format row must name the target that emits it",
                r.id
            );
        }
        if r.verdict == "RATIFIED-OUT" {
            assert_ne!(
                r.column, "v2-decision",
                "{}: a ratified row is a test row",
                r.id
            );
        }
        if (r.verdict == "GAP" || r.verdict == "RATIFIED-OUT") && r.column != "v2-decision" {
            assert!(
                r.finding.starts_with("F-"),
                "{}: a GAP row names its finding",
                r.id
            );
            assert!(
                r.closing_increment.starts_with("WS"),
                "{}: a GAP row names its closing increment",
                r.id
            );
        }
    }
    let v2 = rows.iter().filter(|r| r.column == "v2-decision").count();
    assert_eq!(
        v2, 71,
        "the 71 core-arch rows are ledger lines, never test rows (crit.misw01)"
    );
}

/// Registry entries (`#` comments stripped) of one gate registry file.
fn registry_entries(text: &str) -> Vec<&str> {
    text.lines()
        .map(|l| l.split('#').next().unwrap_or("").trim())
        .filter(|l| !l.is_empty())
        .collect()
}

/// A ledger target nobody runs is a ledger nobody checks: the bijection runs
/// per target, INSIDE the target, so deleting a target from the gate (or
/// never registering it) would leave its rows unverified while the gate stays
/// green. Every target token the ledger names must therefore map to a test
/// target that exists AND that gate 11's registry runs.
#[test]
fn every_ledger_target_is_run_by_gate_ten() {
    const CONFORMANCE_REGISTRY: &str =
        include_str!("../../../../scripts/gates/two-language-ratchets.trust-ir-conformance.tests");
    const CLI_REGISTRY: &str =
        include_str!("../../../../scripts/gates/two-language-ratchets.trust-ir-cli.tests");
    const MANIFEST: &str = include_str!("../../Cargo.toml");
    let conformance = registry_entries(CONFORMANCE_REGISTRY);
    let cli = registry_entries(CLI_REGISTRY);
    assert!(
        conformance.contains(&"two_language_harness"),
        "the harness self-test itself must be gated"
    );
    let rows = parse_ledger(LEDGER).expect("RATCHETS.tsv parses");
    let targets: std::collections::BTreeSet<&str> = rows
        .iter()
        .map(|r| r.target.as_str())
        .filter(|t| *t != "-")
        .collect();
    assert!(!targets.is_empty());
    for target in targets {
        let (test_target, registry, crate_name) = match target {
            "cli" => ("two_language_cli".to_string(), &cli, "trust-ir-cli"),
            "field" => (
                "two_language_field_ratchets".to_string(),
                &conformance,
                "trust-ir-conformance",
            ),
            other => (
                format!("two_language_{other}"),
                &conformance,
                "trust-ir-conformance",
            ),
        };
        assert!(
            registry.contains(&test_target.as_str()),
            "ledger target {target} is emitted by {test_target}, which \
             scripts/gates/two-language-ratchets.{crate_name}.tests does not run"
        );
        if crate_name == "trust-ir-conformance" {
            assert!(
                MANIFEST.contains(&format!("name = \"{test_target}\"")),
                "{test_target} is not a declared [[test]] of trust-ir-conformance"
            );
        }
    }
}

#[test]
fn a_ratified_row_is_held_exactly_and_counts_as_neither_pass_nor_gap() {
    use harness::feature_ratified;
    // Held: the ratified behaviour (a whole-run Panic) still occurs.
    let panic = || Outcome::Refused(vec![Refusal::from_rendered("Panic: assert failed".into())]);
    assert!(feature_ratified(
        "selftest.ratified",
        Expect::refused("Panic"),
        panic(),
        ""
    ));
    // The engine starts taking unwind edges: the run now succeeds. It trips.
    assert!(!feature_ratified(
        "selftest.ratified",
        Expect::refused("Panic"),
        Outcome::Accepted,
        ""
    ));
    // The ledger must say RATIFIED-OUT: a GAP line, or a PASS line, is a
    // verdict mismatch in both directions.
    const RATIFIED: &str = "toy.r\tRATIFIED-OUT\tformat\tF-041\tWS2.5\tunknown\ttoy\n";
    assert_eq!(
        ledger_problems(RATIFIED, "toy", &[row("toy.r", Verdict::RatifiedOut)]),
        Vec::<String>::new()
    );
    for wrong in [Verdict::Gap, Verdict::Pass] {
        let problems = ledger_problems(RATIFIED, "toy", &[row("toy.r", wrong)]);
        assert!(
            problems.iter().any(|p| p.contains("edit RATCHETS.tsv")),
            "{problems:?}"
        );
    }
    let problems = ledger_problems(
        "toy.r\tGAP\tformat\tF-041\tWS2.5\tunknown\ttoy\n",
        "toy",
        &[row("toy.r", Verdict::RatifiedOut)],
    );
    assert!(
        problems.iter().any(|p| p.contains("edit RATCHETS.tsv")),
        "{problems:?}"
    );
}

// ---------------------------------------------------------------------------
// Adversarial review (WS8.6): ways a ratchet could rot that the port's own
// self-tests did not exercise.
// ---------------------------------------------------------------------------

/// A recorded refusal that starts firing at a SECOND site (the same rule, one
/// more error) is a change of shape: the row trips.
#[test]
fn a_gap_trips_when_its_refusal_fires_at_a_second_site() {
    let doubled = Outcome::of(&[FakeError::EmptyFunction, FakeError::EmptyFunction]);
    assert!(!feature_gap(
        "selftest.doubled",
        Expect::refused("EmptyFunction"),
        doubled,
        ""
    ));
}

/// `Outcome::all` must not pool a MIXED set of mutants. Before the review it
/// did: mutant 1 accepted + mutant 2 refused twice pooled to the same two
/// refusals as "both refused once", so a row over two mutants stayed GAP after
/// one of them stopped being refused. A mixed set is now a measurement no
/// expectation can equal.
#[test]
fn outcome_all_never_pools_a_mixed_set_of_mutants() {
    let refused = || Outcome::of(&[FakeError::EmptyFunction]);
    let expect = || Expect::refused("EmptyFunction").with_follow_ons(&["EmptyFunction"]);
    // Recorded shape: both mutants refused once.
    assert!(feature_gap(
        "selftest.mixed",
        expect(),
        Outcome::all([refused(), refused()]),
        ""
    ));
    // Mutant 1 is now accepted; mutant 2 is refused twice.
    let moved = Outcome::all([
        Outcome::Accepted,
        Outcome::of(&[FakeError::EmptyFunction, FakeError::EmptyFunction]),
    ]);
    assert!(matches!(moved, Outcome::Measured(_)), "{moved:?}");
    assert!(!feature_gap("selftest.mixed", expect(), moved, ""));
    // ... and a mixed set never reads as the all-accepted gap either.
    let half = Outcome::all([Outcome::Accepted, refused()]);
    assert!(!feature_gap("selftest.mixed", Expect::Accepted, half, ""));
    // A measurement among refusals is never masked, whatever its position.
    let late = Outcome::all([refused(), Outcome::measured("m")]);
    assert_eq!(late, Outcome::measured("m"));
}

/// Each target checks the ledger rows of the token bound to its Cargo NAME,
/// not whatever its source file passes: two `[[test]]` entries pointing at one
/// file would otherwise check that file twice and the other target's rows
/// never, with gate 10 green.
#[test]
fn a_target_checks_only_the_token_of_its_own_cargo_name() {
    assert_eq!(target_token("two_language_b1"), Some("b1"));
    assert_eq!(target_token("two_language_field_ratchets"), Some("field"));
    assert_eq!(target_token("two_language_cli"), Some("cli"));
    assert_eq!(target_token("two_language_harness"), None);
    assert_eq!(target_token("conformance"), None);
    assert_eq!(target_mismatch("two_language_b3", "b3"), None);
    // `two_language_b2 = { path = "b1_mixed_module.rs" }`: refused by name.
    let copy_paste = target_mismatch("two_language_b2", "b1").expect("a mismatch");
    assert!(copy_paste.contains("two_language_b2") && copy_paste.contains("\"b1\""));
    assert!(target_mismatch("two_language_harness", "b1").is_some());
    // Every token the real ledger names is the token of the target that gate
    // 10 runs for it (the mapping `every_ledger_target_is_run_by_gate_ten`
    // uses), so the binding cannot orphan a ledger target.
    for row in parse_ledger(LEDGER).expect("RATCHETS.tsv parses") {
        if row.target == "-" {
            continue;
        }
        let crate_name = match row.target.as_str() {
            "field" => "two_language_field_ratchets".to_string(),
            other => format!("two_language_{other}"),
        };
        assert_eq!(target_token(&crate_name), Some(row.target.as_str()));
    }
}

/// A ledger line that differs from the emitted row only by invisible bytes (a
/// padded id, a padded target) never matches silently: the bijection fails
/// closed. A CRLF checkout of the ledger is NOT such a difference (`lines()`
/// strips `\r\n`), so it must read exactly like the LF original.
#[test]
fn an_invisibly_different_ledger_line_fails_closed() {
    let emitted = [row("toy.pass", Verdict::Pass), row("toy.gap", Verdict::Gap)];
    let crlf = TOY.replace('\n', "\r\n");
    assert_eq!(parse_ledger(&crlf), parse_ledger(TOY));
    assert_eq!(
        ledger_problems(&crlf, "toy", &emitted),
        Vec::<String>::new()
    );
    let padded_id = TOY.replace("toy.gap\t", "toy.gap \t");
    let problems = ledger_problems(&padded_id, "toy", &emitted);
    assert!(
        problems
            .iter()
            .any(|p| p.contains("toy.gap") && p.contains("does not list")),
        "{problems:?}"
    );
    let padded_target = TOY.replace("unknown\ttoy\ntoy.v2", "unknown\ttoy \ntoy.v2");
    assert_ne!(padded_target, TOY);
    let problems = ledger_problems(&padded_target, "toy", &emitted);
    assert!(
        problems
            .iter()
            .any(|p| p.contains("toy.gap") && p.contains("assigns it to toy ")),
        "{problems:?}"
    );
}

/// A ledger line assigned to ANOTHER real target (not only `-`) fails the
/// bijection in the target that emits it.
#[test]
fn a_row_the_ledger_assigns_to_another_target_fails_the_bijection() {
    let moved = TOY.replace("F-001\tWS1.1\tunknown\ttoy", "F-001\tWS1.1\tunknown\tb7");
    let emitted = [row("toy.pass", Verdict::Pass), row("toy.gap", Verdict::Gap)];
    let problems = ledger_problems(&moved, "toy", &emitted);
    assert!(
        problems
            .iter()
            .any(|p| p.contains("toy.gap") && p.contains("assigns it to b7")),
        "{problems:?}"
    );
}
