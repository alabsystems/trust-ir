from __future__ import annotations

import argparse
import contextlib
import importlib.util
import io
import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
TOOL_PATH = ROOT / "scripts" / "wire_alloc.py"

SPEC = importlib.util.spec_from_file_location("wire_alloc", TOOL_PATH)
assert SPEC is not None and SPEC.loader is not None
TOOL = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = TOOL
SPEC.loader.exec_module(TOOL)

REGISTRY_TEXT = (ROOT / TOOL.REGISTRY).read_text(encoding="utf-8")
BINARY_SRC = (ROOT / "crates/trust-ir/src/binary.rs").read_text(encoding="utf-8")
DOMAINS = TOOL.scan_literals(ROOT)
LEDGER_TEXT = (ROOT / TOOL.VERSION_LEDGER).read_text(encoding="utf-8")
# Derived, never spelled: a test that hard-codes "44" is itself a line every
# version bump has to edit, which is the contention this tool exists to remove.
TABLES = TOOL.parse(REGISTRY_TEXT)
LATEST = dict(TOOL.scan_version_constants(BINARY_SRC))["VERSION"]
NEXT_VERSION = TOOL.next_free(TABLES, "version", None)
NEXT_TY_TAG = TOOL.next_free(TABLES, "tag", "Ty")
NEXT_OBLIGATION_DIGEST = TOOL.next_free(TABLES, "domain", "trust_ir.obligation.digest")


def errors_for(text: str, binary_src: str = BINARY_SRC, domains=None, tsv=None) -> list[str]:
    """`tsv=None` skips the two-ledger binding: most tests here doctor ONE file."""
    return TOOL.check(TOOL.parse(text), binary_src, DOMAINS if domains is None else domains, tsv)


def no_open_versions(text: str) -> str:
    """The registry with every REAL open wire-version reservation removed.
    Scenario tests are about hypothetical lines and nobody else, so they must
    mean the same thing the day a real reservation is on main.  They did not at
    first — measured: one by-the-book `reserve version` turned three of them
    red, because `takeover` rightly moves a line below the REAL reservation too.

    A reservation may already own TAG rows — `reserve tag --since <its own
    version>` is how a lane claims its tag bytes before its code lands — and
    v47's did.  That is the second measurement this helper needed: dropping the
    `wire_version` row ALONE left `since = 47` rows citing a version the fixture
    no longer registers, so every scenario built on it went red with `is not a
    registered wire version` — a failure about the fixture, not the scenario.
    A row reserved UNDER an open version is part of that reservation and leaves
    with it; a row reserved under a LANDED version (a new variant of a shipped
    enum) is not, and stays."""
    open_numbers, inside = set(), False
    for line in text.splitlines():
        if line == "wire_version = [":
            inside = True
        elif line == "]":
            inside = False
        elif inside and 'status = "reserved"' in line:
            match = re.search(r"\bnumber = (\d+)", line)
            if match:
                open_numbers.add(int(match.group(1)))
    kept = []
    for line in text.splitlines():
        if 'status = "reserved"' in line:
            match = re.search(r"\b(?:number|since) = (\d+)", line)
            if match and int(match.group(1)) in open_numbers:
                continue
        kept.append(line)
    return "\n".join(kept) + "\n"


def no_open_ledger_rows(tsv: str) -> str:
    return "".join(line + "\n" for line in tsv.splitlines() if line.startswith("#") or "\treserved\t" not in line)


def scratch_root(tmp: str, settled: bool = False) -> Path:
    """A root the CLI may WRITE to: the registry and the other ledger are COPIES.
    Everything else is a symlink — but never `crates/` or `crates/trust-ir/`
    themselves, or a write to the ledger would land in the real repository.
    `settled` starts both copies with no open wire-version reservation."""
    root = Path(tmp)
    (root / TOOL.REGISTRY).write_text(no_open_versions(REGISTRY_TEXT) if settled else REGISTRY_TEXT, encoding="utf-8")
    os.symlink(ROOT / "frontend", root / "frontend")
    (root / "crates" / "trust-ir").mkdir(parents=True)
    for member in sorted((ROOT / "crates").iterdir()):
        if member.name != "trust-ir":
            os.symlink(member, root / "crates" / member.name)
    os.symlink(ROOT / "crates" / "trust-ir" / "src", root / "crates" / "trust-ir" / "src")
    (root / TOOL.VERSION_LEDGER).write_text(no_open_ledger_rows(LEDGER_TEXT) if settled else LEDGER_TEXT, encoding="utf-8")
    return root


def drop_line(text: str, needle: str) -> str:
    lines = text.splitlines()
    kept = [line for line in lines if needle not in line]
    assert len(kept) + 1 == len(lines), needle
    return "\n".join(kept) + "\n"


class GitHubOwnersUseAgh(unittest.TestCase):
    def test_named_https_and_ssh_remotes_use_the_complete_agh_branch_response(self):
        for url in ("https://github.com/alabsystems/trust-ir.git",
                    "git@github.com:alabsystems/trust-ir.git",
                    "git@www.github.com:alabsystems/trust-ir.git",
                    "git@github.com.:alabsystems/trust-ir.git",
                    "ssh://git@github.com/alabsystems/trust-ir.git",
                    "https://github.com:443/alabsystems/trust-ir.git",
                    "ssh://git@ssh.github.com:443/alabsystems/trust-ir.git"):
            with self.subTest(url=url):
                response = subprocess.CompletedProcess([], 0, json.dumps([
                    {"name": "main", "sha": "a" * 40},
                    {"name": "agents/open", "sha": "b" * 40},
                ]), "")
                with mock.patch.object(TOOL, "git", return_value=subprocess.CompletedProcess([], 0, url, "")) as git_call, \
                        mock.patch.object(TOOL.subprocess, "run", return_value=response) as agh_call:
                    tips, error = TOOL.remote_branches(ROOT, "origin")
                self.assertEqual(tips, {"main": "a" * 40, "agents/open": "b" * 40})
                self.assertEqual(error, "")
                git_call.assert_called_once_with(ROOT, "remote", "get-url", "origin")
                self.assertEqual(agh_call.call_args.args[0], ["agh", "branches", "alabsystems/trust-ir"])

    def test_ambiguous_github_authorities_are_refused_before_any_transport(self):
        for url in ("file://github.com/alabsystems/trust-ir.git",
                    "https://github.com:bad/alabsystems/trust-ir.git",
                    "https://github.com:22/alabsystems/trust-ir.git",
                    "ssh://git@github.com:443/alabsystems/trust-ir.git",
                    "https://github.com/alabsystems/trust-ir.git?other",
                    "https://github.com/alabsystems/trust-ir.git#other"):
            with self.subTest(url=url), \
                    mock.patch.object(TOOL, "git", return_value=subprocess.CompletedProcess([], 0, url, "")) as git_call, \
                    mock.patch.object(TOOL.subprocess, "run") as transport:
                tips, error = TOOL.remote_branches(ROOT, "origin")
                self.assertIsNone(tips)
                self.assertIn("GitHub repository", error)
                transport.assert_not_called()
                git_call.assert_called_once_with(ROOT, "remote", "get-url", "origin")

    def test_refused_or_incomplete_agh_never_falls_back_to_git(self):
        for code in (1, 3, 5, 14):
            with self.subTest(code=code), \
                    mock.patch.object(TOOL, "git", return_value=subprocess.CompletedProcess([], 0, "https://github.com/alabsystems/trust-ir", "")) as git_call, \
                    mock.patch.object(TOOL.subprocess, "run", return_value=subprocess.CompletedProcess([], code, "[]", "refused")):
                tips, error = TOOL.remote_branches(ROOT, "origin")
                self.assertIsNone(tips)
                self.assertEqual(error, "refused")
                git_call.assert_called_once_with(ROOT, "remote", "get-url", "origin")

    def test_malformed_or_duplicate_authority_is_not_a_branch_absence(self):
        for response in ({}, [{"name": "main", "sha": "bad"}],
                         [{"name": "main", "sha": "a" * 40}] * 2):
            with self.subTest(response=response), \
                    mock.patch.object(TOOL, "git", return_value=subprocess.CompletedProcess([], 0, "https://github.com/alabsystems/trust-ir", "")), \
                    mock.patch.object(TOOL.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, json.dumps(response), "")):
                tips, error = TOOL.remote_branches(ROOT, "origin")
                self.assertIsNone(tips)
                self.assertIn("invalid branch response", error)


class TheFixtureIsItselfAValidRegistry(unittest.TestCase):
    """`no_open_versions` builds the registry three scenario tests start from.
    When the fixture is not a valid registry those tests fail for a reason that
    is not the scenario — and the failure names THEM, not the helper, which is
    how a dangling `since = 47` read as "the takeover tests are broken" for a
    day.  Check the helper's own output here, where the failure names it."""

    def test_the_settled_registry_still_checks_out(self) -> None:
        self.assertEqual(errors_for(no_open_versions(REGISTRY_TEXT)), [])

    def test_a_tag_reserved_under_an_open_version_leaves_with_that_version(self) -> None:
        settled = no_open_versions(REGISTRY_TEXT)
        text, _ = TOOL.reserve(settled, argparse.Namespace(
            owner="a", date="2026-09-19", namespace="version",
            feature="line-a", constant="LINE_A_FORMAT_VERSION"))
        text, _ = TOOL.reserve(text, argparse.Namespace(
            owner="a", date="2026-09-19", namespace="tag",
            enum="Ty", variant="LineA", since=LATEST + 1))
        self.assertIn('variant = "LineA"', text)
        # the reservation leaves whole: its version row AND the tag row under it
        self.assertEqual(no_open_versions(text), settled)

    def test_a_tag_reserved_under_a_LANDED_version_stays(self) -> None:
        text, _ = TOOL.reserve(no_open_versions(REGISTRY_TEXT), argparse.Namespace(
            owner="a", date="2026-09-19", namespace="tag",
            enum="Ty", variant="LineA", since=LATEST))
        self.assertIn('variant = "LineA"', no_open_versions(text))


class RegistryIsTrueToday(unittest.TestCase):
    def test_the_checked_in_registry_agrees_with_the_sources(self) -> None:
        self.assertEqual(errors_for(REGISTRY_TEXT, tsv=LEDGER_TEXT), [])


class MissingRowsAreRefused(unittest.TestCase):
    def test_a_new_version_constant_without_a_row(self) -> None:
        doctored = BINARY_SRC + f"\npub const SNEAKED_IN_FORMAT_VERSION: u32 = {NEXT_VERSION};\n"
        errors = errors_for(REGISTRY_TEXT, doctored)
        self.assertTrue(any("SNEAKED_IN_FORMAT_VERSION" in error for error in errors), errors)

    def test_a_version_bump_without_a_row(self) -> None:
        doctored = BINARY_SRC.replace(
            f"pub const VERSION: u32 = {LATEST};", f"pub const VERSION: u32 = {LATEST + 1};"
        )
        self.assertNotEqual(doctored, BINARY_SRC)
        errors = errors_for(REGISTRY_TEXT, doctored)
        self.assertTrue(any(f"`VERSION = {LATEST + 1}`" in error for error in errors), errors)

    def test_a_dropped_version_row(self) -> None:
        errors = errors_for(drop_line(REGISTRY_TEXT, 'constant = "HANDLE_TYPE_FORMAT_VERSION"'))
        self.assertTrue(any("HANDLE_TYPE_FORMAT_VERSION" in error for error in errors), errors)

    def test_a_new_digest_domain_without_a_row(self) -> None:
        sneaked = f"trust_ir.obligation.digest.v{NEXT_OBLIGATION_DIGEST}"
        errors = errors_for(REGISTRY_TEXT, domains=[*DOMAINS, sneaked])
        self.assertTrue(any(sneaked in error and "reserve FIRST" in error for error in errors), errors)

    def test_respelling_a_burned_domain(self) -> None:
        burned = "trust_ir.obligation.digest.v" + "5"
        errors = errors_for(REGISTRY_TEXT, domains=[*DOMAINS, burned])
        self.assertTrue(any("burned" in error for error in errors), errors)

    def test_a_second_claim_to_a_taken_tag(self) -> None:
        lines = REGISTRY_TEXT.splitlines()
        at = max(i for i, line in enumerate(lines) if '{ enum = "Ty", ' in line)
        lines.insert(
            at + 1,
            f'  {{ enum = "Ty", tag = {NEXT_TY_TAG - 1}, variant = "SecondClaim", since = {LATEST}, '
            'status = "reserved", owner = "x" },',
        )
        errors = errors_for("\n".join(lines) + "\n")
        self.assertTrue(any("does not follow" in error for error in errors), errors)


def versioned(name: str, sep: str, version: int) -> str:
    return f"{name}{sep}v{version}"


def drop_lines(text: str, needle: str) -> str:
    kept = [line for line in text.splitlines() if needle not in line]
    assert len(kept) < len(text.splitlines()), needle
    return "\n".join(kept) + "\n"


def insert_after(text: str, needle: str, row: str) -> str:
    lines = text.splitlines()
    at = max(i for i, line in enumerate(lines) if needle in line)
    lines.insert(at + 1, "  " + row + ",")
    return "\n".join(lines) + "\n"


SNEAKED_READER = """
fn read_sneaked(r: &mut Reader<'_>) -> Result<Sneaked, BinaryError> {
    let sneaked = match r.read_u8()? {
        0 => {
            let payload = r.read_u64()?;
            Sneaked::Wide(payload)
        }
        1 => Sneaked::Narrow,
        t => return Err(BinaryError::InvalidTag(t)),
    };
    Ok(sneaked)
}
"""

SNEAKED_WRITER = """
fn write_sneaked(buf: &mut impl BinarySink, value: &Sneaked) {
    match value {
        crate::sneaky::Sneaked::Wide(payload) => {
            write_u8(buf, 0);
            write_u64(buf, *payload);
        }
        crate::sneaky::Sneaked::Narrow => write_u8(buf, 1),
    }
}
"""


class TheListOfTagSpacesIsChecked(unittest.TestCase):
    """The census samples the tag spaces somebody TOLD it about.  On the day it
    landed that hand-kept list was one short, and a wire-breaking re-tag of the
    missing space passed every check.  These fail without the source scan."""

    def test_the_live_tag_space_the_backfill_missed_is_refused_without_its_rows(self) -> None:
        errors = errors_for(drop_lines(REGISTRY_TEXT, 'enum = "DiagnosticSeverity"'))
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("`DiagnosticSeverity` is not a registered tag space", errors[0])

    def test_a_new_inline_tag_space_is_seen_from_its_reader_or_its_writer_alone(self) -> None:
        for sneaked in (SNEAKED_READER, SNEAKED_WRITER):
            errors = errors_for(REGISTRY_TEXT, sneaked + BINARY_SRC)
            self.assertEqual(len(errors), 1, errors)
            self.assertIn("`Sneaked` is not a registered tag space", errors[0])

    def test_a_test_module_is_not_production_and_an_unclosed_one_fails_closed(self) -> None:
        body = "".join(f"    {line}\n" for line in (SNEAKED_READER + SNEAKED_WRITER).splitlines())
        in_tests = "#[cfg(test)]\nmod sneaky_tests {\n" + body + "}\n"
        self.assertEqual(errors_for(REGISTRY_TEXT, in_tests + BINARY_SRC), [])
        with self.assertRaises(TOOL.RegistryError):
            TOOL.production_lines("#[cfg(test)]\nmod t {\n    fn f() {}\n")

    def test_a_closed_tag_match_naming_no_enum_is_refused_and_a_presence_byte_is_not(self) -> None:
        anonymous = (
            "\nfn read_anonymous(r: &mut Reader<'_>) -> Result<Thing, BinaryError> {\n"
            "    match r.read_u8()? {\n        0 => make_first(r),\n        1 => make_second(r),\n"
            "        2 => make_third(r),\n        t => Err(BinaryError::InvalidTag(t)),\n    }\n}\n"
        )
        errors = errors_for(REGISTRY_TEXT, anonymous + BINARY_SRC)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("names no enum", errors[0])
        presence = (
            "\nfn read_optional(r: &mut Reader<'_>) -> Result<Option<u64>, BinaryError> {\n"
            "    match r.read_u8()? {\n        0 => Ok(None),\n        1 => Ok(Some(r.read_u64()?)),\n"
            "        t => Err(BinaryError::InvalidTag(t)),\n    }\n}\n"
        )
        self.assertEqual(errors_for(REGISTRY_TEXT, presence + BINARY_SRC), [])

    def test_a_scanner_gone_blind_is_refused(self) -> None:
        phantom = insert_after(
            REGISTRY_TEXT,
            '{ enum = "Visibility", ',
            f'{{ enum = "ZzPhantom", tag = 0, variant = "A", since = {LATEST}, status = "reserved", owner = "x" }}',
        )
        errors = errors_for(phantom)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("no longer sees `ZzPhantom`", errors[0])

    def test_the_scan_sees_exactly_the_registered_spaces_as_the_rust_census_must(self) -> None:
        # Two scanners, one truth: both must equal the registry on the live
        # source, so they cannot disagree with each other there.
        spelled, unattributed = TOOL.scan_tag_spaces(BINARY_SRC)
        self.assertEqual(unattributed, [])
        self.assertEqual(sorted(spelled), sorted({row.fields["enum"] for row in TABLES["enum_tag"]}))

    def test_an_exemption_is_honoured_only_while_it_exempts_something(self) -> None:
        exempting = insert_after(
            REGISTRY_TEXT, '{ scan = "literal", name = "ty."', '{ scan = "tag-space", name = "Sneaked", reason = "a probe" }'
        )
        self.assertEqual(errors_for(exempting, SNEAKED_READER + BINARY_SRC), [])
        errors = errors_for(exempting)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("exempts nothing", errors[0])


class VersionedIdentitiesAreAClosedWorld(unittest.TestCase):
    """The first scanner matched one spelling, a literal starting `"trust_ir.`.
    Seven live identities sat outside it, one of them already bumped once."""

    def test_the_reviewers_bypass_is_refused(self) -> None:
        bumped = versioned("trust-ir.satres.cnf", ".", 3)
        minted = versioned("trust-ir.sneaked.identity", ".", 1)
        fragment = versioned(".sneaked.concat", ".", 1)
        errors = errors_for(REGISTRY_TEXT, domains=[*DOMAINS, bumped, minted, fragment])
        for literal in (bumped, minted, fragment):
            self.assertTrue(any(f"`{literal}`" in e and "no digest_domain row" in e for e in errors), (literal, errors))

    def test_the_scanner_sees_every_spelling_and_only_production_code(self) -> None:
        q = '"'
        source = [
            f"const A: &str = {q}{versioned('trust-ir.x', '.', 2)}{q};",
            f"const M: &[u8] = b{q}{versioned('TIR-X', '-', 1)}\\0{q};",
            f"const C: &str = concat!({q}trust_ir{q}, {q}{versioned('.sneaked.concat', '.', 1)}{q});",
            f"const S: &str = {q}{versioned('@trust-internal::d', '-', 1)}{q};",
            f"const T: &str = {q}{versioned('trust_ir.test.t', '.', 1)}{q};",
            f"const N: &str = {q}trust_ir.not_versioned{q};",
            f"const V: &str = {q}lean4---v4.30.0{q};",
        ]
        self.assertEqual(
            sorted(TOOL.literals_in(source)),
            sorted(
                [
                    versioned(".sneaked.concat", ".", 1),
                    versioned("@trust-internal::d", "-", 1),
                    versioned("TIR-X", "-", 1),
                    versioned("trust-ir.x", ".", 2),
                ]
            ),
        )
        gated = '#[cfg(all(test, feature = "serde"))]\nmod t {\n' + "\n".join(source) + "\n}\n"
        self.assertEqual(TOOL.literals_in(TOOL.production_lines(gated)), [])

    def test_native_replay_formula_reference_transport_is_registered_exactly(self) -> None:
        domain = "trust.native-bundle.replay-formula-ref"
        identity = versioned(domain, ".", 1)
        rows = [row for row in TABLES["digest_domain"] if row.fields.get("domain") == domain]
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0].fields["version"], 1)
        self.assertEqual(rows[0].fields["status"], "landed")
        self.assertIn(identity, DOMAINS)
        self.assertFalse(any(identity.startswith(row.fields["name"])
            for row in TABLES["scan_exempt"] if row.fields.get("scan") == "literal"))
        missing = errors_for(drop_lines(REGISTRY_TEXT, f'domain = "{domain}"'))
        self.assertEqual(len(missing), 1, missing)
        self.assertIn(f"`{identity}`", missing[0])
        self.assertIn("no digest_domain row", missing[0])
        unallocated = versioned(domain, ".", 2)
        errors = errors_for(REGISTRY_TEXT, domains=[*DOMAINS, unallocated])
        self.assertTrue(any(f"`{unallocated}`" in error and "no digest_domain row" in error for error in errors), errors)

    def test_the_rows_for_the_legacy_spellings_are_load_bearing(self) -> None:
        errors = errors_for(drop_lines(REGISTRY_TEXT, 'domain = "trust-ir.sha256-domain"'))
        self.assertEqual(len(errors), 1, errors)
        self.assertIn(versioned("trust-ir.sha256-domain", ".", 1), errors[0])

    def test_exemptions_are_foreign_namespaces_with_reasons_and_never_idle(self) -> None:
        errors = errors_for(drop_lines(REGISTRY_TEXT, '{ scan = "literal", name = "ay."'))
        self.assertTrue(errors and all("`ay." in e for e in errors), errors)
        for row, refusal in (
            ('{ scan = "literal", name = "zz-unused.", reason = "nothing spells it" }', "exempts nothing"),
            ('{ scan = "literal", name = "zz", reason = "not a namespace" }', "NAMESPACE PREFIX"),
            ('{ scan = "literal", name = "zz.", reason = "" }', "must give its `reason`"),
            ('{ scan = "everything", name = "zz.", reason = "no such scan" }', "is not one of"),
        ):
            errors = errors_for(insert_after(REGISTRY_TEXT, '{ scan = "literal", name = "ty."', row))
            self.assertTrue(any(refusal in e for e in errors), (row, errors))
        for own in ("trust-ir.", "trust_ir.proof.", "trust-"):
            row = f'{{ scan = "literal", name = "{own}", reason = "try" }}'
            errors = errors_for(insert_after(REGISTRY_TEXT, '{ scan = "literal", name = "ty."', row))
            self.assertTrue(any("cannot be exempted" in e for e in errors), (own, errors))

    def test_a_new_identity_is_canonical_and_a_legacy_bump_keeps_its_spelling(self) -> None:
        args = argparse.Namespace(owner="lane", date="2026-09-18", namespace="domain", binds="probe")
        args.domain = "TIR-SATRES"
        text, row = TOOL.reserve(REGISTRY_TEXT, args)
        self.assertIn('version = 2, sep = "-", status = "reserved"', row)
        self.assertEqual(errors_for(text), [])
        args.domain = "trust-ir.brand.new"
        with self.assertRaises(TOOL.RegistryError):
            TOOL.reserve(REGISTRY_TEXT, args)
        minted = insert_after(
            REGISTRY_TEXT,
            'domain = "trust-ir.satres.cnf", version = 2,',
            '{ domain = "trust-ir.satres.dnf", version = 1, status = "reserved", binds = "x", owner = "x" }',
        )
        errors = errors_for(minted)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("a NEW identity is spelled", errors[0])


class TheCompiledHalfCannotGoMissingSilently(unittest.TestCase):
    """Gate 10 selects the census by test NAME, and a filter that matches
    nothing exits 0.  Measured: with `mod wire_census;` dropped, the old gate
    printed `running 0 tests ... ok` and passed."""

    def test_a_dropped_census_hook_is_refused_without_a_compiler(self) -> None:
        unhooked = BINARY_SRC.replace(TOOL.CENSUS_HOOK, "")
        self.assertNotEqual(unhooked, BINARY_SRC)
        errors = errors_for(REGISTRY_TEXT, unhooked)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("orphaned", errors[0])

    def test_every_required_census_test_is_a_real_test_fn(self) -> None:
        census = (ROOT / TOOL.CENSUS_FILE).read_text(encoding="utf-8")
        self.assertTrue(TOOL.REQUIRED_CENSUS_TESTS)
        for name in TOOL.REQUIRED_CENSUS_TESTS:
            self.assertIn(f"#[test]\nfn {name}() {{", census, name)

    def test_gate_ten_requires_the_tests_to_be_seen_not_just_a_zero_exit(self) -> None:
        gates = (ROOT / "scripts" / "ci_gates.sh").read_text(encoding="utf-8")
        self.assertIn("gate wire-allocation-census wire_census_ran", gates)
        self.assertIn("required-census-tests", gates)
        # The bare name-filtered command may appear ONLY inside the guard.
        self.assertEqual(gates.count("binary::wire_census 2>&1"), 1)
        self.assertNotIn("binary::wire_census\n", gates.replace("\\\n", " "))


class VersionsLandInNumberOrder(unittest.TestCase):
    """Read gates are cumulative, so a later reservation cannot land over an
    open earlier one.  `takeover` is the way through that needs no reader hole."""

    # The scenarios are about two hypothetical lines and nobody else, so they
    # start from a registry with every REAL open reservation removed and count
    # from VERSION + 1. They did not at first — measured: one by-the-book
    # `reserve version` on the real registry turned them red, because
    # `takeover` rightly moved line-b below the REAL reservation too.
    FIRST = LATEST + 1

    def two_open(self) -> str:
        args = argparse.Namespace(owner="a", date="2026-09-18", namespace="version", feature="line-a", constant="LINE_A_FORMAT_VERSION")
        text, _ = TOOL.reserve(no_open_versions(REGISTRY_TEXT), args)
        args = argparse.Namespace(owner="b", date="2026-09-18", namespace="version", feature="line-b", constant="LINE_B_FORMAT_VERSION")
        text, _ = TOOL.reserve(text, args)
        args = argparse.Namespace(owner="b", date="2026-09-18", namespace="tag", enum="Ty", variant="LineB", since=self.FIRST + 1)
        text, _ = TOOL.reserve(text, args)
        return text

    def test_takeover_moves_the_ready_line_down_and_everything_it_passes_up(self) -> None:
        text, displaced, moved = TOOL.takeover(self.two_open(), "line-b")
        self.assertEqual(moved, {self.FIRST + 1: self.FIRST, self.FIRST: self.FIRST + 1})
        self.assertEqual(errors_for(text), [])
        rows = {r.fields["feature"]: r.fields for r in TOOL.parse(text)["wire_version"]}
        self.assertEqual(rows["line-b"]["number"], self.FIRST)
        self.assertEqual(rows["line-a"]["number"], self.FIRST + 1)
        self.assertEqual(rows["line-a"]["constant"], "LINE_A_FORMAT_VERSION")
        tag = next(r.fields for r in TOOL.parse(text)["enum_tag"] if r.fields["variant"] == "LineB")
        self.assertEqual(tag["since"], self.FIRST)
        self.assertEqual(len(displaced), 1)
        self.assertIn("line-a", displaced[0])
        # B can now land at the lowest number with no reader hole ...
        landed = text.replace(
            f'number = {self.FIRST}, feature = "line-b", constant = "LINE_B_FORMAT_VERSION", status = "reserved"',
            f'number = {self.FIRST}, feature = "line-b", constant = "LINE_B_FORMAT_VERSION", status = "landed"',
        ).replace(f'variant = "LineB", since = {self.FIRST}, status = "reserved"', f'variant = "LineB", since = {self.FIRST}, status = "landed"')
        source = BINARY_SRC.replace(
            f"pub const VERSION: u32 = {LATEST};",
            f"pub const VERSION: u32 = {self.FIRST};\npub const LINE_B_FORMAT_VERSION: u32 = {self.FIRST};",
        )
        self.assertEqual(errors_for(landed, source), [])
        # ... and the displaced line is TOLD, the first time it merges main.
        stale = source.replace("LINE_B_FORMAT_VERSION", "LINE_A_FORMAT_VERSION")
        errors = errors_for(landed, stale)
        self.assertTrue(any(f"names `LINE_A_FORMAT_VERSION`, which binary.rs declares as {self.FIRST}" in e for e in errors), errors)

    def test_landing_out_of_order_is_refused_and_takeover_of_the_lowest_is_a_no_op(self) -> None:
        text = self.two_open()
        landed = text.replace(
            f'number = {self.FIRST + 1}, feature = "line-b", constant = "LINE_B_FORMAT_VERSION", status = "reserved"',
            f'number = {self.FIRST + 1}, feature = "line-b", constant = "LINE_B_FORMAT_VERSION", status = "landed"',
        )
        source = BINARY_SRC.replace(
            f"pub const VERSION: u32 = {LATEST};",
            f"pub const VERSION: u32 = {self.FIRST + 1};\npub const LINE_B_FORMAT_VERSION: u32 = {self.FIRST + 1};",
        )
        errors = errors_for(landed, source)
        self.assertTrue(any(f"wire version {self.FIRST} is reserved but VERSION is already" in e for e in errors), errors)
        with self.assertRaises(TOOL.RegistryError):
            TOOL.takeover(text, "line-a")
        with self.assertRaises(TOOL.RegistryError):
            TOOL.takeover(text, "no-such-feature")


class TwoLedgersOneCounter(unittest.TestCase):
    """Two sessions each built a lock for "the next wire version" the same day,
    in different files.  Unbound they reintroduce the race: measured, v44 given
    to two owners, one per file, left every live check of both gates green."""

    def reserved(self, feature: str, owner: str) -> str:
        args = argparse.Namespace(owner=owner, date="2026-09-18", namespace="version", feature=feature, constant=None)
        return TOOL.reserve(REGISTRY_TEXT, args)[0]

    def test_a_reservation_in_only_one_ledger_is_refused_and_names_the_way_out(self) -> None:
        theirs_only = TOOL.ledger_with(LEDGER_TEXT, TOOL.ledger_row(NEXT_VERSION, "line-b", None, "WS9.9"))
        errors = errors_for(REGISTRY_TEXT, tsv=theirs_only)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn(f"wire v{NEXT_VERSION} is `reserved` in {TOOL.VERSION_LEDGER}", errors[0])
        self.assertIn("wire_alloc.py sync", errors[0])
        errors = errors_for(self.reserved("line-a", "a"), tsv=LEDGER_TEXT)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn(f"has NO row in {TOOL.VERSION_LEDGER}", errors[0])
        # Reserved in BOTH, for DIFFERENT holders: the race itself, and the one
        # shape a number-and-status comparison calls agreement.  (An earlier
        # draft of this test asserted exactly that, as "bound and green".)
        errors = errors_for(self.reserved("line-a", "a"), tsv=theirs_only)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("reserved in BOTH ledgers, for different holders", errors[0])
        # One holder, named the same way in both: bound and green.
        self.assertEqual(errors_for(self.reserved("line-b", "WS9.9"), tsv=theirs_only), [])

    def test_the_constant_is_named_as_a_whole_identifier(self) -> None:
        args = argparse.Namespace(owner="WS9.9", date="2026-09-18", namespace="version", feature="line-b", constant="B_FORMAT_VERSION")
        text = TOOL.reserve(REGISTRY_TEXT, args)[0]
        theirs = TOOL.ledger_with(LEDGER_TEXT, TOOL.ledger_row(NEXT_VERSION, "line-b", "LINE_B_FORMAT_VERSION", "WS9.9"))
        errors = errors_for(text, tsv=theirs)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("constant `B_FORMAT_VERSION`", errors[0])

    def test_a_status_the_two_files_tell_differently_is_refused(self) -> None:
        retold = LEDGER_TEXT.replace("\trefused\t", "\tshipped\t", 1)
        self.assertNotEqual(retold, LEDGER_TEXT)
        errors = errors_for(REGISTRY_TEXT, tsv=retold)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("says `burned`", errors[0])
        self.assertIn("says `landed`", errors[0])

    def test_sync_copies_an_open_reservation_either_way_and_nothing_else(self) -> None:
        theirs_only = TOOL.ledger_with(LEDGER_TEXT, TOOL.ledger_row(NEXT_VERSION, "proof surface", "PROOF_SURFACE_FORMAT_VERSION", "WS1.12"))
        text, tsv, done = TOOL.sync(REGISTRY_TEXT, theirs_only, "2026-09-18")
        self.assertEqual(len(done), 1, done)
        self.assertEqual(errors_for(text, tsv=tsv), [])
        row = TOOL.parse(text)["wire_version"][-1].fields
        self.assertEqual((row["number"], row["status"], row["owner"]), (NEXT_VERSION, "reserved", "WS1.12"))
        self.assertEqual(row["constant"], "PROOF_SURFACE_FORMAT_VERSION")  # read out of their feature text
        text, tsv, done = TOOL.sync(self.reserved("line-a", "a"), LEDGER_TEXT, "2026-09-18")
        self.assertEqual(len(done), 1, done)
        self.assertEqual(errors_for(text, tsv=tsv), [])
        self.assertTrue(tsv.endswith(f"{NEXT_VERSION}\treserved\tline-a\tself\ta\n"))
        # Already in agreement: nothing to do.  A status disagreement: not sync's to settle.
        self.assertEqual(TOOL.sync(REGISTRY_TEXT, LEDGER_TEXT, "2026-09-18"), (REGISTRY_TEXT, LEDGER_TEXT, []))
        retold = LEDGER_TEXT.replace("\trefused\t", "\tshipped\t", 1)
        self.assertEqual(TOOL.sync(REGISTRY_TEXT, retold, "2026-09-18")[2], [])

    def test_takeover_renumbers_both_ledgers_together(self) -> None:
        first = LATEST + 1  # both copies start settled, so the count starts here
        with tempfile.TemporaryDirectory() as tmp:
            root = scratch_root(tmp, settled=True)

            def cli(*args: str) -> subprocess.CompletedProcess:
                return subprocess.run([sys.executable, "-B", str(TOOL_PATH), "--root", str(root), *args], capture_output=True, text=True, check=False)

            for feature in ("line-a", "line-b"):
                made = cli("reserve", "version", "--feature", feature, "--constant", f"{feature.upper().replace('-', '_')}_FORMAT_VERSION", "--owner", feature)
                self.assertEqual(made.returncode, 0, made.stderr)
            taken = cli("takeover", "--feature", "line-b")
            self.assertEqual(taken.returncode, 0, taken.stderr)
            self.assertIn("line-a", taken.stdout)
            ledger = (root / TOOL.VERSION_LEDGER).read_text(encoding="utf-8")
            self.assertTrue(
                ledger.endswith(
                    f"{first}\treserved\tline-b: LINE_B_FORMAT_VERSION\tself\tline-b\n"
                    f"{first + 1}\treserved\tline-a: LINE_A_FORMAT_VERSION\tself\tline-a\n"
                ),
                ledger[-300:],
            )
            self.assertEqual(cli("check").returncode, 0)
            self.assertEqual(cli("sync").stdout.strip(), "SYNCED: nothing to copy — the two ledgers already agree")
        self.assertEqual((ROOT / TOOL.VERSION_LEDGER).read_text(encoding="utf-8"), LEDGER_TEXT, "the CLI wrote to the REAL ledger")

    def test_a_missing_second_ledger_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = scratch_root(tmp)
            (root / TOOL.VERSION_LEDGER).unlink()
            result = subprocess.run([sys.executable, "-B", str(TOOL_PATH), "--root", str(root), "check"], capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, 1)
        self.assertIn("is missing", result.stderr)


class GrammarMatchesTheRustParser(unittest.TestCase):
    def test_everything_outside_the_one_line_grammar_is_refused(self) -> None:
        for bad in (
            "[[wire_version]]\nnumber = 1\n",
            "wire_version = [\n  { number = 01 },\n]\n",
            "wire_version = [\n  { number = 1, number = 2 },\n]\n",
            'wire_version = [\n  { feature = "a\\"b" },\n]\n',
            "wire_version = [\n  { number = 1 }\n]\n",
            "wire_version = [\n  { number = 1 },\n",
            "wire_version = [\n]\nwire_version = [\n]\n",
        ):
            with self.assertRaises(TOOL.RegistryError, msg=bad):
                TOOL.parse(bad)

    def test_a_comma_inside_a_string_is_data(self) -> None:
        tables = TOOL.parse('# c\n\nwire_version = [\n  { number = 1, feature = "a, b" },\n]\n')
        self.assertEqual(tables["wire_version"][0].fields, {"number": 1, "feature": "a, b"})


class ReservationsLandFirst(unittest.TestCase):
    def reserve(self, **kwargs) -> tuple[str, str]:
        args = argparse.Namespace(owner="lane", date="2026-09-18", **kwargs)
        return TOOL.reserve(REGISTRY_TEXT, args)

    def test_each_namespace_takes_the_next_number_and_stays_green_with_no_code(self) -> None:
        text, row = self.reserve(namespace="version", feature="probe", constant="PROBE_FORMAT_VERSION")
        self.assertIn(f"number = {NEXT_VERSION},", row)
        self.assertEqual(errors_for(text), [])

        text, row = self.reserve(namespace="tag", enum="Ty", variant="Probe", since=LATEST)
        self.assertIn(f"tag = {NEXT_TY_TAG},", row)
        self.assertEqual(errors_for(text), [])

        text, row = self.reserve(namespace="domain", domain="trust_ir.obligation.digest", binds="probe")
        self.assertIn(f"version = {NEXT_OBLIGATION_DIGEST},", row)
        self.assertEqual(errors_for(text), [])

        text, row = self.reserve(namespace="domain", domain="trust_ir.aaa.first", binds="probe")
        self.assertIn("version = 1", row)
        self.assertEqual(errors_for(text), [])

    def test_two_reservations_of_one_number_conflict_textually(self) -> None:
        # The property the one-row-per-line layout exists for: both lines of
        # work insert at the SAME place, so `git merge` reports a conflict
        # instead of silently keeping two owners of v44.
        mine, _ = self.reserve(namespace="version", feature="mine", constant=None)
        theirs, _ = self.reserve(namespace="version", feature="theirs", constant=None)
        with tempfile.TemporaryDirectory() as tmp:
            base, ours, other = (Path(tmp) / name for name in ("base", "ours", "theirs"))
            base.write_text(REGISTRY_TEXT, encoding="utf-8")
            ours.write_text(mine, encoding="utf-8")
            other.write_text(theirs, encoding="utf-8")
            merged = subprocess.run(
                ["git", "merge-file", "-p", str(ours), str(base), str(other)],
                capture_output=True,
                text=True,
                check=False,
            )
        self.assertGreater(merged.returncode, 0, "a double claim must not merge cleanly")
        self.assertIn("<<<<<<<", merged.stdout)

    def test_reservations_in_different_namespaces_merge_cleanly(self) -> None:
        mine, _ = self.reserve(namespace="version", feature="mine", constant=None)
        theirs, _ = self.reserve(namespace="tag", enum="Inst", variant="Probe", since=LATEST)
        with tempfile.TemporaryDirectory() as tmp:
            base, ours, other = (Path(tmp) / name for name in ("base", "ours", "theirs"))
            base.write_text(REGISTRY_TEXT, encoding="utf-8")
            ours.write_text(mine, encoding="utf-8")
            other.write_text(theirs, encoding="utf-8")
            merged = subprocess.run(
                ["git", "merge-file", "-p", str(ours), str(base), str(other)],
                capture_output=True,
                text=True,
                check=False,
            )
        self.assertEqual(merged.returncode, 0, merged.stdout[-400:])
        self.assertEqual(errors_for(merged.stdout), [])

    def test_the_registry_is_never_union_merged(self) -> None:
        # `.gitattributes` gives append-only SETS (`scripts/gates/*.tests`,
        # `CHANGELOG.md`) `merge=union`, which is right for them and exactly
        # wrong here: a union merge would silently KEEP both claims to one
        # number. The registry must stay on git's default text merge, where a
        # double claim is a conflict (proved above with `git merge-file`).
        inside = subprocess.run(
            ["git", "rev-parse", "--is-inside-work-tree"], cwd=ROOT, capture_output=True, text=True
        )
        if inside.returncode != 0:
            self.skipTest("not a git work tree (an exported tarball has no attributes to check)")
        attribute = subprocess.run(
            ["git", "check-attr", "merge", "--", TOOL.REGISTRY],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
        self.assertEqual(attribute, f"{TOOL.REGISTRY}: merge: unspecified")

    def test_the_cli_writes_the_row_and_prints_the_next_steps(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = scratch_root(tmp)
            result = subprocess.run(
                [
                    sys.executable, "-B", str(TOOL_PATH), "--root", str(root),
                    "reserve", "version", "--feature", "probe", "--owner", "lane",
                ],
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('status set to "landed"', result.stdout)
            self.assertIn("wire_alloc.py next", result.stdout)
            self.assertIn(
                f"number = {NEXT_VERSION},", (root / TOOL.REGISTRY).read_text(encoding="utf-8")
            )
            # One counter, two ledgers: the reservation went into BOTH.
            self.assertIn(f"\n{NEXT_VERSION}\treserved\tprobe\tself\tlane\n", (root / TOOL.VERSION_LEDGER).read_text(encoding="utf-8"))
        self.assertEqual((ROOT / TOOL.VERSION_LEDGER).read_text(encoding="utf-8"), LEDGER_TEXT, "the CLI wrote to the REAL ledger")


# A git that reads no global or system configuration (no signing hook, no
# template, no default branch surprise) for the scratch repositories below.
HERMETIC_GIT = {**os.environ, "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"}


def scratch_git(cwd: Path, *args: str) -> str:
    return subprocess.run(
        ["git", "-c", "user.name=t", "-c", "user.email=t@example.invalid", "-c", "commit.gpgsign=false", *args],
        cwd=cwd, env=HERMETIC_GIT, capture_output=True, text=True, check=True,
    ).stdout.strip()


def commit(repo: Path, message: str, *paths: str) -> str:
    """Commit `paths` (the two ledgers by default) as they are; a note file
    named after the message is committed with them, so every commit has a change."""
    (repo / f"{message}.note").write_text(message, encoding="utf-8")
    scratch_git(repo, "add", f"{message}.note", *(paths or (TOOL.REGISTRY, TOOL.VERSION_LEDGER)))
    scratch_git(repo, "commit", "-q", "-m", message)
    return scratch_git(repo, "rev-parse", "HEAD")


PROBE_LANE = "probe/lane"


class ScratchHistory:
    """A git repository the CLI runs in end to end: the two ledgers are
    committed COPIES (scratch_root) with every real pin dropped, since this
    history holds none of those commits, and DEVELOPMENT_ANCHOR is this
    history's first commit for as long as the tree is in use.  That first
    commit introduces every row, so the open claims carried over from the real
    registry are then pinned to it (`carried` of them), as a clean main's
    open claims resolve; the owners audit would otherwise fail on them once
    this main is pushed.

    `landed` is the commit that reserved one claim of `PROBE_LANE` in each
    namespace (a wire version, a tag under it, a digest domain) through the
    CLI; `docs` is a later commit on main that touched no ledger; `tip` is a
    commit on a side branch only."""

    def __init__(self, tmp: str) -> None:
        (Path(tmp) / "tree").mkdir()
        self.root = scratch_root(str(Path(tmp) / "tree"), settled=True)
        for name in (TOOL.REGISTRY, TOOL.VERSION_LEDGER):
            path = self.root / name
            path.write_text(re.sub(r"(owner = \"[^\"@]+)@[0-9a-f]+\"", r'\1"',
                                   re.sub(r"(\t[^\t\n@]+)@[0-9a-f]+$", r"\1", path.read_text(encoding="utf-8"), flags=re.M)),
                            encoding="utf-8")
        scratch_git(self.root, "init", "-q", "-b", "main")
        self.anchor = commit(self.root, "anchor")
        self.carried = self.pin_carried_claims()
        version = TOOL.next_free(TOOL.parse(self.text()), "version", None)
        for args in (
            ["version", "--feature", "probe-pin", "--constant", "PROBE_PIN_FORMAT_VERSION"],
            ["tag", "--enum", "Ty", "--variant", "ProbePin", "--since", str(version)],
            ["domain", "--domain", "trust_ir.probe_pin.claim", "--binds", "a probe"],
        ):
            code, _, err = self.cli("reserve", *args, "--owner", PROBE_LANE, "--date", "2026-09-30")
            assert code == 0, err
        self.landed = commit(self.root, "landed")
        self.docs = commit(self.root, "docs", "docs.note")
        scratch_git(self.root, "switch", "-q", "-c", "side")
        self.tip = commit(self.root, "tip")
        scratch_git(self.root, "switch", "-q", "main")
        tables = TOOL.parse(self.text())
        self.claims = {
            table: next(row for row in tables[table] if row.fields.get("owner") == PROBE_LANE) for table in TOOL.COUNTED
        }
        # Last, so a failure above leaves the module as it was.
        self.patch = mock.patch.object(TOOL, "DEVELOPMENT_ANCHOR", self.anchor)
        self.patch.start()

    def close(self) -> None:
        self.patch.stop()

    def pin_carried_claims(self) -> int:
        """Pin every open claim the anchor carries to the anchor, in both
        ledgers, and commit that; the number of claims pinned."""
        pin = self.anchor[:12]
        lines = self.text().splitlines()
        pinned = 0
        for table in TOOL.COUNTED:
            for row in TOOL.parse(self.text())[table]:
                owner = row.fields.get("owner")
                if row.fields.get("status") == "reserved" and isinstance(owner, str) and "@" not in owner:
                    lines[row.line - 1] = lines[row.line - 1].replace(f'owner = "{owner}"', f'owner = "{owner}@{pin}"')
                    pinned += 1
        (self.root / TOOL.REGISTRY).write_text("\n".join(lines) + "\n", encoding="utf-8")
        ledger = [
            re.sub(r"^(\d+\treserved\t[^\t]*\t[^\t]*\t)([^\t@]+)$", rf"\g<1>\g<2>@{pin}", line)
            for line in self.ledger().splitlines()
        ]
        (self.root / TOOL.VERSION_LEDGER).write_text("\n".join(ledger) + "\n", encoding="utf-8")
        commit(self.root, "carried")
        return pinned

    def text(self) -> str:
        return (self.root / TOOL.REGISTRY).read_text(encoding="utf-8")

    def ledger(self) -> str:
        return (self.root / TOOL.VERSION_LEDGER).read_text(encoding="utf-8")

    def cli(self, *argv: str) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = TOOL.main(["--root", str(self.root), *argv])
        return code, out.getvalue(), err.getvalue()

    def set_owner(self, table: str, owner: str) -> None:
        """Give the probe claim of `table` this owner, in both ledgers for a version."""
        row = self.claims[table]
        lines = self.text().splitlines()
        lines[row.line - 1] = re.sub(r'owner = "[^"]*"', f'owner = "{owner}"', lines[row.line - 1])
        (self.root / TOOL.REGISTRY).write_text("\n".join(lines) + "\n", encoding="utf-8")
        if table == "wire_version":
            number = row.fields["number"]
            ledger = [
                re.sub(r"\t[^\t]*$", f"\t{owner}", line) if line.startswith(f"{number}\t") else line
                for line in self.ledger().splitlines()
            ]
            (self.root / TOOL.VERSION_LEDGER).write_text("\n".join(ledger) + "\n", encoding="utf-8")


class OwnersResolve(unittest.TestCase):
    """An owner is a lane label or a label PINNED to the commit on main that
    landed its claim.  `check` holds every owner to that grammar and resolves
    every pin where the development history is present; `owners` (gate 0, when
    origin can be asked) fails on an open claim whose lane was deleted from
    origin; `pin` writes the pin that fixes it."""

    def reserve_owned_by(self, owner: str) -> str:
        text, _ = TOOL.reserve(no_open_versions(REGISTRY_TEXT), argparse.Namespace(
            owner=owner, date="2026-09-29", namespace="version", feature="probe", constant=None))
        return text

    def history(self) -> ScratchHistory:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        tree = ScratchHistory(tmp.name)
        self.addCleanup(tree.close)
        return tree

    def test_an_owner_is_a_lane_label_or_a_lane_pinned_to_a_commit(self) -> None:
        for good in ("lane", "agents/rm-WS1.14", "lane@abcdef1", "lane@" + "0123456789abcdef" * 2 + "01234567"):
            self.assertEqual(errors_for(self.reserve_owned_by(good)), [], good)
        for bad in ("a b", "lane@", "@abcdef1", "lane@abc123", "lane@ABCDEF1", "lane@abcdefg", "lane@abcdef1@abcdef1",
                    "lane@" + "0" * 41):
            errors = errors_for(self.reserve_owned_by(bad))
            self.assertTrue(any(f"owner `{bad}` is neither" in e for e in errors), (bad, errors))

    def test_every_owner_in_every_namespace_and_status_is_held_to_the_grammar(self) -> None:
        # Not only open wire versions: a tag's or a domain's owner, and the
        # owner of a landed row, are owners too.
        lines = REGISTRY_TEXT.splitlines()
        doctored = 0
        for table in TOOL.COUNTED:
            for status in sorted({row.fields.get("status") for row in TABLES[table]}):
                row = next(row for row in TABLES[table] if row.fields.get("status") == status)
                if "owner" not in row.fields:
                    continue
                broken = lines.copy()
                broken[row.line - 1] = re.sub(r'owner = "[^"]*"', 'owner = "not a lane"', broken[row.line - 1])
                errors = errors_for("\n".join(broken) + "\n")
                self.assertIn(
                    f"line {row.line}: owner `not a lane` is neither a lane label", "\n".join(errors), (table, status)
                )
                doctored += 1
        self.assertGreaterEqual(doctored, len(TOOL.COUNTED) + 1, "every namespace, and more than one status")

    def test_pin_writes_the_landing_commit_and_check_resolves_it_through_the_cli(self) -> None:
        tree = self.history()
        code, out, err = tree.cli("pin", PROBE_LANE)
        self.assertEqual(code, 0, err)
        pinned = f"{PROBE_LANE}@{tree.landed[:12]}"
        for table, row in tree.claims.items():
            self.assertIn(f'owner = "{pinned}"', tree.text().splitlines()[row.line - 1], table)
        number = tree.claims["wire_version"].fields["number"]
        self.assertIn(f"\n{number}\treserved\tprobe-pin: PROBE_PIN_FORMAT_VERSION\tself\t{pinned}\n", tree.ledger())
        self.assertEqual(out.count(f"owner `{pinned}`"), 3, out)
        code, out, err = tree.cli("check")
        self.assertEqual(code, 0, err)
        self.assertIn(f"{3 + tree.carried} owner pin(s) name the commit in HEAD's history that landed their claim", out)
        # Nothing left to pin, and an unknown lane is said, not silently done.
        self.assertEqual(tree.cli("pin", PROBE_LANE)[0], 1)
        self.assertEqual(tree.cli("pin", "nobody")[0], 1)

    def test_check_refuses_a_pin_that_did_not_land_its_claim_in_every_namespace(self) -> None:
        tree = self.history()
        landed = f"{PROBE_LANE}@{tree.landed[:12]}"
        for table in TOOL.COUNTED:
            others = [other for other in TOOL.COUNTED if other != table]
            for other in others:
                tree.set_owner(other, landed)
            name = TOOL.claim_name(table, tree.claims[table])
            for pin, why in (
                (tree.docs, f"did not land {name}"),       # on main, touched no ledger
                (tree.anchor, f"did not land {name}"),     # wrote the ledgers, but not this claim
                (tree.tip, "not in HEAD's history"),       # a branch tip, not main
                ("deadbeef", "which is no commit here"),
            ):
                tree.set_owner(table, f"{PROBE_LANE}@{pin[:12]}")
                code, _, err = tree.cli("check")
                self.assertEqual(code, 1, (table, pin, err))
                self.assertIn(why, err, (table, pin))
                self.assertIn(f"line {tree.claims[table].line}:", err, (table, pin))
            tree.set_owner(table, landed)
            code, _, err = tree.cli("check")
            self.assertEqual(code, 0, (table, err))

    def test_a_commit_that_only_rewrote_the_row_did_not_land_it(self) -> None:
        # A takeover, a note edit or the pin itself rewrites a claim's row:
        # one line out, one in.  Only the commit that introduced it landed it.
        tree = self.history()
        self.assertEqual(tree.cli("pin", PROBE_LANE)[0], 0)
        rewrote = commit(tree.root, "pinned")
        tree.set_owner("wire_version", f"{PROBE_LANE}@{rewrote[:12]}")
        code, _, err = tree.cli("check")
        self.assertEqual(code, 1, err)
        self.assertIn(f"did not land {TOOL.claim_name('wire_version', tree.claims['wire_version'])}", err)

    def test_a_landed_claims_pin_names_the_commit_that_put_it_on_main_not_the_one_that_flipped_it(self) -> None:
        # A lane that LANDED keeps its label: the pin is to the commit that
        # introduced the row (wire_versions.tsv's reserving commit for a
        # version), and the commit that flipped `reserved` to `landed` only
        # rewrote it.  A tag reserved under a landed version is a claim that
        # can land without new version rows; the INST wire batch's tags did.
        tree = self.history()
        landed_version = max(
            row.fields["number"] for row in TOOL.parse(tree.text())["wire_version"] if row.fields.get("status") == "landed"
        )
        code, _, err = tree.cli("reserve", "tag", "--enum", "Ty", "--variant", "ProbeLanded", "--since",
                                str(landed_version), "--owner", "landed/lane", "--date", "2026-10-01")
        self.assertEqual(code, 0, err)
        reserved = commit(tree.root, "reserved-under-a-landed-version")
        text = tree.text()
        flipped_text = re.sub(r'(variant = "ProbeLanded", since = \d+, status = )"reserved"', r'\1"landed"', text)
        self.assertNotEqual(flipped_text, text)
        (tree.root / TOOL.REGISTRY).write_text(flipped_text, encoding="utf-8")
        flipped = commit(tree.root, "landed-it")
        row = next(row for row in TOOL.parse(tree.text())["enum_tag"] if row.fields.get("variant") == "ProbeLanded")
        self.assertEqual(row.fields["status"], "landed")
        self.assertEqual(TOOL.landing_commit(tree.root, "enum_tag", row), reserved)
        lines = tree.text().splitlines()
        for pin, code_wanted in ((flipped, 1), (reserved, 0)):
            lines[row.line - 1] = re.sub(r'owner = "[^"]*"', f'owner = "landed/lane@{pin[:12]}"', lines[row.line - 1])
            (tree.root / TOOL.REGISTRY).write_text("\n".join(lines) + "\n", encoding="utf-8")
            code, out, err = tree.cli("check")
            self.assertEqual(code, code_wanted, (pin, out, err))
            if code_wanted:
                self.assertIn(f"line {row.line}: owner `landed/lane@{pin[:12]}` pins {pin[:12]}, which is on main "
                              "but did not land Ty tag", err)

    def test_a_pin_to_the_commit_that_claimed_another_version_of_the_domain_is_refused(self) -> None:
        tree = self.history()
        code, _, err = tree.cli("reserve", "domain", "--domain", "trust_ir.probe_pin.claim", "--binds", "a second probe",
                                "--owner", "other/lane", "--date", "2026-09-30")
        self.assertEqual(code, 0, err)
        other = commit(tree.root, "next-version")
        rows = TOOL.parse(tree.text())["digest_domain"]
        tree.claims["digest_domain"] = next(row for row in rows if row.fields.get("owner") == PROBE_LANE)
        tree.set_owner("digest_domain", f"{PROBE_LANE}@{other[:12]}")
        code, _, err = tree.cli("check")
        self.assertEqual(code, 1, err)
        self.assertIn("did not land trust_ir.probe_pin.claim.v1", err)

    def test_pin_names_the_newest_landing_when_a_claim_was_released_and_made_again(self) -> None:
        tree = self.history()
        row = tree.claims["digest_domain"]
        lines = tree.text().splitlines()
        released = lines[: row.line - 1] + lines[row.line :]
        (tree.root / TOOL.REGISTRY).write_text("\n".join(released) + "\n", encoding="utf-8")
        commit(tree.root, "released")
        code, _, err = tree.cli("reserve", "domain", "--domain", "trust_ir.probe_pin.claim", "--binds", "a probe, again",
                                "--owner", PROBE_LANE, "--date", "2026-09-30")
        self.assertEqual(code, 0, err)
        again = commit(tree.root, "again")
        code, out, err = tree.cli("pin", PROBE_LANE)
        self.assertEqual(code, 0, err)
        self.assertIn(f"trust_ir.probe_pin.claim.v1: owner `{PROBE_LANE}@{again[:12]}`", out)
        self.assertIn(f"owner `{PROBE_LANE}@{tree.landed[:12]}`", out, "the claims made once keep their landing")

    def test_without_the_development_history_a_pin_is_form_only_and_said(self) -> None:
        tree = self.history()
        tree.set_owner("enum_tag", f"{PROBE_LANE}@deadbeef")
        with mock.patch.object(TOOL, "DEVELOPMENT_ANCHOR", "f" * 40):
            code, out, err = tree.cli("check")
            self.assertEqual(code, 0, err)
            self.assertIn(f"{1 + tree.carried} owner pin(s) checked for FORM ONLY", out)
            self.assertEqual(tree.cli("owners")[0], 2)
            self.assertEqual(tree.cli("pin", PROBE_LANE)[0], 1)

    def test_the_pins_in_this_tree_resolve_or_say_why_not(self) -> None:
        # Never skipped: with the development history every pin must resolve;
        # without it (an exported snapshot) the result must SAY form only.
        problems, said = TOOL.unresolved_pins(TABLES, ROOT)
        self.assertEqual(problems, {})
        pinned = len(TOOL.owner_pins(TABLES))
        if not pinned:
            self.assertEqual(said, "no owner is pinned")
        elif TOOL.has_development_history(ROOT):
            self.assertEqual(said, f"{pinned} owner pin(s) name the commit in HEAD's history that landed their claim")
        else:
            self.assertIn("FORM ONLY", said)

    def test_the_audit_fails_on_a_deleted_lane_even_after_a_pruning_fetch(self) -> None:
        tree = self.history()
        remote = tree.root.parent / "remote.git"
        scratch_git(tree.root.parent, "init", "-q", "--bare", "-b", "main", str(remote))
        scratch_git(tree.root, "remote", "add", "origin", str(remote))
        scratch_git(tree.root, "push", "-q", "origin", "main", f"main:refs/heads/{PROBE_LANE}")
        scratch_git(tree.root, "fetch", "-q", "origin")

        code, out, err = tree.cli("owners")
        self.assertEqual(code, 0, err)
        self.assertRegex(out, rf"branch on origin  {re.escape(PROBE_LANE)}: wire v\d+, Ty tag \d+, trust_ir\.probe_pin\.claim\.v1")

        # Deleted on origin; this clone's tracking ref outlives it.
        scratch_git(remote, "branch", "-D", PROBE_LANE)
        code, _, err = tree.cli("owners")
        self.assertEqual(code, 1, err)
        self.assertIn(f"DELETED from origin  {PROBE_LANE}:", err)
        self.assertIn(f"`python3 scripts/wire_alloc.py pin {PROBE_LANE}`", err)

        # A pruning fetch removes the tracking ref; the audit remembers.
        scratch_git(tree.root, "fetch", "-q", "--prune", "origin")
        self.assertNotIn(PROBE_LANE, scratch_git(tree.root, "for-each-ref", "--format=%(refname)"))
        code, _, err = tree.cli("owners")
        self.assertEqual(code, 1, err)
        self.assertIn(f"DELETED from origin  {PROBE_LANE}:", err)

        # The fix the audit names.
        self.assertEqual(tree.cli("pin", PROBE_LANE)[0], 0)
        code, out, err = tree.cli("owners")
        self.assertEqual(code, 0, err)
        self.assertIn(f"pinned  {PROBE_LANE}@{tree.landed[:12]}:", out)

        # Nothing judged when origin cannot be asked.
        code, _, err = tree.cli("owners", "--remote", "nowhere")
        self.assertEqual(code, 2)
        self.assertIn("nothing was judged", err)

    def test_the_audit_knows_a_lane_merged_from_origin(self) -> None:
        tree = self.history()
        remote = tree.root.parent / "remote.git"
        scratch_git(tree.root.parent, "init", "-q", "--bare", "-b", "main", str(remote))
        scratch_git(tree.root, "remote", "add", "origin", str(remote))
        scratch_git(tree.root, "push", "-q", "origin", "main")
        # A lane merged into main FROM origin, deleted and pruned before any
        # audit here saw it: the merge in HEAD's history is the evidence.
        scratch_git(tree.root, "switch", "-q", "-c", "merged/lane")
        commit(tree.root, "lane-work", "lane-work.note")
        scratch_git(tree.root, "push", "-q", "origin", "merged/lane")
        scratch_git(tree.root, "switch", "-q", "main")
        scratch_git(tree.root, "fetch", "-q", "origin")
        scratch_git(tree.root, "merge", "-q", "--no-ff", "--no-edit", "origin/merged/lane")
        scratch_git(remote, "branch", "-D", "merged/lane")
        scratch_git(tree.root, "branch", "-q", "-D", "merged/lane")
        scratch_git(tree.root, "fetch", "-q", "--prune", "origin")
        tree.set_owner("enum_tag", "merged/lane")
        code, out, err = tree.cli("owners")
        self.assertEqual(code, 1, out + err)
        self.assertIn("DELETED from origin  merged/lane: Ty tag", err)

    def test_a_claim_on_origins_main_under_a_lane_no_branch_carries_fails_until_it_is_pinned(self) -> None:
        # The roadmap runner commits its `agents/rm-*` lanes straight onto main
        # and never pushes them: such a label resolves only in the clone that
        # wrote it, and once its claim is on origin's main the audit fails in
        # every other clone until the claim is pinned.
        lane = "agents/straight-to-main"
        tree = self.history()
        remote = tree.root.parent / "remote.git"
        scratch_git(tree.root.parent, "init", "-q", "--bare", "-b", "main", str(remote))
        scratch_git(tree.root, "remote", "add", "origin", str(remote))
        for table in TOOL.COUNTED:
            tree.set_owner(table, lane)
        commit(tree.root, "relabelled")

        # Not on origin's main yet (origin has no main): listed, not judged.
        code, out, err = tree.cli("owners")
        self.assertEqual(code, 0, err)
        self.assertRegex(out, rf"not seen here  {re.escape(lane)}: wire v\d+, Ty tag \d+, trust_ir\.probe_pin\.claim\.v1")

        scratch_git(tree.root, "push", "-q", "origin", "main")
        code, out, err = tree.cli("owners")
        self.assertEqual(code, 1, out + err)
        self.assertRegex(err, rf"UNPINNED ON MAIN  {re.escape(lane)}: wire v\d+, Ty tag \d+, trust_ir\.probe_pin\.claim\.v1")
        self.assertIn(f"`python3 scripts/wire_alloc.py pin {lane}`", err)

        # Origin's main moved on in another clone: this one lacks the tip
        # origin reports, and judges by its remote-tracking main.
        other = tree.root.parent / "other"
        scratch_git(tree.root.parent, "clone", "-q", str(remote), str(other))
        commit(other, "elsewhere", "elsewhere.note")
        scratch_git(other, "push", "-q", "origin", "main")
        code, _, err = tree.cli("owners")
        self.assertEqual(code, 1, err)
        self.assertIn(f"UNPINNED ON MAIN  {lane}:", err)
        # Without that ref either, it cannot tell that the claim is on
        # origin's main.
        scratch_git(tree.root, "update-ref", "-d", "refs/remotes/origin/main")
        code, out, err = tree.cli("owners")
        self.assertEqual(code, 0, err)
        self.assertIn(f"not seen here  {lane}:", out)
        scratch_git(tree.root, "fetch", "-q", "origin")
        code, _, err = tree.cli("owners")
        self.assertEqual(code, 1, err)
        self.assertIn(f"UNPINNED ON MAIN  {lane}:", err)

        # In the clone that holds the lane's branch, the label resolves.
        scratch_git(tree.root, "branch", "-q", lane)
        code, out, err = tree.cli("owners")
        self.assertEqual(code, 0, err)
        self.assertIn(f"local branch only  {lane}:", out)
        scratch_git(tree.root, "branch", "-q", "-D", lane)

        # The fix the audit names.
        self.assertEqual(tree.cli("pin", lane)[0], 0)
        code, out, err = tree.cli("owners")
        self.assertEqual(code, 0, err)
        self.assertIn(f"pinned  {lane}@{tree.landed[:12]}:", out)
        commit(tree.root, "pinned")

        # The same lane's next claim, committed here but not pushed: listed.
        code, _, err = tree.cli("reserve", "domain", "--domain", "trust_ir.probe_unpushed.claim", "--binds",
                                "an unpushed probe", "--owner", lane, "--date", "2026-10-02")
        self.assertEqual(code, 0, err)
        commit(tree.root, "unpushed")
        code, out, err = tree.cli("owners")
        self.assertEqual(code, 0, err)
        self.assertIn(f"not seen here  {lane}: trust_ir.probe_unpushed.claim.v1", out)


class GateZeroRunsTheOwnersAudit(unittest.TestCase):
    """The audit counts only if something runs it: gate 0 does, as a FAIL on a
    deleted lane and a printed SKIP (pass) when origin cannot be asked."""

    GATES = (ROOT / "scripts" / "ci_gates.sh").read_text(encoding="utf-8")

    def test_gate_zero_runs_it(self) -> None:
        gate_zero = self.GATES.split("# --- Gate 0:", 1)[1].split("# --- Gate 1:", 1)[0]
        self.assertIn("gate wire-allocation-owners wire_owners_audit\n", gate_zero)

    def test_the_gate_maps_the_audit_exit_codes(self) -> None:
        function = re.search(r"^wire_owners_audit\(\) \{\n.*?^\}\n", self.GATES, re.M | re.S)
        self.assertIsNotNone(function)
        with tempfile.TemporaryDirectory() as tmp:
            # A stand-in for wire_alloc.py that exits with the code it is told.
            (Path(tmp) / "scripts").mkdir()
            (Path(tmp) / "scripts" / "wire_alloc.py").write_text(
                "import os, sys\nprint(' '.join(sys.argv[1:]))\nsys.exit(int(os.environ['AUDIT_RC']))\n", encoding="utf-8"
            )
            for audit, gate, said in ((0, 0, ""), (1, 1, ""), (2, 0, "SKIP: the wire-allocation owners audit")):
                run = subprocess.run(
                    ["bash", "-c", f'ROOT="$1"; {function.group(0)}\nwire_owners_audit', "gate", tmp],
                    env={**os.environ, "AUDIT_RC": str(audit)}, capture_output=True, text=True, check=False,
                )
                self.assertEqual(run.returncode, gate, (audit, run.stdout, run.stderr))
                self.assertIn(f"--root {tmp} owners", run.stdout)
                self.assertIn(said, run.stdout)


if __name__ == "__main__":
    unittest.main()
