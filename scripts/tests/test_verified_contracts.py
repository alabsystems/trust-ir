"""Guards for the verified lane (scripts/verified_contracts.py, gate 13).

The lane's own claim is per row, so its inputs must be exact: every mutant's
anchor occurs exactly once in the real source (trust-ir's included), every law
a mutant is said to flip is a real law inside the mutant's scope, laws.rs
declares nothing public but laws, the scoped copy of laws.rs keeps exactly the
scope's laws, and the report reader accepts only `proved` + `Certified` +
`KernelRechecked` rows. None of this runs the Trust compiler; it holds the
gate's bookkeeping to the tree.
"""

import contextlib
import copy
import dataclasses
import io
import json
import os
import re
import shlex
import shutil
import sys
import tempfile
import unittest
from collections import Counter
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

import verified_contracts as vc  # noqa: E402


def report(rows):
    """A minimal report.json shape: rows = [(name, [(kind, status, assurance, validation)])]."""
    prefix = (
        'cargo-target(package_id="path+file:///x#trust-ir-laws@0.14.0",package="trust-ir-laws",'
        'kind=["lib"],proof_unit_role="primary")'
    )
    functions = []
    for name, obs in rows:
        functions.append(
            {
                "function": f"{prefix}::trust_ir_laws::laws::{name}",
                "summary": {"verdict": "Verified" if all(o[1] == "proved" for o in obs) and obs else "Inconclusive"},
                "obligations": [
                    {
                        "obligation_id": f"vc:trust_ir_laws__{name}:{kind}:0",
                        "kind": kind,
                        "outcome": {
                            "status": status,
                            "strength": {"assurance": assurance, "grade": {"validation": validation}},
                        },
                    }
                    for kind, status, assurance, validation in obs
                ],
            }
        )
    return {"functions": functions}


class MutantBookkeeping(unittest.TestCase):
    def test_every_anchor_occurs_exactly_once_in_the_real_source(self):
        for m in vc.MUTANTS:
            self.assertTrue(m.edits, m.name)
            by_file = {}
            for e in m.edits:
                self.assertIn(e.crate, vc.CRATE_DIRS, m.name)
                self.assertNotEqual(e.old, e.new, m.name)
                by_file.setdefault((e.crate, e.file), []).append(e)
            for (crate, file), edits in by_file.items():
                text = (ROOT / vc.CRATE_DIRS[crate] / file).read_text(encoding="utf-8")
                for e in edits:
                    self.assertEqual(text.count(e.old), 1, f"{m.name}: anchor must occur exactly once")
                # the edits of one file apply together, without overlap
                self.assertNotEqual(vc.apply_edits(text, edits, m.name), text, m.name)

    def test_every_flip_names_a_law_inside_the_scope(self):
        laws = vc.law_functions(ROOT)
        for m in vc.MUTANTS:
            self.assertTrue(m.flips, m.name)
            self.assertTrue(m.scope, m.name)
            flips = vc.expand_flips(m, laws)
            self.assertTrue(flips, m.name)
            scope = set(vc.scoped_laws(m, laws))
            self.assertLess(len(flips), len(scope), f"{m.name}: some law in scope must HOLD")
            for f in flips:
                self.assertIn(f, scope, f"{m.name} flips `{f}`, outside its scope")

    def test_flips_entries_that_name_nothing_are_refused(self):
        laws = vc.law_functions(ROOT)
        for bad in ("no_such_law", "no_such_family_*"):
            m = vc.Mutant(name="x", edits=(), flips=(bad,), scope=("",), why="")
            with self.assertRaises(SystemExit):
                vc.expand_flips(m, laws)
        glob = vc.Mutant(name="x", edits=(), flips=("license_*",), scope=("",), why="")
        self.assertEqual(vc.expand_flips(glob, laws), [l for l in laws if l.startswith("license_")])

    def test_a_mutant_copies_trust_ir_exactly_when_it_edits_it(self):
        for m in vc.MUTANTS:
            self.assertEqual(m.mutates_trust_ir, any(e.crate == vc.IR_CRATE for e in m.edits))
        names = {m.name for m in vc.MUTANTS if m.mutates_trust_ir}
        self.assertTrue(names, "the trust-ir-resident tables have mutants")

    def test_every_law_is_flipped_by_some_mutant(self):
        # The per-row claim is "proved under a refuting same-shape mutant";
        # a law no mutant names would be proved about nothing (a wrapper that
        # stops calling its table still proves `ensures result == false`).
        laws = vc.law_functions(ROOT)
        self.assertEqual(vc.laws_without_a_mutant(laws), [])
        # And the check is live: hide one mutant's flips and the law it alone
        # refutes surfaces by name.
        expanded = {m.name: vc.expand_flips(m, laws) for m in vc.MUTANTS}
        only = [
            m for m in vc.MUTANTS
            if all(sum(f in expanded[n.name] for n in vc.MUTANTS) == 1 for f in expanded[m.name])
        ]
        self.assertTrue(only, "at least one mutant is the sole refuter of its laws")
        saved = vc.MUTANTS
        try:
            vc.MUTANTS = tuple(m for m in saved if m is not only[0])
            self.assertEqual(vc.laws_without_a_mutant(laws), expanded[only[0].name])
        finally:
            vc.MUTANTS = saved

    def test_every_table_has_a_mutant(self):
        names = " ".join(m.name for m in vc.MUTANTS)
        self.assertIn("coverage-", names)
        self.assertIn("license-", names)
        edited = "".join(e.old for m in vc.MUTANTS for e in m.edits)
        # every local subject table is edited by some mutant
        for subject, spelling in (
            ("visibility_contradicts_linkage", "Visibility::Hidden"),
            ("evidence_admits_kind", "ProofEvidenceShape::"),
            ("proof_ref_kind_is_ambiguous", "ObligationKindShape::Liveness\n    )"),
        ):
            self.assertIn(subject, vc.SUBJECTS)
            self.assertIn(spelling, edited, subject)

    def test_apply_mutation_fails_closed(self):
        m = vc.MUTANTS[0]
        e = m.edits[0]
        with tempfile.TemporaryDirectory() as tmp:
            src = Path(tmp) / e.file
            src.parent.mkdir(parents=True)
            src.write_text("nothing here\n", encoding="utf-8")
            with self.assertRaises(SystemExit):
                vc.apply_mutation({vc.CRATE: Path(tmp)}, m)
            src.write_text(e.old + e.old, encoding="utf-8")
            with self.assertRaises(SystemExit):
                vc.apply_mutation({vc.CRATE: Path(tmp)}, m)
            src.write_text("a\n" + e.old + "b\n", encoding="utf-8")
            vc.apply_mutation({vc.CRATE: Path(tmp)}, m)
            self.assertEqual(src.read_text(encoding="utf-8"), "a\n" + e.new + "b\n")
            # a mutant may not edit a crate it did not copy
            with self.assertRaises(SystemExit):
                vc.apply_mutation({}, m)

    def test_edits_of_one_file_apply_together_and_never_overlap(self):
        text = "aa bb cc\n"
        ab = [vc.laws_edit("f", "aa", "bb"), vc.laws_edit("f", "bb", "aa")]
        # applied to the ORIGINAL text together: a swap, not a double rewrite
        self.assertEqual(vc.apply_edits(text, ab, "t"), "bb aa cc\n")
        with self.assertRaises(SystemExit):
            vc.apply_edits(text, [vc.laws_edit("f", "aa b", "x"), vc.laws_edit("f", "a bb", "y")], "t")
        with self.assertRaises(SystemExit):
            vc.apply_edits(text, [vc.laws_edit("f", "aa", "aa")], "t")


class ScopedLawsFile(unittest.TestCase):
    def test_every_law_is_a_block_and_the_full_scope_is_the_file(self):
        text = (ROOT / vc.LAWS_FILE).read_text(encoding="utf-8")
        laws = vc.law_functions(ROOT)
        self.assertEqual([b[0] for b in vc.law_blocks(text)], laws)
        self.assertEqual(vc.scope_laws_source(text, set(laws)), text)

    def test_a_scope_keeps_exactly_its_laws_and_drops_their_docs(self):
        text = (ROOT / vc.LAWS_FILE).read_text(encoding="utf-8")
        laws = vc.law_functions(ROOT)
        for m in vc.MUTANTS:
            keep = set(vc.scoped_laws(m, laws))
            scoped = vc.scope_laws_source(text, keep)
            self.assertEqual(sorted(vc.LAW_FN.findall(scoped)), sorted(keep), m.name)
            self.assertEqual(scoped.count("ensures "), len(keep), m.name)
        # a removed law's doc comment goes with it (a dangling `///` does not compile)
        doc = "use super::*;\n\n/// doc\n/// more\npub fn a() -> bool\n    ensures result\n{\n    true\n}\n\npub fn b() -> bool\n    ensures result\n{\n    true\n}\n"
        self.assertEqual(
            vc.scope_laws_source(doc, {"b"}),
            "use super::*;\n\n\npub fn b() -> bool\n    ensures result\n{\n    true\n}\n",
        )


class MutantWorkspace(unittest.TestCase):
    def fake_root(self, base: Path) -> Path:
        root = base / "root"
        (root / "crates" / "trust-ir-laws" / "src").mkdir(parents=True)
        (root / "crates" / "trust-ir" / "src").mkdir(parents=True)
        (root / "crates" / "trust-ir" / "tests").mkdir()
        (root / "Cargo.toml").write_text(
            '[workspace]\nmembers = []\n\n[workspace.package]\nversion = "9.9.0"\nedition = "2024"\n'
            "\n[trust]\nfunction_budget_ms = 1\n",
            encoding="utf-8",
        )
        laws_src = root / "crates" / "trust-ir-laws" / "src"
        (laws_src / "lib.rs").write_text("pub fn table() -> bool { true }\n", encoding="utf-8")
        (laws_src / "laws.rs").write_text(
            "use super::*;\n\npub fn keep_me() -> bool\n    ensures result\n{\n    table()\n}\n\n"
            "pub fn drop_me() -> bool\n    ensures result\n{\n    table()\n}\n",
            encoding="utf-8",
        )
        (root / "crates" / "trust-ir" / "Cargo.toml").write_text("[package]\n", encoding="utf-8")
        (root / "crates" / "trust-ir" / "src" / "lib.rs").write_text("pub const X: bool = true;\n", encoding="utf-8")
        (root / "crates" / "trust-ir" / "tests" / "t.rs").write_text("", encoding="utf-8")
        (root / "Cargo.lock").write_text(
            'version = 4\n\n[[package]]\nname = "libc"\nversion = "0.2.189"\n', encoding="utf-8"
        )
        return root

    def test_a_laws_only_mutant_depends_on_the_real_trust_ir(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.fake_root(Path(tmp))
            dest = Path(tmp) / "m"
            m = vc.Mutant(
                name="m", edits=(vc.laws_edit("src/lib.rs", "{ true }", "{ false }"),),
                flips=("keep_me",), scope=("keep_",), why="",
            )
            vc.write_mutant_crate(root, dest, m, ["keep_me", "drop_me"])
            self.assertFalse((dest / "trust-ir").exists())
            manifest = (dest / "trust-ir-laws" / "Cargo.toml").read_text(encoding="utf-8")
            self.assertIn(f'trust-ir = {{ path = "{(root / "crates" / "trust-ir").as_posix()}" }}', manifest)
            ws = (dest / "Cargo.toml").read_text(encoding="utf-8")
            self.assertIn('members = ["trust-ir-laws"]', ws)
            self.assertIn('version = "9.9.0"', ws)
            self.assertIn("function_budget_ms = 1", ws)
            laws = (dest / "trust-ir-laws" / "src" / "laws.rs").read_text(encoding="utf-8")
            self.assertIn("keep_me", laws)
            self.assertNotIn("drop_me", laws)
            self.assertIn("{ false }", (dest / "trust-ir-laws" / "src" / "lib.rs").read_text(encoding="utf-8"))

    def test_a_trust_ir_mutant_builds_against_its_own_mutated_copy(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.fake_root(Path(tmp))
            dest = Path(tmp) / "m"
            m = vc.Mutant(
                name="m", edits=(vc.ir_edit("src/lib.rs", "X: bool = true", "X: bool = false"),),
                flips=("keep_me",), scope=("keep_", "drop_"), why="",
            )
            vc.write_mutant_crate(root, dest, m, ["keep_me", "drop_me"])
            self.assertIn("X: bool = false", (dest / "trust-ir" / "src" / "lib.rs").read_text(encoding="utf-8"))
            self.assertFalse((dest / "trust-ir" / "tests").exists(), "tests are never copied")
            self.assertIn("X: bool = true", (root / "crates" / "trust-ir" / "src" / "lib.rs").read_text(encoding="utf-8"))
            manifest = (dest / "trust-ir-laws" / "Cargo.toml").read_text(encoding="utf-8")
            self.assertIn('trust-ir = { path = "../trust-ir" }', manifest)
            self.assertIn('members = ["trust-ir-laws", "trust-ir"]', (dest / "Cargo.toml").read_text(encoding="utf-8"))

    def test_a_mutant_resolves_through_the_roots_lockfile(self):
        # The base run builds the root's locked versions; a mutant that
        # resolved afresh could build (and execute the build script of) a
        # newer release than the base run did.
        m = vc.Mutant(
            name="m", edits=(vc.laws_edit("src/lib.rs", "{ true }", "{ false }"),),
            flips=("keep_me",), scope=("keep_",), why="",
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = self.fake_root(Path(tmp))
            dest = Path(tmp) / "m"
            vc.write_mutant_crate(root, dest, m, ["keep_me", "drop_me"])
            self.assertEqual(
                (dest / "Cargo.lock").read_text(encoding="utf-8"), (root / "Cargo.lock").read_text(encoding="utf-8")
            )
            (root / "Cargo.lock").unlink()
            with self.assertRaises(SystemExit) as refused:
                vc.write_mutant_crate(root, dest, m, ["keep_me", "drop_me"])
            self.assertIn("Cargo.lock is missing", str(refused.exception))


class LawWiring(unittest.TestCase):
    """Every law is exactly one call of its own table at the cell its name
    spells. The batched trust-ir mutant negates every table at once, so it
    flips a law WHICHEVER table the law calls; this is the half of "the law is
    about its table" the flip cannot give (review, 2026-09-29)."""

    KERNEL = "pub fn kernel_tier_pending() -> bool\n    ensures result == false\n{\n    ProofStatus::Pending.is_kernel_tier()\n}"
    TERMINATOR = "pub fn terminator_bin_op() -> bool\n    ensures result == false\n{\n    InstShape::BinOp.is_terminator()\n}"

    def laws_text(self):
        return (ROOT / vc.LAWS_FILE).read_text(encoding="utf-8")

    def miswired(self):
        """The review's measured mis-wiring: both laws still PROVED (their
        polarity happens to match) and both flipped under the every-table
        negation, so the gate passed."""
        text = self.laws_text()
        self.assertEqual(text.count(self.KERNEL), 1)
        self.assertEqual(text.count(self.TERMINATOR), 1)
        return text.replace(self.KERNEL, self.KERNEL.replace("is_kernel_tier", "is_discharged_tier")).replace(
            self.TERMINATOR,
            self.TERMINATOR.replace("InstShape::BinOp.is_terminator", "AllocOrigin::CMalloc.is_reference_counted"),
        )

    def test_every_law_calls_its_own_table_at_its_own_cell(self):
        text = self.laws_text()
        self.assertEqual([name for name, _ in vc.law_bodies(text)], vc.law_functions(ROOT))
        self.assertEqual(vc.law_wiring_errors(text), [])

    def test_every_wiring_entry_is_used_and_the_entries_are_disjoint(self):
        bodies = [vc.normalize_body(body) for _, body in vc.law_bodies(self.laws_text())]
        for w in vc.WIRING:
            rx = vc.wiring_regex(w)
            self.assertTrue(any(rx.fullmatch(b) for b in bodies), f"WIRING entry `{w.name}` matches no law")
        for b in bodies:
            self.assertEqual(sum(1 for w in vc.WIRING if vc.wiring_regex(w).fullmatch(b)), 1, b)

    def test_a_law_repointed_at_another_table_is_refused_by_name(self):
        errors = vc.law_wiring_errors(self.miswired())
        self.assertEqual(len(errors), 2, errors)
        self.assertTrue(errors[0].startswith("kernel_tier_pending: "), errors)
        self.assertIn("`discharged_tier_pending`", errors[0])
        self.assertTrue(errors[1].startswith("terminator_bin_op: "), errors)
        self.assertIn("`rc_c_malloc`", errors[1])

    def test_the_wrong_cell_a_constant_or_a_second_call_is_refused(self):
        text = self.laws_text()
        for body in (
            "ProofStatus::Failed.is_kernel_tier()",
            "false",
            "ProofStatus::Pending.is_kernel_tier() && ProofStatus::Pending.is_discharged_tier()",
            "!ProofStatus::Pending.is_kernel_tier()",
        ):
            with self.subTest(body=body):
                bad = text.replace(self.KERNEL, self.KERNEL.replace("ProofStatus::Pending.is_kernel_tier()", body))
                errors = vc.law_wiring_errors(bad)
                self.assertEqual(len(errors), 1, errors)
                self.assertTrue(errors[0].startswith("kernel_tier_pending: "), errors)

    def test_the_gate_refuses_a_miswired_law_before_any_run(self):
        # main() checks the wiring before it resolves targo, so a mis-wired
        # laws.rs never reaches the lane (and this test needs no toolchain).
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "root"
            (root / vc.LAWS_FILE).parent.mkdir(parents=True)
            (root / vc.LAWS_FILE).write_text(self.miswired(), encoding="utf-8")
            with mock.patch.object(vc, "resolve_targo", side_effect=AssertionError("reached the lane")):
                with self.assertRaises(SystemExit) as refused:
                    vc.main(["--root", str(root), "--out", str(Path(tmp) / "out")])
            message = str(refused.exception.code)
            self.assertIn("kernel_tier_pending", message)
            self.assertIn("terminator_bin_op", message)

    def test_snake_spells_variants_as_the_law_names_do(self):
        for variant, name in (
            ("SysV64", "sys_v64"),
            ("CMalloc", "c_malloc"),
            ("CUnwind", "c_unwind"),
            ("GEP", "gep"),
            ("AtomicRMW", "atomic_rmw"),
            ("ICmp", "i_cmp"),
            ("U128", "u128"),
            ("SeqMapAddK", "seq_map_add_k"),
            ("LinkOnceOdr", "link_once_odr"),
        ):
            self.assertEqual(vc.snake(variant), name)

    def test_normalization_keeps_tokens_apart_and_drops_layout(self):
        self.assertEqual(
            vc.normalize_body("    coverage_supports(\n        CoverageBound::UnwindBounded { depth: d },\n        CoverageBound::Unrecorded,\n    )"),
            "coverage_supports(CoverageBound::UnwindBounded{depth:d},CoverageBound::Unrecorded)",
        )
        self.assertEqual(vc.normalize_body("    if a < b {\n        return true;\n    }"), "if a<b{return true;}")


class WhatGate13Holds(unittest.TestCase):
    """`holding`: gate 13's pre-run rules over a laws file, stated ONCE, and
    read by gate 0 (`scripts/check_enforcement_links.py`), whose
    `(proved-contract)` class is witnessed only by a law this holds. A law is
    held when EVERY pre-run rule passes for the whole file, because gate 13
    then refuses to run at all: no law of a file it refuses is proved."""

    def laws_text(self):
        return (ROOT / vc.LAWS_FILE).read_text(encoding="utf-8")

    def held_in(self, text):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            if text is not None:
                (root / vc.LAWS_FILE).parent.mkdir(parents=True)
                (root / vc.LAWS_FILE).write_text(text, encoding="utf-8")
            return vc.holding(root)

    def test_the_live_laws_file_is_held_whole_and_each_law_names_its_table(self):
        held = vc.holding(ROOT)
        self.assertEqual(held.errors, ())
        self.assertEqual(held.held, tuple(vc.law_functions(ROOT)))
        # A law's table is the one its WIRING family calls; the only family
        # that calls no table is u64 `>=` transitivity (half of L8).
        self.assertEqual(set(held.tables), set(held.held))
        self.assertEqual([law for law in held.held if held.tables[law] is None], ["u64_ge_is_transitive"])
        self.assertEqual(held.tables["rc_rust_heap"], "AllocOrigin::is_reference_counted")
        self.assertEqual(held.tables["coverage_reflexive_unbounded"], "coverage_supports")

    def test_a_law_no_mutant_names_makes_the_file_hold_nothing(self):
        # `coverage_*` is wired by name, so the new law is well-wired; no
        # mutant's `flips` names it, and gate 13 refuses the whole file.
        extra = "\npub fn coverage_unflipped() -> bool\n    ensures result\n{\n    coverage_supports(CoverageBound::Unbounded, CoverageBound::Unbounded)\n}\n"
        held = self.held_in(self.laws_text() + extra)
        self.assertEqual(held.held, ())
        self.assertTrue(any("coverage_unflipped" in e for e in held.errors), held.errors)

    def test_a_miswired_law_makes_the_file_hold_nothing(self):
        text = self.laws_text().replace(
            "{\n    ProofStatus::Pending.is_kernel_tier()\n}", "{\n    ProofStatus::Pending.is_discharged_tier()\n}"
        )
        self.assertNotEqual(text, self.laws_text())
        held = self.held_in(text)
        self.assertEqual(held.held, ())
        self.assertTrue(any("kernel_tier_pending" in e for e in held.errors), held.errors)

    def test_a_missing_or_foreign_laws_file_holds_nothing(self):
        # ... a file with a law whose block never closes included: never a raise.
        for text in (None, "pub struct NotALaw;\n", "", "pub fn unclosed() -> bool\n    ensures result\n{\n    true\n"):
            with self.subTest(text=text):
                held = self.held_in(text)
                self.assertEqual(held.held, ())
                self.assertTrue(held.errors)

    def test_main_refuses_on_the_holding_rules_before_any_run(self):
        # The pre-run refusal and gate 0's witness rule are ONE rule: main()
        # raises exactly the holding's errors.
        extra = "\npub fn coverage_unflipped() -> bool\n    ensures result\n{\n    coverage_supports(CoverageBound::Unbounded, CoverageBound::Unbounded)\n}\n"
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "root"
            (root / vc.LAWS_FILE).parent.mkdir(parents=True)
            (root / vc.LAWS_FILE).write_text(self.laws_text() + extra, encoding="utf-8")
            with mock.patch.object(vc, "resolve_targo", side_effect=AssertionError("reached the lane")):
                with self.assertRaises(SystemExit) as refused:
                    vc.main(["--root", str(root), "--out", str(Path(tmp) / "out")])
            self.assertEqual(str(refused.exception.code), "\n".join(vc.holding(root).errors))

    def test_every_held_law_has_the_verdict_its_ensures_states(self):
        # Gate 0's rule E5 reads each law's verdict from here, so the map
        # covers the held laws exactly, each of one `ENSURES_SHAPES` kind,
        # and a verdict spells back to the `ensures` line it was read from.
        held = vc.holding(ROOT)
        verdicts = getattr(held, "verdicts", None)
        self.assertIsNotNone(verdicts, "gate 13's holding reads no law's verdict")
        self.assertEqual(set(held.verdicts), set(held.held))
        kinds = {kind for kind, _ in vc.ENSURES_SHAPES}
        self.assertEqual({v.kind for v in held.verdicts.values()}, kinds)
        text = self.laws_text()
        for law, verdict in held.verdicts.items():
            self.assertIn(f"pub fn {law}(", text)
            block = text[text.index(f"pub fn {law}(") :]
            self.assertEqual(" ".join(block.split("{", 1)[0].split("ensures", 1)[1].split()), verdict.ensures, law)
        self.assertEqual(held.verdicts["rc_rust_heap"], vc.Verdict("false"))
        self.assertEqual(held.verdicts["rc_clean_heap"], vc.Verdict("true"))
        self.assertEqual(held.verdicts["coverage_unwind_is_magnitude_order"], vc.Verdict("relation", "have >= need"))
        # ... and what E5 reads beside it: each law's family, each cell law's
        # operands, each operand enum's variants.
        self.assertEqual(held.families["rc_rust_heap"], "rc_{V}")
        self.assertEqual(held.cells["rc_rust_heap"], (("variant", "AllocOrigin", "RustHeap"),))
        self.assertIn("RustHeap", held.domains["AllocOrigin"])
        self.assertNotIn("coverage_reflexive_unbounded", held.cells)

    def test_a_contract_outside_the_ensures_shapes_makes_the_file_hold_nothing(self):
        text = self.laws_text()
        law = "rc_clean_heap"
        signature = f"pub fn {law}() -> bool\n    ensures result\n"
        self.assertEqual(text.count(signature), 1)
        for contract in (
            "    ensures !result\n",
            "    ensures result == true\n",
            "    ensures result == (a) || (b)\n",
            "    requires true\n    ensures result\n",
            "    ensures result\n    ensures result\n",
        ):
            with self.subTest(contract=contract):
                held = self.held_in(text.replace(signature, f"pub fn {law}() -> bool\n" + contract))
                self.assertEqual(held.held, ())
                self.assertTrue(any(e.startswith(f"{law}: its contract") and "ensures result == false" in e for e in held.errors), held.errors)
        # Whitespace is not a shape: a wrapped clause reads the same.
        held = self.held_in(text.replace(signature, f"pub fn {law}() -> bool\n    ensures\n        result\n"))
        self.assertFalse(any(e.startswith(f"{law}:") for e in held.errors), held.errors)

    def test_main_refuses_a_contract_outside_the_ensures_shapes_before_any_run(self):
        signature = "pub fn rc_clean_heap() -> bool\n    ensures result\n"
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "root"
            (root / vc.LAWS_FILE).parent.mkdir(parents=True)
            (root / vc.LAWS_FILE).write_text(self.laws_text().replace(signature, signature.replace("ensures result", "ensures !result")), encoding="utf-8")
            with mock.patch.object(vc, "resolve_targo", side_effect=AssertionError("reached the lane")):
                with self.assertRaises(SystemExit) as refused:
                    vc.main(["--root", str(root), "--out", str(Path(tmp) / "out")])
            self.assertIn("rc_clean_heap: its contract `ensures !result`", str(refused.exception.code))

    def test_every_wiring_table_names_the_call_its_body_makes(self):
        # Gate 0 holds a `(proved-contract)` entry to citing its laws' TABLE
        # by this field, so the field must name the call the body makes: a
        # `Type::method` table's body starts at `Type::` and calls
        # `.method(`; a free table's body starts with the call; a family
        # that calls nothing names no table.
        for w in vc.WIRING:
            with self.subTest(family=w.name):
                if w.table_fn is None:
                    self.assertIsNone(re.search(r"[A-Za-z_][A-Za-z0-9_]*\(", w.body), w.body)
                    continue
                segments = w.table_fn.split("::")
                self.assertIn(len(segments), (1, 2), w.table_fn)
                if len(segments) == 2:
                    self.assertTrue(w.body.startswith(segments[0] + "::"), w.body)
                    self.assertEqual(w.body.count("." + segments[1] + "("), 1, w.body)
                else:
                    self.assertTrue(w.body.startswith(segments[0] + "("), w.body)


class EveryCellOfACellTableHasALaw(unittest.TestCase):
    """`cell_completeness`, one of `holding`'s pre-run rules: a table every
    law of which is one call over unit variants and enum-typed parameters is
    a CELL TABLE, and it is held to a law at every cell of its operand enums,
    read from the source. Before this rule a deleted cell law (the review's
    a13: `ambiguous_custom`) or a new variant with no law left gate 13 and
    gate 0 green while a `PROVED, every cell` comment and a glob citation
    still claimed the cell."""

    def laws_text(self):
        return (ROOT / vc.LAWS_FILE).read_text(encoding="utf-8")

    def holding_of(self, laws_text, edit=None):
        """`holding` over a tree carrying `laws_text` and a copy of every
        source file that defines an enum the real laws range over, after
        `edit(root)`."""
        names = vc.cell_enum_names(self.laws_text())
        defs, errors = vc.enum_definitions(ROOT, names)
        self.assertEqual(errors, [])
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for path in sorted({d.path for ds in defs.values() for d in ds}):
                (root / path).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / path, root / path)
            (root / vc.LAWS_FILE).parent.mkdir(parents=True, exist_ok=True)
            (root / vc.LAWS_FILE).write_text(laws_text, encoding="utf-8")
            if edit is not None:
                edit(root)
            return vc.holding(root)

    @staticmethod
    def edit_file(path, old, new):
        def edit(root):
            text = (root / path).read_text(encoding="utf-8")
            assert text.count(old) == 1, (path, old)
            (root / path).write_text(text.replace(old, new), encoding="utf-8")

        return edit

    def without_law(self, name):
        text = self.laws_text()
        for law, start, end in vc.law_blocks(text):
            if law == name:
                return text[:start] + text[end:]
        self.fail(f"no law {name}")

    def test_the_live_tables_over_enums_are_held_complete_and_the_payload_table_is_not_enumerated(self):
        held = vc.holding(ROOT)
        self.assertEqual(held.errors, ())
        tables = {t for t in held.tables.values() if t}
        # `coverage_supports` has laws over `u64` depths: no finite domain.
        self.assertNotIn("coverage_supports", held.cell_tables)
        for table in (
            "AllocOrigin::is_reference_counted",
            "ExternRefSite::admits_shape",
            "evidence_admits_kind",
            "license_admits_body",
            "proof_ref_kind_is_ambiguous",
            "visibility_contradicts_linkage",
        ):
            self.assertIn(table, held.cell_tables)
        # Every table is either held complete or has a law that is not a cell law.
        rows = vc.cell_rows(self.laws_text(), vc.law_wiring(self.laws_text()))
        for table in tables - set(held.cell_tables):
            self.assertTrue(any(ops is None for _, _, ops in rows[table]), table)

    def test_the_copied_tree_holds_every_law(self):
        # The control for every test below: the copy alone refuses nothing.
        self.assertEqual(self.holding_of(self.laws_text()).errors, ())

    def test_a_deleted_cell_law_makes_the_file_hold_nothing(self):
        held = self.holding_of(self.without_law("ambiguous_custom"))
        self.assertEqual(held.held, ())
        self.assertTrue(
            any(
                "`proof_ref_kind_is_ambiguous`" in e and "(ObligationKindShape::Custom)" in e and "`pub fn ambiguous_custom`" in e
                for e in held.errors
            ),
            held.errors,
        )

    def test_a_new_variant_without_its_law_makes_the_file_hold_nothing(self):
        edit = self.edit_file(
            "crates/trust-ir/src/inst.rs", "pub enum AllocOrigin {", "pub enum AllocOrigin {\n    /// Planted.\n    PlantedHeap,"
        )
        held = self.holding_of(self.laws_text(), edit)
        self.assertEqual(held.held, ())
        self.assertTrue(
            any("(AllocOrigin::PlantedHeap)" in e and "`pub fn rc_planted_heap`" in e for e in held.errors), held.errors
        )

    def test_a_new_obligation_kind_leaves_every_table_with_a_cell_family_over_kinds_incomplete(self):
        # The review's forward scenario: a 17th kind. A table whose kind axis
        # is only ever a parameter would stay complete; none is.
        edit = self.edit_file(
            "crates/trust-ir/src/proof/obligations.rs",
            "        Ownership,\n        Custom,\n    }\n}",
            "        Ownership,\n        Custom,\n        Planted,\n    }\n}",
        )
        held = self.holding_of(self.laws_text(), edit)
        rows = vc.cell_rows(self.laws_text(), vc.law_wiring(self.laws_text()))
        over_kinds = {
            table
            for table, laws in rows.items()
            if any(op[:2] == ("variant", "ObligationKindShape") for _, _, ops in laws for op in ops or [])
        }
        self.assertIn("proof_ref_kind_is_ambiguous", over_kinds)
        self.assertIn("ExternRefSite::admits_shape", over_kinds)
        refused = {t for t in over_kinds if any(f"cell table `{t}`" in e and "ObligationKindShape::Planted" in e for e in held.errors)}
        self.assertEqual(refused, over_kinds)
        self.assertTrue(any("`pub fn backed_by_planted`" in e for e in held.errors), held.errors)

    def test_an_enum_defined_twice_or_not_at_all_cannot_be_enumerated(self):
        def twice(root):
            with open(root / "crates/trust-ir-laws/src/lib.rs", "a", encoding="utf-8") as f:
                f.write("\npub enum AllocOrigin { Other }\n")

        held = self.holding_of(self.laws_text(), twice)
        self.assertTrue(any("cannot enumerate `AllocOrigin`" in e and "2 definitions" in e for e in held.errors), held.errors)

        def gone(root):
            (root / "crates/trust-ir/src/proof/obligations.rs").unlink()

        held = self.holding_of(self.laws_text(), gone)
        self.assertTrue(any("cannot enumerate `ProofStatus`" in e and "0 definitions" in e for e in held.errors), held.errors)
        self.assertEqual(held.held, ())

    def test_a_commented_out_enum_is_no_definition(self):
        # Comments and literals are masked before the scan.
        def commented(root):
            with open(root / "crates/trust-ir-laws/src/lib.rs", "a", encoding="utf-8") as f:
                f.write('\n// pub enum AllocOrigin { Other }\nconst S: &str = "enum AllocOrigin { Other }";\n')

        self.assertEqual(self.holding_of(self.laws_text(), commented).errors, ())

    def test_a_law_over_a_variant_its_enum_lacks_is_refused(self):
        stray = "\npub fn interposable_bogus() -> bool\n    ensures result\n{\n    Linkage::Bogus.is_interposable()\n}\n"
        held = self.holding_of(self.laws_text() + stray)
        self.assertTrue(any("interposable_bogus (`Linkage::Bogus` is no variant" in e for e in held.errors), held.errors)

    def test_a_table_leaves_the_rule_only_by_name(self):
        # A law that stops being a cell law (its enum parameter retyped) would
        # otherwise take its whole table out of the rule, silently.
        sig = "pub fn call_edge_admits_nothing(kind: ObligationKindShape) -> bool"
        self.assertEqual(self.laws_text().count(sig), 1)
        held = self.holding_of(self.laws_text().replace(sig, sig.replace("ObligationKindShape", "u64")))
        self.assertTrue(
            any("cell table `ExternRefSite::admits_shape`" in e and "call_edge_admits_nothing" in e for e in held.errors),
            held.errors,
        )
        # A path-typed parameter is the same enum.
        qualified = self.laws_text().replace(sig, sig.replace("ObligationKindShape", "trust_ir::proof::ObligationKindShape"))
        self.assertEqual(self.holding_of(qualified).errors, ())
        # And the list names only tables that ARE over payloads.
        with mock.patch.object(vc, "PAYLOAD_TABLES", vc.PAYLOAD_TABLES + ("AllocOrigin::is_reference_counted",)):
            held = self.holding_of(self.laws_text())
        self.assertTrue(any("`AllocOrigin::is_reference_counted` is named in PAYLOAD_TABLES" in e for e in held.errors), held.errors)

    def test_variant_names_skip_docs_attributes_payloads_and_discriminants(self):
        from check_no_ignored_rust import mask_non_code

        body = mask_non_code(
            "\n    /// A doc, with a comma.\n    #[default]\n    A,\n    B(u32, u64),\n    C { x: u8, y: u8 },\n"
            '    #[cfg(feature = "x")]\n    D = 4,\n    // E,\n'
        )
        self.assertEqual(vc.enum_variant_names(body), ("A", "B", "C", "D"))

    def test_cell_operands(self):
        kinds = {"kind": "ObligationKindShape"}
        self.assertEqual(vc.cell_operands("Linkage::Weak.is_interposable()", {}), [("variant", "Linkage", "Weak")])
        self.assertEqual(
            vc.cell_operands("ExternRefSite::CallEdge.admits_shape(kind)", kinds),
            [("variant", "ExternRefSite", "CallEdge"), ("all", "ObligationKindShape")],
        )
        self.assertEqual(
            vc.cell_operands("license_admits_body(GateShape::Gated,unlicensed)", {"unlicensed": "UnlicensedBodyPolicy"}),
            [("variant", "GateShape", "Gated"), ("all", "UnlicensedBodyPolicy")],
        )
        self.assertEqual(
            vc.cell_operands("ExternRefSite::CallEdge.admits_shape(kind)", {"kind": "trust_ir::proof::ObligationKindShape"}),
            [("variant", "ExternRefSite", "CallEdge"), ("all", "ObligationKindShape")],
        )
        # A payload, a `u64` parameter, an unknown parameter or no call: not a cell law.
        self.assertIsNone(vc.cell_operands("coverage_supports(CoverageBound::UnwindBounded{depth:d},CoverageBound::Unbounded)", {}))
        self.assertIsNone(vc.cell_operands("coverage_supports(CoverageBound::Unbounded,n)", {"n": "u64"}))
        self.assertIsNone(vc.cell_operands("ExternRefSite::CallEdge.admits_shape(kind)", {}))
        self.assertIsNone(vc.cell_operands("if a<b{return true;}if b<c{return true;}a>=c", {}))


class TheFreshIdRuleIsHeldRowByRow(unittest.TestCase):
    """Round 11's ONE fresh-id rule (`trust_ir::value::{FreshIds, IdRun}`,
    r11 R1) decides by three monomorphic `u32` tables resident in trust-ir:
    whether an id has a successor (the exhaustion row: refused, never wrapped,
    at `u32::MAX`), whether a run fits the room above its first id, and
    whether an id lies below a reserved bound. Gate 13 holds a law at every
    boundary row of each, wired to its own table and named by a refuting
    mutant. The generic cursor itself has no provable form in the lane
    (measured: its rows are UNKNOWN), which is why the decisions are tables."""

    VALUE_RS = vc.IR_CRATE_DIR / "src" / "value.rs"
    ROWS = {
        "fresh_id_has_successor": (
            "fresh_successor_iff_below_max",
            "fresh_successor_absent_at_max",
            "fresh_successor_present_below_max",
            "fresh_successor_present_at_zero",
        ),
        "fresh_run_fits": (
            "fresh_run_fits_iff_within_room",
            "fresh_run_fits_single_id_anywhere",
            "fresh_run_fits_whole_space",
            "fresh_run_fits_refused_past_max",
        ),
        "fresh_id_below": (
            "fresh_below_iff_less",
            "fresh_below_refuses_the_bound",
            "fresh_below_admits_the_last_id_under_the_bound",
        ),
    }

    def test_every_boundary_row_is_a_held_law_of_its_own_table(self):
        held = vc.holding(ROOT)
        self.assertEqual(held.errors, ())
        for table, rows in self.ROWS.items():
            with self.subTest(table=table):
                # A table over u32 payloads: its rows are its named laws.
                self.assertIn(table, vc.PAYLOAD_TABLES)
                self.assertEqual(sorted(law for law in held.held if held.tables[law] == table), sorted(rows))

    def test_the_wrap_is_a_mutant_and_refutes_the_exhaustion_row(self):
        # The defect class the rule exists to prevent — `u32::MAX` given a
        # successor, which wraps onto id 0 — is a same-shape mutant of the
        # exhaustion table, and the exhaustion row is among the laws it flips.
        laws = vc.law_functions(ROOT)
        wraps = [
            m for m in vc.MUTANTS
            if any(e.crate == vc.IR_CRATE and e.file == "src/value.rs" and "id <= u32::MAX" in e.new for e in m.edits)
        ]
        self.assertEqual(len(wraps), 1, [m.name for m in wraps])
        flipped = vc.expand_flips(wraps[0], laws)
        self.assertIn("fresh_successor_absent_at_max", flipped)
        self.assertIn("fresh_successor_iff_below_max", flipped)
        self.assertNotIn("fresh_successor_present_below_max", flipped)

    @staticmethod
    def repointed(text, law, body):
        """`text` with the one-line body of `law` replaced by `body`."""
        start = text.index(f"pub fn {law}(")
        end = text.index("\n}\n", start)
        lines = text[start:end].split("\n")
        opened = lines.index("{")
        return text[:start] + "\n".join(lines[: opened + 1] + [f"    {body}"]) + text[end:]

    def test_a_boundary_row_law_repointed_at_another_row_is_refused(self):
        # Each law's NAME is the row it states, and the ratification cites
        # each row by its law, so a law must call its table at exactly that
        # row. Measured 2026-10-01 by review (run C): with the rows wired as
        # `{ARGS}` globs, the first three re-pointings below passed WIRING and
        # gate 13 PASSED with all three proved, so "the bound's own id is
        # refused (`laws::fresh_below_refuses_the_bound`)" stayed green with
        # that law at (0, 0). The last two are a row moved onto its sibling's
        # arguments and a body that never calls the table.
        text = (ROOT / vc.LAWS_FILE).read_text(encoding="utf-8")
        self.assertEqual(vc.law_wiring_errors(text), [])
        for law, body in (
            ("fresh_successor_present_below_max", "fresh_id_has_successor(0)"),
            ("fresh_below_refuses_the_bound", "fresh_id_below(0, 0)"),
            ("fresh_run_fits_whole_space", "fresh_run_fits(0, 0)"),
            ("fresh_successor_iff_below_max", "fresh_id_has_successor(4294967295)"),
            ("fresh_successor_absent_at_max", "fresh_id_has_successor({ return false; })"),
        ):
            with self.subTest(law=law, body=body):
                errors = vc.law_wiring_errors(self.repointed(text, law, body))
                self.assertEqual(len(errors), 1, errors)
                self.assertTrue(errors[0].startswith(f"{law}: "), errors)

    def test_each_table_is_defined_once_and_the_cursor_reads_it(self):
        text = (ROOT / self.VALUE_RS).read_text(encoding="utf-8")
        code = text.split("#[cfg(test)]\nmod tests {", 1)[0]
        for table in self.ROWS:
            with self.subTest(table=table):
                self.assertEqual(code.count(f"pub const fn {table}("), 1)
                # called outside its definition and outside the tests
                self.assertGreaterEqual(code.count(f"{table}("), 2)


class LawsFile(unittest.TestCase):
    def test_laws_are_pub_fns_and_nothing_else_is_pub(self):
        laws = vc.law_functions(ROOT)
        self.assertGreaterEqual(len(laws), 20)
        self.assertEqual(len(laws), len(set(laws)))
        text = (ROOT / vc.LAWS_FILE).read_text(encoding="utf-8")
        self.assertEqual(text.count("ensures "), len(laws), "every law carries exactly one `ensures`")

    def test_laws_module_is_cfg_gated_and_rustfmt_skipped(self):
        lib = (ROOT / vc.TABLES_FILE).read_text(encoding="utf-8")
        self.assertIn("#[cfg(trust_verify)]\n#[rustfmt::skip]\npub mod laws;", lib)
        manifest = (ROOT / vc.CRATE_DIR / "Cargo.toml").read_text(encoding="utf-8")
        self.assertIn("check-cfg = ['cfg(trust_verify)']", manifest)

    def test_subjects_are_defined_in_the_tables_file(self):
        lib = (ROOT / vc.TABLES_FILE).read_text(encoding="utf-8")
        for s in vc.SUBJECTS:
            self.assertIn(f"pub fn {s}(", lib)


class ReportReader(unittest.TestCase):
    def test_only_certified_kernel_rechecked_rows_count_as_proved(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "report.json"
            p.write_text(
                __import__("json").dumps(
                    report(
                        [
                            ("good", [("postcondition", "proved", "Certified", "KernelRechecked")]),
                            ("weak", [("postcondition", "proved", "Certified", "Unrecorded")]),
                            ("unknown", [("postcondition", "unknown", None, None)]),
                            ("empty", []),
                        ]
                    )
                ),
                encoding="utf-8",
            )
            results = vc.parse_report(p)
            idx = vc.by_leaf(results)
            self.assertTrue(idx["good"].fully_proved())
            self.assertFalse(idx["weak"].fully_proved())
            self.assertFalse(idx["unknown"].fully_proved())
            self.assertFalse(idx["empty"].fully_proved(), "no obligations is not a proof")
            fails = vc.check_rows(results, ["good", "weak", "unknown", "empty"], {"good", "weak", "unknown", "empty"}, set(), "")
            self.assertEqual(len(fails), 3, fails)

    def test_a_subject_table_may_carry_no_row_but_never_an_unproved_one(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "report.json"
            data = {"functions": []}
            prefix = 'cargo-target(package="trust-ir-laws",proof_unit_role="primary")::trust_ir_laws::'
            for name, obs in (
                ("rowless", []),
                ("proved", [("unreachable", "proved", "Certified", "KernelRechecked")]),
                ("unknown", [("unreachable", "unknown", None, None)]),
            ):
                data["functions"].append(
                    {
                        "function": prefix + name,
                        "summary": {"verdict": "x"},
                        "obligations": [
                            {
                                "obligation_id": f"vc:{name}",
                                "kind": kind,
                                "outcome": {
                                    "status": status,
                                    "strength": {"assurance": a, "grade": {"validation": v}},
                                },
                            }
                            for kind, status, a, v in obs
                        ],
                    }
                )
            p.write_text(__import__("json").dumps(data), encoding="utf-8")
            results = vc.parse_report(p)
            self.assertEqual(vc.check_subjects(results, ["rowless", "proved"]), [])
            self.assertEqual(len(vc.check_subjects(results, ["unknown"])), 1)
            self.assertEqual(len(vc.check_subjects(results, ["absent"])), 1)
            # a LAW with no row is still refused
            self.assertEqual(len(vc.check_rows(results, ["rowless"], {"rowless"}, set(), "")), 1)
            self.assertFalse(vc.by_leaf(results)["rowless"].fully_proved())

    def test_refuted_needs_the_runner_line_and_a_non_proved_row(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "report.json"
            p.write_text(
                __import__("json").dumps(
                    report(
                        [
                            ("flipped", [("postcondition", "unknown", None, None)]),
                            ("held", [("postcondition", "proved", "Certified", "KernelRechecked")]),
                        ]
                    )
                ),
                encoding="utf-8",
            )
            results = vc.parse_report(p)
            no_line = vc.check_rows(results, ["flipped", "held"], {"held"}, {"flipped"}, "")
            self.assertEqual(len(no_line), 1, no_line)
            self.assertIn("refuted obligation", no_line[0])
            line = "note: native runner refuted obligation vc:trust_ir_laws__flipped:postcondition:0; refusing\n"
            self.assertEqual(vc.check_rows(results, ["flipped", "held"], {"held"}, {"flipped"}, line), [])
            wrong = vc.check_rows(results, ["flipped", "held"], {"flipped"}, {"held"}, line)
            self.assertEqual(len(wrong), 3, wrong)

    def test_dependency_and_foreign_rows_are_ignored(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "report.json"
            data = report([("good", [("postcondition", "proved", "Certified", "KernelRechecked")])])
            data["functions"].append(
                {
                    "function": 'cargo-target(package="trust-ir",proof_unit_role="dependency")::trust_ir::x',
                    "summary": {"verdict": "Verified"},
                    "obligations": [],
                }
            )
            for ty in ("GateShape", "UnlicensedBodyPolicy"):
                for path in (f"<trust_ir_laws::{ty} as core::clone::Clone>::clone", f"trust_ir_laws::{ty}::name"):
                    data["functions"].append(
                        {
                            "function": 'cargo-target(package="trust-ir-laws",proof_unit_role="primary")'
                            f"::{path}",
                            "summary": {"verdict": "NoObligations"},
                            "obligations": [],
                        }
                    )
            data["functions"].append(
                {
                    "function": 'cargo-target(package="trust-ir-laws",proof_unit_role="primary")'
                    "::trust_ir_laws::coverage_supports",
                    "summary": {"verdict": "Verified"},
                    "obligations": [],
                }
            )
            p.write_text(__import__("json").dumps(data), encoding="utf-8")
            results = vc.parse_report(p)
            self.assertEqual(len(results), 6)
            self.assertNotIn("trust_ir::x", " ".join(results))
            # Two derived `clone`s and two inherent `name`s share leaf names;
            # they are not laws and must neither collide nor be indexed. A
            # top-level subject is indexed beside the laws.
            self.assertEqual(sorted(vc.by_leaf(results)), ["coverage_supports", "good"])


FIXTURES = Path(__file__).resolve().parent / "fixtures" / "verified_lane"
# The r7 survey's census line for crate trust-ir, verbatim (a real trustc note).
R7_TRUST_IR_CENSUS = (
    "note: trust: memory census: 10604 bodies verified and compacted, 47 compacted slots recomputed, "
    "0 bodies skipped at the memory ceiling; resident 1.6 GiB, peak 4.2 GiB, ceiling 3.0 GiB"
)
# What an RSS trip at an early poll left on p4 (direct seal trustc,
# ceiling 1 byte, steps 4096*16+3): no budget word anywhere in it.
RSS_TRIP_REASON = (
    "unsupported MIR `MalformedTrustIr`: malformed Trust MIR for `p4`: BinaryOp(Rem) does not match "
    "the audited Rust binary operation operand/destination types"
)


def build_executions():
    """fixtures/verified_lane/build_executions.json: each run fixture's
    build-script executions, as `check_build_scripts` reads them."""
    return json.loads((FIXTURES / "build_executions.json").read_text(encoding="utf-8"))


def load_run(name):
    """A real gate run projected by fixtures/verified_lane/refresh.py:
    (report data, LaneRun, the laws the report names, the expected flips).
    The report carries the build-script executions `build_executions.json`
    records for this fixture (see that file's provenance and refresh.py)."""
    doc = json.loads((FIXTURES / name).read_text(encoding="utf-8"))
    run = vc.LaneRun(code=doc["exit"], output="\n".join(doc["output_lines"]), rss_bound=doc["rss_bound_bytes"])
    data = doc["report"]
    executions = build_executions()[name]
    data["assumptions"] = executions["assumptions"]
    data.setdefault("cargo_proof_inventory", {})["excluded_active_units"] = executions["excluded_active_units"]
    laws = sorted(
        {k for k in (vc.law_key(n) for n, _ in vc.primary_rows(data)) if k and k not in vc.SUBJECTS}
    )
    return data, run, laws, set(doc["provenance"].get("flips", []))


def fixture_subjects(data):
    """The subject tables a fixture's report names (its tree's `SUBJECTS`)."""
    return sorted({k for k in (vc.law_key(n) for n, _ in vc.primary_rows(data)) if k in vc.SUBJECTS})


def budget_entries():
    return json.loads((FIXTURES / "budget_rows.json").read_text(encoding="utf-8"))["entries"]


def measured_omitted(name):
    """A measured omitted-request list (header + entry lines) of the r7 crate."""
    return json.loads((FIXTURES / "budget_rows.json").read_text(encoding="utf-8"))["omitted"][name]["lines"]


def withheld_entries(output):
    return [line for found in vc.omitted_lists(output) for line in found.entries if "; proof withheld" in line]


def with_output(run, output):
    return vc.LaneRun(run.code, output, run.rss_bound)


def with_row(data, function, row):
    """`data` with `row` appended to `function` (a path after the cargo-target
    prefix), creating the function entry when the report has none."""
    data = copy.deepcopy(data)
    for entry in data["functions"]:
        if entry["function"].endswith(")::" + function):
            entry["obligations"].append(copy.deepcopy(row))
            return data
    data["functions"].append(
        {
            "function": f'cargo-target(package="{vc.CRATE}",proof_unit_role="primary")::{function}',
            "summary": {"verdict": "Inconclusive"},
            "obligations": [copy.deepcopy(row)],
        }
    )
    return data


def ceiling_of(data):
    ceiling, why = vc.memory_ceiling(data)
    assert ceiling is not None, why
    return ceiling


class NotJudged(unittest.TestCase):
    """Rule 4 of gate 13 (`verified_contracts.not_judged`, THE RULE): a run is
    judged only below the memory ceiling, with no budget-attributable and no
    unexplained row. Every input here is a real run or a measured row; the
    mutations are the named ways a run must stop being judged."""

    def judged(self, data, run, flips=frozenset()):
        return vc.not_judged(data, run, set(flips))

    def assert_not_judged(self, reasons, needle):
        self.assertTrue(reasons, "expected NOT JUDGED")
        self.assertTrue(all(r.startswith(vc.NOT_JUDGED) for r in reasons), reasons)
        self.assertTrue(any(needle in r for r in reasons), (needle, reasons))

    # --- the real current runs pass ------------------------------------
    def test_the_real_base_run_is_judged_and_every_law_proved(self):
        data, run, laws, _ = load_run("laws_base_run.json")
        self.assertEqual(run.code, 0)
        self.assertGreaterEqual(len(laws), 20)
        self.assertEqual(self.judged(data, run), [])
        results = vc.parse_report_data(data)
        self.assertEqual(vc.check_rows(results, laws, set(laws), set(), run.output), [])
        # The subject tables the fixture's tree had (it predates the second
        # wave's three rowless local tables); the gate holds every one of
        # `vc.SUBJECTS` on the real tree through the same `check_subjects`.
        subjects = fixture_subjects(data)
        self.assertIn("coverage_supports", subjects)
        self.assertEqual(vc.check_subjects(results, subjects), [])

    def test_the_real_mutant_run_is_judged_and_refutes_exactly_its_flips(self):
        data, run, laws, flips = load_run("laws_mutant_run.json")
        self.assertNotEqual(run.code, 0)
        self.assertTrue(flips)
        # Real refutation text (long, CHC/PDR prose) is not mistaken for a stop.
        self.assertEqual(self.judged(data, run, flips), [])
        results = vc.parse_report_data(data)
        self.assertEqual(vc.check_rows(results, laws, set(laws) - flips, flips, run.output), [])

    def test_the_fixtures_carry_no_local_path(self):
        for f in FIXTURES.glob("*.json"):
            self.assertNotIn("/Users/", f.read_text(encoding="utf-8"), f.name)

    # --- (a) memory --------------------------------------------------------
    def test_a_peak_at_or_above_the_ceiling_is_not_judged(self):
        data, run, _, _ = load_run("laws_base_run.json")
        ceiling = ceiling_of(data)
        self.assertEqual(ceiling, 3 << 30, "targo injects physmem/8 = 3 GiB on the 24 GiB host that ran it")
        for peak in (ceiling, ceiling + 1, 5 << 30):
            with self.subTest(peak=peak):
                reasons = self.judged(data, vc.LaneRun(run.code, run.output, peak))
                self.assert_not_judged(reasons, "reached the verification memory ceiling")
        self.assertEqual(self.judged(data, vc.LaneRun(run.code, run.output, ceiling - 1)), [])

    def test_trustcs_own_census_at_the_ceiling_is_not_judged_whatever_wait4_says(self):
        data, run, _, _ = load_run("laws_base_run.json")
        reasons = self.judged(data, vc.LaneRun(run.code, run.output + "\n" + R7_TRUST_IR_CENSUS, run.rss_bound))
        self.assert_not_judged(reasons, "trustc memory note")
        below = R7_TRUST_IR_CENSUS.replace("peak 4.2 GiB", "peak 1.9 GiB")
        self.assertEqual(self.judged(data, vc.LaneRun(run.code, run.output + "\n" + below, run.rss_bound)), [])
        # Printed to one decimal: 2.9 GiB may be 2.95 GiB, still below 3.0.
        edge = R7_TRUST_IR_CENSUS.replace("peak 4.2 GiB", "peak 2.9 GiB")
        self.assertEqual(self.judged(data, vc.LaneRun(run.code, run.output + "\n" + edge, run.rss_bound)), [])
        at = R7_TRUST_IR_CENSUS.replace("peak 4.2 GiB", "peak 3.0 GiB")
        self.assert_not_judged(self.judged(data, vc.LaneRun(run.code, run.output + "\n" + at, run.rss_bound)), "memory")

    def test_every_other_memory_signal_is_not_judged(self):
        data, run, _, _ = load_run("laws_base_run.json")
        cases = {
            "skipped": R7_TRUST_IR_CENSUS.replace("peak 4.2", "peak 1.0").replace("0 bodies skipped", "3 bodies skipped"),
            "reached": "warning: trust: verification memory ceiling reached after 12 verified bodies (resident 3.1 GiB, "
            "peak 3.1 GiB, ceiling 3.0 GiB): `f` and every later body of this crate are reported UNKNOWN",
            "prints ceiling": R7_TRUST_IR_CENSUS.replace("peak 4.2", "peak 1.0").replace("ceiling 3.0 GiB", "ceiling 8.0 GiB"),
            "unparsed": "note: trust: memory census: reworded by a newer toolchain, peak 9 GiB",
        }
        for needle, line in cases.items():
            with self.subTest(needle):
                self.assert_not_judged(self.judged(data, vc.LaneRun(run.code, run.output + "\n" + line, run.rss_bound)), needle)

    def test_no_process_tree_reading_is_not_judged(self):
        data, run, _, _ = load_run("laws_base_run.json")
        self.assert_not_judged(self.judged(data, vc.LaneRun(run.code, run.output, None)), "wait4 unavailable")

    def test_the_ceiling_must_be_the_one_the_report_records(self):
        data, run, _, _ = load_run("laws_base_run.json")
        flags_of = lambda d: d["cargo_proof_inventory"]["completed"]["primary_roots"][0]["semantics"]["unit_rustflags"]
        absent = copy.deepcopy(data)
        flags = flags_of(absent)
        i = next(i for i, f in enumerate(flags) if f.startswith(vc.MEMORY_CEILING_OPTION))
        del flags[i - 1:i + 1]
        self.assert_not_judged(self.judged(absent, run), "records no -Ztrust-verify-memory-ceiling-bytes")
        two = copy.deepcopy(data)
        two["cargo_proof_inventory"]["completed"]["primary_roots"].append(
            {"semantics": {"unit_rustflags": ["-Z", f"{vc.MEMORY_CEILING_OPTION}=1"]}}
        )
        self.assert_not_judged(self.judged(two, run), "different memory ceilings")
        disabled = copy.deepcopy(data)
        flags = flags_of(disabled)
        flags[i] = f"{vc.MEMORY_CEILING_OPTION}=0"
        # A disabled ceiling has no RSS latch: rule (a) holds at any peak.
        self.assertEqual(self.judged(disabled, vc.LaneRun(run.code, run.output, 64 << 30)), [])

    # --- (b) budget-attributable rows and diagnostics -----------------------
    def test_every_measured_budget_row_is_not_judged_wherever_it_lands(self):
        data, run, laws, _ = load_run("laws_base_run.json")
        for name, entry in budget_entries().items():
            for function in (f"{vc.CRATE_IDENT}::laws::{laws[0]}", f"<{vc.CRATE_IDENT}::GateShape as core::clone::Clone>::clone"):
                with self.subTest(entry=name, function=function):
                    reasons = self.judged(with_row(data, function, entry["row"]), run)
                    needle = "neither proved nor an expected refutation" if "note" in entry else "budget-attributable"
                    self.assert_not_judged(reasons, needle)

    def test_a_budget_row_inside_an_expected_refutation_is_still_not_judged(self):
        # The one place an unknown row is expected: a flipped law of a mutant.
        # A stop there would hide or fake the refutation, so it names the run.
        data, run, _, flips = load_run("laws_mutant_run.json")
        law = sorted(flips)[0]
        for name, entry in budget_entries().items():
            if "note" in entry:
                continue
            with self.subTest(entry=name):
                reasons = self.judged(with_row(data, f"{vc.CRATE_IDENT}::laws::{law}", entry["row"]), run, flips)
                self.assert_not_judged(reasons, "budget-attributable")

    def test_the_strict_budget_diagnostic_is_not_judged(self):
        data, run, _, _ = load_run("laws_base_run.json")
        entry = budget_entries()["strict_budget_build_error"]
        reasons = self.judged(data, vc.LaneRun(run.code, run.output + "\n" + entry["diagnostic"], run.rss_bound))
        self.assert_not_judged(reasons, "budget stop: `count_args` exceeded its per-function budget")

    def test_every_per_function_budget_line_is_not_judged(self):
        # The seal's second budget diagnostic (trust_verify.rs, the
        # overflow-check origin replay: a warning in every policy) is its
        # format string instantiated here, NOT a measured line — no run of
        # this change triggered it. A line that says the words in any other
        # shape is refused verbatim (a reworded diagnostic fails closed).
        data, run, _, _ = load_run("laws_base_run.json")
        replay = (
            "warning: Trust: the overflow-check origin replay for `trust_ir_laws::coverage_supports` exceeded "
            "its per-function budget (3000 ms / 64000000 steps), so proven-overflow-check elision is DECLINED "
            "for this function and every check is kept. Verification of `trust_ir_laws::coverage_supports` is "
            "unaffected. Raise `-Ztrust-verify-function-budget-ms` / `-steps` or simplify the function."
        )
        self.assert_not_judged(
            self.judged(data, with_output(run, run.output + "\n" + replay)),
            "during overflow-check origin replay",
        )
        reworded = "warning: Trust: `f` exceeded its per-function budget in a phase this gate has not seen"
        self.assert_not_judged(
            self.judged(data, with_output(run, run.output + "\n" + reworded)), "budget stop (unparsed diagnostic)"
        )

    # --- (c) requests publication omitted from report.json -----------------
    def test_the_real_runs_carry_withheld_omissions_and_nothing_else(self):
        # Every real run of the lane omits requests from report.json: the
        # laws' def-site markers, favorable at the compiler, withheld at
        # publication. They parse whole and are the one omission admitted.
        for name in ("laws_base_run.json", "laws_mutant_run.json"):
            with self.subTest(name):
                _, run, _, _ = load_run(name)
                lists = vc.omitted_lists(run.output)
                self.assertTrue(lists, "the fixture must carry the run's omitted-request list")
                for found in lists:
                    self.assertEqual(found.count, len(found.entries))
                    self.assertTrue(found.entries)
                    self.assertTrue(all(vc.OMITTED_ENTRY.match(e) for e in found.entries), found.entries)
                self.assertEqual(len(withheld_entries(run.output)), sum(len(f.entries) for f in lists))

    def test_an_omitted_request_that_is_not_a_withheld_claim_is_not_judged(self):
        # The measured shape (r7, strict, timeout_ms = 1): a request that was
        # a published FAILED row at 3000 ms leaves report.json and is listed
        # only as `[UNKNOWN]`, with no budget word. Transplanted onto a law of
        # this crate, it makes the run NOT JUDGED.
        data, run, _, _ = load_run("laws_base_run.json")
        header, r7 = measured_omitted("strict_solver_timeout_twin")
        measured = vc.OMITTED_ENTRY.match(r7)
        self.assertIsNotNone(measured, "the parser reads the measured line")
        self.assertEqual((measured["outcome"], measured["withheld"]), ("UNKNOWN", None))
        self.assertIsNone(vc.primary_function(measured["function"]), "another crate's unit is not this lane's")
        law_entry = withheld_entries(run.output)[0]
        law_function = vc.OMITTED_ENTRY.match(law_entry)["function"]
        transplanted = r7.replace(measured["function"], law_function)
        output = run.output + "\n" + header + "\n" + transplanted
        self.assert_not_judged(self.judged(data, with_output(run, output)), "was omitted from the published rows as UNKNOWN")
        # The same request with the withheld mark is the admitted omission.
        self.assertEqual(self.judged(data, with_output(run, run.output + "\n" + header + "\n" + law_entry)), [])
        # And the real line of another crate's unit is not this lane's to judge.
        self.assertEqual(self.judged(data, with_output(run, run.output + "\n" + header + "\n" + r7)), [])

    def test_an_unwithheld_omission_is_admitted_only_inside_an_expected_refutation(self):
        # A REAL line: in mutant u64-ge-transitive-strict the law's whole-clause
        # marker was UNKNOWN at the compiler and elided as the alias of the one
        # return path that proved, while another path was refuted. That run is
        # judged only because the law is the mutant's expected refutation.
        data, run, _, _ = load_run("laws_base_run.json")
        header, line = measured_omitted("laws_transitivity_mutant_elided_marker")
        entry = vc.OMITTED_ENTRY.match(line)
        self.assertEqual((entry["outcome"], entry["withheld"]), ("UNKNOWN", None))
        law = vc.law_key(vc.primary_function(entry["function"]))
        self.assertEqual(law, "u64_ge_is_transitive")
        output = run.output + "\n" + header + "\n" + line
        self.assertEqual(self.judged(data, with_output(run, output), {law}), [])
        self.assert_not_judged(self.judged(data, with_output(run, output)), "was omitted from the published rows as UNKNOWN")
        other = next(l for l in withheld_entries(run.output) if f"::laws::{law} " not in l)
        self.assert_not_judged(
            self.judged(data, with_output(run, output + "\n" + header + "\n" + other.replace("; proof withheld at publication", "")), {law}),
            "was omitted from the published rows as UNKNOWN",
        )

    def test_the_omitted_request_accounting_must_parse_whole(self):
        data, run, _, _ = load_run("laws_base_run.json")
        lines = run.output.splitlines()
        entries = withheld_entries(run.output)
        n = len(entries)
        cases = {
            f"prints {n} request(s) but carries {n - 1}": "\n".join(l for l in lines if l != entries[-1]),
            "unparsed omitted-request list header": run.output.replace(
                "Compiler requests omitted from the published proof rows:", "Compiler requests omitted from the published proof rows (v2):"
            ),
            "unparsed omitted-request entry": run.output.replace(entries[0], "  [UNKNOWN] a reworded entry"),
            "cannot attribute every withheld row": "\n".join(
                l + "; 1 unattributed — publication accounting defect" if l.startswith("Publication boundary:") else l
                for l in lines
            ),
        }
        for needle, output in cases.items():
            with self.subTest(needle):
                self.assertNotEqual(output, run.output, "the mutation must change the run")
                self.assert_not_judged(self.judged(data, with_output(run, output)), needle)

    def test_each_measured_row_is_attributed_by_the_field_that_names_it(self):
        attribution = {n: vc.row_budget_attribution(e["row"]) for n, e in budget_entries().items()}
        self.assertIn("solver trust-verify-budget", attribution["advisory_preprocessing_budget"])
        self.assertIn("status timeout", attribution["strict_timeout"])
        self.assertIn("`budget`", attribution["strict_native_bundle_budget_expired"])
        self.assertIsNone(attribution["strict_budget_build_error"], "that row names no stop; rule (c) catches it")

    # --- (c) unexplained rows ---------------------------------------------
    def test_a_row_that_names_no_stop_is_not_judged(self):
        data, run, _, _ = load_run("laws_base_run.json")
        row = {"obligation_id": "vc:x:custom:0", "kind": "unknown", "solver": "trust-full-verifier",
               "description": RSS_TRIP_REASON, "outcome": {"status": "unknown", "reason": RSS_TRIP_REASON}}
        self.assertIsNone(vc.row_budget_attribution(row))
        reasons = self.judged(with_row(data, f"{vc.CRATE_IDENT}::GateShape::name", row), run)
        self.assert_not_judged(reasons, "neither proved nor an expected refutation")

    def test_a_proof_without_its_kernel_recheck_is_not_judged(self):
        data, run, _, _ = load_run("laws_base_run.json")
        weak = copy.deepcopy(data)
        weak["functions"][-1]["obligations"][0]["outcome"]["strength"]["grade"]["validation"] = "Unrecorded"
        self.assert_not_judged(self.judged(weak, run), "without a Clean-kernel re-check")

    def test_counts_inventory_and_coverage_are_never_read(self):
        data, run, _, _ = load_run("laws_base_run.json")
        noisy = copy.deepcopy(data)
        noisy["verification_gate"] = {"counts": {"proved": 0, "total": 1}, "coverage": {"coverage_complete": False}}
        self.assertEqual(self.judged(noisy, run), [])

    # --- missing expected refutations ---------------------------------------
    def test_a_missing_expected_refutation_is_not_judged_never_a_pass(self):
        data, run, laws, flips = load_run("laws_mutant_run.json")
        results = vc.parse_report_data(data)
        silent = "\n".join(l for l in run.output.splitlines() if not vc.REFUTED_LINE.search(l))
        findings = vc.check_rows(results, laws, set(laws) - flips, flips, silent)
        self.assertEqual(len(findings), len(flips), findings)
        self.assertTrue(all(f.startswith(vc.NOT_JUDGED + " expected refutation missing") for f in findings), findings)


class CurrentDeterminism(unittest.TestCase):
    """The original C6 failure, projected without changing any row's grade,
    stable identity or stop. Parsing schema 4 must not qualify that failure.
    """

    def setUp(self):
        self.fixture = json.loads((FIXTURES / "schema4_c6_report.json").read_text(encoding="utf-8"))
        self.data = self.fixture["report"]
        self.record = self.data["verification_gate"]["determinism"]
        self.flags = self.data["cargo_proof_inventory"]["completed"]["primary_roots"][0]["semantics"]["unit_rustflags"]

    def assert_refused(self, needle):
        reasons = vc.determinism_not_judged(self.data)
        self.assertTrue(any(needle in r for r in reasons), (needle, reasons))

    def rehash_vector(self):
        vector = self.record["vector"]
        vector.sort(key=lambda e: (e["obligation"], e["status"], e["stop"]))
        self.record["vector_digest"] = vc.determinism_digest(
            b"trust-verdict-vector/v2\0",
            [entry[key] for entry in vector for key in ("obligation", "status", "stop")], len(vector),
        )
        self.record["stop_causes"] = dict(Counter(e["stop"] for e in vector))

    def test_the_entire_original_report_remains_unqualified(self):
        self.assertEqual(self.fixture["provenance"]["report_sha256"],
                         "548216882025d55b722517eddb3562e3eb68ec7abe126f1f0233fcefbf3e402f")
        self.assertEqual(self.fixture["provenance"]["compiler_commits"],
                         ["c6d3ebc2042626ee4a24e77bf33cbf40b916a122"])
        self.assertEqual(self.record["budget_profile_id"],
                         "c870797a6939da587fae99d7b0aa4c5e64be43e1e0798966417b011f955f05f9")
        self.assertEqual(self.record["vector_digest"],
                         "365739ae75ee0c0649b635d5d06dbbb6192f118088deb2655281caf4fe68ff84")
        rows = [ob for _, ob in vc.primary_rows(self.data)]
        self.assertEqual(len(rows), 1116)
        self.assertEqual(Counter(ob["outcome"]["status"] for ob in rows), {"proved": 326, "unknown": 790})
        self.assertEqual(Counter(ob["outcome"].get("strength", {}).get("assurance") for ob in rows
                                 if ob["outcome"]["status"] == "proved"), {"Certified": 9, "Sound": 317})
        certified = [ob for ob in rows if ob["outcome"].get("strength", {}).get("assurance") == "Certified"]
        self.assertTrue(all(ob["outcome"]["strength"]["grade"]["validation"] == "KernelRechecked" for ob in certified))
        laws = vc.law_functions(ROOT)
        self.assertEqual(len(laws), 412)
        results = vc.parse_report_data(self.data)
        # Preserve the frozen report, including every original unknown/weak
        # row. It cannot certify the later MakeClosure and tensor-region
        # (TensorContract, TensorMap, TensorReduce, TensorView, TensorGather,
        # TensorScatter) table cells or BoxDeref either.
        added = {
            "terminator_make_closure",
            "borrow_permission_make_closure",
            "terminator_tensor_contract",
            "borrow_permission_tensor_contract",
            "terminator_tensor_map",
            "borrow_permission_tensor_map",
            "terminator_tensor_reduce",
            "borrow_permission_tensor_reduce",
            "terminator_tensor_view",
            "borrow_permission_tensor_view",
            "terminator_tensor_gather",
            "borrow_permission_tensor_gather",
            "terminator_tensor_scatter",
            "borrow_permission_tensor_scatter",
            "terminator_box_deref",
            "borrow_permission_box_deref",
        }
        historical = set(laws) - added
        self.assertEqual(len(historical), 396)
        reported = set(vc.by_leaf(results))
        self.assertTrue(historical <= reported)
        self.assertEqual(set(laws) - reported, added)
        failures = vc.check_rows(results, laws, set(laws), set(), "")
        self.assertTrue(failures)
        for law in added:
            self.assertIn(f"{law}: absent from the report (not verified at all)", failures)
        reasons = vc.determinism_not_judged(self.data)
        self.assertEqual(reasons, [
            f"{vc.NOT_JUDGED} determinism: typed verdict vector records resource or unexplained stops: unclassified=790",
            f"{vc.NOT_JUDGED} determinism: the run's outcome is 'not-reproducible', not measured",
        ])
        # No RSS value is invented: current accounting has no compiler ceiling
        # latch. The real typed stops, weak grades and unknown rows still refuse.
        findings = vc.not_judged(self.data, vc.LaneRun(3, "", None), set())
        self.assertTrue(any("unclassified=790" in f for f in findings))
        self.assertTrue(any("Sound/SoundAnalysis" in f for f in findings))
        self.assertFalse(any("records no -Ztrust-verify-memory-ceiling" in f for f in findings))
        self.assertIn("budget schema 4, determinism not-reproducible", vc.memory_evidence(self.data, vc.LaneRun(3, "", None)))

    def test_older_and_unknown_profile_schemas_have_precise_diagnostics(self):
        for schema in (None, True, 1, 2, 3, 5):
            with self.subTest(schema=schema):
                self.record["budget_profile"] = {"schema": schema, "old_memory_field": 1}
                reasons = vc.determinism_not_judged(self.data)
                self.assertEqual(len(reasons), 1)
                self.assertIn(f"budget profile schema {schema!r} is not readable", reasons[0])
                self.assertNotIn("memory-ceiling-bytes", reasons[0])

    def test_missing_current_accounting_cannot_fall_back_to_an_invented_zero_ceiling(self):
        self.data["verification_gate"].pop("determinism")
        self.flags += ["-Z", f"{vc.MEMORY_CEILING_OPTION}=0"]
        reasons = vc.memory_not_judged(self.data, "", None)
        self.assertTrue(any("no determinism record" in r for r in reasons), reasons)

    def test_the_current_profile_requires_its_actual_bound_fields_and_digest(self):
        original = copy.deepcopy(self.record["budget_profile"])
        for key, value in (("effort", 0), ("effort", True), ("effort", 100_001), ("backstop", 0),
                           ("backstop", 1 << 32), ("worker_threads", -1), ("retired_memory_ceiling", 0)):
            with self.subTest(key=key, value=value):
                self.record["budget_profile"] = {**original, key: value}
                self.assert_refused("budget profile")
        self.record["budget_profile"] = original
        self.record["budget_profile_id"] = "0" * 64
        self.assert_refused("budget_profile_id does not match")

    def test_each_primary_root_must_record_the_matching_compiler_controls(self):
        roots = self.data["cargo_proof_inventory"]["completed"]["primary_roots"]
        for replacement in ([], ["-Z", []], ["-Z", "trust-verify-effort=1"],
                            self.flags + ["-Z", "trust-verify-effort=384"]):
            with self.subTest(flags=replacement):
                roots.append({"semantics": {"unit_rustflags": replacement}})
                self.assert_refused("primary root 1 must record exactly")
                roots.pop()
        self.flags += ["-Z", f"{vc.MEMORY_CEILING_OPTION}=0"]
        self.assert_refused("retired memory-ceiling option")

    def test_the_profile_clocks_and_worker_cap_are_not_independent_controls(self):
        for name in ("trust-verify-timeout-ms", "trust-verify-function-budget-ms"):
            i = next(i for i, f in enumerate(self.flags) if f.startswith(name + "="))
            original = self.flags[i]
            self.flags[i] = name + "=1"
            self.assert_refused(f"exactly -Z{name}=")
            self.flags[i] = original
        self.flags += ["-Z", "trust-verify-worker-threads=8"]
        self.assert_refused("worker-thread cap absent")
        self.record["budget_profile"]["worker_threads"] = 8
        self.assertFalse(any("primary root" in r or "budget_profile_id" in r
                             for r in vc.determinism_not_judged(self.data)))

    def test_a_vector_cannot_drop_duplicate_or_relabel_rows_even_if_rehashed(self):
        original = copy.deepcopy(self.record["vector"])
        for mutation in (lambda v: v.pop(), lambda v: v.append(copy.deepcopy(v[0])),
                         lambda v: v[0].update(status="unknown"), lambda v: v[0].update(obligation="another#key")):
            self.record["vector"] = copy.deepcopy(original)
            mutation(self.record["vector"])
            self.rehash_vector()
            self.assert_refused("does not match every published row")

    def test_vector_digest_tally_and_canonical_order_are_checked(self):
        self.record["vector_digest"] = "0" * 64
        self.assert_refused("vector_digest does not match")
        self.record["stop_causes"] = {"solved": 1116, "unclassified": 0}
        self.assert_refused("positive counts")
        self.record["vector"].reverse()
        self.assert_refused("not in canonical")
        self.data["verification_gate"]["counts"]["total"] = 0
        self.assert_refused("the gate's total does not match")

    def test_an_omitted_vector_cannot_shrink_the_original_report(self):
        self.record.pop("vector")
        self.assert_refused("the gate's total does not match")
        self.assert_refused("does not match every published row")

    def test_deterministic_unsupported_remains_unknown_and_cannot_become_a_proof(self):
        # A synthetic accounting-only mutant: suppose a producer finally names
        # every formerly unexplained stop as Unsupported. Keep ALL original
        # rows and grades. Even measured accounting cannot turn them into proof.
        for entry in self.record["vector"]:
            if entry["status"] == "unknown":
                entry["stop"] = "unsupported"
        self.record["outcome"] = "measured"
        self.rehash_vector()
        self.assertEqual(vc.determinism_not_judged(self.data), [])
        findings = vc.not_judged(self.data, vc.LaneRun(3, "", None), set())
        self.assertTrue(any("is unknown, neither proved nor an expected refutation" in r
                            and "typed stop vector establishes no proof authority" in r for r in findings))
        laws = vc.law_functions(ROOT)
        self.assertTrue(vc.check_rows(vc.parse_report_data(self.data), laws, set(laws), set(), ""))

    def test_typed_resource_stops_and_out_of_row_stops_cannot_be_laundered(self):
        original = copy.deepcopy(self.record["vector"])
        for stop in vc.RESOURCE_STOPS:
            with self.subTest(stop=stop):
                self.record["vector"] = copy.deepcopy(original)
                entry = next(e for e in self.record["vector"] if e["status"] == "unknown")
                entry["stop"] = stop
                self.record["outcome"] = "measured"
                self.rehash_vector()
                self.assert_refused(stop + "=")
        self.record["noted_stops"] = [{"lane": "internal-proof-attempt", "cause": "wall-backstop", "count": 1}]
        self.assert_refused("noted_stops is not empty")
        for key in ("volatile_keys", "unkeyed_functions"):
            self.record[key] = ["missing stable key"]
            self.assert_refused(key + " is not empty")

    def test_malformed_typed_vector_is_refused_without_a_parser_exception(self):
        original = copy.deepcopy(self.record["vector"][0])
        for key, value in (("status", []), ("stop", {}), ("stop", "future-stop"), ("obligation", None)):
            self.record["vector"][0] = {**original, key: value}
            self.assert_refused("malformed typed verdict vector entry 0")

    def test_current_reports_cannot_hide_legacy_memory_trip_diagnostics(self):
        reasons = vc.memory_not_judged(self.data, R7_TRUST_IR_CENSUS, 1)
        self.assertTrue(any("legacy memory-ceiling diagnostic" in r for r in reasons), reasons)


class Verdict(unittest.TestCase):
    def test_a_not_judged_run_sets_its_findings_aside_and_a_judged_one_fails(self):
        findings = [
            ("base", f"{vc.NOT_JUDGED} budget stop: `f` exceeded its per-function budget"),
            ("base", "coverage_reflexive_unwind: expected every row proved+Certified+KernelRechecked"),
            ("mutant m", "strict gate exit 0"),
        ]
        failed, unjudged, set_aside = vc.sort_findings(findings)
        self.assertEqual(failed, [findings[2]], "a judged run's wrong verdict is a FAIL")
        self.assertEqual(unjudged, [findings[0]])
        self.assertEqual(set_aside, [findings[1]], "an unjudged run's row finding is not evidence")
        self.assertEqual(vc.sort_findings(findings[:2])[0], [], "no FAIL when the only run is NOT JUDGED")


REGISTRY = "registry+https://github.com/rust-lang/crates.io-index"


def fixture_version(name):
    """The root's workspace version when the fixture's build executions were
    recorded (a path unit's version is judged against it)."""
    return build_executions()["provenance"]["workspace_version"]


def fixture_build_scripts(name):
    """The build scripts a fixture's run executed (its tree's committed list:
    the run passed the gate, so the two were equal)."""
    data, _, _, _ = load_run(name)
    carried, errors = vc.build_executions(data, fixture_version(name))
    assert not errors, errors
    return set(carried)


def free_index(data):
    """A unit index the report does not use."""
    used = {u["proof_unit_index"] for u in vc.inventory_units(data)}
    for row in data.get("assumptions") or []:
        m = vc.SUBJECT_INDEX.search(row.get("subject", ""))
        if m:
            used.add(int(m.group(1)))
    return max(used, default=0) + 1


def with_build_script(data, package, package_id, *, row=True, inventory=True, mode="run-custom-build", index=None):
    """`data` with one more build-script execution, in the report's two shapes:
    an `assumptions` row tagged `build-execution-scope` (the subject spelled as
    the seal spells it) and the inventory's excluded unit with the same index."""
    data = copy.deepcopy(data)
    index = free_index(data) if index is None else index
    if row:
        data.setdefault("assumptions", []).append(
            {
                "scope": "crate",
                "subject": (
                    f'cargo-target(package_id="{package_id}",package="{package}",kind=["custom-build"],'
                    f'target="build-script-build",compile_target="aarch64-apple-darwin",compile_mode="{mode}",'
                    f'compile_kind="host",proof_unit_index={index},proof_unit_mode="{mode}",'
                    'proof_unit_role="excluded");graph_role="control"'
                ),
                "tag": "build-execution-scope",  # the seal's spelling (Trust dep_tcb.rs)
                "source": "dep-tcb-cargo-unit-inventory",
            }
        )
    if inventory:
        inv = data.setdefault("cargo_proof_inventory", {})
        inv.setdefault("excluded_active_units", []).append(
            {
                "package_id": package_id,
                "package_name": package,
                "target_name": "build-script-build",
                "proof_unit_index": index,
                "proof_unit_mode": mode,
                "exclusion_reason": "build-script-execution",
            }
        )
    return data


class BuildScriptPremise(unittest.TestCase):
    """THE BUILD-SCRIPT PREMISE of gate 13 (`check_build_scripts`): the build
    scripts a run executed outside the proof channel — its report's
    `build-execution-scope` rows, uncontained under Trust blocker B5 — must
    equal the committed list, and the report's two views of them must agree.
    The inputs are the real runs of fixtures/verified_lane/; the mutations are
    one more (or one fewer) build script."""

    BASE = "laws_base_run.json"

    @property
    def EXTRA(self):  # noqa: N802 — the one extra build script of these tests
        return vc.BuildScript("cc", REGISTRY, "1.2.41")

    def base(self):
        data, _, _, _ = load_run(self.BASE)
        return data, fixture_version(self.BASE), fixture_build_scripts(self.BASE)

    def test_the_real_runs_executed_build_scripts_and_both_views_agree(self):
        scripts = fixture_build_scripts(self.BASE)
        self.assertTrue(scripts, "every run of the lane executes build scripts")
        self.assertIn(
            vc.BuildScript("trust-ir", vc.PATH_SOURCE, vc.WORKSPACE_VERSION), scripts,
            "trust-ir's own build.rs runs, at the workspace version",
        )
        self.assertEqual(
            fixture_build_scripts("laws_mutant_run.json"), scripts,
            "a mutant run executes exactly the base run's build scripts",
        )
        data, version, _ = self.base()
        self.assertEqual(vc.check_build_scripts(data, scripts, version)[1], [])

    def test_one_extra_build_script_fails_by_name(self):
        data, version, scripts = self.base()
        extra = with_build_script(data, "cc", f"{REGISTRY}#cc@1.2.41")
        carried, findings = vc.check_build_scripts(extra, scripts, version)
        self.assertIn(self.EXTRA, carried)
        self.assertEqual(len(findings), 1, findings)
        self.assertIn(f"build script {self.EXTRA} ran uncontained", findings[0])
        self.assertIn(str(vc.BUILD_SCRIPTS), findings[0])
        self.assertFalse(findings[0].startswith(vc.NOT_JUDGED), "a wrong premise set is a FAIL, not NOT JUDGED")

    def test_a_listed_build_script_the_run_did_not_execute_fails(self):
        data, version, scripts = self.base()
        _, findings = vc.check_build_scripts(data, scripts | {self.EXTRA}, version)
        self.assertEqual(len(findings), 1, findings)
        self.assertIn(f"build script {self.EXTRA} is in {vc.BUILD_SCRIPTS}", findings[0])
        dropped = sorted(scripts)[0]
        _, findings = vc.check_build_scripts(data, scripts - {dropped}, version)
        self.assertEqual(len(findings), 1, findings)
        self.assertIn(f"build script {dropped} ran uncontained", findings[0])

    def test_the_reports_two_views_must_agree(self):
        data, version, scripts = self.base()
        package_id = f"{REGISTRY}#cc@1.2.41"
        for row, inventory in ((True, False), (False, True)):
            one_view = with_build_script(data, "cc", package_id, row=row, inventory=inventory)
            _, findings = vc.check_build_scripts(one_view, scripts | {self.EXTRA}, version)
            self.assertTrue(any("two views of build-script execution" in f for f in findings), findings)
        index = free_index(data)
        skewed = with_build_script(data, "cc", package_id, inventory=False, index=index)
        skewed = with_build_script(skewed, "cc", f"{REGISTRY}#cc@1.2.40", row=False, index=index)
        _, findings = vc.check_build_scripts(skewed, scripts | {self.EXTRA}, version)
        self.assertEqual(len(findings), 1, findings)
        self.assertIn("cc@1.2.40", findings[0])

    def test_a_report_without_the_assumptions_table_is_one_finding(self):
        data, version, scripts = self.base()
        data = copy.deepcopy(data)
        del data["assumptions"]
        carried, findings = vc.check_build_scripts(data, scripts, version)
        self.assertEqual(carried, [])
        self.assertEqual(len(findings), 1, findings)
        self.assertIn("no `assumptions` table", findings[0])
        data["assumptions"] = []
        _, findings = vc.check_build_scripts(data, scripts, version)
        self.assertTrue(findings, "an empty table is read: every listed script is missing and the inventory disagrees")

    def test_a_tagged_row_that_is_not_an_execution_is_a_finding(self):
        data, version, scripts = self.base()
        compiled = with_build_script(data, "cc", f"{REGISTRY}#cc@1.2.41", inventory=False, mode="build")
        _, findings = vc.check_build_scripts(compiled, scripts, version)
        self.assertEqual(len(findings), 1, findings)
        self.assertIn("not one build-script execution", findings[0])

    def test_package_ids_name_their_build_script(self):
        of = vc.build_script_of
        self.assertEqual(of("libc", f"{REGISTRY}#libc@0.2.189", "0.14.0"), (vc.BuildScript("libc", REGISTRY, "0.2.189"), None))
        workspace = vc.BuildScript("trust-ir", vc.PATH_SOURCE, vc.WORKSPACE_VERSION)
        self.assertEqual(of("trust-ir", "path+file://<path>#0.14.0", "0.14.0"), (workspace, None))
        self.assertEqual(of("trust-ir", "path+file:///x/crates/ir#trust-ir@0.14.0", "0.14.0"), (workspace, None))
        # a path package NOT at the workspace version keeps its own version
        self.assertEqual(
            of("trust-ir", "path+file://<path>#0.14.0", "0.15.0"),
            (vc.BuildScript("trust-ir", vc.PATH_SOURCE, "0.14.0"), None),
        )
        # ...and so can never be listed: the gate says so instead of "add its row"
        data, _, scripts = self.base()
        foreign = with_build_script(data, "clean-kernel", "path+file://<path>#0.9.0")
        _, findings = vc.check_build_scripts(foreign, scripts, "0.14.0")
        self.assertEqual(len(findings), 1, findings)
        self.assertIn("not this workspace's crate and cannot be listed", findings[0])
        for package, package_id in (("libc", f"{REGISTRY}#cc@1.0.0"), ("libc", REGISTRY), ("", f"{REGISTRY}#1.0.0")):
            unit, why = of(package, package_id, "0.14.0")
            self.assertIsNone(unit, package_id)
            self.assertTrue(why, package_id)


LIST_HEADER = "package\tsource\tversion\tdoes"  # the committed format, spelled here on purpose


class BuildScriptList(unittest.TestCase):
    """The committed list (`parse_build_scripts` / `load_build_scripts`), and
    the live one held to the tree: every registry row is locked at its version
    in Cargo.lock, every path row is a workspace crate with a build.rs."""

    def test_rows_parse_and_malformed_ones_are_named(self):
        good = f"# note\n{LIST_HEADER}\nlibc\t{REGISTRY}\t0.2.189\tprobes rustc\ntrust-ir\tpath\tworkspace\tgit sha\n"
        rows, errors = vc.parse_build_scripts(good)
        self.assertEqual(errors, [])
        self.assertEqual(
            set(rows),
            {vc.BuildScript("libc", REGISTRY, "0.2.189"), vc.BuildScript("trust-ir", "path", "workspace")},
        )
        for bad, needle in (
            ("package\tsource\tversion\nlibc\tr\t1\tx\n", "header"),
            (f"{LIST_HEADER}\nlibc\t{REGISTRY}\t0.2.189\n", "columns"),
            (f"{LIST_HEADER}\nlibc\t{REGISTRY}\t0.2.189\t\n", "columns"),
            (f"{LIST_HEADER}\nlibc\t{REGISTRY}\t0.2.189\tx\nlibc\t{REGISTRY}\t0.2.189\ty\n", "twice"),
            (f"{LIST_HEADER}\ntrust-ir\tpath+file:///x\tworkspace\tx\n", "never its local path"),
            (f"{LIST_HEADER}\nlibc\t{REGISTRY}\tworkspace\tx\n", "`workspace`"),
            (f"{LIST_HEADER}\ntrust-ir\tpath\t0.14.0\tx\n", "`workspace`"),
            ("# only a comment\n", "no header"),
        ):
            _, errors = vc.parse_build_scripts(bad)
            self.assertTrue(any(needle in e for e in errors), (bad, errors))

    def test_an_empty_or_missing_list_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _, errors = vc.load_build_scripts(root)
            self.assertTrue(any("missing" in e for e in errors), errors)
            (root / vc.BUILD_SCRIPTS).parent.mkdir(parents=True)
            (root / vc.BUILD_SCRIPTS).write_text(f"{LIST_HEADER}\n", encoding="utf-8")
            _, errors = vc.load_build_scripts(root)
            self.assertTrue(any("no row" in e for e in errors), errors)

    def test_the_committed_list_holds_to_the_lockfile_and_the_tree(self):
        scripts, errors = vc.load_build_scripts(ROOT)
        self.assertEqual(errors, [])
        self.assertTrue(scripts)
        locked = set()
        for block in (ROOT / "Cargo.lock").read_text(encoding="utf-8").split("[[package]]")[1:]:
            fields = dict(re.findall(r'(?m)^(name|version|source) = "([^"]*)"$', block))
            if "source" in fields:
                locked.add((fields["name"], fields["source"], fields["version"]))
        members = {}
        for manifest in (ROOT / "crates").glob("*/Cargo.toml"):
            m = re.search(r'(?m)^name\s*=\s*"([^"]+)"', manifest.read_text(encoding="utf-8"))
            if m:
                members[m.group(1)] = manifest.parent
        for unit in scripts:
            if unit.source == vc.PATH_SOURCE:
                self.assertIn(unit.package, members, f"{unit}: no workspace crate of that name")
                self.assertTrue((members[unit.package] / "build.rs").is_file(), f"{unit}: the crate has no build.rs")
            else:
                self.assertIn((unit.package, unit.source, unit.version), locked, f"{unit}: not locked in Cargo.lock")
        self.assertEqual(vc.workspace_version(ROOT), re.search(
            r'(?ms)^\[workspace\.package\].*?^version\s*=\s*"([^"]+)"', (ROOT / "Cargo.toml").read_text(encoding="utf-8")
        ).group(1))


def refresh_module():
    """fixtures/verified_lane/refresh.py, imported (it is a script, not a package)."""
    import importlib.util

    spec = importlib.util.spec_from_file_location("verified_lane_refresh", FIXTURES / "refresh.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class FixtureProvenance(unittest.TestCase):
    """refresh.py records the tree and workspace version of the checkout it
    runs in, so it refuses a run that checkout did not make, or a checkout
    whose HEAD is not what ran. The first build_executions.json was projected
    from another worktree's kept run and recorded a tree that never ran."""

    def test_a_run_outside_the_checkout_is_refused(self):
        refresh = refresh_module()
        self.assertEqual(refresh.provenance_refusals(ROOT / "target" / "verified-lane", ROOT, ""), [])
        with tempfile.TemporaryDirectory() as tmp:
            refusals = refresh.provenance_refusals(Path(tmp) / "verified-lane", ROOT, "")
        self.assertEqual(len(refusals), 1, refusals)
        self.assertIn("is not inside this checkout", refusals[0])

    def test_uncommitted_changes_outside_the_fixture_directory_are_refused(self):
        refresh = refresh_module()
        here = FIXTURES.relative_to(ROOT).as_posix()
        out = ROOT / "target" / "verified-lane"
        # the fixtures it writes do not count, so a second refresh is not refused
        self.assertEqual(refresh.provenance_refusals(out, ROOT, f" M {here}/build_executions.json\n"), [])
        refusals = refresh.provenance_refusals(out, ROOT, " M scripts/verified_contracts.py\n?? scratch.rs\n")
        self.assertEqual(len(refusals), 1, refusals)
        self.assertIn("scripts/verified_contracts.py", refusals[0])
        self.assertIn("scratch.rs", refusals[0])


class GateMain(unittest.TestCase):
    """Rule 4 as the GATE applies it: `main()` end to end, with only the Trust
    lane stubbed — `run_lane` serves the two REAL runs (base and one mutant,
    `fixtures/verified_lane/`) and writes their reports where `main` reads
    them. The law list and the mutant table are the fixture's own, so the
    test does not move when laws.rs grows. Without this, `not_judged` could be
    right and the gate still PASS a NOT JUDGED run (the verdict ignoring it, or
    a run never judged). `SUBJECTS` is the fixture's too, and the mutant row
    keeps `MUTANTS[0]`'s `scope` (the families of the fixture's laws)."""

    def gate(self, base=None, mutant=None, extra=(), flips_spelled=None, base_data=None, mutant_data=None):
        data_b, run_b, laws, _ = load_run("laws_base_run.json")
        data_m, run_m, laws_m, flips = load_run("laws_mutant_run.json")
        data_b = data_b if base_data is None else base_data
        data_m = data_m if mutant_data is None else mutant_data
        self.assertEqual(laws, laws_m, "both fixtures come from one tree")
        name = self.mutant_label()
        self.assertTrue(name.startswith("mutant "), name)
        mutant_row = dataclasses.replace(
            vc.MUTANTS[0], name=name[len("mutant "):], flips=tuple(flips_spelled or sorted(flips))
        )
        served = []

        def run_lane(targo, cwd, report_dir, target_dir, extra_args):
            is_base = report_dir.name == "base"
            data, run = (data_b, base or run_b) if is_base else (data_m, mutant or run_m)
            if report_dir.exists():
                shutil.rmtree(report_dir)
            report_dir.mkdir(parents=True)
            (report_dir / "report.json").write_text(json.dumps(data), encoding="utf-8")
            served.append("base" if is_base else "mutant")
            return run

        out, err = io.StringIO(), io.StringIO()
        with tempfile.TemporaryDirectory() as tmp, mock.patch.multiple(
            vc,
            resolve_targo=lambda: "targo",
            toolchain_identity=lambda targo: "stub (the lane is served from real runs)",
            run_lane=run_lane,
            law_functions=lambda root: list(laws),
            laws_without_a_mutant=lambda laws: [],
            write_mutant_crate=lambda root, dest, m, laws: None,
            MUTANTS=(mutant_row,),
            # the fixture's tree's subject tables (it predates the three
            # rowless local tables of the second wave)
            SUBJECTS=tuple(fixture_subjects(data_b)),
            # and its tree's build-script list and workspace version
            load_build_scripts=lambda root: (fixture_build_scripts("laws_base_run.json"), []),
            workspace_version=lambda root: fixture_version("laws_base_run.json"),
        ), contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = vc.main(["--out", tmp, *extra])
        expected = ["base"] if "--base-only" in extra else ["base", "mutant"]
        self.assertEqual(served, expected, "every run of the gate went through the stub")
        return code, out.getvalue(), err.getvalue()

    @staticmethod
    def mutant_label():
        """The gate's label for the fixture's mutant run (`mutant <name>`)."""
        return json.loads((FIXTURES / "laws_mutant_run.json").read_text(encoding="utf-8"))["provenance"]["run"]

    def assert_not_judged_exit(self, result, run_label):
        code, out, err = result
        self.assertEqual(code, 1, (out, err))
        self.assertIn("verified-contracts: NOT JUDGED", err)
        self.assertIn(f"{vc.NOT_JUDGED} {run_label}:", err)
        self.assertNotIn("verified-contracts: PASS", out)

    def test_the_real_runs_pass_the_gate(self):
        code, out, err = self.gate()
        self.assertEqual(code, 0, (out, err))
        self.assertIn("verified-contracts: PASS", out)
        self.assertEqual(err, "")
        # the premise is printed: the list held, each run's executions, the verdict
        scripts = sorted(fixture_build_scripts("laws_base_run.json"))
        self.assertIn(f"build scripts held ({len(scripts)}, {vc.BUILD_SCRIPTS}): {', '.join(map(str, scripts))}", out)
        self.assertEqual(out.count(vc.build_script_line(scripts)), 2, "one line per run")
        self.assertIn(f"build-script executions equal {vc.BUILD_SCRIPTS}", out)

    def test_one_extra_build_script_fails_the_gate(self):
        # Red before the premise was held: the gate read no build-execution
        # row, so a JUDGED run that executed an unlisted script still PASSED.
        extra = vc.BuildScript("cc", REGISTRY, "1.2.41")
        data_b, _, _, _ = load_run("laws_base_run.json")
        data_m, _, _, _ = load_run("laws_mutant_run.json")
        served = {
            "base": dict(base_data=with_build_script(data_b, "cc", f"{REGISTRY}#cc@1.2.41")),
            self.mutant_label(): dict(mutant_data=with_build_script(data_m, "cc", f"{REGISTRY}#cc@1.2.41")),
        }
        for run_label, kwargs in served.items():
            for extra_args in ((), ("--base-only",)) if run_label == "base" else ((),):
                code, out, err = self.gate(extra=extra_args, **kwargs)
                self.assertEqual(code, 1, (run_label, out, err))
                self.assertIn(f"FAIL: {run_label}: build script {extra} ran uncontained", err)
                self.assertIn("verified-contracts: FAIL (1 finding(s) in judged runs; 0 run(s) NOT JUDGED)", err)
                self.assertNotIn("verified-contracts: PASS", out)
                self.assertIn(str(extra), out, "the run's executions are printed, the extra one included")

    def test_an_extra_build_script_of_a_not_judged_run_is_set_aside(self):
        data_b, run_b, _, _ = load_run("laws_base_run.json")
        at = vc.LaneRun(run_b.code, run_b.output, ceiling_of(data_b))
        result = self.gate(base=at, base_data=with_build_script(data_b, "cc", f"{REGISTRY}#cc@1.2.41"))
        self.assert_not_judged_exit(result, "base")
        self.assertIn("set aside (run NOT JUDGED, not evidence): base: build script cc@1.2.41", result[2])

    def test_a_malformed_list_stops_the_gate_before_any_run(self):
        def refused(root):
            return set(), [f"{vc.BUILD_SCRIPTS}: line 3: libc is listed twice"]

        with tempfile.TemporaryDirectory() as tmp, self.assertRaises(SystemExit) as stop, mock.patch.multiple(
            vc,
            run_lane=mock.Mock(side_effect=AssertionError("no run may start")),
            resolve_targo=mock.Mock(side_effect=AssertionError("refused before the lane is resolved")),
            load_build_scripts=refused,
        ), contextlib.redirect_stdout(io.StringIO()):
            vc.main(["--out", tmp])
        self.assertIn("listed twice", str(stop.exception))

    def test_glob_flips_reach_the_judge_expanded(self):
        # The second wave spells `flips` with globs; the judge must receive
        # the EXPANDED set, the one `check_rows` receives, or every flipped
        # law's non-proved row would be an unexplained request (NOT JUDGED).
        _, _, laws, flips = load_run("laws_mutant_run.json")
        globs = (
            "coverage_unrecorded_demand_met_by_*",
            "coverage_unbounded_supplies_unrecorded",
            "coverage_*_never_supplies_unbounded",
        )
        row = vc.Mutant(name="g", edits=(), flips=globs, scope=("coverage_",), why="")
        self.assertEqual(set(vc.expand_flips(row, laws)), flips, "the globs name exactly the fixture's flips")
        code, out, err = self.gate(flips_spelled=globs)
        self.assertEqual(code, 0, (out, err))
        self.assertIn("verified-contracts: PASS", out)
        with mock.patch.object(vc, "expand_flips", lambda m, laws: list(m.flips)):
            unexpanded = self.gate(flips_spelled=globs)
        self.assertEqual(unexpanded[0], 1, "an unexpanded glob set does not explain the flipped rows")

    def test_a_base_run_at_the_ceiling_fails_the_gate_with_every_row_proved(self):
        data_b, run_b, _, _ = load_run("laws_base_run.json")
        at = vc.LaneRun(run_b.code, run_b.output, ceiling_of(data_b))
        self.assert_not_judged_exit(self.gate(base=at), "base")
        self.assert_not_judged_exit(self.gate(base=at, extra=("--base-only",)), "base")

    def test_a_mutant_run_at_the_ceiling_fails_the_gate(self):
        data_m, run_m, _, _ = load_run("laws_mutant_run.json")
        at = vc.LaneRun(run_m.code, run_m.output, ceiling_of(data_m))
        self.assert_not_judged_exit(self.gate(mutant=at), self.mutant_label())

    def test_a_mutant_run_without_its_refutation_lines_fails_the_gate(self):
        _, run_m, _, _ = load_run("laws_mutant_run.json")
        silent = "\n".join(l for l in run_m.output.splitlines() if not vc.REFUTED_LINE.search(l))
        self.assertNotEqual(silent, run_m.output)
        self.assert_not_judged_exit(
            self.gate(mutant=vc.LaneRun(run_m.code, silent, run_m.rss_bound)), self.mutant_label()
        )


class ProcessTreeBound(unittest.TestCase):
    """Rule (a)'s own reading: `run_lane` reaps targo with `wait4`, whose
    `ru_maxrss` covers every descendant targo reaped — here a grandchild that
    touches 256 MiB, as a trustc two levels below targo does."""

    def test_the_bound_covers_a_grandchilds_peak(self):
        if not hasattr(os, "wait4"):
            self.skipTest("wait4 unavailable; rule (a) then reports every run NOT JUDGED")
        with tempfile.TemporaryDirectory(prefix="process tree's inputs ") as tmp:
            base = Path(tmp)
            fake = base / "targo"
            (base / "grandchild.py").write_text(
                "b = bytearray(256 << 20)\nfor i in range(0, len(b), 4096):\n    b[i] = 1\n", encoding="utf-8"
            )
            (base / "child.py").write_text(
                "import subprocess, sys\n"
                f"subprocess.run([sys.executable, {str(base / 'grandchild.py')!r}], check=True)\n",
                encoding="utf-8",
            )
            fake.write_text(
                f"#!/bin/sh\n{shlex.quote(sys.executable)} {shlex.quote(str(base / 'child.py'))} || exit 1\necho 'Summary: 0 proved'\n",
                encoding="utf-8",
            )
            fake.chmod(0o755)
            env = {k: v for k, v in os.environ.items() if k not in ("RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_ENCODED_RUSTFLAGS")}
            with mock.patch.dict(os.environ, env, clear=True):
                run = vc.run_lane(str(fake), base, base / "report", base / "target", [])
            self.assertEqual(run.code, 0, run.output)
            self.assertIn("Summary: 0 proved", run.output)
            self.assertIsNotNone(run.rss_bound)
            self.assertGreaterEqual(run.rss_bound, 200 << 20, run.rss_bound)


class NativeInputRetention(unittest.TestCase):
    def test_failed_runs_keep_distinct_real_outputs_through_mutant_cleanup(self):
        with tempfile.TemporaryDirectory(prefix="native inputs with spaces ") as tmp:
            root = Path(tmp)
            fake = root / "targo"
            fake.write_text(
                "#!/bin/sh\n"
                "if [ \"${2-}\" = --help ]; then\n"
                "  echo '  --native-bundle-dir <dir> Diagnostic output only'\n  exit 0\nfi\n"
                "report_path=\nnative_path=\n"
                "while [ \"$#\" -gt 0 ]; do\n"
                "  case \"$1\" in\n"
                "    --report-dir) shift; report_path=$1 ;;\n"
                "    --native-bundle-dir) shift; native_path=$1 ;;\n"
                "  esac\n  shift\ndone\n"
                "test -n \"$report_path\" && test -n \"$native_path\" || exit 9\n"
                "mkdir -p \"$native_path\"\n"
                "printf '%s' '{\"diagnostic\":true}' > \"$native_path/input.json\"\n"
                "printf '%s' '{\"control\":true}' > \"$report_path/report.json\"\n"
                "echo NATIVE_INPUT_CAPTURE_CONTROL_RAN\nexit 7\n",
                encoding="utf-8",
            )
            fake.chmod(0o755)
            logical = root / "mutants" / "case.report"
            logical.mkdir(parents=True)
            stale = logical / "report.json"
            stale.write_text("old run; must never be judged or destroyed", encoding="utf-8")
            env = {k: v for k, v in os.environ.items()
                   if k not in ("RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_ENCODED_RUSTFLAGS")}
            with mock.patch.dict(os.environ, env, clear=True):
                runs = [vc.run_lane(str(fake), root, logical, root / "target", [], release=release)
                        for release in (False, True)]
            self.assertNotEqual(runs[0].report_dir, runs[1].report_dir)
            self.assertEqual(stale.read_text(encoding="utf-8"), "old run; must never be judged or destroyed")
            shutil.rmtree(root / "mutants")  # maintained main()'s normal workspace retirement
            for run in runs:
                self.assertEqual(run.code, 7)
                self.assertIn("NATIVE_INPUT_CAPTURE_CONTROL_RAN", run.output)
                retained = vc.retained_report_dir(run, logical)
                self.assertEqual(json.loads((retained / "report.json").read_text()), {"control": True})
                self.assertEqual(json.loads((retained / "native-bundles/input.json").read_text()),
                                 {"diagnostic": True})
                request = json.loads((retained / "request.json").read_text())
                self.assertFalse(request["complete_census"])
                self.assertFalse(request["proof_authority"])
                self.assertEqual(request["native_bundle_export"], "requested")
                self.assertEqual(request["command"][request["command"].index("--report-dir") + 1], str(retained))
                self.assertEqual(json.loads((retained / "run.lane.json").read_text())["exit"], 7)

    def test_older_toolchain_keeps_verification_without_forwarding_an_unknown_option(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fake = root / "targo"
            fake.write_text(
                "#!/bin/sh\n"
                "if [ \"${2-}\" = --help ]; then\n"
                "  echo '  --native-bundle-directory-lookalike <dir>'\n  exit 0\nfi\n"
                "report_path=\nwhile [ \"$#\" -gt 0 ]; do\n"
                "  case \"$1\" in\n"
                "    --native-bundle-dir) exit 9 ;;\n"
                "    --report-dir) shift; report_path=$1 ;;\n"
                "  esac\n  shift\ndone\n"
                "printf '%s' '{\"old-toolchain-control\":true}' > \"$report_path/report.json\"\n"
                "echo OLD_NATIVE_RUN_CONTROL_RAN\nexit 7\n",
                encoding="utf-8",
            )
            fake.chmod(0o755)
            env = {k: v for k, v in os.environ.items()
                   if k not in ("RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_ENCODED_RUSTFLAGS")}
            with mock.patch.dict(os.environ, env, clear=True):
                run = vc.run_lane(str(fake), root, root / "report", root / "target", [])
            self.assertEqual(run.code, 7)
            self.assertIn("OLD_NATIVE_RUN_CONTROL_RAN", run.output)
            retained = vc.retained_report_dir(run, root / "report")
            request = json.loads((retained / "request.json").read_text())
            self.assertEqual(request["native_bundle_export"], "not-advertised")
            self.assertNotIn("--native-bundle-dir", request["command"])
            self.assertFalse((retained / "native-bundles").exists())
            self.assertTrue((retained / "report.json").is_file())

    def test_policy_refusal_leaves_existing_evidence_untouched(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            report = root / "report"
            report.mkdir()
            (report / "evidence").write_text("retained", encoding="utf-8")
            with mock.patch.dict(os.environ, {"RUSTFLAGS": "untrusted control"}):
                with self.assertRaises(SystemExit):
                    vc.run_lane("must-not-launch", root, report, root / "target", [])
            self.assertEqual((report / "evidence").read_text(), "retained")
            self.assertFalse((root / "verified-inputs").exists())


class RootManifest(unittest.TestCase):
    def test_trust_table_and_edition_are_read_from_the_root(self):
        # The root's `[trust]` table is read verbatim, comments included; its
        # comment names the retirement below.
        self.assertIn("BUDGET-1a", vc.root_trust_table(ROOT))
        self.assertEqual(vc.workspace_edition(ROOT), "2024")

    def test_the_root_declares_no_retired_budget_key(self):
        # Trust retired `function_budget_ms` and `timeout_ms` (its
        # DECISION_QUEUE BUDGET-1a): a targo that carries the retirement refuses
        # either key in this workspace's root, and every mutant workspace copies
        # this table.
        keys = [
            line.split("=", 1)[0].strip()
            for line in vc.root_trust_table(ROOT).splitlines()
            if "=" in line and not line.lstrip().startswith("#")
        ]
        for retired in ("function_budget_ms", "timeout_ms"):
            self.assertNotIn(retired, keys)


class ToolchainIdentity(unittest.TestCase):
    """The diagnostic must not describe an unrelated PATH compiler as the
    compiler belonging to an explicitly selected SDK."""

    @staticmethod
    def fake_trustc(directory: Path, label: str, *, code: int = 0) -> Path:
        directory.mkdir(parents=True, exist_ok=True)
        compiler = directory / "trustc"
        marker = directory / "identity-probed"
        compiler.write_text(
            "#!/bin/sh\n"
            f"printf probed > {shlex.quote(str(marker))}\n"
            f"printf '%s\\n' {shlex.quote('rustc ' + label)}\n"
            f"exit {code}\n",
            encoding="utf-8",
        )
        compiler.chmod(0o755)
        return compiler

    def test_missing_sdk_compiler_never_borrows_the_path_compiler(self):
        with tempfile.TemporaryDirectory(prefix="identity with spaces ") as tmp:
            root = Path(tmp)
            unrelated = self.fake_trustc(root / "unrelated", "unrelated")
            with mock.patch.dict(os.environ, {"PATH": str(unrelated.parent)}):
                identity = vc.toolchain_identity(str(root / "selected" / "targo"))
            self.assertIn("unavailable", identity)
            self.assertNotIn("rustc unrelated", identity)
            self.assertFalse((unrelated.parent / "identity-probed").exists())

    def test_identity_names_and_probes_only_the_selected_sibling(self):
        with tempfile.TemporaryDirectory(prefix="identity with spaces ") as tmp:
            root = Path(tmp)
            selected = self.fake_trustc(root / "selected", "selected")
            unrelated = self.fake_trustc(root / "unrelated", "unrelated")
            with mock.patch.dict(os.environ, {"PATH": str(unrelated.parent)}):
                identity = vc.toolchain_identity(str(selected.with_name("targo")))
            self.assertIn(str(selected), identity)
            self.assertIn("rustc selected", identity)
            self.assertNotIn("rustc unrelated", identity)
            self.assertTrue((selected.parent / "identity-probed").exists())
            self.assertFalse((unrelated.parent / "identity-probed").exists())

    def test_relative_targo_selection_never_turns_the_sibling_into_a_path_lookup(self):
        with tempfile.TemporaryDirectory(prefix="relative identity ") as tmp:
            root = Path(tmp)
            selected = self.fake_trustc(root / "selected", "selected")
            unrelated = self.fake_trustc(root / "unrelated", "unrelated")
            targo = selected.with_name("targo")
            targo.write_text("#!/bin/sh\necho targo 0.0.0\n", encoding="utf-8")
            targo.chmod(0o755)
            previous = Path.cwd()
            try:
                os.chdir(selected.parent)
                with mock.patch.dict(
                    os.environ, {"PATH": str(unrelated.parent), "TRUST_TARGO_BIN": "./targo"}
                ):
                    identity = vc.toolchain_identity(vc.resolve_targo())
            finally:
                os.chdir(previous)
            self.assertIn(str(selected), identity)
            self.assertIn("rustc selected", identity)
            self.assertNotIn("rustc unrelated", identity)
            self.assertTrue((selected.parent / "identity-probed").exists())
            self.assertFalse((unrelated.parent / "identity-probed").exists())

    def test_failed_probe_cannot_publish_its_version_shaped_stdout(self):
        with tempfile.TemporaryDirectory() as tmp:
            selected = self.fake_trustc(Path(tmp), "unearned identity", code=7)
            identity = vc.toolchain_identity(str(selected.with_name("targo")))
            self.assertIn("unavailable", identity)
            self.assertIn("exit 7", identity)
            self.assertNotIn("rustc unearned identity", identity)

    def test_a_nonexecutable_or_directory_sibling_is_unavailable(self):
        with tempfile.TemporaryDirectory() as tmp:
            compiler = Path(tmp) / "trustc"
            compiler.mkdir()
            self.assertIn("unavailable", vc.toolchain_identity(str(compiler.with_name("targo"))))
            compiler.rmdir()
            compiler.write_text("rustc never executed\n", encoding="utf-8")
            compiler.chmod(0o644)
            self.assertIn("unavailable", vc.toolchain_identity(str(compiler.with_name("targo"))))
            compiler.chmod(0o755)
            self.assertIn("unavailable", vc.toolchain_identity(str(compiler.with_name("targo"))))

    def test_non_utf8_probe_output_is_unavailable_on_either_stream(self):
        for redirection in (">&1", ">&2"):
            with self.subTest(stream=redirection), tempfile.TemporaryDirectory() as tmp:
                compiler = self.fake_trustc(Path(tmp), "selected")
                compiler.write_text(
                    "#!/bin/sh\n" + r"printf '\377' " + redirection + "\nexit 7\n",
                    encoding="utf-8",
                )
                self.assertIn("unavailable", vc.toolchain_identity(str(compiler.with_name("targo"))))

    def test_a_timed_out_probe_is_unavailable(self):
        with tempfile.TemporaryDirectory() as tmp:
            compiler = self.fake_trustc(Path(tmp), "selected")
            with mock.patch.object(
                vc.subprocess, "run", side_effect=vc.subprocess.TimeoutExpired([str(compiler), "-vV"], 30)
            ):
                identity = vc.toolchain_identity(str(compiler.with_name("targo")))
            self.assertIn("unavailable", identity)


class TargoResolution(unittest.TestCase):
    """Gate 13 is the ONE verified lane, so a cargo-in-disguise (upstream Cargo
    installed as `targo`, which rejects `--unverified`) must be refused on
    every path `resolve_targo` can take, not only the one CI happens to hit."""

    @staticmethod
    def fake_targo(directory: Path, *, genuine: bool) -> Path:
        directory.mkdir(parents=True, exist_ok=True)
        targo = directory / "targo"
        rejection = "" if genuine else (
            'case "$1" in --unverified) echo "error: unexpected argument \'--unverified\'" >&2; exit 1;; esac\n'
        )
        targo.write_text(f"#!/bin/sh\n{rejection}echo targo 0.0.0\n", encoding="utf-8")
        targo.chmod(0o755)
        return targo

    @staticmethod
    def fake_rustup(directory: Path, targo: Path) -> None:
        directory.mkdir(parents=True, exist_ok=True)
        rustup = directory / "rustup"
        rustup.write_text(
            "#!/bin/sh\n"
            f'[ "$*" = "which --toolchain trust targo" ] && {{ echo "{targo}"; exit 0; }}\n'
            "exit 1\n",
            encoding="utf-8",
        )
        rustup.chmod(0o755)

    def resolve_via(self, path: str, genuine: bool) -> str:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            env = {k: v for k, v in os.environ.items() if k != "TRUST_TARGO_BIN"}
            if path == "TRUST_TARGO_BIN":
                env["TRUST_TARGO_BIN"] = str(self.fake_targo(base / "explicit", genuine=genuine))
                env["PATH"] = str(base / "empty")
            elif path == "PATH":
                env["PATH"] = str(self.fake_targo(base / "on-path", genuine=genuine).parent)
            else:
                targo = self.fake_targo(base / "toolchain" / "bin", genuine=genuine)
                self.fake_rustup(base / "rustup-bin", targo)
                env["PATH"] = str(base / "rustup-bin")
            with mock.patch.dict(os.environ, env, clear=True):
                return vc.resolve_targo()

    def test_cargo_in_disguise_is_refused_on_every_resolution_path(self):
        for path in ("TRUST_TARGO_BIN", "PATH", "rustup"):
            with self.subTest(path=path):
                with self.assertRaises(SystemExit) as refused:
                    self.resolve_via(path, genuine=False)
                self.assertIn("not Trust's targo", str(refused.exception.code))

    def test_a_targo_that_accepts_the_discriminator_resolves_on_every_path(self):
        for path in ("TRUST_TARGO_BIN", "PATH", "rustup"):
            with self.subTest(path=path):
                self.assertTrue(self.resolve_via(path, genuine=True).endswith("/targo"))


if __name__ == "__main__":
    unittest.main()
