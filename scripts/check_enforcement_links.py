#!/usr/bin/env python3
"""The enforcement-link gate: a normative claim names its enforcement, and the
named enforcement EXISTS.

WHY THIS EXISTS
---------------
The owner's goal, verbatim: "I want to move in-text claims to mechanically
verified proof."  This gate is the FIRST RUNG of that ladder and not the
destination.  It proves nothing about any claim.  What it does is make an
UNBACKED or ROTTED claim a gate failure instead of a sentence nobody re-reads:

* `docs/SPEC_RATIFICATIONS.md` ends its sections in `*Enforcement:*` lines that
  name tests and files.  Until this gate nothing checked that a named test was
  still a test, or that a named file still existed, so a rename silently turned
  "pinned by `foo`" into a sentence about nothing.
* Nothing said WHAT KIND of evidence a claim had.  "Enforced by a test" and
  "unrepresentable, rustc checks it" and "a Lean theorem" and "nothing in this
  tree" all read the same in prose.  The class is now a machine-readable column.

Precedent: the Clean repository's `scripts/check_doc_claims.py` (D1 asks whether a cited
PATH exists; D4 whether the cited LINE says what the prose claims) and
the Trust repository's claim ledger.  This gate is D1-shaped: it checks EXISTENCE,
except rule E5, a D4 rung for the two proved classes: their entries must say
what the cited statement says, in a closed vocabulary.

THE GRAMMAR
-----------
Line form, anywhere in a governed section (the paragraph runs to a blank line):

    *Enforcement (test):* `crates/x/tests/y.rs`, pinned by `a_test_fn`.

Table form, for a section that already tabulates its boundary: a Markdown table
with a column headed exactly `Enforcement`, each body cell beginning `(class)`.
If the table also has a column headed `Item`, a row attaches to that NUMBERED
ITEM of the document (this is how `TRUST.md`'s trusted-base items are covered
without rewriting the canonical prose of each item).

The classes, a closed set: the checked ones weakest first, then the three that
are not checked evidence (`CLASSES` below ranks them, strongest first):

  test                evidence, not proof: something EXECUTES and would fail.
                      Witness: a `#[test]` fn, a file or `#[cfg(test)]` module
                      holding one (in a workspace member, or in a test
                      target of a workspace-EXCLUDED package that a
                      standing gate runs by manifest path:
                      `gated_excluded_test_files`), a `scripts/tests`
                      test, or a Lean
                      `#guard_msgs` file (a whole-file test context, like a
                      `tests/*.rs`) that the `lean-proofs` gate builds, a
                      `native_decide` fixture theorem it builds (see
                      `lean-theorem`), or the census file that gate runs
                      (`lean/trust_ir-semantics/ProofCensus.lean`).  A
                      `ci_gates.sh` gate name and a
                      conformance fixture RESOLVE as citations but witness
                      nothing alone: naming `workspace-format` is a rewording.
  corpus              the test rung for a "consumer MUST refuse" claim: it
                      cites a row of the must-refuse corpus as `refuse/<row>`
                      (KIND 4, 2026-09-24).  Witness: a row of
                      `crates/trust-ir-conformance/tests/fixtures/refuse/MANIFEST.tsv`,
                      which `tests/refuse_corpus.rs` byte-pins and runs against
                      the trust-ir entry point that refuses it, and which a
                      consumer runs through `trust_ir_conformance::refuse`.
                      Evidence about the refusal, never proof of it.
  type-level          unrepresentable by construction; rustc checks it.
                      Witness: a Rust type, or a Cargo feature that is OFF in
                      the default build — checked against the manifest's
                      `default` closure, not read off the feature's name.
  proved-contract     a Trust contract gate 13 (`verified-contracts`,
                      scripts/verified_contracts.py) PROVES about one pure
                      decision table: every row `proved`, `Certified` and
                      `KernelRechecked` (the Clean kernel re-checks it), under
                      a same-shape mutant that must refute it.  Witness: a law
                      — a `pub fn` of `crates/trust-ir-laws/src/laws.rs`, or a
                      glob over their names (`laws::rc_*`, as gate 13's
                      `flips` spell it) — that gate 13 HOLDS: the law exists,
                      every law of the file is exactly one call of its own
                      table at the cell its name spells (`WIRING`), every law
                      is named by some mutant's `flips`, and every table over
                      enum cells has a law at every cell of its operand enums
                      (so a glob over such a family names every cell; a table
                      over `u64` payloads, named in gate 13's PAYLOAD_TABLES —
                      `coverage_supports` — is not enumerated, and a glob over
                      its laws names the laws that exist).  Gate 13 refuses to run otherwise, so on such a
                      file it proves NO law, and none witnesses.  The rule is
                      read from gate 13's code (`verified_contracts.holding`),
                      never restated here.  And each cited law must FOLLOW A
                      CITATION OF ITS OWN TABLE: the table the entry cites
                      most recently before the law must be the one its WIRING
                      family calls, where a table citation is a spelling that
                      ends with the table's WIRING path (`Type::method` or the
                      free `fn`'s name) and resolves to that table's own
                      definition — in the source a law can call — and to
                      nothing else (a law of a family that calls no table
                      witnesses nothing).  That is a SYNTACTIC check of which
                      table a law is cited under.  Rule E5 adds the verdict:
                      the entry must give each law the verdict its `ensures`
                      states (gate 13 reads it, `Holding.verdicts`).
                      WHAT IS PROVED, EXACTLY: the table's rows, about its
                      OPTIMIZED MIR (`--release`) under the pinned trustc.
                      A law is a wrapper, and its clause is about the table
                      only because the MIR inliner puts the table's body in
                      it; for every constant-valued law the case analysis is
                      then done by rustc's MIR optimizer, which folds the
                      wrapper to a constant, and the kernel re-checks that
                      constant — the optimizer is TRUSTED there, not checked.
                      Only the `u64` magnitude laws make the solver reason.
                      That is why it ranks BELOW `lean-theorem` and
                      `kernel-certificate` (whose case analysis the kernel
                      itself checks) and above `type-level` and `test` (it
                      is about every input of the table, `u64` payloads
                      included).  A refuting mutant shows only that a law is
                      not proved about a constant; the wiring check is what
                      ties each law to its own table.  It is NOT a proof that
                      the rule citing the table reads it; rule E5 ties each
                      law's verdict in the entry to its `ensures`, and no
                      further (the rest of the words are not read).
  lean-theorem        a mechanized Lean `theorem`/`lemma` that a standing gate
                      BUILDS.  Witness: a theorem in the import closure of
                      `lean/trust_ir-semantics/TrustIr.lean`, the library the
                      `lean-proofs` gate (scripts/lean_proofs.py) compiles and
                      whose every safe constant it censuses for axioms, and
                      NOT in one of the `native_decide` fixture modules its
                      census names (`nativeDecideModules` in
                      `lean/trust_ir-semantics/ProofCensus.lean`, read from
                      there): a fixture theorem is an EVALUATION that trusts
                      the Lean compiler (`Lean.ofReduceBool`), so it witnesses
                      `test`.  A theorem in any other `.lean` file (a
                      `reports/` probe, a file no root
                      imports) resolves as a citation and witnesses nothing
                      but `code`: nothing compiles it.
  kernel-certificate  a Clean-kernel re-checked certificate.  Witness: a
                      `KERNEL_ANCHOR_*` constant (the re-check's wiring).
  code                names the code that implements the rule, and NOTHING that
                      executes to check it.  The mechanism exists; no evidence
                      says it works.  Witness: any non-test item or file.
  external            enforced by a NAMED artifact in another repository.  This
                      tree cannot check it; its citations are NOT resolved.
  prose-only          nothing mechanical backs it.  Said out loud, and counted.

RULES, all fail-closed
----------------------
  E1 NAMED     Every normative unit (a `##`/`###` section of the ratifications;
               a numbered trusted-base item of `TRUST.md`) carries at least one
               Enforcement entry.  An entry with no class, or an unknown class,
               is refused.
  E2 RESOLVES  In every entry except `external`, EVERY backticked token is a
               citation and must resolve in the tree: a path must exist, an
               identifier must be a real item (qualifiers included, so
               `imports::tests::f` cannot resolve to an unrelated `f`).
  E3 WITNESS   The class must be WITNESSED: a `(test)` entry must cite at least
               one thing that resolves to a test artifact, `(lean-theorem)` a
               Lean theorem, and so on.  This is what stops a class being
               upgraded by rewording.  A `(proved-contract)` entry is held to
               more: EVERY law it cites must be one gate 13 holds, cited
               after a citation of its own table (above).
  E5 SAYS      A `(proved-contract)` or `(lean-theorem)` entry says what each
               statement it cites says, in the closed vocabulary `VERDICTS`
               (negators: `NEGATORS`).  Each cited LAW is given, by a phrase
               that governs it in its clause, the verdict its `ensures`
               states (true, false, or the relation itself).  Each cited
               THEOREM is given the verdict the reader classifies its
               conclusion as (UB, runs, a no-op, true, false) and is held to
               the backticked Lean identifiers its clause names before it
               (at least one; each must occur in the statement, negated in
               the entry exactly where the statement has it only after a
               `≠` or `¬`).  A theorem whose conclusion the reader cannot
               classify is held to NAMES ONLY, and a verdict phrase that
               governs one is refused; the reader decides the tier, never
               the author.  Refused too: a negated verdict phrase (F1), a
               closing phrase that governs no citation (F2), a citation
               right after a negator (F3), a wrong count in "the N other
               laws of", an "exactly at" that misses a law of its family
               with that verdict, "one law per" after a table over
               payloads, and a variant named beside laws that is no cell of
               them.  The law half is silent while gate 13 holds nothing
               (E3 refuses every law then); the Lean half always runs.
  E4 RATCHET   The units with NO CHECKED EVIDENCE in this tree (every entry
               `code`, `external` or `prose-only`: nothing executes, no compiler
               refuses, no theorem, no certificate) are recorded in
               `scripts/gates/enforcement-ratchet.txt`, three ways.  COUNT rows
               are the history: append-only, non-increasing, and the last one
               must EQUAL the measurement (higher is a regression; lower means
               somebody must write the smaller number down).  MEMBER lines are
               the present: exactly the debts measured today, BY NAME, so the
               file is the to-do list and no comment has to name them.
               CORRECTION rows are the one way a count rises, by exactly one:
               a unit somebody READ, found overclassed, and downgraded.  A
               ratchet that refuses that cannot tell honesty from regression,
               and rewards leaving the overclaim standing.  When git can name
               the merge-base with `origin/main`, the history rows there must
               be a PREFIX of today's, the member set may only have SHRUNK
               except by a correction naming a unit that EXISTED there WITH
               checked evidence (so a NEW unbacked claim cannot be called a
               correction), and a unit that was normative there cannot be
               marked not-normative.  (Until the ledger first lands there is
               no base to compare with; that window is unguarded.)
               A section that states no rule (an appendix, a changelog) opts
               out with `<!-- enforcement-links: not-normative <why> -->`; the
               reason is required, and BOTH `check` and the census print every
               opt-out, because one leaves the unit count AND the debt list.
  P  PATHS     Outside entries too: a repo-rooted path backticked anywhere in a
               governed document must exist (or be declared external with a
               `<!-- enforcement-links: external <path> -->` marker).
  V  VARIANTS  Every `ValidationError` variant is a refusal rule, and its
               rustdoc is a claim ("... Rejected.").  Two counts are ratcheted
               the same way: variants NO test context names, and variants NO
               non-test code CONSTRUCTS at all (a documented refusal that
               cannot fire; the definition and a `Display` arm are not a rule).
  R  ROWS      Every row of the must-refuse manifest names, in its
               `obligation` column, the file where its "consumer MUST"
               sentence lives, and that file CITES THE ROW BACK as
               `refuse/<row>` — so the two-way link between a claim and its
               artifact cannot rot in either direction (a renamed row, a
               moved sentence).  A `none` row (an obligation the corpus cannot
               express) is held to the same link: the sentence says so.

WHAT THIS HONESTLY DOES NOT DO
------------------------------
* It checks that a cited test EXISTS, never that it tests the claim.  Whether
  the cited line says what the prose says is checked only for the two proved
  classes (E5), and there only as follows.
* E5 is a clause grammar over the entry and a reader of Lean SOURCE TEXT, not
  of the elaborated type: test evidence, never a proof about the English.  It
  binds a verdict and NAMES, never their roles: an identifier is checked for
  presence and negation, not for order or quantifier, so "a `Store` after a
  `Release`" also matches a statement holding both the other way round.  A
  sentence that cites nothing is not bound, and neither is a unit's prose
  outside its entries or TRUST.md's claim column.  The reader classifies a
  subset of conclusions (an equation whose right-hand side is a UB error, a
  run, the unchanged state, `true` or `false`); a conjunction, a frame
  condition or a negation is held to names only, counted apart.  The
  identifiers an entry names are the author's choice, so E5 catches drift and
  honest error, not an adversary.  A negation spelled outside `NEGATORS`
  ("fails to be") still gets through.  A `(test)` entry's theorems and the
  `(kernel-certificate)` entries are outside it.
* EXISTS is also weaker than RUNS.  `scripts/ci_gates.sh` runs a subset of the
  workspace's tests; a cited test may run only under `scripts/ci-self-verify.sh`.
  A `(lean-theorem)` witness is the exception, since 2026-09-29: it must lie in
  what the `lean-proofs` gate builds (above), so on a machine with `lake` a
  standing gate does compile it and census its axioms.  That gate SKIPS where
  there is no `lake`; this script cannot tell, and does not try.
* A `(proved-contract)` witness is checked against what gate 13 HOLDS before
  any run (the law exists, is wired to its table, is named by a mutant),
  never against a run: this gate is toolchain-free.  The run is gate 13, a
  standing gate that FAILS, never skips, where the verified lane is missing.
  Which table a law is cited under is checked, and so is the verdict the
  entry gives the law (E5); that the rest of the entry's words are about that
  table is not.
* The unit is the SECTION.  A section with one tested sub-clause and five
  untested ones counts as backed.  The per-section classes were assigned by
  reading; a wrong class that still has a witness passes.
* A correction is checked for SHAPE, never for truth: that the unit existed,
  had checked evidence, and is downgraded once, with a reason.  Whether the
  reason is right is a reader's judgement, which is the point of recording it.
* Deleting a section deletes its claim, its debt and its count together.  That
  is a change to the normative DOCUMENT and is left to review; what the gate
  refuses is retiring a debt with a marker while the claim stays on the page.
* `external` citations are not resolved even when the sibling repo is on disk.
  A cross-repo claim can rot under this gate (one did, in a day: see the
  2026-09-18 note in the ratifications, section 7).
* "Names a variant" (rule V) is weaker than "tests the rule".
* Like every gate in this repository it runs on the `--unverified` lane and
  makes NO proof claim of its own.
"""

from __future__ import annotations

import argparse
import bisect
import datetime
import fnmatch
import functools
import json
import os
import posixpath
import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Set, Tuple

sys.dont_write_bytecode = True
sys.path.insert(0, os.fspath(Path(__file__).resolve().parent))
from check_no_ignored_rust import mask_non_code  # noqa: E402  (shared Rust lexer)
# What the `lean-proofs` gate builds, stated once (gate 14): the TrustIr import
# closure, and the native_decide fixture modules its census names.
from lean_proofs import CENSUS_FILE as LEAN_CENSUS_FILE  # noqa: E402
from lean_proofs import PACKAGE as LEAN_PACKAGE  # noqa: E402
from lean_proofs import import_closure, native_decide_modules  # noqa: E402
# What gate 13 holds of its laws file, stated once (`verified_contracts.holding`):
# the `(proved-contract)` witness rule.  A module, not names, so a test can
# patch what gate 13 holds.
import verified_contracts as gate13  # noqa: E402

RATCHET = "scripts/gates/enforcement-ratchet.txt"
# Strongest first.  The first six are CHECKED evidence (something refuses when
# the claim breaks); the last three are not, and are what the ratchet counts.
CLASSES = ("kernel-certificate", "lean-theorem", "proved-contract", "type-level", "test", "corpus", "code", "external", "prose-only")
IN_TREE = ("kernel-certificate", "lean-theorem", "proved-contract", "type-level", "test", "corpus")
# Gate 13's laws: `(proved-contract)` citations resolve against its `pub fn`s.
LAWS_FILE = gate13.LAWS_FILE.as_posix()
# A citation of every law a glob names (`laws::rc_*`), as gate 13's `flips` do.
# It leads with an identifier, so a deref such as `*mut` stays opaque prose.
LAW_GLOB = re.compile(r"((?:[A-Za-z_][A-Za-z0-9_]*::)*)([A-Za-z_][A-Za-z0-9_]*\*[A-Za-z0-9_*]*)\Z")
# The must-refuse corpus manifest (KIND 4): `refuse/<row>` citations resolve
# against its rows, and rule R holds each row to its cited document.
REFUSE_MANIFEST = "crates/trust-ir-conformance/tests/fixtures/refuse/MANIFEST.tsv"
# The level-S template corpus (amendment S) is a manifest of its own, in a
# sibling directory (a module consumer meets none of its rows): its rows are
# cited as `refuse_templates/<row>` and held to rule R the same way.
REFUSE_TEMPLATE_MANIFEST = "crates/trust-ir-conformance/tests/fixtures/refuse_templates/MANIFEST.tsv"
REFUSE_TOKEN = re.compile(r"(?:refuse|refuse_templates)/([a-z0-9_]+)\Z")
SECTION_LEDGER = "units-without-checked-evidence"
VARIANT_LEDGER = "validation-error-variants-unnamed"
DEAD_LEDGER = "validation-error-variants-never-constructed"
LEDGERS = (SECTION_LEDGER, VARIANT_LEDGER, DEAD_LEDGER)

# Kinds a citation can resolve to, and which of them witness which class.
# What EXECUTES and would fail.  A `gate` name and a `fixture` stem still RESOLVE
# as citations (rule E2) but witness nothing on their own: `workspace-format` is
# a gate, and naming it is a rewording, not evidence that an interpreter is
# normative.  An entry that leans on a gate cites the test the gate runs.
# A `lean-native-decide` theorem is an evaluation the `lean-proofs` gate runs
# through the Lean compiler: a test.  A `lean-theorem-unbuilt` is a theorem no
# standing gate compiles: it names something, and checks nothing.
TEST_KINDS = {"test-fn", "test-file", "test-mod", "py-test", "lean-native-decide"}
CODE_KINDS = {"fn", "type", "variant", "field", "const", "mod", "macro", "file", "dir", "lean-def", "lean-ctor", "lean-theorem-unbuilt", "kernel-anchor", "feature", "default-off-feature", "gate", "fixture", "law"}
WITNESS = {
    "test": TEST_KINDS,
    "corpus": {"refuse-row"},
    "code": CODE_KINDS,
    # A `pub fn` of gate 13's laws file.  Necessary, not sufficient: the law
    # must also be HELD and cited after its own table (`check_proved_contract`).
    "proved-contract": {"law"},
    # A Cargo feature is type-level evidence in exactly one sense: it is OFF in
    # the default build, so rustc never sees what it gates.  That is CHECKED
    # (the manifest's `default` closure), not read off the feature's name.
    "type-level": {"type", "default-off-feature"},
    "lean-theorem": {"lean-theorem"},
    "kernel-certificate": {"kernel-anchor"},
}

VALIDATION_ERROR_FILE = "crates/trust-ir-build/src/validate.rs"
VALIDATION_ERROR_ENUM = "ValidationError"


class Doc:
    """One governed document.  `units` is how its normative claims are cut:
    "sections" (every `##`/`###` heading), "items" (numbered bold list items
    inside `region`), or "paths" (rule P only, no units)."""

    def __init__(self, path: str, units: str, region: Optional[str] = None, exported: bool = True):
        self.path = path
        self.units = units
        self.region = region
        self.exported = exported


GOVERNED = (
    Doc("docs/SPEC_RATIFICATIONS.md", "sections", exported=False),
    Doc("TRUST.md", "items", region="## Trusted base"),
    Doc("CLAUDE.md", "paths", region="## Serialization", exported=False),
)


# What a PUBLIC SNAPSHOT never carries (both are denied by the publication
# manifest).  A tree missing BOTH is a snapshot; a tree missing only a governed
# document is a broken checkout, and still fails closed.
SNAPSHOT_NEVER_SHIPS = ("docs", "CLAUDE.md")


def is_public_snapshot(root: Path) -> bool:
    return not any((root / name).exists() for name in SNAPSHOT_NEVER_SHIPS)


class Finding:
    def __init__(self, path: str, line: int, rule: str, message: str) -> None:
        self.path, self.line, self.rule, self.message = path, line, rule, message

    def __str__(self) -> str:
        return f"{self.path}:{self.line}: [{self.rule}] {self.message}"


# --------------------------------------------------------------------------
# The tree index: what EXISTS.
# --------------------------------------------------------------------------


class Definition:
    def __init__(self, name: str, kind: str, path: str, line: int, context: Sequence[str]) -> None:
        self.name, self.kind, self.path, self.line = name, kind, path, line
        self.context = frozenset(context)


class Index:
    def __init__(self) -> None:
        self.files: Set[str] = set()
        self.defs: Dict[str, List[Definition]] = {}
        self.test_files: Set[str] = set()
        # masked source, split by whether a test context holds it (rule V)
        self.test_code: List[str] = []
        self.live_code: List[str] = []
        self.members: Optional[List[str]] = None
        # level aliases, `type NAME = NAMEG<..>;` (amendment S): (module
        # context, NAME). The alias carries every member of its generic
        # carrier, so `Ty::Handle` resolves through `TyG`'s variants.
        self.level_aliases: List[Tuple[frozenset, str]] = []
        # must-refuse manifest rows: id -> (line, carrier, obligation path)
        self.refuse_rows: Dict[str, Tuple[int, str, str]] = {}
        # the template corpus's rows, the same shape
        self.refuse_template_rows: Dict[str, Tuple[int, str, str]] = {}
        self.refuse_manifest_findings: List[Finding] = []
        # an unreadable `lean-proofs` census scope (rule E3 fails closed on it)
        self.lean_findings: List[Finding] = []
        # `Validation:<Variant>` verdicts the manifest pins: each is RUN by
        # `refuse_corpus.rs` against the entry point that returns it, so the
        # variant counts as named by a test context (rule V)
        self.refuse_named: Set[str] = set()
        # what gate 13 holds of its laws file (None: the tree carries none)
        self.gate13: Optional[gate13.Holding] = None
        # rule E5's per-file cache of Lean sources, read on first use
        self.lean_sources: Dict[str, str] = {}
        # (name, its `law` definitions) for every name with one, built on
        # first use by `law_names`; dropped whenever a definition is added
        # or re-kinded (`add`, `index_laws`)
        self.law_defs: Optional[List[Tuple[str, List["Definition"]]]] = None

    def add(self, name: str, kind: str, path: str, line: int, context: Sequence[str]) -> None:
        self.defs.setdefault(name, []).append(Definition(name, kind, path, line, context))
        self.law_defs = None


def visible_files(root: Path) -> List[str]:
    """Git-visible files (tracked plus untracked-not-ignored), so an artifact
    that exists only in one author's working tree cannot satisfy a citation
    forever; outside a repository (unit-test trees), every file."""
    try:
        result = subprocess.run(
            ["git", "-C", os.fspath(root), "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
        )
        names = [os.fsdecode(n) for n in result.stdout.split(b"\0") if n]
        names = [n for n in names if (root / n).is_file()]
        if names:
            return sorted(names)
    except (OSError, subprocess.CalledProcessError):
        pass
    found = []
    for base, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in {".git", "target", ".lake", "__pycache__"}]
        for name in files:
            found.append(os.path.relpath(os.path.join(base, name), root))
    return sorted(found)


ITEM_HEADER = re.compile(
    r"\b(?:(fn)|(mod)|(struct|enum|trait|union|type)|(const|static)|(macro_rules)\s*!)\s+"
    r"(?:mut\s+)?(?!(?:fn|unsafe|extern|async|in|for|as|if|impl|where)\b)([A-Za-z_][A-Za-z0-9_]*)"
)
IMPL_START = re.compile(r"(?:(?:unsafe|default)\s+)*impl\b")
# `type Ty = TyG<NoExt>;`: a level alias of a level-generic carrier (amendment
# S). Only the `NAME = NAMEG<..>` shape is an alias the index follows.
LEVEL_ALIAS = re.compile(r"\btype\s+([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*\1G\s*<")
# `impl<'a> Report<'a> {`: the shared lexer takes the text between two lifetimes
# on one line for a char literal and blanks it, which would strip the type off
# every method of a lifetime-generic impl.  A lifetime carries no structure this
# index needs, so blank it first.  `'a'` (a char) is left for the lexer.
LIFETIME = re.compile(r"'[A-Za-z_][A-Za-z0-9_]*(?!')")
MACRO_CALL = re.compile(r"[a-z_][a-z0-9_]*\s*!\s*\Z")
MACRO_DEFINED = re.compile(r"\s*([A-Z][A-Za-z0-9]*)\b")
MACRO_PAREN = re.compile(r"[a-z_][a-z0-9_]*\s*!\s*\(\s*([A-Z][A-Za-z0-9]*)\b")
ATTRIBUTE = re.compile(r"#\s*!?\s*\[[^\]]*\]")
TEST_ATTR = re.compile(r"#\s*\[\s*(?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*test\b")
CFG_TEST = re.compile(r"#\s*\[\s*cfg\s*\(\s*(?:all\s*\(\s*)?test\b")
IMPL_HEADER = re.compile(r"\bimpl\b")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def module_context(path: str) -> List[str]:
    """`crates/trust-ir/src/a/b.rs` -> [trust_ir, a, b]; tests/ and lib/mod files
    contribute the components a reader would write in a `crate::path`."""
    parts = path.split("/")
    context: List[str] = []
    if len(parts) >= 2 and parts[0] == "crates":
        context.append(parts[1].replace("-", "_"))
        parts = parts[2:]
    else:
        context.append(parts[0].replace("-", "_"))
        parts = parts[1:]
    for part in parts:
        stem = part[:-3] if part.endswith(".rs") else part
        if stem in {"src", "lib", "main", "mod"}:
            continue
        context.append(stem)
    return context


def _impl_target(header: str) -> Optional[str]:
    """The type an `impl` block is for: last path segment, generics stripped."""
    text = header[IMPL_HEADER.search(header).end():]  # type: ignore[union-attr]
    depth, out = 0, []
    for ch in text:  # drop every <...> group
        if ch == "<":
            depth += 1
        elif ch == ">":
            depth = max(0, depth - 1)
        elif depth == 0:
            out.append(ch)
    flat = "".join(out)
    if " for " in flat:
        flat = flat.split(" for ", 1)[1]
    flat = flat.split(" where ", 1)[0]
    names = IDENT.findall(flat)
    names = [n for n in names if n not in {"dyn", "mut", "const", "unsafe", "crate", "self", "super"}]
    return names[-1] if names else None


FIELD = re.compile(r"\s*([A-Za-z_][A-Za-z0-9_]*)\s*:(?!:)")
VARIANT = re.compile(r"\s*([A-Za-z_][A-Za-z0-9_]*)\s*(?:[({=]|\Z)")


def _members(body: str, kind: str) -> List[str]:
    """Variant names of an enum body, or field names of a struct body.  `body`
    is already masked.  A chunk must LOOK like a member: splitting
    `map: HashMap<K, V>` on its comma must not mint a field called `V`."""
    names, depth, chunk = [], 0, []
    shape = VARIANT if kind == "enum" else FIELD
    for ch in body + ",":
        if ch in "{([":
            depth += 1
        elif ch in "})]":
            depth -= 1
        if ch == "," and depth == 0:
            text = ATTRIBUTE.sub(" ", "".join(chunk))  # masked: no strings left to confuse this
            text = re.sub(r"\bpub\s*(?:\([^)]*\))?", " ", text)
            match = shape.match(text)
            if match:
                names.append(match.group(1))
            chunk = []
        else:
            chunk.append(ch)
    return names


def index_rust(index: Index, path: str, source: str, cfg_test_files: Set[str]) -> None:
    masked = mask_non_code(LIFETIME.sub(lambda m: " " * len(m.group(0)), source))
    base = module_context(path)
    in_tests_dir = "/tests/" in "/" + path or "/benches/" in "/" + path
    whole_file_test = in_tests_dir or path in cfg_test_files
    # scope stack: (label, kind, open_index, is_test)
    stack: List[Tuple[Optional[str], str, int, bool]] = []
    header_start = 0
    test_spans: List[Tuple[int, int]] = []
    line_starts = [0]
    for match in re.finditer("\n", masked):
        line_starts.append(match.end())

    def line_of(offset: int) -> int:
        return bisect.bisect_right(line_starts, offset)

    for delim in re.finditer(r"[{};]", masked):
        pos, ch = delim.start(), delim.group(0)
        if ch == "}":
            if stack:
                label, kind, opened, is_test = stack.pop()
                if kind == "macro-call":
                    # `typed_id! { /// docs\n ImportId }`: an item-level macro whose
                    # body LEADS with a type name defines that type.
                    defined = MACRO_DEFINED.match(ATTRIBUTE.sub(" ", masked[opened + 1 : pos]))
                    if defined:
                        index.add(defined.group(1), "type", path, line_of(opened), base + _labels(stack))
                if kind in {"enum", "struct"} and label:
                    for member in _members(masked[opened + 1 : pos], kind):
                        member_kind = "variant" if kind == "enum" else "field"
                        index.add(member, member_kind, path, line_of(opened), base + _labels(stack) + [label])
                if is_test and not any(s[3] for s in stack):
                    test_spans.append((opened, pos))
            header_start = pos + 1
            continue
        header = masked[header_start:pos]
        header_start = pos + 1
        context = base + _labels(stack)
        inherited_test = any(s[3] for s in stack)
        label, kind, is_test = None, "block", False
        item = None
        bare = ATTRIBUTE.sub(" ", header).strip()
        at_item_level = not any(s[1] == "fn" for s in stack)
        paren_form = MACRO_PAREN.match(bare) if ch == ";" and at_item_level else None
        if paren_form:
            # `typed_id!(/// docs\n FuncId);`, the same definition in its paren form.
            index.add(paren_form.group(1), "type", path, line_of(max(0, pos - len(header))), context)
        elif ch == "{" and MACRO_CALL.match(bare) and at_item_level:
            kind = "macro-call"
        elif ch == "{" and IMPL_START.match(bare):
            # An `impl` block, decided FIRST: `impl<const N: usize> Foo<N> {` also
            # contains a `const N`, which is a generic parameter and not an item.
            label, kind = _impl_target(header), "impl"
        else:
            for item in ITEM_HEADER.finditer(header):
                pass  # the LAST item keyword in the header is the one this delimiter closes
        if item is not None:
            is_fn, is_mod, is_type, is_const, is_macro, name = item.groups()
            offset = header_start - len(header) - 1 + item.start()
            line = line_of(max(0, offset))
            if is_fn:
                tested = bool(TEST_ATTR.search(header))
                index.add(name, "test-fn" if tested else "fn", path, line, context)
                label, kind, is_test = name, "fn", tested
            elif is_mod:
                cfg_test = bool(CFG_TEST.search(header))
                index.add(name, "test-mod" if (cfg_test or inherited_test) else "mod", path, line, context)
                label, kind, is_test = name, "mod", cfg_test
            elif is_type:
                index.add(name, "type", path, line, context)
                label, kind = name, item.group(3)
                if ch == ";" and item.group(3) == "type" and LEVEL_ALIAS.search(header[item.start():]):
                    index.level_aliases.append((frozenset(context), name))
            elif is_const:
                const_kind = "kernel-anchor" if name.startswith("KERNEL_ANCHOR_") else "const"
                index.add(name, const_kind, path, line, context)
            elif is_macro:
                index.add(name, "macro", path, line, context)
                label, kind = name, "macro"
        if ch == "{":
            stack.append((label, kind, pos, is_test))
    # Only a file that is a test context IN FULL witnesses `(test)`: citing
    # `binary.rs` because it happens to hold a `#[cfg(test)]` module names the
    # implementation, not a test.  Cite the test fn or the test module instead.
    if whole_file_test:
        index.test_files.add(path)
    if whole_file_test:
        index.test_code.append(masked)
        return
    index.test_code.extend(masked[a:b] for a, b in test_spans)
    live, cursor = [], 0
    for a, b in sorted(test_spans):
        live.append(masked[cursor:a])
        cursor = b
    live.append(masked[cursor:])
    index.live_code.append("".join(live))


def apply_level_aliases(index: Index) -> None:
    """Give each level alias `NAME` (amendment S, `type NAME = NAMEG<..>;`) the
    members its generic carrier `NAMEG` has in the same module: a level-R
    reader cites `Ty::Handle` and `Constant::U128`, and those ARE `TyG`'s and
    `ConstantG`'s variants at the level-R extension."""
    for module, alias in index.level_aliases:
        carrier = alias + "G"
        for defs in list(index.defs.values()):
            for d in list(defs):
                if carrier in d.context and module <= d.context:
                    defs.append(Definition(d.name, d.kind, d.path, d.line, (d.context - {carrier}) | {alias}))


def _labels(stack: Sequence[Tuple[Optional[str], str, int, bool]]) -> List[str]:
    return [s[0] for s in stack if s[0] and s[1] in {"mod", "impl", "enum", "struct", "trait"}]


# A `mod` keyword and the item it opens, on MASKED source (no string or
# comment can fake one).  Group 1 is the name; group 2 is `;` for an
# out-of-line module (a file) or `{` for an inline one.  The match is anchored
# on the keyword; the item's visibility and outer attributes are read
# BACKWARD from it (`_item_prefix`), each character once: a pattern that
# began with the attribute run re-scanned that run from every `#` in it when
# no `mod` followed (quadratic in a long run of attributes).
MOD_KEYWORD = re.compile(r"(?<![A-Za-z0-9_])mod\s+([A-Za-z_][A-Za-z0-9_]*)\s*([;{])")
# Braces, or a `mod` item, in one left-to-right pass.
MOD_OR_BRACE = re.compile(r"[{}]|" + MOD_KEYWORD.pattern)
# `#[path = "..."]` (or a raw string), read from the ORIGINAL source text of an
# item's attributes: masking blanks the literal.  rustc takes the first one.
PATH_ATTRIBUTE = re.compile(r'#\s*\[\s*path\s*=\s*(?:"((?:[^"\\]|\\.)*)"|r(#*)"(.*?)"\2)\s*\]', re.S)
# The files that own their directory whatever loaded them: a nested plain
# `mod x;` in one resolves to `x.rs` beside it.
DIRECTORY_OWNERS = {"lib.rs", "main.rs", "mod.rs", "build.rs"}


class ScanWork:
    """What the module scanner did, counted where it is done, so the tests can
    hold it to the input's size: `read`, the characters read backward in
    front of `mod` items; `scopes`, the inline modules resolved to a
    directory."""

    def __init__(self) -> None:
        self.read = 0
        self.scopes = 0


def _skip_space_back(text: str, end: int, work: Optional[ScanWork] = None) -> int:
    """The start of the whitespace run that ends at `end`."""
    start = end
    while start > 0 and text[start - 1].isspace():
        start -= 1
    if work is not None:
        work.read += end - start
    return start


def _word_before(text: str, end: int, word: str) -> int:
    """The start of `word` if `text[:end]` ends with it as a whole word, else -1."""
    start = end - len(word)
    if start < 0 or text[start:end] != word:
        return -1
    if start > 0 and (text[start - 1].isalnum() or text[start - 1] == "_"):
        return -1
    return start


def _back_to(text: str, end: int, opening: str, closing: str, work: Optional[ScanWork] = None) -> int:
    """The position of the `opening` that pairs with the `closing` at `end - 1`
    (no nesting, as `#[...]` and `pub(...)` are matched here), or -1."""
    position = end - 2
    while position >= 0 and text[position] not in (opening, closing):
        position -= 1
    if work is not None:
        work.read += end - 1 - max(position, 0)
    return position if position >= 0 and text[position] == opening else -1


def _item_prefix(masked: str, keyword: int, work: Optional[ScanWork] = None) -> int:
    """The start of the visibility and outer attributes (`#[...]`, possibly
    several) in front of the `mod` keyword at `keyword`.  Each character is
    read once per item, and the runs in front of distinct items are disjoint,
    so a file costs O(its length)."""
    start = keyword
    end = _skip_space_back(masked, keyword, work)
    if end > 0 and masked[end - 1] == ")":
        opening = _back_to(masked, end, "(", ")", work)
        if opening >= 0:
            pub = _word_before(masked, _skip_space_back(masked, opening, work), "pub")
            if pub >= 0:
                start = pub
    else:
        pub = _word_before(masked, end, "pub")
        if pub >= 0:
            start = pub
    while True:
        end = _skip_space_back(masked, start, work)
        if end == 0 or masked[end - 1] != "]":
            return start
        opening = _back_to(masked, end, "[", "]", work)
        if opening < 0:
            return start
        hash_end = _skip_space_back(masked, opening, work)
        if hash_end == 0 or masked[hash_end - 1] != "#":
            return start
        start = hash_end - 1


class InlineModule:
    """An inline `mod name { ... }`: its `#[path]` (if any), whether it or an
    inline module around it is `#[cfg(test)]`, and the inline module around
    it (`parent`, None at file level).  A declaration points at its innermost
    one, so recording where a declaration sits is O(1) however deep it is."""

    __slots__ = ("name", "path", "test", "parent")

    def __init__(self, name: str, path: Optional[str], test: bool, parent: Optional["InlineModule"]) -> None:
        self.name, self.path, self.parent = name, path, parent
        self.test = test or (parent is not None and parent.test)


class ModuleDecl:
    """One out-of-line `mod name;` of a file: its `#[path]` (if any), whether it
    is compiled only under test (its own `#[cfg(test)]` or an enclosing inline
    module's), and the innermost inline module around it (`scope`)."""

    def __init__(self, name: str, path: Optional[str], test: bool, scope: Optional[InlineModule]) -> None:
        self.name, self.path, self.scope = name, path, scope
        self.test = test or (scope is not None and scope.test)

    @property
    def inline(self) -> List[Tuple[str, Optional[str]]]:
        """The inline modules around the declaration, outermost first, as
        (name, `#[path]`)."""
        chain = []
        scope = self.scope
        while scope is not None:
            chain.append((scope.name, scope.path))
            scope = scope.parent
        return chain[::-1]


def _path_attribute(attributes: str) -> Optional[str]:
    match = PATH_ATTRIBUTE.search(attributes)
    if not match:
        return None
    if match.group(1) is not None:
        return re.sub(r"\\(.)", r"\1", match.group(1))
    return match.group(3)


def module_decls(source: str, work: Optional[ScanWork] = None) -> List[ModuleDecl]:
    """Every out-of-line module declaration of one file, with the inline
    modules it sits in, in one left-to-right pass over the file's `mod` items
    and braces."""
    masked = mask_non_code(source)
    decls: List[ModuleDecl] = []
    # The innermost inline module, and one saved value of it per open brace.
    scope: Optional[InlineModule] = None
    saved: List[Optional[InlineModule]] = []
    for match in MOD_OR_BRACE.finditer(masked):
        text = match.group(0)
        if text == "{":
            saved.append(scope)
            continue
        if text == "}":
            if saved:
                scope = saved.pop()
            continue
        name, kind = match.group(1), match.group(2)
        prefix = _item_prefix(masked, match.start(), work)
        test = bool(CFG_TEST.search(masked, prefix, match.start()))
        path = _path_attribute(source[prefix : match.start()])
        if kind == "{":
            saved.append(scope)
            scope = InlineModule(name, path, test, scope)
        else:
            decls.append(ModuleDecl(name, path, test, scope))
    return decls


class _Directory:
    """A directory of the source tree: its subdirectories, and its files (by
    name, to their full path)."""

    __slots__ = ("parent", "dirs", "files")

    def __init__(self, parent: Optional["_Directory"]) -> None:
        self.parent = parent
        self.dirs: Dict[str, "_Directory"] = {}
        self.files: Dict[str, str] = {}


# A place a module path can name: the deepest existing directory on the way
# there and how many components beyond it do not exist (a `..` can climb back
# out of those), or None above the tree's root, where no source file is.
_Place = Optional[Tuple[_Directory, int]]


def _step(place: _Place, component: str) -> _Place:
    if place is None or component in ("", "."):
        return place
    directory, missing = place
    if component == "..":
        if missing:
            return directory, missing - 1
        return (directory.parent, 0) if directory.parent is not None else None
    if not missing and component in directory.dirs:
        return directory.dirs[component], 0
    return directory, missing + 1


def _walk(place: _Place, relative: str) -> _Place:
    if relative.startswith("/"):
        return None  # an absolute path names no file of the tree
    for component in relative.split("/"):
        place = _step(place, component)
    return place


def _file_at(place: _Place, relative: str) -> Optional[str]:
    directory, _, name = relative.rpartition("/")
    place = _walk(place, directory) if directory else place
    if place is None or place[1] or name in ("", ".", ".."):
        return None
    return place[0].files.get(name)


class ModuleResolver:
    """Resolves module declarations to the source files they load, by rustc's
    rules (`rustc_expand::module`): a `#[path]` is relative to the declaring
    file's DIRECTORY (inside inline modules, to the directory they name); a
    plain `mod name;` is `name.rs` or `name/mod.rs` in the file's module
    directory, which is its own directory when the file owns it (a crate or
    `mod.rs` root, or a file itself loaded by `#[path]`) and `<dir>/<stem>/`
    otherwise.  `owns_directory` None means both readings (the scanner does
    not rebuild how every file was loaded), so a plain declaration may name
    one extra candidate; a `#[path]` outside inline modules is exact either
    way.

    Paths are walked through a directory tree of the sources, never built as
    strings, and each inline module is resolved once per reading and
    memoized, so resolving every declaration costs O(the sources' paths +
    the declarations + their attribute text), however deeply modules nest."""

    def __init__(self, paths: Sequence[str], work: Optional[ScanWork] = None) -> None:
        self.work = work
        self.root = _Directory(None)
        self.directories: Dict[str, _Directory] = {"": self.root}
        for path in paths:
            directory, _, name = path.rpartition("/")
            self._directory(directory).files[name] = path
        # Per inline module (each belongs to one file) and reading.
        self.memo: Dict[Tuple[int, bool], Tuple[_Place, Optional[str]]] = {}

    def _directory(self, directory: str) -> _Directory:
        node = self.directories.get(directory)
        if node is not None:
            return node
        node = self.root
        for name in directory.split("/"):
            child = node.dirs.get(name)
            if child is None:
                child = node.dirs[name] = _Directory(node)
            node = child
        self.directories[directory] = node
        return node

    def _scope(self, path: str, owned: bool, scope: Optional[InlineModule]) -> Tuple[_Place, Optional[str]]:
        """Where declarations inside `scope` of file `path` resolve from: a
        place, and the file's stem when its module directory is still to be
        entered (a non-owning file at file level)."""
        directory, _, filename = path.rpartition("/")
        state: Tuple[_Place, Optional[str]] = ((self.directories[directory], 0), None if owned else filename[:-3])
        pending: List[InlineModule] = []
        while scope is not None:
            known = self.memo.get((id(scope), owned))
            if known is not None:
                state = known
                break
            pending.append(scope)
            scope = scope.parent
        for inline in reversed(pending):
            if self.work is not None:
                self.work.scopes += 1
            place, stem = state
            if inline.path is not None:
                # An inline module's `#[path]` names a DIRECTORY.
                place = _walk(place, inline.path)
            else:
                if stem is not None:
                    place = _step(place, stem)
                place = _step(place, inline.name)
            state = (place, None)
            self.memo[(id(inline), owned)] = state
        return state

    def resolve(self, path: str, owns_directory: Optional[bool], decl: ModuleDecl) -> List[str]:
        """The source files `decl` in `path` loads (see the class docs)."""
        found: List[str] = []
        for owned in [owns_directory] if owns_directory is not None else [True, False]:
            place, stem = self._scope(path, owned, decl.scope)
            if decl.path is not None:
                candidates = [_file_at(place, decl.path)]
            else:
                module_dir = _step(place, stem) if stem is not None else place
                candidates = [_file_at(module_dir, f"{decl.name}.rs"), _file_at(module_dir, f"{decl.name}/mod.rs")]
            for candidate in candidates:
                if candidate is not None and candidate not in found:
                    found.append(candidate)
        return found


# A Cargo manifest's target table that names a source path, and the key.
MANIFEST_SECTION = re.compile(r"^\s*\[\[?\s*([A-Za-z0-9_.-]+)\s*\]\]?\s*(?:#.*)?$")
MANIFEST_PATH = re.compile(r'^\s*(path|build)\s*=\s*"([^"]*)"')


def cargo_target_roots(paths: Sequence[str], manifests: Dict[str, str]) -> Set[str]:
    """The source files Cargo compiles as the ROOT of a non-test target — a
    library, a binary, a build script or an example — which no `mod` loads:
    by Cargo's discovery (`src/lib.rs`, `src/main.rs`, `build.rs`,
    `src/bin/*.rs`, `src/bin/*/main.rs`, `examples/*.rs`,
    `examples/*/main.rs`) in each package, and by an explicit `[lib]` /
    `[[bin]]` / `[[example]]` `path` or a `[package]` `build`.  A package is a
    manifest's directory; with no manifests (a unit-test tree), every
    directory holding a `src/`.  Erring toward a root only keeps a file live
    code, never makes one test code."""
    present = set(paths)
    packages: Set[str] = set()
    roots: Set[str] = set()
    for manifest, text in manifests.items():
        package = manifest.rpartition("/")[0]
        packages.add(package)
        section = ""
        for line in text.split("\n"):
            header = MANIFEST_SECTION.match(line)
            if header:
                section = header.group(1)
                continue
            entry = MANIFEST_PATH.match(line)
            if not entry:
                continue
            key, value = entry.groups()
            if (key == "path" and section in ("lib", "bin", "example")) or (key == "build" and section == "package"):
                roots.add(posixpath.normpath(posixpath.join(package, value)))
    if not manifests:
        for path in paths:
            parts = path.split("/")
            for index, part in enumerate(parts[:-1]):
                if part == "src":
                    packages.add("/".join(parts[:index]))
    for path in paths:
        parts = path.split("/")
        tails = [
            (2, ["src", "lib.rs"]),
            (2, ["src", "main.rs"]),
            (1, ["build.rs"]),
        ]
        for length, tail in tails:
            if parts[-length:] == tail and "/".join(parts[:-length]) in packages:
                roots.add(path)
        # src/bin/x.rs, src/bin/x/main.rs, examples/x.rs, examples/x/main.rs
        for directory in (["src", "bin"], ["examples"]):
            width = len(directory)
            for nested in (False, True):
                head = len(parts) - width - (2 if nested else 1)
                if head < 0 or parts[head : head + width] != directory:
                    continue
                if nested and parts[-1] != "main.rs" or not parts[-1].endswith(".rs"):
                    continue
                if "/".join(parts[:head]) in packages:
                    roots.add(path)
    return roots & present


def cfg_test_module_files(
    sources: Dict[str, str], roots: Optional[Set[str]] = None, work: Optional[ScanWork] = None
) -> Set[str]:
    """The files that are test contexts in full: every module declaration
    that loads one is compiled only under test — a `#[cfg(test)]` on it or on
    an inline module around it, or a declaration inside a file that is itself
    a test context (a `tests/` / `benches/` file, or one found here).  A file
    that some live declaration also loads (a `#[path]`-shared helper) is live
    code, and so is a Cargo target root (`roots`; by default
    [`cargo_target_roots`] with no manifests), which Cargo loads live
    whatever a test-only `#[path]` also does.  Resolution follows rustc,
    `#[path]` included ([`ModuleResolver`]).  Linear in the sources: one pass
    per file for its declarations, a memoized directory walk to resolve them,
    and a worklist, not a fixpoint sweep."""
    if roots is None:
        roots = cargo_target_roots(list(sources), {})
    decls = {path: module_decls(source, work) for path, source in sources.items() if "mod" in source}
    resolver = ModuleResolver(list(sources), work)
    # Files some `#[path]` loads own their directory (rustc treats them as
    # `mod.rs` files).  A top-level `#[path]` resolves the same either way.
    # A file a plain `mod name;` loads as `name.rs` does not (its submodules
    # live in `name/`).  Otherwise both readings are kept.
    path_loaded: Set[str] = set()
    default_loaded: Set[str] = set()
    for path, items in decls.items():
        owned = True if path.rpartition("/")[2] in DIRECTORY_OWNERS else None
        for decl in items:
            for target in resolver.resolve(path, owned, decl):
                if decl.path is not None:
                    path_loaded.add(target)
                elif not target.endswith("/mod.rs"):
                    default_loaded.add(target)

    def owns_directory(path: str) -> Optional[bool]:
        if path.rpartition("/")[2] in DIRECTORY_OWNERS or path in path_loaded:
            return True
        if path in default_loaded:
            return False
        return None

    def in_test_tree(path: str) -> bool:
        return "/tests/" in "/" + path or "/benches/" in "/" + path

    # For each loaded file: how many loads are not (yet) known to be test-only,
    # and, per declaring file, the loads that stop blocking once it is a test.
    # A target root starts with one load nothing unblocks: Cargo's own.
    blocking: Dict[str, int] = {root: 1 for root in roots}
    unblocks: Dict[str, List[str]] = {}
    for path, items in decls.items():
        owned = owns_directory(path)
        for decl in items:
            for target in resolver.resolve(path, owned, decl):
                if target == path:
                    continue
                blocking.setdefault(target, 0)
                if not (decl.test or in_test_tree(path)):
                    blocking[target] += 1
                    unblocks.setdefault(path, []).append(target)
    found = {target for target, count in blocking.items() if count == 0}
    work = list(found)
    while work:
        for target in unblocks.get(work.pop(), []):
            blocking[target] -= 1
            if blocking[target] == 0:
                found.add(target)
                work.append(target)
    return found


LEAN_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque)\s+([A-Za-z_][\w.'!?]*)"
)
LEAN_CTOR = re.compile(r"^\s*\|\s*([A-Za-z_][\w']*)")


# How the `lean-proofs` gate treats a `.lean` file: compiled and censused as a
# proof ("built"), compiled as a native_decide evaluation ("native"), or never
# compiled by a standing gate ("unbuilt").
LEAN_THEOREM_KIND = {"built": "lean-theorem", "native": "lean-native-decide", "unbuilt": "lean-theorem-unbuilt"}


def lean_build_scope(root: Path, index: Index) -> Dict[str, str]:
    """Repo-relative path -> "built" | "native" for every `.lean` file the
    `lean-proofs` gate compiles (the `TrustIr` import closure).  Every other
    `.lean` file is "unbuilt".  The fixture list is READ from the census, so it
    is stated once; a census whose list cannot be read is a finding, and then
    no file of the closure counts as a fixture."""
    package = root / LEAN_PACKAGE
    closure = import_closure(package)
    census = os.fspath(LEAN_PACKAGE / LEAN_CENSUS_FILE)
    try:
        native = native_decide_modules(package)
    except ValueError as err:
        index.lean_findings.append(Finding(census, 1, "E3", f"cannot read the native_decide fixture modules: {err}"))
        native = []
    if closure and native is None:
        index.lean_findings.append(Finding(census, 1, "E3", "the Lean package has no census file; the `lean-proofs` gate cannot run"))
    if native is not None:
        # The census is a check the gate EXECUTES, and it fails by name: a test.
        index.test_files.add(census)
    for module in native or []:
        if module not in closure:
            index.lean_findings.append(Finding(census, 1, "E3", f"`nativeDecideModules` names `{module}`, which the TrustIr import closure does not build"))
    return {
        os.fspath(path.relative_to(root)): "native" if module in (native or []) else "built"
        for module, path in closure.items()
    }


def index_lean(index: Index, path: str, source: str, scope: str = "unbuilt") -> None:
    source = re.sub(r"/-.*?-/", lambda m: re.sub(r"[^\n]", " ", m.group(0)), source, flags=re.S)
    context = [p[:-5] if p.endswith(".lean") else p for p in path.split("/")]
    namespaces: List[str] = []
    inductive: Optional[str] = None
    guarded = False
    for number, raw in enumerate(source.split("\n"), 1):
        line = raw.split("--", 1)[0]
        if "#guard_msgs" in line or re.match(r"\s*#guard\b", line):
            guarded = True
        opened = re.match(r"\s*(namespace|section)\b\s*([\w.]*)", line)
        if opened:
            namespaces.append(opened.group(2) if opened.group(1) == "namespace" else "")
            continue
        if re.match(r"\s*end\b\s*[\w.]*\s*$", line) and namespaces:
            namespaces.pop()
            continue
        decl = LEAN_DECL.match(line)
        if decl:
            keyword, full = decl.groups()
            theorem = LEAN_THEOREM_KIND[scope]
            kind = {"theorem": theorem, "lemma": theorem, "axiom": "lean-axiom"}.get(keyword, "lean-def")
            parts = [p for ns in namespaces for p in ns.split(".") if p] + full.split(".")
            index.add(parts[-1], kind, path, number, context + parts[:-1])
            inductive = parts[-1] if keyword in {"inductive", "structure"} else None
            inductive_context = context + parts[:-1]
            continue
        ctor = LEAN_CTOR.match(line)
        if ctor and inductive:
            index.add(ctor.group(1), "lean-ctor", path, number, inductive_context + [inductive])
    # A `#guard_msgs` file is a test context only where a gate compiles it.
    if guarded and scope != "unbuilt":
        index.test_files.add(path)


def index_laws(index: Index, root: Path) -> None:
    """Gate 13's laws: every `pub fn` of its laws file (indexed as Rust, since
    the file is a workspace member's source) becomes a `law`, and what gate 13
    HOLDS of the file is read from gate 13's own code, once.  A tree whose
    workspace does not compile the file has no laws."""
    if LAWS_FILE not in index.files or not any(d.path == LAWS_FILE for defs in index.defs.values() for d in defs):
        return
    index.gate13 = gate13.holding(root)
    for name in index.gate13.laws:
        for definition in index.defs.get(name, []):
            if definition.path == LAWS_FILE and definition.kind == "fn":
                definition.kind = "law"
                index.law_defs = None


def law_names(index: Index, token: str) -> List[str]:
    """The laws a citation names: one for a law's name (qualifiers held to
    where it lives), every matching law for a glob, else none."""
    token = token.strip()
    glob = LAW_GLOB.match(token)
    if glob:
        qualifiers = [q for q in glob.group(1).split("::") if q]
        if index.law_defs is None:
            index.law_defs = [
                (name, [d for d in defs if d.kind == "law"])
                for name, defs in index.defs.items()
                if any(d.kind == "law" for d in defs)
            ]
        return sorted(
            {
                name
                for name, laws in index.law_defs
                if fnmatch.fnmatchcase(name, glob.group(2))
                and any(all(q in d.context for q in qualifiers) for d in laws)
            }
        )
    match = IDENT_PATH.match(token)
    if not match:
        return []
    segments = [s for s in re.split(r"::|\.", match.group(0)) if s not in {"crate", "self", "super"}]
    if not segments:
        return []
    name, qualifiers = segments[-1], segments[:-1]
    if any(d.kind == "law" and all(q in d.context for q in qualifiers) for d in index.defs.get(name, [])):
        return [name]
    return []


def workspace_members(root: Path) -> Optional[List[str]]:
    """Directories whose Rust a gate can actually compile: the root manifest's
    `members`.  `None` when there is no root manifest (a unit-test tree)."""
    manifest = root / "Cargo.toml"
    if not manifest.is_file():
        return None
    block = re.search(r"(?m)^members\s*=\s*\[(.*?)\]", manifest.read_text(encoding="utf-8"), re.S)
    return re.findall(r'"([^"]+)"', block.group(1)) if block else []


def excluded_packages(root: Path) -> List[str]:
    """The root manifest's workspace `exclude` list: packages no `--workspace`
    gate compiles (`frontend`)."""
    manifest = root / "Cargo.toml"
    if not manifest.is_file():
        return []
    block = re.search(r"(?m)^exclude\s*=\s*\[(.*?)\]", manifest.read_text(encoding="utf-8"), re.S)
    return re.findall(r'"([^"]+)"', block.group(1)) if block else []


def gated_excluded_test_files(root: Path, names: Set[str]) -> Set[str]:
    """The test-target sources of workspace-EXCLUDED packages that a standing
    gate RUNS: every target a `scripts/gates/<gate>.<package>.tests` registry
    lists for a package the root manifest excludes, provided
    `scripts/ci_gates.sh` runs that registry
    (`gate <gate> run_excluded_registry <gate> <package>`).  Only those
    targets: a test of an excluded package that no gate runs is no more
    evidence than an archived one under `reports/`."""
    gates_path = root / "scripts" / "ci_gates.sh"
    gates = gates_path.read_text(encoding="utf-8", errors="replace") if gates_path.is_file() else ""
    found: Set[str] = set()
    for package in excluded_packages(root):
        package = package.rstrip("/")
        for registry in sorted((root / "scripts" / "gates").glob(f"*.{package}.tests")):
            gate = registry.name[: -len(f".{package}.tests")]
            if not re.search(rf"(?m)^gate {re.escape(gate)} run_excluded_registry {re.escape(gate)} {re.escape(package)}\s*$", gates):
                continue
            for line in registry.read_text(encoding="utf-8", errors="replace").split("\n"):
                target = line.split("#", 1)[0].strip()
                if not target:
                    continue
                for source in (f"{package}/tests/{target}.rs", f"{package}/tests/{target}/main.rs"):
                    if source in names:
                        found.add(source)
    return found


def build_index(root: Path) -> Index:
    index = Index()
    names = visible_files(root)
    index.files = set(names)
    # `reports/` carries archived `.rs` files no package owns.  A `#[test]` that
    # no gate can run is not evidence, so only workspace members are code —
    # plus the test targets of a workspace-EXCLUDED package that a standing
    # gate runs by its manifest path (`gated_excluded_test_files`).
    members = workspace_members(root)
    index.members = members
    gated = gated_excluded_test_files(root, index.files) if members is not None else set()
    rust = {
        n: (root / n).read_text(encoding="utf-8", errors="replace")
        for n in names
        if n.endswith(".rs")
        and (members is None or n in gated or any(n.startswith(m.rstrip("/") + "/") for m in members))
    }
    manifests = {
        n: (root / n).read_text(encoding="utf-8", errors="replace")
        for n in names
        if n.rpartition("/")[2] == "Cargo.toml" and (members is None or any(n.startswith(m.rstrip("/") + "/") for m in members))
    }
    cfg_test_files = cfg_test_module_files(rust, cargo_target_roots(list(rust), manifests))
    for name, source in rust.items():
        index_rust(index, name, source, cfg_test_files)
    apply_level_aliases(index)
    index_laws(index, root)
    lean_scope = lean_build_scope(root, index)
    for name in names:
        path = root / name
        if name.endswith(".lean"):
            index_lean(index, name, path.read_text(encoding="utf-8", errors="replace"), lean_scope.get(name, "unbuilt"))
        elif name.endswith("Cargo.toml"):
            _index_manifest(index, name, path.read_text(encoding="utf-8", errors="replace"))
        elif name.startswith("scripts/tests/") and name.endswith(".py"):
            text = path.read_text(encoding="utf-8", errors="replace")
            for number, line in enumerate(text.split("\n"), 1):
                match = re.match(r"\s*def (test_\w+)", line)
                if match:
                    index.add(match.group(1), "py-test", name, number, ["scripts", "tests"])
            index.test_files.add(name)
        elif name == "scripts/ci_gates.sh":
            text = path.read_text(encoding="utf-8", errors="replace")
            for number, line in enumerate(text.split("\n"), 1):
                match = re.match(r"\s*gate\s+([a-z0-9][a-z0-9-]*)\b", line)
                if match:
                    index.add(match.group(1), "gate", name, number, ["ci_gates"])
        elif name == REFUSE_MANIFEST:
            index_refuse_manifest(index, name, path.read_text(encoding="utf-8", errors="replace"))
        elif name == REFUSE_TEMPLATE_MANIFEST:
            index_refuse_template_manifest(index, name, path.read_text(encoding="utf-8", errors="replace"))
        elif "/tests/fixtures/" in name:
            stem = name.rsplit("/", 1)[-1].split(".", 1)[0]
            index.add(stem, "fixture", name, 1, ["fixtures"])
    return index


REFUSE_COLUMNS = ["row", "carrier", "verdicts", "text_losses", "obligation", "why"]


def index_refuse_manifest(index: Index, name: str, text: str) -> None:
    """One `refuse-row` definition per manifest row (the Rust runner owns the
    full grammar; this reads only what rules E2/E3/R need, and refuses a
    manifest it cannot read rather than indexing nothing)."""
    header_seen = False
    for number, raw in enumerate(text.split("\n"), 1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        cells = [c.strip() for c in raw.split("\t")]
        if not header_seen:
            if cells != REFUSE_COLUMNS:
                index.refuse_manifest_findings.append(Finding(name, number, "R", f"the first non-comment line must be the header `{chr(9).join(REFUSE_COLUMNS)}`"))
                return
            header_seen = True
            continue
        if len(cells) != len(REFUSE_COLUMNS):
            index.refuse_manifest_findings.append(Finding(name, number, "R", f"expected {len(REFUSE_COLUMNS)} tab-separated cells, got {len(cells)}"))
            continue
        row, carrier, obligation = cells[0], cells[1], cells[4]
        if not re.match(r"[a-z0-9_]+\Z", row) or carrier not in {"module", "bytes", "control", "none"}:
            index.refuse_manifest_findings.append(Finding(name, number, "R", f"row `{row}` / carrier `{carrier}` is malformed"))
            continue
        if row in index.refuse_rows:
            index.refuse_manifest_findings.append(Finding(name, number, "R", f"row `{row}` is listed twice"))
            continue
        index.refuse_rows[row] = (number, carrier, obligation)
        index.add(f"refuse/{row}", "refuse-row", name, number, ["refuse"])
        for pair in cells[2].split(";"):
            verdict = pair.split("=", 1)[1] if "=" in pair else ""
            if verdict.startswith("Validation:"):
                index.refuse_named.add(verdict[len("Validation:"):])


REFUSE_TEMPLATE_COLUMNS = ["row", "carrier", "verdicts", "obligation", "why"]
# carrier -> the artifact files a row of it ships (`refuse_corpus` rule R).
REFUSE_TEMPLATE_ARTIFACTS = {
    "template_bytes": (".tmbs",),
    "template": (".json",),
    "instance": (".json", ".host.json"),
    "control": (".json", ".host.json"),
}


def index_refuse_template_manifest(index: Index, name: str, text: str) -> None:
    """The template corpus's rows, read as `index_refuse_manifest` reads the
    module corpus's (its own columns and carriers; `template_refuse_corpus.rs`
    owns the full grammar)."""
    header_seen = False
    for number, raw in enumerate(text.split("\n"), 1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        cells = [c.strip() for c in raw.split("\t")]
        if not header_seen:
            if cells != REFUSE_TEMPLATE_COLUMNS:
                index.refuse_manifest_findings.append(Finding(name, number, "R", f"the first non-comment line must be the header `{chr(9).join(REFUSE_TEMPLATE_COLUMNS)}`"))
                return
            header_seen = True
            continue
        if len(cells) != len(REFUSE_TEMPLATE_COLUMNS):
            index.refuse_manifest_findings.append(Finding(name, number, "R", f"expected {len(REFUSE_TEMPLATE_COLUMNS)} tab-separated cells, got {len(cells)}"))
            continue
        row, carrier, obligation = cells[0], cells[1], cells[3]
        if not re.match(r"[a-z0-9_]+\Z", row) or carrier not in REFUSE_TEMPLATE_ARTIFACTS:
            index.refuse_manifest_findings.append(Finding(name, number, "R", f"row `{row}` / carrier `{carrier}` is malformed"))
            continue
        if row in index.refuse_template_rows:
            index.refuse_manifest_findings.append(Finding(name, number, "R", f"row `{row}` is listed twice"))
            continue
        index.refuse_template_rows[row] = (number, carrier, obligation)
        index.add(f"refuse_templates/{row}", "refuse-row", name, number, ["refuse_templates"])


def manifest_features(text: str) -> Dict[str, Tuple[int, List[str]]]:
    """`[features]` as name -> (line, the SAME-CRATE features it enables).
    Arrays may span lines; `dep:x` and `other-crate/feature` entries enable
    nothing in this crate's own feature graph."""
    features: Dict[str, Tuple[int, List[str]]] = {}
    table, pending = "", None
    for number, raw in enumerate(text.split("\n"), 1):
        line = raw.split("#", 1)[0]
        header = re.match(r"\s*\[([^\]]+)\]", line)
        if header and pending is None:
            table = header.group(1).strip()
            continue
        if table != "features":
            continue
        if pending is None:
            key = re.match(r'\s*"?([A-Za-z0-9_\-]+)"?\s*=(.*)', line)
            if not key:
                continue
            pending, line = key.group(1), key.group(2)
            features[pending] = (number, [])
        features[pending][1].extend(v for v in re.findall(r'"([^"]+)"', line) if "/" not in v and not v.startswith("dep:"))
        if "]" in line:
            pending = None
    return features


def _index_manifest(index: Index, name: str, text: str) -> None:
    features = manifest_features(text)
    on, frontier = set(), ["default"]
    while frontier:
        feature = frontier.pop()
        if feature in features and feature not in on:
            on.add(feature)
            frontier.extend(features[feature][1])
    for feature, (number, _) in features.items():
        index.add(feature, "feature", name, number, ["features"])
        if feature not in on:
            index.add(feature, "default-off-feature", name, number, ["features"])
    table = ""
    for number, line in enumerate(text.split("\n"), 1):
        header = re.match(r"\s*\[([^\]]+)\]", line)
        if header:
            table = header.group(1).strip()
            continue
        key = re.match(r'\s*"?([A-Za-z0-9_\-]+)"?\s*=', line)
        if not key:
            continue
        if table == "package" and key.group(1) == "name":
            value = re.search(r'=\s*"([^"]+)"', line)
            if value:
                index.add(value.group(1), "crate", name, number, [])
                index.add(value.group(1).replace("-", "_"), "crate", name, number, [])


# --------------------------------------------------------------------------
# Citations: what a backticked token claims exists, and whether it does.
# --------------------------------------------------------------------------

TOKEN = re.compile(r"`([^`\n]+)`")
PATH_EXTENSIONS = ("rs", "lean", "toml", "md", "py", "sh", "json", "txt", "lock", "tmbc", "tmir", "msgpack", "tsv")
IDENT_PATH = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:(?:::|\.)[A-Za-z_][A-Za-z0-9_']*)*")
KEBAB = re.compile(r"[a-z0-9]+(?:[-_][a-z0-9]+)*\Z")
TOP_LEVEL = ("crates", "lean", "scripts", "docs", "frontend", "publish", "benchmarks", "designs", "reports")


def is_external_path(token: str) -> bool:
    return token.startswith(("~/", "../", "/"))


def looks_like_path(token: str) -> bool:
    if " " in token or "::" in token or any(ch in token for ch in "<>{}…"):
        return False  # a template (`<gate>.<crate>.tests`) names no one file
    if "/" in token:
        return True
    return "." in token and token.rsplit(".", 1)[1] in PATH_EXTENSIONS


def resolve_path(index: Index, root: Path, token: str) -> Tuple[Optional[Set[str]], str]:
    """(kinds, detail).  kinds is None when the path does not resolve."""
    clean = token.rstrip("/")
    if any(ch in clean for ch in "*?["):
        hits = fnmatch.filter(index.files, clean)
        return ({"file"}, f"{len(hits)} files") if hits else (None, "the pattern matches no file")
    if clean in index.files:
        return {"test-file" if clean in index.test_files else "file"}, clean
    if (root / clean).is_dir() and any(f.startswith(clean + "/") for f in index.files):
        return {"dir"}, clean
    if clean.split("/", 1)[0] in TOP_LEVEL:
        return None, "no such repo-rooted path"
    suffix = [f for f in index.files if f == clean or f.endswith("/" + clean)]
    if len(suffix) == 1:
        return {"test-file" if suffix[0] in index.test_files else "file"}, suffix[0]
    if len(suffix) > 1:
        return None, "ambiguous, matches " + ", ".join(sorted(suffix)[:4]) + "; write the repo-rooted path"
    return None, "no file with this name or path suffix"


def resolve_identifier(index: Index, token: str) -> Tuple[Optional[Set[str]], str]:
    match = IDENT_PATH.match(token)
    if not match:
        return None, "not an identifier"
    segments = re.split(r"::|\.", match.group(0))
    segments = [s for s in segments if s not in {"crate", "self", "super"}]
    if not segments:
        return None, "not an identifier"
    name, qualifiers = segments[-1], segments[:-1]
    candidates = index.defs.get(name, [])
    if not candidates:
        return None, f"no item named `{name}` in the tree"
    qualified = [d for d in candidates if all(q in d.context for q in qualifiers)]
    if not qualified:
        where = sorted({f"{d.path}:{d.line}" for d in candidates})[:3]
        return None, f"`{name}` exists ({', '.join(where)}) but not under `{'::'.join(qualifiers)}`"
    return {d.kind for d in qualified}, f"{qualified[0].path}:{qualified[0].line}"


def resolve(index: Index, root: Path, token: str) -> Tuple[str, Optional[Set[str]], str]:
    """(shape, kinds, detail).  shape in external|path|ident|opaque."""
    token = token.strip()
    if is_external_path(token):
        return "external", set(), "outside this tree; not resolved"
    if REFUSE_TOKEN.match(token):
        found = index.defs.get(token, [])
        if found:
            return "ident", {d.kind for d in found}, f"{found[0].path}:{found[0].line}"
        manifest = REFUSE_TEMPLATE_MANIFEST if token.startswith("refuse_templates/") else REFUSE_MANIFEST
        return "ident", None, f"no must-refuse corpus row named `{token}` in {manifest}"
    if looks_like_path(token):
        kinds, detail = resolve_path(index, root, token)
        return "path", kinds, detail
    if LAW_GLOB.match(token):
        laws = law_names(index, token)
        if laws:
            return "ident", {"law"}, f"{len(laws)} law(s) of {LAWS_FILE}"
        return "ident", None, f"the glob matches no law of {LAWS_FILE} (a glob cites gate 13's laws only)"
    if KEBAB.match(token) and "-" in token:
        found = index.defs.get(token, [])
        if found:
            return "ident", {d.kind for d in found}, f"{found[0].path}:{found[0].line}"
        return "ident", None, f"no gate, feature, crate or fixture named `{token}`"
    if IDENT_PATH.match(token):
        kinds, detail = resolve_identifier(index, token)
        return "ident", kinds, detail
    return "opaque", set(), "not a citation shape; not resolved"


# --------------------------------------------------------------------------
# Documents: units, entries.
# --------------------------------------------------------------------------

ENTRY_LINE = re.compile(r"^\s*\*Enforcement(?:\s*\(([^)]*)\))?\s*:\*\s*(.*)$")
LEGACY_INLINE = re.compile(r"\*Enforcement[^*\n]*:\*")
CELL_CLASS = re.compile(r"^\(([^)]*)\)\s*(.*)$", re.S)
HEADING = re.compile(r"^(#{1,6})\s+(.*?)\s*$")
ITEM = re.compile(r"^ {0,3}(\d+)\.\s+\*\*")
EXTERNAL_MARKER = re.compile(r"<!--\s*enforcement-links:\s*external\s+(\S+)[^>]*-->")
NOT_NORMATIVE = re.compile(r"<!--\s*enforcement-links:\s*not-normative\b\s*(.*?)\s*-->")


class Entry:
    def __init__(self, line: int, cls: Optional[str], text: str, form: str) -> None:
        self.line, self.cls, self.text, self.form = line, cls, text, form
        self.kinds: Set[str] = set()  # what its citations resolved to


class Unit:
    def __init__(self, ident: str, title: str, line: int) -> None:
        self.ident, self.title, self.line = ident, title, line
        self.entries: List[Entry] = []
        self.not_normative: Optional[str] = None

    def backed_in_tree(self) -> bool:
        return any(e.cls in IN_TREE for e in self.entries)


def split_row(line: str) -> List[str]:
    """Split a Markdown table row on `|`, ignoring pipes inside backticks."""
    cells, current, ticked = [], [], False
    for ch in line.strip():
        if ch == "`":
            ticked = not ticked
        if ch == "|" and not ticked:
            cells.append("".join(current).strip())
            current = []
        else:
            current.append(ch)
    cells.append("".join(current).strip())
    return cells[1:-1] if len(cells) >= 2 else cells


def parse_document(doc: Doc, text: str) -> Tuple[List[Unit], List[Finding], Tuple[int, int]]:
    """Units with their entries, grammar findings, and the governed line span."""
    lines = text.split("\n")
    findings: List[Finding] = []
    units: List[Unit] = []
    start, end = 0, len(lines)
    if doc.region:
        try:
            start = next(i for i, line in enumerate(lines) if line.strip() == doc.region)
        except StopIteration:
            findings.append(Finding(doc.path, 1, "E1", f"governed region `{doc.region}` is missing"))
            return units, findings, (0, 0)
        level = len(doc.region) - len(doc.region.lstrip("#"))
        for i in range(start + 1, len(lines)):
            heading = HEADING.match(lines[i])
            if heading and len(heading.group(1)) <= level:
                end = i
                break
    if doc.units == "paths":
        return units, findings, (start, end)

    current: Optional[Unit] = None
    by_item: Dict[str, Unit] = {}
    pending_rows: List[Tuple[str, Entry]] = []
    fenced = False
    i = start
    while i < end:
        line = lines[i]
        if line.lstrip().startswith("```"):
            fenced = not fenced
            i += 1
            continue
        if fenced:
            i += 1
            continue
        heading = HEADING.match(line)
        if doc.units == "sections" and heading and len(heading.group(1)) in (2, 3):
            title = heading.group(2)
            number = re.match(r"([0-9]+(?:\.[0-9]+)*)", title)
            current = Unit("§" + number.group(1) if number else title, title, i + 1)
            units.append(current)
        elif doc.units == "items" and ITEM.match(line):
            number = ITEM.match(line).group(1)  # type: ignore[union-attr]
            title = re.sub(r"\*\*", "", line.split(".", 1)[1]).strip()
            if number in by_item:
                findings.append(Finding(doc.path, i + 1, "E1", f"item {number} is numbered twice in the governed region"))
            current = Unit(f"item {number}", title[:70], i + 1)
            by_item[number] = current
            units.append(current)

        opted_out = NOT_NORMATIVE.search(line)
        if opted_out and current is not None:
            if not opted_out.group(1):
                findings.append(Finding(doc.path, i + 1, "E1", "a `not-normative` marker must say WHY"))
            else:
                current.not_normative = opted_out.group(1)
        entry = ENTRY_LINE.match(line)
        if entry:
            body = [entry.group(2)]
            j = i + 1
            while j < end and lines[j].strip() and not lines[j].lstrip().startswith(("|", "#")):
                body.append(lines[j].strip())
                j += 1
            made = Entry(i + 1, entry.group(1), " ".join(body), "line")
            if current is None:
                findings.append(Finding(doc.path, i + 1, "E1", "Enforcement entry outside any normative unit"))
            else:
                current.entries.append(made)
            i = j
            continue
        if LEGACY_INLINE.search(line) and not line.lstrip().startswith("|"):
            findings.append(
                Finding(doc.path, i + 1, "E1", "`*Enforcement` must START its paragraph: `*Enforcement (class):* ...`")
            )

        if line.lstrip().startswith("|") and i + 1 < end and re.match(r"^\s*\|[\s:|-]+\|\s*$", lines[i + 1]):
            header = split_row(line)
            if "Enforcement" in header:
                column = header.index("Enforcement")
                item_column = header.index("Item") if "Item" in header else None
                j = i + 2
                while j < end and lines[j].lstrip().startswith("|"):
                    cells = split_row(lines[j])
                    cell = cells[column] if column < len(cells) else ""
                    classed = CELL_CLASS.match(cell)
                    made = Entry(j + 1, classed.group(1) if classed else None, classed.group(2) if classed else cell, "table")
                    if item_column is not None:
                        key = re.sub(r"[^0-9]", "", cells[item_column]) if item_column < len(cells) else ""
                        pending_rows.append((key, made))
                    elif current is None:
                        findings.append(Finding(doc.path, j + 1, "E1", "Enforcement table outside any normative unit"))
                    else:
                        current.entries.append(made)
                    j += 1
                i = j
                continue
        i += 1

    for key, made in pending_rows:
        if key in by_item:
            by_item[key].entries.append(made)
        else:
            findings.append(Finding(doc.path, made.line, "E1", f"evidence row names item `{key}`, which is not a numbered item of the governed region"))
    return units, findings, (start, end)


# --------------------------------------------------------------------------
# The rules.
# --------------------------------------------------------------------------


class Report:
    def __init__(self) -> None:
        self.findings: List[Finding] = []
        self.units: List[Tuple[str, Unit]] = []
        self.unbacked: List[str] = []
        self.unnamed_variants: List[str] = []
        self.dead_variants: List[str] = []
        self.variant_total = 0
        self.skipped: List[str] = []
        self.opted_out: List[str] = []
        self.opted_out_units: List[Tuple[str, str]] = []  # (doc + unit key, why)
        self.corrections: List[str] = []
        self.citations = {"resolved": 0, "unresolved": 0, "external": 0, "opaque": 0}
        self.prose: Dict[str, Dict[str, int]] = {}
        self.notes: List[str] = []
        self.refuse_rows = 0
        # Rule E5: law and theorem citations whose stated verdict is the
        # statement's own, theorem citations held to names only (their
        # conclusion is outside the reader), and identifier checks.
        self.says = {"laws": 0, "theorems": 0, "names_only": 0, "identifiers": 0}


def check_entry(index: Index, root: Path, doc: Doc, unit: Unit, entry: Entry, report: Report, strict: bool) -> None:
    if entry.cls is None:
        if strict:
            report.findings.append(
                Finding(doc.path, entry.line, "E1", f"{unit.ident}: Enforcement entry has no evidence class; write `*Enforcement (class):*` with one of: " + ", ".join(CLASSES))
            )
            return
    elif entry.cls not in CLASSES:
        report.findings.append(Finding(doc.path, entry.line, "E1", f"{unit.ident}: unknown evidence class `{entry.cls}`; the closed set is: " + ", ".join(CLASSES)))
        return
    if entry.cls == "external":
        report.citations["external"] += len(TOKEN.findall(entry.text))
        if not TOKEN.search(entry.text):
            report.findings.append(Finding(doc.path, entry.line, "E3", f"{unit.ident}: an `external` entry must NAME the artifact it relies on, in backticks"))
        return
    witnessed: Set[str] = set()
    entry.kinds = witnessed
    resolved: List[str] = []
    for token in TOKEN.findall(entry.text):
        shape, kinds, detail = resolve(index, root, token)
        if shape in {"external", "opaque"}:
            report.citations[shape] += 1
            continue
        if kinds is None:
            report.citations["unresolved"] += 1
            report.findings.append(
                Finding(doc.path, entry.line, "E2", f"{unit.ident}: cited `{token}` does not resolve: {detail}. Every backticked token in an Enforcement entry is a citation; cite a real item, or take the backticks off prose.")
            )
            continue
        report.citations["resolved"] += 1
        witnessed |= kinds
        if shape == "ident":
            resolved.append(token)
    needed = WITNESS.get(entry.cls or "")
    if needed is not None and not (witnessed & needed):
        report.findings.append(
            Finding(doc.path, entry.line, "E3", f"{unit.ident}: class `{entry.cls}` is not witnessed: no citation resolves to one of {sorted(needed)} (resolved kinds: {sorted(witnessed) or 'none'}). Cite the artifact, or downgrade the class; a class is never upgraded by rewording.")
        )
    if entry.cls == "proved-contract":
        check_proved_contract(index, doc, unit, entry, resolved, report)
    if entry.cls in SAYS_CLASSES:
        check_says(index, root, doc, unit, entry, report)


# The source a law can call (gate 13's `CRATE_DIRS`): a table's own definition
# lives there, and nowhere else counts as the table.
LAW_CALLABLE_SRC = tuple(f"{d.as_posix()}/src/" for d in gate13.CRATE_DIRS.values())


def table_definitions(index: Index, held: "gate13.Holding") -> Dict[str, List[Definition]]:
    """Each table a held law calls -> its own definition(s): a `fn` named the
    table path's last segment, under every qualifier of that path, in the
    source a law can call (`LAW_CALLABLE_SRC`)."""
    out: Dict[str, List[Definition]] = {}
    for table in sorted({t for t in held.tables.values() if t}):
        segments = table.split("::")
        out[table] = [
            d
            for d in index.defs.get(segments[-1], [])
            if d.kind == "fn" and all(q in d.context for q in segments[:-1]) and d.path.startswith(LAW_CALLABLE_SRC)
        ]
    return out


def cited_table(index: Index, token: str, definitions: Dict[str, List[Definition]]) -> Optional[str]:
    """The table `token` cites: the one whose WIRING path the spelling ends
    with (`Type::method`, or the free `fn`'s name) and whose own definition(s)
    are ALL it resolves to (qualifiers held), else None.  A spelling that
    also resolves to another item — `validate::proof_ref_kind_is_ambiguous`,
    the validator's private `&ObligationKind` wrapper, or the bare name that
    names both — is no citation of the table, and neither is a bare method
    name (`is_reference_counted`), which does not say whose table it is."""
    match = IDENT_PATH.match(token.strip())
    if not match:
        return None
    segments = [s for s in re.split(r"::|\.", match.group(0)) if s not in {"crate", "self", "super"}]
    if not segments:
        return None
    qualified = {d for d in index.defs.get(segments[-1], []) if all(q in d.context for q in segments[:-1])}
    for table, own in definitions.items():
        path = table.split("::")
        if segments[-len(path) :] == path and qualified and own and qualified <= set(own):
            return table
    return None


def check_proved_contract(index: Index, doc: Doc, unit: Unit, entry: Entry, resolved: Sequence[str], report: Report) -> None:
    """The rest of rule E3 for `(proved-contract)`: EVERY law the entry cites
    is one gate 13 holds (`gate13.holding`, its pre-run rules, read from its
    code), and each law FOLLOWS A CITATION OF ITS OWN TABLE: the table the
    entry cites most recently before the law must be the one the law's WIRING
    family calls, where a table citation is a spelling that resolves to that
    table's own definition and to nothing else (`cited_table`).  A syntactic
    proxy, and said so: it pins which table each law is cited under (rule
    E5 checks each law's verdict, not the rest of the words).
    `resolved` is the entry's resolved identifier citations, in text order.
    A missing law is rule E2's, and no law at all is the witness check's;
    this adds what a citation of a law must also be."""
    cited = [(token, law_names(index, token)) for token in resolved]
    if not any(laws for _, laws in cited):
        return

    def refuse(message: str) -> None:
        report.findings.append(Finding(doc.path, entry.line, "E3", f"{unit.ident}: {message}"))

    held = index.gate13
    if held is None or not held.held:
        why = "; ".join(held.errors) if held is not None else f"this tree carries no {LAWS_FILE}"
        refuse(f"class `proved-contract`: gate 13 holds no law of this tree, so none witnesses. Its pre-run checks (`verified_contracts.holding`) refuse: {why}")
        return
    definitions = table_definitions(index, held)
    current: Optional[str] = None
    for token, laws in cited:
        if not laws:
            current = cited_table(index, token, definitions) or current
            continue
        # One finding per citation and reason: a glob names many laws.
        tableless = [law for law in laws if held.tables.get(law) is None]
        if tableless:
            refuse(f"{brief(tableless)} (cited as `{token}`) is held by gate 13, but its WIRING family calls no table, so it witnesses no claim about one. Cite a law of the table the claim is about.")
        by_table: Dict[str, List[str]] = {}
        for law in laws:
            table = held.tables.get(law)
            if table is not None and table != current:
                by_table.setdefault(table, []).append(law)
        for table, strays in sorted(by_table.items()):
            own = definitions.get(table, [])
            if not own:
                refuse(f"{brief(strays)} (cited as `{token}`) is a law of `{table}`, which has no definition in {', '.join(LAW_CALLABLE_SRC)}: no spelling of it can be cited.")
                continue
            after = f"the table citation it follows is `{current}`" if current else "no table citation precedes it"
            where = ", ".join(f"{d.path}:{d.line}" for d in own)
            refuse(f"{brief(strays)} (cited as `{token}`) is a law of `{table}`, but {after}: a law is read under the table the entry cites most recently before it. Cite `{table}` before its laws, by a spelling that resolves to its definition ({where}) alone.")


def brief(laws: Sequence[str]) -> str:
    """`a`, or `a`, `b` and N more: the laws one finding is about."""
    shown = ", ".join(f"`{law}`" for law in laws[:3])
    return shown + (f" and {len(laws) - 3} more" if len(laws) > 3 else "")


# --------------------------------------------------------------------------
# Rule E5 SAYS: an entry says what its proved statement says.
# --------------------------------------------------------------------------
#
# A `(proved-contract)` entry gives each law it cites the verdict the law's
# `ensures` states (gate 13 reads it: `Holding.verdicts`); a `(lean-theorem)`
# entry gives each theorem it cites the verdict its conclusion states, when
# the reader below classifies that conclusion, and always names identifiers
# of its statement.  The vocabulary is CLOSED: one table of phrases, one
# tuple of negators, both grown only by a reviewed change and a test.  It is
# a clause grammar over the entry's text and a reader of Lean source text:
# test evidence that the English agrees with the statement, never a proof.

SAYS_CLASSES = ("proved-contract", "lean-theorem")
# The citation kinds a `(lean-theorem)` entry binds (a native_decide fixture
# theorem has a statement too), and the kinds a named identifier resolves to.
THEOREM_KINDS = {"lean-theorem", "lean-native-decide"}
LEAN_NAME_KINDS = {"lean-def", "lean-ctor"}

# (spellings, kind, verdict).  A LEADING phrase governs every bound citation
# after it in its clause, until the next leading phrase; a CLOSING phrase
# governs the bound citations before it in its clause that nothing governs
# yet, back to the previous verdict.  `<relation>` is plain text compared
# with a law's `ensures` relation (whitespace-normalized).  Phrases are
# matched outside backticks only, case-sensitively, as whole words.
VERDICTS: Tuple[Tuple[Tuple[str, ...], str, str], ...] = (
    (("true exactly when <relation> at", "is true exactly when <relation> at", "are true exactly when <relation> at"), "leading", "relation"),
    (("true at", "is true at", "are true at", "true exactly at", "is true exactly at", "are true exactly at"), "leading", "true"),
    (("false at", "is false at", "are false at", "false exactly at", "is false exactly at", "are false exactly at"), "leading", "false"),
    (("is UB", "are UB", "is undefined behaviour", "are undefined behaviour"), "leading", "ub"),
    (("runs",), "leading", "runs"),
    (("is a no-op",), "leading", "noop"),
    (("(true)", "(each true)", ", each true)"), "closing", "true"),
    (("(false)", "(each false)", ", each false)"), "closing", "false"),
)
# One tuple of negators, read by F1 (before a leading phrase), F3 (before a
# bound citation) and the identifier rule (before a named identifier).
NEGATORS: Tuple[str, ...] = (
    "non-", "without", "other than", "not", "no", "no longer", "never", "neither", "nor", "except", "unlike", "excluding", "cannot", "n't",
)
# What a stated verdict also covers: `runs` is true of a no-op.
SUBSUMES = {"runs": {"runs", "noop"}}
# Masks a backticked citation, so no phrase is read inside one.
MASK = "\x01"
# How far before a named identifier a negator negates it.
NEGATOR_REACH = 12
# A Lean statement runs from its declaration to its top-level `:=` within
# this many lines, or the reader cannot delimit it.
LEAN_STATEMENT_LINES = 120
NUMBER_WORDS = (
    "zero one two three four five six seven eight nine ten eleven twelve thirteen fourteen fifteen sixteen "
    "seventeen eighteen nineteen twenty"
).split()
OTHER_LAWS = re.compile(r"(?:\bthe (?P<count>[A-Za-z0-9]+) other laws of|\bevery other law of)\s*\Z")
ONE_LAW_PER = re.compile(r"\bone law per (?P<noun>[A-Za-z-]+)")


def vocabulary() -> str:
    """The closed vocabulary, rendered from `VERDICTS` for every message."""
    rows = [f"{kind} {verdict}: " + ", ".join(f"`{s}`" for s in spellings) for spellings, kind, verdict in VERDICTS]
    return "; ".join(rows) + " (`runs` also covers a no-op)"


def _phrase_pattern(spelling: str, i: int) -> str:
    """One spelling as a regex: words joined by whitespace, `<relation>` a
    group (`relation<i>`), `exactly` before `at` a group (`exactly<i>`),
    whole words at each alphanumeric end."""
    words = spelling.split(" ")
    parts = []
    for n, word in enumerate(words):
        if word == "<relation>":
            parts.append(f"(?P<relation{i}>[^{MASK};]+?)")
        elif word == "exactly" and words[n + 1 : n + 2] == ["at"]:
            parts.append(f"(?P<exactly{i}>exactly)")
        else:
            parts.append(re.escape(word))
    head = r"(?<![A-Za-z0-9_'-])" if spelling[0].isalnum() else ""
    tail = r"(?![A-Za-z0-9_'-])" if spelling[-1].isalnum() else ""
    return head + r"\s+".join(parts) + tail


# One alternation, longest spellings first, so `is true at` is read whole and
# never as `true at` after an `is`.
_PHRASES = sorted(((s, kind, verdict) for spellings, kind, verdict in VERDICTS for s in spellings), key=lambda r: -len(r[0]))
PHRASE = re.compile("|".join(f"(?P<p{i}>{_phrase_pattern(s, i)})" for i, (s, _, _) in enumerate(_PHRASES)))
_NEGATOR_WORDS = "|".join(
    re.escape(n).replace(r"\ ", r"\s+") for n in sorted((n for n in NEGATORS if n[0].isalpha() and n[-1].isalpha()), key=len, reverse=True)
)
_NEGATOR_AFFIXES = "|".join(re.escape(n) for n in NEGATORS if not (n[0].isalpha() and n[-1].isalpha()))
# Text that ENDS in a negator (F1, F3), and a negator anywhere (the
# identifier rule's window).
NEGATED_END = re.compile(rf"(?:(?<![A-Za-z])(?:{_NEGATOR_WORDS})|{_NEGATOR_AFFIXES})\s*\Z", re.I)
NEGATOR_ANYWHERE = re.compile(rf"(?<![A-Za-z])(?:{_NEGATOR_WORDS})(?![A-Za-z])|{_NEGATOR_AFFIXES}", re.I)


def masked_text(text: str) -> str:
    """`text` with every backticked span (backticks included) masked."""
    return TOKEN.sub(lambda m: MASK * len(m.group(0)), text)


ABBREVIATION = re.compile(r"(?<![A-Za-z])(?:e\.g|i\.e)\Z")
# What follows a `.` that ends a clause.
SENTENCE_GAP = re.compile(r"\s+[A-Z`(]|\s*\Z")


def clauses(text: str) -> List[Tuple[int, int]]:
    """The clauses of an entry: split at `;`, and at a `.` followed by
    whitespace and then a capital, a backtick or `(` (or at the end of the
    text), never inside backticks and never after `e.g` / `i.e`."""
    spans: List[Tuple[int, int]] = []
    start, ticked = 0, False
    for i, ch in enumerate(text):
        if ch == "`":
            ticked = not ticked
            continue
        if ticked:
            continue
        if ch == ";" or (ch == "." and SENTENCE_GAP.match(text, i + 1) and not ABBREVIATION.search(text, 0, i)):
            spans.append((start, i))
            start = i + 1
    spans.append((start, len(text)))
    return [(a, b) for a, b in spans if text[a:b].strip()]


def negated_before(masked: str, at: int, strip: str = " \t(") -> bool:
    """Does the masked text before `at` end in a negator (after `strip`)?"""
    return NEGATED_END.search(masked[:at].rstrip(strip)) is not None


def number_word(word: str) -> Optional[int]:
    if word.isdigit():
        return int(word)
    return NUMBER_WORDS.index(word.lower()) if word.lower() in NUMBER_WORDS else None


def qualified_definitions(index: Index, token: str) -> List[Definition]:
    """The definitions a token names, qualifiers held (`resolve_identifier`)."""
    match = IDENT_PATH.match(token.strip())
    if not match or match.group(0) != token.strip():
        return []
    segments = [s for s in re.split(r"::|\.", match.group(0)) if s not in {"crate", "self", "super"}]
    if not segments:
        return []
    return [d for d in index.defs.get(segments[-1], []) if all(q in d.context for q in segments[:-1])]


# --- The Lean reader ------------------------------------------------------
#
# It reads SOURCE TEXT, not the elaborated type: a theorem's statement runs
# from its name to its top-level `:=`; its binders end at their top-level
# `:`; the conclusion is the rest.  `lean_conclusion_verdict` classifies a
# conclusion or answers None (the names-only tier).

LEAN_OPEN, LEAN_CLOSE = "([{⟨⦃", ")]}⟩⦄"


def lean_uncomment(text: str) -> str:
    """`text` with every comment (`--` to the line's end, nested `/- -/`)
    blanked, newlines and string literals kept, so offsets and lines hold."""
    out: List[str] = []
    i = 0
    while i < len(text):
        if text.startswith("/-", i):
            nested, j = 1, i + 2
            while j < len(text) and nested:
                if text.startswith("/-", j):
                    nested, j = nested + 1, j + 2
                elif text.startswith("-/", j):
                    nested, j = nested - 1, j + 2
                else:
                    j += 1
            out.append(re.sub(r"[^\n]", " ", text[i:j]))
            i = j
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = len(text) if j < 0 else j
            out.append(" " * (j - i))
            i = j
            continue
        if text[i] == '"':
            j = i + 1
            while j < len(text) and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i : j + 1])
            i = j + 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def lean_chars(text: str):
    """`(offset, char, depth, in_string)` for each character of uncommented
    Lean text; `depth` is the bracket depth around the character (a bracket
    itself sits at the depth outside it)."""
    depth, in_string, i = 0, False, 0
    while i < len(text):
        ch = text[i]
        if in_string:
            yield i, ch, depth, True
            if ch == "\\" and i + 1 < len(text):
                i += 1
                yield i, text[i], depth, True
            elif ch == '"':
                in_string = False
            i += 1
            continue
        if ch == '"':
            in_string = True
            yield i, ch, depth, True
            i += 1
            continue
        if ch in LEAN_CLOSE:
            depth -= 1
        yield i, ch, depth, False
        if ch in LEAN_OPEN:
            depth += 1
        i += 1


@functools.lru_cache(maxsize=8192)
def _depth_zero_offsets(text: str) -> Tuple[int, ...]:
    """Every offset of `text` at bracket depth 0 outside string literals
    (`lean_chars`), computed once per text: E5 asks `top_level` of the same
    statement chunk for several needles, entry after entry."""
    return tuple(i for i, _, depth, quoted in lean_chars(text) if not quoted and depth == 0)


def top_level(text: str, needle: str) -> List[int]:
    """Offsets of `needle` at bracket depth 0, outside string literals."""
    return [i for i in _depth_zero_offsets(text) if text.startswith(needle, i)]


def blank_strings(text: str) -> str:
    """`text` with every string literal blanked: `"Dealloc: …"` names no
    identifier."""
    chars = list(text)
    for i, _, _, quoted in lean_chars(text):
        if quoted:
            chars[i] = " "
    return "".join(chars)


def binder_groups(binders: str) -> List[str]:
    """The top-level bracketed groups of a binder list (`(h : p ≠ q)`)."""
    groups: List[str] = []
    start: Optional[int] = None
    for i, ch, depth, quoted in lean_chars(binders):
        if quoted or depth != 0:
            continue
        if ch in LEAN_OPEN:
            start = i
        elif ch in LEAN_CLOSE and start is not None:
            groups.append(binders[start : i + 1])
            start = None
    return groups


class LeanStatement:
    """A theorem's statement as source text: binders and conclusion
    (comments blanked, strings kept), and the SEGMENTS the identifier rule
    reads — each top-level binder group, then the conclusion — with string
    literals blanked."""

    def __init__(self, binders: str, conclusion: str) -> None:
        self.binders = binders
        self.conclusion = conclusion
        self.segments = [blank_strings(group) for group in binder_groups(binders)] + [blank_strings(conclusion)]

    @property
    def text(self) -> str:
        shown = " ".join(f"{self.binders} : {self.conclusion}".split())
        return shown if len(shown) <= 600 else shown[:600] + " …"


def lean_statement(index: Index, root: Path, definition: Definition) -> Optional[LeanStatement]:
    """The statement of the theorem `definition` names, or None when it
    cannot be delimited (no top-level `:=` within `LEAN_STATEMENT_LINES`
    lines, or no top-level `:` before it).  Files are read once."""
    source = index.lean_sources.get(definition.path)
    if source is None:
        try:
            source = lean_uncomment((root / definition.path).read_text(encoding="utf-8"))
        except OSError:
            return None
        index.lean_sources[definition.path] = source
    chunk = "\n".join(source.split("\n")[definition.line - 1 : definition.line - 1 + LEAN_STATEMENT_LINES])
    head = re.search(r"\b(?:theorem|lemma)\s+[A-Za-z_][\w.'!?]*", chunk)
    if not head:
        return None
    chunk = chunk[head.end() :]
    # The statement ends at its top-level `:=`, or at the first equation
    # arm: a top-level `|` that starts its line (`| .I8 => by simp`).
    arms = [i for i in top_level(chunk, "|") if not chunk[chunk.rfind("\n", 0, i) + 1 : i].strip()]
    ends = sorted(top_level(chunk, ":=") + arms)
    if not ends:
        return None
    statement = chunk[: ends[0]]
    colons = [i for i in top_level(statement, ":") if not statement.startswith("::", i) and not statement.startswith(":", i + 1)]
    if not colons:
        return None
    return LeanStatement(statement[: colons[0]], statement[colons[0] + 1 :])


# A conclusion with one of these at top level is outside the reader.
TOP_CONNECTIVES = ("≠", "¬", "↔", "∧", "∨", "→", "/\\", "\\/", "<", "≤", ">", "≥")


def strip_parens(text: str) -> str:
    """`text` without the parentheses that wrap all of it."""
    text = text.strip()
    while len(text) >= 2 and text[0] == "(" and text[-1] == ")":
        inner = [depth for i, _, depth, _ in lean_chars(text) if 0 < i < len(text) - 1]
        if not all(depth >= 1 for depth in inner):
            break
        text = text[1:-1].strip()
    return text


def head_word(text: str) -> str:
    """The head constructor of an expression: its first word, a leading `.`
    or `(` dropped (`.ok (..)` -> `ok`, `some v` -> `some`)."""
    match = re.match(r"[.(\s]*([A-Za-z_][\w.']*)", text)
    return match.group(1).split(".")[-1] if match else ""


OK_HEAD = re.compile(r"(?:Except)?\.ok\b")
ERROR_HEAD = re.compile(r"(?:Except)?\.error\b")
UB_ERROR = re.compile(r"(?:Except)?\.error \(\.ub\b")


def lean_conclusion_verdict(conclusion: str) -> Optional[str]:
    """The verdict class of a theorem's conclusion — `ub`, `runs`, `noop`,
    `true` or `false` — or None when the reader cannot classify it:
    `∃` binders stripped; a top-level connective (`TOP_CONNECTIVES`) is
    unreadable; exactly one top-level ` = `; a `match` left-hand side has
    its own rule (`match_verdict`); otherwise the right-hand side decides."""
    text = " ".join(conclusion.split())
    while text.startswith("∃"):
        commas = top_level(text, ",")
        if not commas:
            return None
        text = text[commas[0] + 1 :].strip()
    if any(top_level(text, connective) for connective in TOP_CONNECTIVES):
        return None
    equals = top_level(text, " = ")
    if len(equals) != 1:
        return None
    lhs, rhs = strip_parens(text[: equals[0]]), strip_parens(text[equals[0] + 3 :])
    if lhs.startswith("match "):
        return match_verdict(lhs, rhs)
    if UB_ERROR.match(rhs) or rhs.startswith('"error:ub'):
        return "ub"
    if OK_HEAD.match(rhs):
        final = lhs.split()[-1]
        noop = re.fullmatch(r"(?:Except)?\.ok \(\(\), " + re.escape(final) + r"\)", rhs)
        return "noop" if noop else "runs"
    if rhs.startswith('"ok:'):
        return "runs"
    if rhs in ("true", "false"):
        return rhs
    return None


def match_verdict(lhs: str, rhs: str) -> Optional[str]:
    """A `match` left-hand side, the only rule for one: `match … with | .ok …
    => X | .error _ => Y` reads `runs` when the right-hand side is X (or both
    are `some …`) AND Y's head constructor is the opposite of the right-hand
    side's (`none` against `some`, `false` against `true`); else None."""
    withs = top_level(lhs, " with ")
    if not withs:
        return None
    body = lhs[withs[0] + len(" with ") :]
    bars = top_level(body, "|")
    if not bars or body[: bars[0]].strip():
        return None
    arms: Dict[str, str] = {}
    for a, b in zip(bars, bars[1:] + [len(body)]):
        piece = body[a + 1 : b].strip()
        arrows = top_level(piece, "=>")
        if len(arrows) != 1:
            return None
        pattern, result = piece[: arrows[0]].strip(), strip_parens(piece[arrows[0] + 2 :])
        arm = "ok" if OK_HEAD.match(pattern) else "error" if ERROR_HEAD.match(pattern) else None
        if arm is None or arm in arms:
            return None
        arms[arm] = result
    if set(arms) != {"ok", "error"}:
        return None
    same = rhs == arms["ok"] or (head_word(rhs) == "some" and head_word(arms["ok"]) == "some")
    opposite = (head_word(rhs), head_word(arms["error"])) in {("some", "none"), ("true", "false")}
    return "runs" if same and opposite else None


def identifier_occurrences(statement: LeanStatement, name: str) -> Tuple[bool, bool]:
    """(occurs after a `≠` or `¬` in its segment, occurs with none before
    it): `name` compared by its last dotted segment, as a whole identifier."""
    last = re.split(r"::|\.", name)[-1]
    pattern = re.compile(r"(?<![A-Za-z0-9_'])" + re.escape(last) + r"(?![A-Za-z0-9_'])")
    negated = plain = False
    for segment in statement.segments:
        for match in pattern.finditer(segment):
            if re.search("[≠¬]", segment[: match.start()]):
                negated = True
            else:
                plain = True
    return negated, plain


# --- The rule -------------------------------------------------------------


class _Cite:
    """One bound citation in a clause: the token, its laws (a law citation)
    or theorem definitions (a theorem citation), and the named identifiers it
    is held to, each with whether the entry negates it."""

    def __init__(self, token: str, laws: Sequence[str] = (), theorems: Sequence[Definition] = ()) -> None:
        self.token, self.laws, self.theorems = token, list(laws), list(theorems)
        self.ids: List[Tuple[str, bool]] = []


def check_says(index: Index, root: Path, doc: Doc, unit: Unit, entry: Entry, report: Report) -> None:
    """Rule E5 over one `(proved-contract)` / `(lean-theorem)` entry.  The
    law half is silent when gate 13 holds nothing (rule E3 already refuses
    every law citation then); the Lean half always runs."""
    text = entry.text
    masked = masked_text(text)
    held = index.gate13
    laws_on = entry.cls == "proved-contract" and held is not None and bool(held.held)
    theorems_on = entry.cls == "lean-theorem"
    if not laws_on and not theorems_on:
        return
    vocab = vocabulary()

    def refuse(message: str) -> None:
        report.findings.append(Finding(doc.path, entry.line, "E5", f"{unit.ident}: {message}"))

    verdicted: Set[str] = set()
    statements: Dict[str, Optional[LeanStatement]] = {}

    def read(cite: _Cite) -> Tuple[Optional[str], List[LeanStatement]]:
        """The reader's verdict of a theorem citation (None: unreadable),
        and its statement(s)."""
        found, verdicts = [], set()
        for d in cite.theorems:
            key = f"{d.path}:{d.line}"
            if key not in statements:
                statements[key] = lean_statement(index, root, d)
            statement = statements[key]
            if statement is None:
                return None, []
            found.append(statement)
            verdicts.add(lean_conclusion_verdict(statement.conclusion))
        return (verdicts.pop() if len(verdicts) == 1 else None), found

    def check_names(cite: _Cite, found: List[LeanStatement], tier: str) -> None:
        if not cite.ids:
            refuse(
                f"`{cite.token}` ({tier}): the clause names no identifier of its statement. E5 holds a theorem citation to "
                "at least one backticked Lean definition or constructor its statement contains (a `semDealloc`, an "
                f"`arcRef`), written in the same clause before it. The statement: `{found[0].text if found else '?'}`"
            )
            return
        for name, negated in cite.ids:
            report.says["identifiers"] += 1
            for statement in found:
                under_not, plain = identifier_occurrences(statement, name)
                if negated and not under_not:
                    why = "is negated in the entry (a negator within reach before it), but the statement never has it after a `≠` or `¬`" if plain else "does not occur in the statement"
                elif not negated and not plain:
                    why = "occurs in the statement only after a `≠` or `¬`, so the entry must negate it (`other than`, `not`)" if under_not else "does not occur in the statement (string literals are blanked)"
                else:
                    continue
                refuse(f"`{cite.token}`: the named identifier `{name}` {why}. The statement: `{statement.text}`")
                break

    def judge_theorem(cite: _Cite, stated: Optional[str], phrase: str) -> None:
        verdict, found = read(cite)
        if not found:
            refuse(f"`{cite.token}`: E5 cannot delimit its statement (no top-level `:=` within {LEAN_STATEMENT_LINES} lines of its declaration), so it cannot check what the entry says of it")
            return
        if verdict is None:
            if stated is not None:
                refuse(
                    f"`{cite.token}`: E5 reads no verdict of this conclusion, yet `{phrase}` gives it one; state none for it (a "
                    f"separate clause that names its identifiers), or extend the reader with a test. The statement: `{found[0].text}`"
                )
                return
            report.says["names_only"] += 1
            check_names(cite, found, "held to names only")
            return
        if stated is None:
            refuse(f"`{cite.token}`: no verdict phrase governs it, and its statement says `{verdict}`. Give it its verdict in the closed vocabulary ({vocab}). The statement: `{found[0].text}`")
            return
        if verdict not in SUBSUMES.get(stated, {stated}):
            refuse(f"`{cite.token}`: `{phrase}` says `{stated}`, but its statement says `{verdict}`: `{found[0].text}`. State the statement's own verdict ({vocab})")
            return
        report.says["theorems"] += 1
        check_names(cite, found, "verdict read")

    def judge_law(cite: _Cite, law: str, stated: Optional[Tuple[str, str]], phrase: str) -> None:
        verdict = held.verdicts.get(law)  # type: ignore[union-attr]
        if verdict is None:
            return  # gate 13 refuses the file then, and E3 says so
        if stated is None:
            refuse(f"`{law}` (cited as `{cite.token}`): no verdict phrase governs it, and its `ensures {verdict.ensures}` says `{verdict}`. Give it its verdict in the closed vocabulary ({vocab})")
            return
        # Given a verdict, right or wrong: `the N other laws of` excludes it.
        verdicted.add(law)
        kind, relation = stated
        if kind != verdict.kind or (kind == "relation" and " ".join(relation.split()) != verdict.relation):
            said = f"true exactly when {' '.join(relation.split())}" if kind == "relation" else kind
            refuse(f"`{law}` (cited as `{cite.token}`): `{phrase}` says `{said}`, but its `ensures {verdict.ensures}` says `{verdict}`. State the law's own verdict ({vocab})")
            return
        report.says["laws"] += 1

    def govern(cite: _Cite, stated: Optional[Tuple[str, str]], phrase: str) -> None:
        if cite.laws:
            for law in cite.laws:
                judge_law(cite, law, stated, phrase)
        else:
            judge_theorem(cite, stated[0] if stated else None, phrase)

    # `one law per <noun>`: the table cited most recently before it is a cell table.
    if laws_on:
        definitions = table_definitions(index, held)  # type: ignore[arg-type]
        tables_at = [(m.start(), t) for m in TOKEN.finditer(text) for t in [cited_table(index, m.group(1), definitions)] if t]
        for per in ONE_LAW_PER.finditer(masked):
            if per.group("noun") == "cell":
                continue
            before = [t for at, t in tables_at if at < per.start()]
            if not before or before[-1] not in held.cell_tables:  # type: ignore[union-attr]
                what = f"`{before[-1]}`, a table over payloads, which gate 13 does not enumerate" if before else "no table citation precedes it"
                refuse(f"\"one law per {per.group('noun')}\" claims a law at every cell, but {what}. Say what the laws are; only a cell table is held to a law at every cell")

    for start, end in clauses(text):
        events: List[Tuple[int, str, object]] = []
        for phrase in PHRASE.finditer(masked, start, end):
            index_ = next(i for i in range(len(_PHRASES)) if phrase.group(f"p{i}") is not None)
            _, kind, verdict = _PHRASES[index_]
            groups = phrase.groupdict()
            relation = groups.get(f"relation{index_}") or ""
            exactly = bool(groups.get(f"exactly{index_}"))
            events.append((phrase.start(), "phrase", (kind, verdict, relation, exactly, phrase.group(0))))
        for token_match in TOKEN.finditer(text, start, end):
            if token_match.end() > end:
                continue
            events.append((token_match.start(), "token", token_match.group(1).strip()))
        events.sort(key=lambda e: e[0])

        lead: Optional[Tuple[str, str]] = None
        lead_phrase = ""
        lead_exactly: Optional[List[str]] = None
        exactly_sets: List[Tuple[str, str, List[str]]] = []
        pending: List[_Cite] = []
        needles: List[Tuple[str, bool]] = []
        subject: List[Tuple[str, bool]] = []
        variants: List[str] = []
        governed_laws: List[str] = []

        def ungoverned() -> None:
            for cite in pending:
                govern(cite, None, "")
            pending.clear()

        for at, what, payload in events:
            if what == "phrase":
                kind, verdict, relation, exactly, said = payload  # type: ignore[misc]
                if kind == "leading":
                    # The word before the phrase, past an `is` / `are`.
                    before = masked[start:at]
                    if not said.startswith(("is ", "are ")):
                        before = re.sub(r"(?<![A-Za-z])(?:is|are)\s*\Z", "", before.rstrip())
                    if NEGATED_END.search(before.rstrip()):
                        refuse(f"F1: `{said}` follows a negator. E5 reads no negated verdict; write the statement's own (`false at`, not `not true at`; `is UB`, not `never runs`)")
                    ungoverned()
                    lead = (verdict, relation)
                    lead_phrase = said
                    lead_exactly = [] if exactly else None
                    if exactly:
                        exactly_sets.append((verdict, said, lead_exactly))  # type: ignore[arg-type]
                    subject, needles = needles, []
                else:
                    if not pending:
                        refuse(f"F2: the closing phrase `{said}` governs no citation: every bound citation before it in its clause already has a verdict, or there is none. A closer gives a verdict to the citations before it that nothing governs yet")
                    for cite in pending:
                        govern(cite, (verdict, ""), said)
                        governed_laws.extend(cite.laws)
                    pending.clear()
                continue
            token = payload  # type: ignore[assignment]
            assert isinstance(token, str)
            kinds = resolve(index, root, token)[1] or set()
            laws = law_names(index, token) if laws_on else []
            theorems = [d for d in qualified_definitions(index, token) if d.kind in THEOREM_KINDS] if theorems_on else []
            if laws or theorems:
                if negated_before(masked, at):
                    refuse(f"F3: the citation `{token}` directly follows a negator. A negated citation has no verdict E5 can check; state the cited statement's own verdict")
                cite = _Cite(token, laws=laws, theorems=theorems)
                if laws:
                    other = OTHER_LAWS.search(masked[start:at])
                    if other:
                        cite.laws = [law for law in laws if law not in verdicted]
                        count = other.group("count")
                        if count is not None and number_word(count) != len(cite.laws):
                            refuse(f"`{token}`: \"the {count} other laws of\" it are {len(cite.laws)} (its {len(laws)} laws less the {len(laws) - len(cite.laws)} given a verdict earlier in the entry): {brief(cite.laws)}")
                else:
                    cite.ids = subject + needles if lead is not None else list(needles)
                    needles = []
                if lead is not None:
                    govern(cite, lead, lead_phrase)
                    governed_laws.extend(cite.laws)
                    if lead_exactly is not None:
                        lead_exactly.extend(cite.laws)
                else:
                    pending.append(cite)
                continue
            if theorems_on and kinds & LEAN_NAME_KINDS:
                window = masked[max(start, at - NEGATOR_REACH) : at]
                needles.append((token, NEGATOR_ANYWHERE.search(window) is not None))
            if laws_on and "variant" in kinds:
                variants.append(token)
        ungoverned()

        if laws_on:
            for verdict, said, laws_said in exactly_sets:
                for family in sorted({held.families.get(law, "") for law in laws_said}):  # type: ignore[union-attr]
                    every = {law for law in held.held if held.families.get(law) == family and held.verdicts.get(law) and held.verdicts[law].kind == verdict}  # type: ignore[union-attr]
                    missing = sorted(every - set(laws_said))
                    if missing:
                        refuse(f"`{said}` claims the laws it governs are ALL the `{verdict}` laws of the family `{family}`, but it does not govern {brief(missing)}")
            enums = {op[1] for law in governed_laws for op in held.cells.get(law, ())}  # type: ignore[union-attr]
            for token in variants:
                name = re.split(r"::|\.", token)[-1]
                for enum in sorted(e for e in enums if name in held.domains.get(e, ())):  # type: ignore[union-attr]
                    covered = any(
                        op[1] == enum and (op[0] == "all" or op[2] == name) for law in governed_laws for op in held.cells.get(law, ())  # type: ignore[union-attr]
                    )
                    if not covered:
                        refuse(f"`{token}` is a variant of `{enum}`, an operand of the laws this clause gives a verdict, but no cell of them: they are {brief(sorted(set(governed_laws)))}. Name the cells the laws state")


def check_paths(index: Index, root: Path, doc: Doc, text: str, span: Tuple[int, int], report: Report) -> None:
    declared = set(EXTERNAL_MARKER.findall(text))
    lines = text.split("\n")
    stats = report.prose.setdefault(doc.path, {"paths": 0, "paths_external": 0})
    for number in range(span[0], span[1]):
        if ENTRY_LINE.match(lines[number]):
            continue  # E2 owns entries and reports them with the unit named
        for token in TOKEN.findall(lines[number]):
            token = token.strip()
            if not looks_like_path(token) or is_external_path(token):
                continue
            if token.split("/", 1)[0] not in TOP_LEVEL:
                continue  # rule P is about REPO-ROOTED paths; partial paths are E2's business
            stats["paths"] += 1
            if token in declared:
                stats["paths_external"] += 1
                continue
            kinds, detail = resolve_path(index, root, token)
            if kinds is None:
                report.findings.append(
                    Finding(doc.path, number + 1, "P", f"cited path `{token}` does not exist ({detail}). If it lives in another repository, declare it: <!-- enforcement-links: external {token} -->")
                )
    for marker in declared:
        if marker in index.files:
            report.findings.append(Finding(doc.path, 1, "P", f"`{marker}` is declared external but exists in this tree; delete the marker"))


def check_refuse_rows(index: Index, root: Path, snapshot: bool, report: Report) -> None:
    """Rule R: every manifest row's cited document exists and names the row
    back.  Runs only where the manifest can exist (the conformance crate is in
    the tree); a tree without it is a unit-test tree, not a broken one."""
    report.findings.extend(index.refuse_manifest_findings)
    report.findings.extend(index.lean_findings)
    manifest_dir = REFUSE_MANIFEST.rsplit("/", 1)[0]
    if REFUSE_MANIFEST not in index.files:
        if (root / "crates" / "trust-ir-conformance").is_dir():
            report.findings.append(Finding(REFUSE_MANIFEST, 1, "R", "the must-refuse corpus manifest is missing; the corpus cannot be vacuous"))
        return
    for row, (line, carrier, obligation) in sorted(index.refuse_rows.items()):
        report.refuse_rows += 1
        token = f"refuse/{row}"
        if obligation not in index.files:
            if snapshot and obligation.startswith("docs/"):
                continue  # not exported; the full tree checks it
            report.findings.append(Finding(REFUSE_MANIFEST, line, "R", f"row `{row}` cites `{obligation}`, which does not exist"))
            continue
        text = (root / obligation).read_text(encoding="utf-8", errors="replace")
        # A token boundary: `refuse/row_one` must not be satisfied by
        # `refuse/row_one_renamed`.
        if not re.search(re.escape(token) + r"(?![A-Za-z0-9_])", text):
            report.findings.append(
                Finding(REFUSE_MANIFEST, line, "R", f"row `{row}` ({carrier}) cites `{obligation}`, which does not name `{token}` back: the sentence stating the obligation cites its corpus row, or says the corpus cannot express it")
            )
        artifact = root / manifest_dir / f"{row}.tmbc"
        if carrier == "none" and artifact.exists():
            report.findings.append(Finding(REFUSE_MANIFEST, line, "R", f"row `{row}` is a `none` row yet `{artifact.relative_to(root)}` exists"))
        if carrier != "none" and not artifact.exists():
            report.findings.append(Finding(REFUSE_MANIFEST, line, "R", f"row `{row}` ({carrier}) has no `{manifest_dir}/{row}.tmbc`"))


def check_refuse_template_rows(index: Index, root: Path, snapshot: bool, report: Report) -> None:
    """Rule R over the template corpus: every row's cited document exists and
    names `refuse_templates/<row>` back, and its carrier's artifacts exist."""
    manifest_dir = REFUSE_TEMPLATE_MANIFEST.rsplit("/", 1)[0]
    if REFUSE_TEMPLATE_MANIFEST not in index.files:
        if (root / manifest_dir).is_dir():
            report.findings.append(Finding(REFUSE_TEMPLATE_MANIFEST, 1, "R", "the template corpus directory exists but its manifest is missing"))
        return
    if not index.refuse_template_rows:
        report.findings.append(Finding(REFUSE_TEMPLATE_MANIFEST, 1, "R", "the template corpus manifest has no rows; the corpus cannot be vacuous"))
    for row, (line, carrier, obligation) in sorted(index.refuse_template_rows.items()):
        report.refuse_rows += 1
        token = f"refuse_templates/{row}"
        if obligation not in index.files:
            if snapshot and obligation.startswith("docs/"):
                continue  # not exported; the full tree checks it
            report.findings.append(Finding(REFUSE_TEMPLATE_MANIFEST, line, "R", f"row `{row}` cites `{obligation}`, which does not exist"))
            continue
        text = (root / obligation).read_text(encoding="utf-8", errors="replace")
        if not re.search(re.escape(token) + r"(?![A-Za-z0-9_])", text):
            report.findings.append(
                Finding(REFUSE_TEMPLATE_MANIFEST, line, "R", f"row `{row}` ({carrier}) cites `{obligation}`, which does not name `{token}` back: the sentence stating the obligation cites its corpus row")
            )
        for suffix in REFUSE_TEMPLATE_ARTIFACTS[carrier]:
            if not (root / manifest_dir / f"{row}{suffix}").exists():
                report.findings.append(Finding(REFUSE_TEMPLATE_MANIFEST, line, "R", f"row `{row}` ({carrier}) has no `{manifest_dir}/{row}{suffix}`"))


def variant_census(index: Index, report: Report) -> None:
    variants = sorted(
        {d.name for defs in index.defs.values() for d in defs if d.kind == "variant" and d.path == VALIDATION_ERROR_FILE and VALIDATION_ERROR_ENUM in d.context}
    )
    report.variant_total = len(variants)
    if not variants:
        report.findings.append(Finding(VALIDATION_ERROR_FILE, 1, "V", f"no `{VALIDATION_ERROR_ENUM}` variants found; the census cannot be vacuous"))
        return
    words: Set[str] = set()
    for code in index.test_code:
        words.update(IDENT.findall(code))
    # A variant a must-refuse manifest row pins is named by the test that
    # runs that row (`refuse_corpus.rs` reads the manifest, so the name is
    # not spelled in Rust).
    words |= index.refuse_named
    report.unnamed_variants = [v for v in variants if v not in words]
    constructed: Set[str] = set()
    for code in index.live_code:
        if VALIDATION_ERROR_ENUM in code:
            constructed |= constructed_variants(code)
    report.dead_variants = [v for v in variants if v not in constructed]


VARIANT_USE = re.compile(r"\b(?:ValidationError|Self)\s*::\s*([A-Z][A-Za-z0-9_]*)")


def constructed_variants(code: str) -> Set[str]:
    """Variants some expression BUILDS.  A use is a PATTERN, not a construction,
    when what follows it (past any `)`/`]` closing an enclosing pattern such as
    `Some(..)`) is `=>`, `|`, `if` or a lone `=`, or when it sits inside a
    `matches!(..)`.  Everything else that names the variant builds it."""
    built: Set[str] = set()
    for use in VARIANT_USE.finditer(code):
        i = use.end()
        while i < len(code) and code[i].isspace():
            i += 1
        if i < len(code) and code[i] in "{(":
            depth, opener = 0, code[i]
            closer = "}" if opener == "{" else ")"
            while i < len(code):
                if code[i] == opener:
                    depth += 1
                elif code[i] == closer:
                    depth -= 1
                    if depth == 0:
                        i += 1
                        break
                i += 1
        while i < len(code) and (code[i].isspace() or code[i] in ")]"):
            i += 1
        following = code[i : i + 3]
        is_pattern = (
            following.startswith("=>")
            or (following.startswith("|") and not following.startswith("||"))
            or re.match(r"if\b", following) is not None
            or (following.startswith("=") and not following.startswith("=="))
            or _inside_matches(code, use.start())
        )
        if not is_pattern:
            built.add(use.group(1))
    return built


def _inside_matches(code: str, position: int) -> bool:
    """Is `position` inside the argument list of a `matches!(` / `assert_matches!(`?"""
    depth, i, floor = 0, position - 1, max(0, position - 4000)
    while i >= floor:
        ch = code[i]
        if ch in ")]}":
            depth += 1
        elif ch in "([{":
            if depth == 0:
                if ch == "{":
                    return False  # left the expression: a block opened here
                if re.search(r"matches!\s*$", code[max(0, i - 24) : i]):
                    return True
            else:
                depth -= 1
        elif ch == ";" and depth == 0:
            return False
        i -= 1
    return False


# --------------------------------------------------------------------------
# The ratchet ledger.
# --------------------------------------------------------------------------


class Ledger:
    def __init__(self) -> None:
        self.rows: Dict[str, List[Tuple[int, str, int]]] = {}  # ledger -> (line, date, count)
        self.members: Dict[str, Dict[str, int]] = {}  # ledger -> member -> line
        self.corrections: Dict[str, int] = {}  # member -> line (SECTION_LEDGER only)
        self.findings: List[Finding] = []


CORRECTION = re.compile(r"correction\s+(\S+)\s+(\S+)\s+(.+?)\s+::\s*(.*)\Z")


def parse_ledger(text: str, path: str = RATCHET) -> Ledger:
    """Three kinds of line.  COUNT rows `<ledger> <date> <count> <why>` are the
    history: append-only, non-increasing.  MEMBER lines `member <ledger> <name>`
    are the present: exactly the debts measured today, by name.  CORRECTION
    rows `correction <ledger> <date> <member> :: <why>` are history too, and the
    ONE way a count rises: by exactly one, for a unit somebody READ and found
    its cited evidence does not back it.  Without them the ratchet could not
    tell an honest downgrade from a regression, and so rewarded leaving an
    overclaim standing."""
    ledger = Ledger()
    for number, raw in enumerate(text.split("\n"), 1):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        if line.startswith("correction "):
            made = CORRECTION.match(line)
            if not made or not made.group(4).strip():
                ledger.findings.append(Finding(path, number, "E4", "expected `correction <ledger> <YYYY-MM-DD> <member> :: <why the earlier class was wrong>`; the reason is required"))
                continue
            name, date, member = made.group(1), made.group(2), made.group(3).strip()
            if name != SECTION_LEDGER:
                ledger.findings.append(Finding(path, number, "E4", f"a correction applies to `{SECTION_LEDGER}` only: whether a test NAMES a variant is measured, not judged, so there is nothing to correct in `{name}`"))
                continue
            try:
                datetime.date.fromisoformat(date)
            except ValueError:
                ledger.findings.append(Finding(path, number, "E4", f"`{date}` is not an ISO date"))
                continue
            history = ledger.rows.setdefault(name, [])
            if not history:
                ledger.findings.append(Finding(path, number, "E4", "a correction corrects a recorded count; there is no count row above it"))
                continue
            if date < history[-1][1]:
                ledger.findings.append(Finding(path, number, "E4", f"`{name}` correction is dated before the row above it; the ledger is append-only"))
            if member in ledger.corrections:
                ledger.findings.append(Finding(path, number, "E4", f"`{member}` is corrected twice; one unit is downgraded once"))
            ledger.corrections[member] = number
            history.append((number, date, history[-1][2] + 1))
            continue
        if line.startswith("member "):
            parts = line.split(None, 2)
            if len(parts) < 3 or parts[1] not in LEDGERS:
                ledger.findings.append(Finding(path, number, "E4", f"expected `member <ledger> <name>` with a ledger in: {', '.join(LEDGERS)}"))
                continue
            names = ledger.members.setdefault(parts[1], {})
            if parts[2] in names:
                ledger.findings.append(Finding(path, number, "E4", f"`{parts[2]}` is listed twice"))
            names[parts[2]] = number
            continue
        parts = line.split(None, 3)
        if len(parts) < 4 or not parts[2].isdigit():
            ledger.findings.append(Finding(path, number, "E4", "expected `<ledger> <YYYY-MM-DD> <count> <why>` or `member <ledger> <name>`"))
            continue
        name, date, count = parts[0], parts[1], int(parts[2])
        if name not in LEDGERS:
            ledger.findings.append(Finding(path, number, "E4", f"unknown ledger `{name}`; known: {', '.join(LEDGERS)}"))
            continue
        try:
            datetime.date.fromisoformat(date)
        except ValueError:
            ledger.findings.append(Finding(path, number, "E4", f"`{date}` is not an ISO date"))
            continue
        history = ledger.rows.setdefault(name, [])
        if history and count > history[-1][2]:
            ledger.findings.append(Finding(path, number, "E4", f"`{name}` rose from {history[-1][2]} to {count}; a COUNT row only goes DOWN. Back the claim instead of raising the count. (An honest downgrade of a unit that was overclassed is a `correction` row, not a count row.)"))
        if history and date < history[-1][1]:
            ledger.findings.append(Finding(path, number, "E4", f"`{name}` row is dated before the row above it; the ledger is append-only"))
        history.append((number, date, count))
    return ledger


def count_rows(text: str) -> List[str]:
    """The HISTORY lines: count rows and correction rows, normalized."""
    lines = [" ".join(l.split("#", 1)[0].split()) for l in text.split("\n")]
    return [l for l in lines if l and not l.startswith("member ")]


def check_ledger_prefix(
    old_text: str,
    new_text: str,
    ref: str,
    units_then: Optional[Dict[str, bool]] = None,
) -> List[Finding]:
    """Against a shared ancestor: every HISTORY row it had is still there, in
    order, first; and no MEMBER was added (a debt retired may not be swapped
    for a new one, which a count alone cannot see) EXCEPT by a correction row
    added since, naming a unit that EXISTED there with checked evidence.
    `units_then` maps each unit of the ancestor's governed documents to whether
    it had checked evidence; None means the ancestor's documents could not be
    read, and then only the correction row itself is required."""
    found: List[Finding] = []
    old, new = count_rows(old_text), count_rows(new_text)
    if new[: len(old)] != old:
        found.append(Finding(RATCHET, 1, "E4", f"history rows recorded at {ref} were edited or removed; the ledger is append-only (a row may be added below, never changed)"))
    then, now = parse_ledger(old_text), parse_ledger(new_text)
    corrected = {m: line for m, line in now.corrections.items() if m not in then.corrections}
    for name in LEDGERS:
        for added in sorted(set(now.members.get(name, {})) - set(then.members.get(name, {}))):
            if name == SECTION_LEDGER and added in corrected:
                continue
            found.append(Finding(RATCHET, now.members[name][added], "E4", f"`{added}` is a NEW member of `{name}` since {ref}; the set only shrinks. Back the claim; retiring a different debt does not buy a new one. If this unit EXISTED at {ref} and was overclassed, record the downgrade: `correction {SECTION_LEDGER} <date> {added} :: <why>`"))
    for member, line in sorted(corrected.items()):
        if units_then is None:
            continue
        if member not in units_then:
            found.append(Finding(RATCHET, line, "E4", f"`{member}` did not exist at {ref}: a correction downgrades a claim that was already made. A NEW claim with no checked evidence is a regression, not a correction; back it."))
        elif not units_then[member]:
            found.append(Finding(RATCHET, line, "E4", f"`{member}` already had no checked evidence at {ref}: there is nothing to correct"))
    return found


def check_ratchet(
    root: Path,
    measured: Dict[str, Tuple[int, List[str]]],
    base_ref: Optional[str],
    report: Report,
    ledger_text: Optional[str] = None,
    base: Optional[Tuple[Optional[str], Optional[Dict[str, bool]]]] = None,
) -> None:
    """`base` = (ledger text, units) as of the merge-base, for tests; when None
    and `base_ref` is set, both are read from git."""
    path = root / RATCHET
    if ledger_text is None and not path.is_file():
        report.findings.append(Finding(RATCHET, 1, "E4", "the ratchet ledger is missing"))
        return
    text = path.read_text(encoding="utf-8") if ledger_text is None else ledger_text
    ledger = parse_ledger(text)
    report.findings.extend(ledger.findings)
    report.corrections = sorted(ledger.corrections)
    today = datetime.date.today().isoformat()
    for name, (count, members) in measured.items():
        history = ledger.rows.get(name)
        if not history:
            report.findings.append(Finding(RATCHET, 1, "E4", f"ledger `{name}` has no count row; measured {count}"))
            continue
        number, _, recorded = history[-1]
        listed = ledger.members.get(name, {})
        unlisted = [m for m in members if m not in listed]
        retired = [m for m in listed if m not in members]
        if count > recorded:
            how = (
                f" If a unit was READ and its cited evidence found not to back it, that is an honest downgrade, and it is recorded, not refused: add `member {name} <unit>` and append `correction {name} {today} <unit> :: <why the earlier class was wrong>` (one row per unit; it must have existed, with checked evidence, at the merge-base)."
                if name == SECTION_LEDGER
                else ""
            )
            report.findings.append(Finding(RATCHET, number, "E4", f"`{name}`: measured {count}, ledger says {recorded}. A claim lost its backing or a new unbacked one was added: {'; '.join(unlisted) or '; '.join(members)}.{how}"))
        elif count < recorded:
            report.findings.append(Finding(RATCHET, number, "E4", f"`{name}`: measured {count}, ledger still says {recorded}. The ratchet tightens only when written down; append: `{name} {today} {count} <what got backed>`"))
        for member in unlisted:
            if count <= recorded:  # otherwise the count finding above already names it
                report.findings.append(Finding(RATCHET, number, "E4", f"`{member}` has no checked evidence but is not a listed member of `{name}`; the member lines must be exactly what is measured"))
        for member in retired:
            report.findings.append(Finding(RATCHET, listed[member], "E4", f"`{member}` is listed under `{name}` but is backed now: delete this line" + ("" if count < recorded else f" (and check the count row: measured {count})")))
    if base is None and base_ref:
        base = (ledger_at_merge_base(root, base_ref), units_at_merge_base(root, base_ref))
    if base is not None:
        ref = f"the merge-base with {base_ref or 'the given base'}"
        old, units_then = base
        if old is None:
            report.notes.append(f"append-only check skipped: no ledger at {ref} (first landing, or no such ref)")
        else:
            report.findings.extend(check_ledger_prefix(old, text, ref, units_then))
        # A marker does not retire a claim.  `not-normative` takes a unit out of
        # BOTH the unit count and the debt list, so without this a debt could
        # be "paid" by a comment and the ledger would record the gain.
        for key, why in report.opted_out_units:
            if units_then is not None and key in units_then:
                report.findings.append(Finding(RATCHET, 1, "E4", f"`{key}` was a NORMATIVE unit at {ref} and is now marked not-normative ({why}). A marker does not retire a claim: back it, or record it honestly as prose-only. If the section truly states no rule any more, that is a change to the DOCUMENT — remove or rewrite the section, in a commit that says so."))


def units_at_merge_base(root: Path, base_ref: str, governed: Optional[Sequence[Doc]] = None) -> Optional[Dict[str, bool]]:
    """Every NORMATIVE unit of the governed documents as of the merge-base,
    mapped to whether it had checked evidence there (by declared class: what
    resolved then is not re-derived).  None when git cannot answer."""
    units: Dict[str, bool] = {}
    answered = False
    for doc in GOVERNED if governed is None else governed:
        if doc.units == "paths":
            continue
        text = file_at_merge_base(root, base_ref, doc.path)
        if text is None:
            continue
        answered = True
        for unit in parse_document(doc, text)[0]:
            if unit.not_normative is None:
                units[f"{doc.path} {unit.ident}"] = unit.backed_in_tree()
    return units if answered else None


def file_at_merge_base(root: Path, base_ref: str, path: str) -> Optional[str]:
    def git(*args: str) -> Optional[str]:
        try:
            done = subprocess.run(["git", "-C", os.fspath(root), *args], check=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        except (OSError, subprocess.CalledProcessError):
            return None
        return done.stdout.decode("utf-8")

    base = git("merge-base", "HEAD", base_ref)
    return git("show", f"{base.strip()}:{path}") if base else None


def ledger_at_merge_base(root: Path, base_ref: str) -> Optional[str]:
    """The ledger as of `merge-base(HEAD, base_ref)`, NOT as of `base_ref`.

    Another session pushes here continuously, so a working clone is BEHIND
    `origin/main` most of the time, and a ledger that merely lacks rows origin
    has since gained is not a ledger somebody edited.  The merge-base is the
    newest history both sides share: any version of an append-only file is a
    prefix of every later one, so a stale ref only weakens this check and can
    never fail it falsely."""

    def git(*args: str) -> Optional[str]:
        try:
            done = subprocess.run(["git", "-C", os.fspath(root), *args], check=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        except (OSError, subprocess.CalledProcessError):
            return None
        return done.stdout.decode("utf-8")

    base = git("merge-base", "HEAD", base_ref)
    return git("show", f"{base.strip()}:{RATCHET}") if base else None


# --------------------------------------------------------------------------
# Driver.
# --------------------------------------------------------------------------


def run(
    root: Path,
    strict: bool = True,
    snapshot: bool = False,
    base_ref: Optional[str] = "origin/main",
    governed: Sequence[Doc] = GOVERNED,
    overrides: Optional[Dict[str, str]] = None,
    index: Optional[Index] = None,
    ledger_text: Optional[str] = None,
    base: Optional[Tuple[Optional[str], Optional[Dict[str, bool]]]] = None,
) -> Report:
    """`overrides` (path -> text) and `ledger_text` substitute file contents in
    memory, so a test can mutate the LIVE documents without writing to the
    repository; `base` substitutes what git would say about the merge-base;
    `index` reuses a tree index that is expensive to build."""
    report = Report()
    overrides = overrides or {}
    index = index if index is not None else build_index(root)
    if index.members is not None and not index.members:
        report.findings.append(Finding("Cargo.toml", 1, "E2", "no workspace `members` found; the index of what EXISTS cannot be empty"))
    for doc in governed:
        path = root / doc.path
        if doc.path not in overrides and not path.is_file():
            if snapshot and not doc.exported:
                report.skipped.append(doc.path)
                continue
            report.findings.append(Finding(doc.path, 1, "E1", "governed document is missing" + ("" if doc.exported else " (it is not exported; a public snapshot runs with --snapshot)")))
            continue
        text = overrides[doc.path] if doc.path in overrides else path.read_text(encoding="utf-8")
        units, findings, span = parse_document(doc, text)
        report.findings.extend(findings)
        check_paths(index, root, doc, text, span, report)
        if doc.units == "paths":
            continue
        if not units:
            report.findings.append(Finding(doc.path, 1, "E1", "no normative units found; the gate cannot be vacuous"))
        for unit in units:
            if unit.not_normative is not None:
                if unit.entries:
                    report.findings.append(Finding(doc.path, unit.line, "E1", f"{unit.ident}: marked not-normative yet carries Enforcement entries; it is one or the other"))
                report.opted_out.append(f"{doc.path} {unit.ident}: {unit.not_normative}")
                report.opted_out_units.append((f"{doc.path} {unit.ident}", unit.not_normative))
                continue
            report.units.append((doc.path, unit))
            if not unit.entries:
                report.findings.append(
                    Finding(doc.path, unit.line, "E1", f"{unit.ident} ({unit.title}): no Enforcement entry. Every normative unit names what enforces it; if nothing does, say `(prose-only)`, and the ratchet will count it.")
                )
            for entry in unit.entries:
                check_entry(index, root, doc, unit, entry, report, strict)
            if unit.entries and not unit.backed_in_tree():
                report.unbacked.append(f"{doc.path} {unit.ident}")
    variant_census(index, report)
    check_refuse_rows(index, root, snapshot, report)
    check_refuse_template_rows(index, root, snapshot, report)
    if not snapshot or not report.skipped:
        measured = {
            SECTION_LEDGER: (len(report.unbacked), report.unbacked),
            VARIANT_LEDGER: (len(report.unnamed_variants), report.unnamed_variants),
            DEAD_LEDGER: (len(report.dead_variants), report.dead_variants),
        }
        if strict:
            check_ratchet(root, measured, base_ref, report, ledger_text, base)
    else:
        report.notes.append("ratchet skipped: a public snapshot does not carry every governed document")
    return report


def strongest(unit: Unit, pick=min) -> str:
    classes = [e.cls for e in unit.entries if e.cls in CLASSES]
    if not unit.entries:
        return "NO ENTRY"
    if not classes:
        return "unclassified"
    return pick(classes, key=CLASSES.index)


def weakest(unit: Unit) -> str:
    """The floor.  A unit's STRONGEST class flatters it: a trusted-base item
    whose certificate covers one narrow sub-claim still rests on an assumption
    nothing checks, and the summary has to show both ends."""
    return strongest(unit, max)


def census(report: Report) -> Dict[str, object]:
    per_doc: Dict[str, Dict[str, int]] = {}
    rows = []
    for path, unit in report.units:
        top = strongest(unit)
        per_doc.setdefault(path, {}).setdefault(top, 0)
        per_doc[path][top] += 1
        rows.append({"doc": path, "unit": unit.ident, "title": unit.title, "strongest": top, "weakest": weakest(unit), "classes": [e.cls for e in unit.entries]})
    partly_unchecked = [f"{path} {unit.ident}" for path, unit in report.units if any(e.cls not in IN_TREE for e in unit.entries)]
    return {
        "units": rows,
        "units_with_any_unchecked_sub_claim": partly_unchecked,
        "strongest_class_per_doc": per_doc,
        "units_without_checked_evidence": report.unbacked,
        "opted_out_not_normative": report.opted_out,
        "citations": report.citations,
        "repo_rooted_paths_in_prose": report.prose,
        "validation_error_variants": {
            "total": report.variant_total,
            "unnamed_by_any_test": report.unnamed_variants,
            "never_constructed": report.dead_variants,
        },
        "must_refuse_corpus_rows_linked_both_ways": report.refuse_rows,
        # Rule E5: law and theorem citations given their statement's own
        # verdict, theorem citations held to names only, identifier checks.
        "statements_said": dict(report.says),
        "findings": len(report.findings),
    }


def said_line(report: Report) -> str:
    """Rule E5's counts, the verdict tier and the names-only tier apart."""
    said = report.says
    return (
        f"{said['laws'] + said['theorems']} proved statements' verdicts stated as they say "
        f"({said['laws']} law, {said['theorems']} theorem), "
        f"{said['names_only']} Lean citation(s) held to names only (conclusion outside the reader), "
        f"{said['identifiers']} identifier check(s)"
    )


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n", 1)[0])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--snapshot", action="store_true", help="public snapshot: skip governed documents that are not exported (detected on its own when neither docs/ nor CLAUDE.md exists)")
    parser.add_argument("--base-ref", default="origin/main", help="git ref the ratchet ledger must extend (append-only); '' disables")
    parser.add_argument("command", nargs="?", default="check", choices=("check", "census"))
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    if not args.snapshot and is_public_snapshot(root):
        # `scripts/` ships whole, so this gate and its tests run in the public
        # clone too; there the unexported documents are absent BY DESIGN.
        args.snapshot = True
        print(f"note: public snapshot detected (none of {', '.join(SNAPSHOT_NEVER_SHIPS)} exists): unexported governed documents are skipped, and the ratchet with them")

    if args.command == "census":
        report = run(root, strict=False, snapshot=args.snapshot, base_ref=None)
        data = census(report)
        if args.json:
            print(json.dumps(data, indent=2))
            return 0
        for row in data["units"]:  # type: ignore[union-attr]
            print(f"{row['doc']:<28} {row['unit']:<10} strongest={row['strongest']:<19} weakest={row['weakest']:<11} {','.join(str(c) for c in row['classes'])}")
        print()
        for path, counts in data["strongest_class_per_doc"].items():  # type: ignore[union-attr]
            print(path + ": " + ", ".join(f"{k}={v}" for k, v in sorted(counts.items())))
        print(f"units without checked evidence: {len(report.unbacked)}  {report.unbacked}")
        partly = data["units_with_any_unchecked_sub_claim"]
        print(f"units carrying at least one sub-claim with no checked evidence (NOT ratcheted: disclosure is not penalized): {len(partly)} of {len(report.units)}")  # type: ignore[arg-type]
        print(f"sections opted out as not-normative: {report.opted_out}")
        print(f"citations in entries: {report.citations}")
        print(f"repo-rooted paths in governed prose: {report.prose}")
        print(f"ValidationError variants: {report.variant_total}, named by no test: {report.unnamed_variants}")
        print(f"ValidationError variants no non-test code constructs: {report.dead_variants}")
        print(f"must-refuse corpus rows linked both ways (rule R): {report.refuse_rows}")
        print(f"rule E5, statements said: {said_line(report)}")
        print(f"findings a `check` would raise (grammar aside): {len(report.findings)}")
        return 0

    report = run(root, strict=True, snapshot=args.snapshot, base_ref=args.base_ref or None)
    for note in report.notes:
        print(f"note: {note}")
    for opted in report.opted_out:
        print(f"note: opted out as not-normative (leaves the unit count AND the debt list): {opted}")
    for member in report.corrections:
        print(f"note: correction on record (an honest downgrade, counted): {member}")
    for skipped in report.skipped:
        print(f"SKIPPED (not exported): {skipped}")
    if report.findings:
        for finding in report.findings:
            print(finding, file=sys.stderr)
        print(f"\nFAIL: {len(report.findings)} enforcement-link finding(s).", file=sys.stderr)
        return 1
    print(
        f"PASS: {len(report.units)} normative units, {report.citations['resolved']} citations resolve, "
        f"{len(report.unbacked)} unit(s) without checked evidence, "
        f"{len(report.opted_out)} opted out as not-normative, {len(report.corrections)} correction(s) on record, "
        f"{len(report.unnamed_variants)}/{report.variant_total} ValidationError variants named by no test "
        f"({len(report.dead_variants)} never constructed), {report.refuse_rows} must-refuse corpus row(s) linked both ways, "
        f"{said_line(report)}. "
        "This gate checks that named enforcement EXISTS, and for the proved classes what it says (E5); it proves no claim."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
