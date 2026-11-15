"""Tests of the gate selector (scripts/gate_select.py) and the host scaler
(scripts/host_scale.py), each with MUTANTS: a weakened copy of the code that
the matching property test must catch.

  * a selector that drops a check the change affects (no reverse-dependency
    closure; no run-time reads; no Lean import closure; a Lean reader that
    stops at a header comment; doc comments not read for doctests);
  * a selector that maps an unknown path to anything less than everything
    (unknown paths treated as documentation; build inputs not global);
  * a cache keyed on fewer inputs (no required execution identity,
    no environment, no gate scripts, no blob contents, no
    history or no origin/main for a history reader, no existence bit);
  * a scaler that oversubscribes (no margin, rounding up, physical memory for
    available memory, cores ignored).

Plus the record rules: a PASS is not cached once the tree differs from the
one planned, and only a green run records the identity that judged it.

The real-repository cases read `targo metadata --no-deps` (no build) and
the tree; nothing here compiles.
"""

from __future__ import annotations

import os
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Dict, List
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, os.fspath(ROOT / "scripts"))

import gate_select as gs  # noqa: E402
import host_scale as hs  # noqa: E402


WHOLE_TREE = {"enforcement-links", "internal-gate-tests", "wire-allocation-owners"}
_REAL: Dict[str, object] = {}
FAKE_TOOLCHAIN = {name: "fixture-" + name for name in (
    "host", "python3", "python3-file", "git", "git-file", "cc", "cc-file",
    "targo", "targo-version", "targo-file", "trustc", "trustc-vV", "trustc-file",
    "lake", "lake-file", "lean", "lean-file")}


def real():
    """(units, pin legs, graph) of this repository, computed once."""
    if not _REAL:
        tree = gs.Tree(ROOT)
        graph = gs.Graph(ROOT, tree, gs.load_metadata(ROOT))
        _REAL["units"] = gs.build_units(graph, {})
        _REAL["pins"] = gs.pin_leg_paths()
        _REAL["graph"] = graph
    return _REAL["units"], _REAL["pins"], _REAL["graph"]


def selected(paths: List[str], units=None) -> gs.Selection:
    u, pins, _ = real()
    return gs.select(units if units is not None else u, paths, pins)


def fresh_units() -> Dict[str, gs.Unit]:
    """Units rebuilt from scratch (so a mutant patched into the module takes
    effect)."""
    tree = gs.Tree(ROOT)
    graph = gs.Graph(ROOT, tree, gs.load_metadata(ROOT))
    return gs.build_units(graph, {})


def runs(sel: gs.Selection, unit: str) -> bool:
    return sel.units[unit]["run"]


def targets(sel: gs.Selection, unit: str) -> List[str]:
    return sel.units[unit]["targets"]


# --------------------------------------------------------------------------
# Property checks: each returns the violations it found (empty = holds).
# --------------------------------------------------------------------------


def selection_violations(units=None) -> List[str]:
    """The selector keeps every check a change affects."""
    out = []

    def need(paths, unit, target=None):
        sel = selected(paths, units)
        if not runs(sel, unit):
            out.append(f"{paths} does not run {unit}")
        elif target is not None and sel.mode == "selected" and target not in targets(sel, unit):
            out.append(f"{paths} does not run {unit}::{target}")

    # reverse-dependency closure: a core-crate change reaches every dependent
    need(["crates/trust-ir/src/inst.rs"], "cli-gate-tests", "bin:trust-ir")
    need(["crates/trust-ir/src/inst.rs"], "validator-fail-closed", "validation_holes")
    need(["crates/trust-ir/src/inst.rs"], "frontend-lowering", "switch_case_lowering")
    need(["crates/trust-ir/src/inst.rs"], "verified-contracts")
    need(["crates/trust-ir/src/function_dependencies/observed_graph/native_queries.rs"],
         "minimal-feature-build")
    need(["crates/trust-ir/src/function_dependencies/observed_graph/native_queries/tests.rs"],
         "minimal-feature-build")
    need(["crates/trust-ir-laws/src/laws.rs"], "verified-contracts")
    need(["crates/trust-ir-build/src/validate.rs"], "frontend-lowering", "switch_case_lowering")
    # dev edges: trust-ir-ay's tests dev-depend on trust-ir-build
    need(["crates/trust-ir-build/src/validate.rs"], "formula-dag")
    # run-time reads named in the sources (derived and declared)
    need(["lowering-target-subset.md"], "wire-format-goldens")
    need(["docs/binary-format.md"], "wire-format-goldens", "back_compat")
    need(["wire-allocations.toml"], "wire-allocation-census")
    need(["wire-allocations.toml"], "wire-allocation-registry")
    need(["crates/trust-ir-fmt/src/main.rs"], "cli-gate-tests", "cli_version")
    # the Lean import closure of the executable the differential builds
    need(["lean/trust_ir-semantics/TrustIr/Semantics/Eval.lean"], "lean-exec-differential",
         "lean_exec_differential")
    need(["lean/trust_ir-semantics/TrustIr/Semantics/Eval.lean"], "lean-schema-parity")
    need(["lean/trust_ir-semantics/TrustIr/Proofs/UnwindProps.lean"], "lean-proofs")
    # data-driven reads (paths the must-refuse manifest names)
    need(["docs/SPEC_RATIFICATIONS.md"], "wire-format-goldens", "refuse_corpus")
    # the CLI binary legs force the build that produces their binary
    need(["crates/trust-ir-conformance/tests/fixtures/chc_batch.tmbc"], "workspace-build")
    return out


def fail_closed_violations(units=None) -> List[str]:
    """Anything the selector cannot attribute, and every build or gate input,
    runs EVERYTHING."""
    out = []
    for paths in (
        ["some-new-root-file.cfg"],
        ["tools/new_tool.rs"],
        ["lean/other-package/X.lean"],
        ["Cargo.lock"],
        ["crates/trust-ir-fmt/Cargo.toml"],
        ["rust-toolchain.toml"],
        ["crates/trust-ir/build.rs"],
        [".cargo/config.toml"],
        ["frontend/Cargo.lock"],
        ["scripts/ci_gates.sh"],
        ["scripts/gates/wire-format-goldens.trust-ir.tests"],
        ["scripts/gates/test-reads.tsv"],
        ["lean/trust_ir-semantics/lakefile.lean"],
        ["crates/trust-ir-ay/src/vc.rs"],  # a dependency-pin leg
    ):
        sel = selected(paths, units)
        if sel.mode != "all":
            out.append(f"{paths} selected {sel.mode}, not everything")
        elif not all(u["run"] for u in sel.units.values()):
            out.append(f"{paths}: mode all but some leg skipped")
    return out


def doc_only_violations(units=None) -> List[str]:
    out = []
    for paths in (["docs/roadmap/README.md"], ["reports/2026-10-14-x/README.md"], ["HANDOFF.md"]):
        sel = selected(paths, units)
        ran = {n for n, u in sel.units.items() if u["run"]}
        if ran != WHOLE_TREE:
            out.append(f"{paths} ran {sorted(ran)}, expected only {sorted(WHOLE_TREE)}")
    return out


def key_violations() -> List[str]:
    """A cache key moves with every element of the complete input set."""
    out = []
    with tempfile.TemporaryDirectory(prefix="gate-key-") as tmp:
        root = Path(tmp)
        subprocess.run(["git", "init", "-q", os.fspath(root)], check=True)
        (root / "crates" / "a").mkdir(parents=True)
        (root / "crates" / "a" / "lib.rs").write_text("pub fn a() {}\n")
        (root / "crates" / "z").mkdir(parents=True)
        (root / "crates" / "z" / "lib.rs").write_text("pub fn z() {}\n")
        (root / "scripts").mkdir()
        (root / "scripts" / "ci_gates.sh").write_text("#!/bin/sh\n")
        (root / "Cargo.lock").write_text("lock\n")
        tree = gs.Tree(root)
        ident = {"targo": "/store/a/targo", "targo-version": "v1", "trustc": "/store/a/trustc",
                 "trustc-vV": "commit-hash: aaaa", "lake": "/elan/lake", "lean": "4.8.0",
                 "host": "Darwin arm64", "python3": "/usr/bin/python3 3.9", "cc": "/usr/bin/cc clang 17",
                 "git": "/usr/bin/git 2.50"}
        hist = {"HEAD": "h1", "origin-merge-base": "m1", "origin/main": "o1"}
        base_ctx = gs.KeyContext(ident, {"CARGO_HOME": "/c"}, {}, gs.global_patterns(set()), hist)

        def key(tree_=None, ctx=None, history=False, patterns=frozenset({"crates/a/"})):
            return gs.unit_key(tree_ or tree, "u", "spec", set(patterns), ctx or base_ctx, history)

        k0 = key()
        if k0 != key():
            out.append("the key is not deterministic")
        # content of an input file
        (root / "crates" / "a" / "lib.rs").write_text("pub fn a() { }\n")
        if key(gs.Tree(root)) == k0:
            out.append("an input file's content does not move the key")
        (root / "crates" / "a" / "lib.rs").write_text("pub fn a() {}\n")
        # a file outside the unit's inputs does not move it (precision)
        (root / "crates" / "z" / "lib.rs").write_text("pub fn z() { }\n")
        if key(gs.Tree(root)) != k0:
            out.append("a file outside the inputs moved the key")
        # the gate scripts (GLOBAL) and the lockfile
        (root / "scripts" / "ci_gates.sh").write_text("#!/bin/sh\n# changed\n")
        if key(gs.Tree(root)) == k0:
            out.append("a gate script does not move the key")
        (root / "scripts" / "ci_gates.sh").write_text("#!/bin/sh\n")
        (root / "Cargo.lock").write_text("lock2\n")
        if key(gs.Tree(root)) == k0:
            out.append("Cargo.lock does not move the key")
        (root / "Cargo.lock").write_text("lock\n")
        # toolchain identity, environment, configuration outside the tree
        # An unknown unit must conservatively retain every identity field.
        for field in ("targo", "targo-version", "trustc", "trustc-vV", "lake", "lean", "host", "python3", "cc",
                      "git"):
            other = dict(ident, **{field: ident[field] + "-other"})
            ctx = gs.KeyContext(other, base_ctx.env, {}, base_ctx.globals, base_ctx.history)
            if key(ctx=ctx) == k0:
                out.append(f"toolchain identity field {field} does not move the key")
        ctx = gs.KeyContext(ident, {"CARGO_HOME": "/c", "RUSTFLAGS": "-Cfoo"}, {}, base_ctx.globals, base_ctx.history)
        if key(ctx=ctx) == k0:
            out.append("the environment does not move the key")
        ctx = gs.KeyContext(ident, base_ctx.env, {"/home/.cargo/config.toml": "abc"}, base_ctx.globals,
                            base_ctx.history)
        if key(ctx=ctx) == k0:
            out.append("a Cargo configuration outside the tree does not move the key")
        # history, for a leg that reads it: HEAD, the merge-base, origin/main
        kh = key(history=True)
        for field in hist:
            ctx = gs.KeyContext(ident, base_ctx.env, {}, base_ctx.globals, dict(hist, **{field: "other"}))
            if key(ctx=ctx, history=True) == kh:
                out.append(f"{field} does not move a history reader's key")
        # an existence-only read: the key carries whether the path exists
        ke = key(patterns={"crates/a/", gs.EXISTS + "docs"})
        (root / "docs").mkdir()
        (root / "docs" / "x.md").write_text("x\n")
        if key(gs.Tree(root), patterns={"crates/a/", gs.EXISTS + "docs"}) == ke:
            out.append("an existence read does not move the key when its path appears")
    return out


def scaler_violations() -> List[str]:
    """jobs x cap fits the measured room, on every host shape."""
    out = []
    for cores in (1, 4, 14, 64, 192):
        for phys_gib in (8, 24, 128, 512):
            phys = phys_gib * 1024
            for frac in (0.0, 0.05, 0.2, 0.5, 0.9, 1.0):
                avail = int(phys * frac)
                for cap in (256, 1024, 3072, 16384):
                  for reserve in (0, 2048, 5000):
                    r = hs.Reading(cores, phys, avail, "test", 1.0)
                    for want in (None, 1, 3, 1000):
                        p = hs.plan_jobs(r, cap, want, reserve)
                        margin = max(hs.MIN_MARGIN_MB, int(phys * hs.MARGIN_FRACTION))
                        room = avail - margin
                        if p.refused:
                            if cap + reserve <= avail:
                                out.append(f"refused though one child ({cap} + {reserve}) fits in {avail} "
                                           f"({cores} cores, {phys_gib} GiB)")
                            continue
                        if p.jobs < 1 or p.jobs > cores:
                            out.append(f"jobs {p.jobs} outside 1..{cores}")
                        if p.jobs * cap + reserve > avail:
                            out.append(f"jobs {p.jobs} x cap {cap} + reserve {reserve} > available {avail}")
                        if p.jobs > 1 and p.jobs * cap + reserve > room:
                            out.append(f"jobs {p.jobs} x cap {cap} + reserve {reserve} > room {room} (avail {avail})")
                        if p.jobs == 1 and cap + reserve > room and not p.note:
                            out.append("a waived margin must be said")
                        if want is not None and p.jobs > want:
                            out.append(f"jobs {p.jobs} > wanted {want}")
    r = hs.Reading(8, 16384, None, "unreadable", None)
    if not hs.plan_jobs(r, 1024).refused:
        out.append("an unmeasurable host was admitted")
    return out


# --------------------------------------------------------------------------
# The tests
# --------------------------------------------------------------------------


class SelectorHolds(unittest.TestCase):
    def test_units_are_ci_gates_legs(self):
        units, _, _ = real()
        self.assertEqual(sorted(units), sorted(set(gs.gate_names(ROOT))))

    def test_selection(self):
        self.assertEqual(selection_violations(), [])

    def test_fail_closed(self):
        self.assertEqual(fail_closed_violations(), [])

    def test_docs_only_runs_only_the_whole_tree_legs(self):
        self.assertEqual(doc_only_violations(), [])

    def test_skips_what_a_change_cannot_reach(self):
        sel = selected(["crates/trust-ir-build/src/validate.rs"])
        self.assertFalse(runs(sel, "verified-contracts"))  # laws do not depend on trust-ir-build
        self.assertFalse(runs(sel, "lean-proofs"))
        sel = selected(["lean/trust_ir-semantics/TrustIr/Proofs/UnwindProps.lean"])
        self.assertFalse(runs(sel, "lean-exec-differential"))  # not in trustir_eval's imports
        self.assertFalse(runs(sel, "workspace-clippy"))
        sel = selected(["frontend/src/lib.rs"])
        self.assertFalse(runs(sel, "validator-fail-closed"))
        self.assertTrue(runs(sel, "frontend-lowering"))

    def test_an_empty_change_runs_only_what_follows_outside_inputs(self):
        sel = selected([])
        self.assertEqual({n for n, u in sel.units.items() if u["run"]}, {"wire-allocation-owners"})

    def test_the_runner_and_the_plan_name_the_same_targets(self):
        # ci_gates.sh's crate_tests names trust-ir-cli's targets from the
        # filesystem (tests/<name>.rs, tests/<name>/main.rs) and filters them
        # by the plan, which names them from `targo metadata`: a name only one
        # side knows would be dropped silently, so the two must agree.
        units, _, graph = real()
        crate = ROOT / "crates" / "trust-ir-cli" / "tests"
        on_disk = {p.stem for p in crate.glob("*.rs")} | {p.parent.name for p in crate.glob("*/main.rs")}
        self.assertEqual(set(units["cli-gate-tests"].targets), on_disk | {"bin:trust-ir"})
        # every registry line names a target the graph knows (else the
        # planner notes it, and test_declarations_are_clean fails)
        self.assertFalse([n for n in graph.notes if "no test target named" in n])

    def test_declarations_are_clean(self):
        _, _, graph = real()
        self.assertEqual(graph.decl_errors, [])
        self.assertEqual(sorted(set(graph.notes)), [])

    def test_cache_keys(self):
        self.assertEqual(key_violations(), [])

    def test_scaler(self):
        self.assertEqual(scaler_violations(), [])


class Mutants(unittest.TestCase):
    """Each mutant weakens one rule; its property check must FAIL under it."""

    # -- selector drops a check the change affects ---------------------------
    def test_mutant_no_reverse_dependency_closure(self):
        with mock.patch.object(gs, "closure_dirs", lambda packages, pdir, test_run: {pdir}):
            units = fresh_units()
        self.assertNotEqual(selection_violations(units), [])

    def test_mutant_no_runtime_reads(self):
        with mock.patch.object(gs.Graph, "file_reads", lambda self, f, d: (set(), False)):
            units = fresh_units()
        self.assertNotEqual(selection_violations(units), [])

    def test_mutant_no_declarations(self):
        with mock.patch.object(gs, "load_declarations", lambda tree: ({}, [])):
            units = fresh_units()
        # undeclared root readers read EVERYTHING: still sound, so the
        # selection holds; the precision property (docs-only) is what breaks
        self.assertEqual(selection_violations(units), [])
        self.assertNotEqual(doc_only_violations(units), [])

    def test_mutant_lean_imports_not_followed(self):
        # (An EMPTY closure is caught by the declaration audit instead: the
        # file's literal names the package, nothing declared covers it, and
        # the reads fall back to EVERYTHING.)
        def root_only(tree, pkg, module):
            return {f"{pkg}/{module.replace('.', '/')}.lean"}

        with mock.patch.object(gs, "lean_closure", root_only):
            units = fresh_units()
        self.assertNotEqual(selection_violations(units), [])

    def test_mutant_module_closure_stops_at_crate_root(self):
        with mock.patch.object(gs, "module_closure", lambda src, f, cfg_test=True: ([f], False)):
            units = fresh_units()
        self.assertNotEqual(selection_violations(units), [])

    # -- an unknown path maps to less than everything ------------------------
    def test_mutant_unknown_path_is_documentation(self):
        with mock.patch.object(gs, "is_doc", lambda path: True):
            self.assertNotEqual(fail_closed_violations(), [])

    def test_mutant_build_inputs_not_global(self):
        with mock.patch.object(gs, "is_global", lambda path, pins: False):
            self.assertNotEqual(fail_closed_violations(), [])

    def test_mutant_extension_globs_map_paths(self):
        units, _, _ = real()
        loose = sorted({q for u in units.values() for q in u.patterns if q != gs.EVERYTHING})
        with mock.patch.object(gs, "mapping_claims", lambda units: loose):
            self.assertNotEqual(fail_closed_violations(), [])

    # -- a cache keyed on fewer inputs ---------------------------------------
    def test_mutant_key_without_toolchain(self):
        real_key = gs.unit_key

        def no_toolchain(tree, name, spec, patterns, ctx, history, target=None):
            ctx = gs.KeyContext({}, ctx.env, ctx.outside, ctx.globals, ctx.history)
            return real_key(tree, name, spec, patterns, ctx, history, target)

        with mock.patch.object(gs, "unit_key", no_toolchain):
            self.assertNotEqual(key_violations(), [])

    def test_mutant_unknown_unit_with_an_unreviewed_toolchain_slice(self):
        # A unit without a reviewed execution contract cannot omit Lean.
        real_key = gs.unit_key

        def trust_only(tree, name, spec, patterns, ctx, history, target=None):
            keep = {k: v for k, v in ctx.ident.items() if k not in ("lake", "lean")}
            ctx = gs.KeyContext(keep, ctx.env, ctx.outside, ctx.globals, ctx.history)
            return real_key(tree, name, spec, patterns, ctx, history, target)

        with mock.patch.object(gs, "unit_key", trust_only):
            self.assertNotEqual(key_violations(), [])

    def test_mutant_key_without_environment(self):
        real_key = gs.unit_key

        def no_env(tree, name, spec, patterns, ctx, history, target=None):
            ctx = gs.KeyContext(ctx.ident, {}, {}, ctx.globals, ctx.history)
            return real_key(tree, name, spec, patterns, ctx, history, target)

        with mock.patch.object(gs, "unit_key", no_env):
            self.assertNotEqual(key_violations(), [])

    def test_mutant_key_without_gate_scripts(self):
        real_key = gs.unit_key

        def no_globals(tree, name, spec, patterns, ctx, history, target=None):
            ctx = gs.KeyContext(ctx.ident, ctx.env, ctx.outside, [], ctx.history)
            return real_key(tree, name, spec, patterns, ctx, history, target)

        with mock.patch.object(gs, "unit_key", no_globals):
            self.assertNotEqual(key_violations(), [])

    def test_mutant_key_on_paths_not_contents(self):
        real_digest = gs.Tree.digest

        def names_only(self, patterns):
            saved = self.files
            self.files = {p: "-" for p in saved}
            try:
                return real_digest(self, patterns)
            finally:
                self.files = saved

        with mock.patch.object(gs.Tree, "digest", names_only):
            self.assertNotEqual(key_violations(), [])

    def test_mutant_key_without_history(self):
        real_key = gs.unit_key

        def no_history(tree, name, spec, patterns, ctx, history, target=None):
            return real_key(tree, name, spec, patterns, ctx, False, target)

        with mock.patch.object(gs, "unit_key", no_history):
            self.assertNotEqual(key_violations(), [])

    def test_mutant_key_without_origin_main(self):
        real_key = gs.unit_key

        def no_origin(tree, name, spec, patterns, ctx, history, target=None):
            h = {k: v for k, v in ctx.history.items() if k != "origin/main"}
            return real_key(tree, name, spec, patterns, gs.KeyContext(ctx.ident, ctx.env, ctx.outside,
                                                                      ctx.globals, h), history, target)

        with mock.patch.object(gs, "unit_key", no_origin):
            self.assertNotEqual(key_violations(), [])

    def test_mutant_key_without_existence(self):
        real_key = gs.unit_key

        def no_exists(tree, name, spec, patterns, ctx, history, target=None):
            return real_key(tree, name, spec, {p for p in patterns if not p.startswith(gs.EXISTS)}, ctx,
                            history, target)

        with mock.patch.object(gs, "unit_key", no_exists):
            self.assertNotEqual(key_violations(), [])

    # -- a scaler that oversubscribes ----------------------------------------
    def _plan_mutant(self, fn) -> None:
        with mock.patch.object(hs, "plan_jobs", fn):
            self.assertNotEqual(scaler_violations(), [])

    def test_mutant_scaler_without_margin(self):
        def no_margin(r, cap_mb, want=None, reserve_mb=0):
            if r.available_mb is None:
                return hs.Plan(0, cap_mb, 0, 0, "unmeasured")
            jobs = min(want or r.cores, r.cores, r.available_mb // cap_mb)
            return hs.Plan(jobs, cap_mb, 0, r.available_mb, None if jobs >= 1 else "none")
        self._plan_mutant(no_margin)

    def test_mutant_scaler_rounds_up(self):
        def ceil(r, cap_mb, want=None, reserve_mb=0):
            margin = max(hs.MIN_MARGIN_MB, int(r.physical_mb * hs.MARGIN_FRACTION))
            if r.available_mb is None:
                return hs.Plan(0, cap_mb, margin, 0, "unmeasured")
            room = r.available_mb - margin
            jobs = min(want or r.cores, r.cores, -(-room // cap_mb))
            return hs.Plan(jobs, cap_mb, margin, room, None if jobs >= 1 else "none")
        self._plan_mutant(ceil)

    def test_mutant_scaler_reads_physical_memory(self):
        real_plan = hs.plan_jobs

        def physical(r, cap_mb, want=None, reserve_mb=0):
            return real_plan(hs.Reading(r.cores, r.physical_mb, r.physical_mb, r.source, r.load1),
                             cap_mb, want, reserve_mb)
        self._plan_mutant(physical)

    def test_mutant_scaler_ignores_cores(self):
        def coreless(r, cap_mb, want=None, reserve_mb=0):
            margin = max(hs.MIN_MARGIN_MB, int(r.physical_mb * hs.MARGIN_FRACTION))
            if r.available_mb is None:
                return hs.Plan(0, cap_mb, margin, 0, "unmeasured")
            room = r.available_mb - margin
            jobs = room // cap_mb if room > 0 else 0
            if want:
                jobs = min(jobs, want)
            return hs.Plan(jobs, cap_mb, margin, room, None if jobs >= 1 else "none")
        self._plan_mutant(coreless)

    def test_mutant_scaler_ignores_the_heavy_child(self):
        real_plan = hs.plan_jobs

        def no_reserve(r, cap_mb, want=None, reserve_mb=0):
            return real_plan(r, cap_mb, want, 0)
        self._plan_mutant(no_reserve)

    def test_mutant_scaler_admits_the_unmeasurable(self):
        real_plan = hs.plan_jobs

        def guess(r, cap_mb, want=None, reserve_mb=0):
            if r.available_mb is None:
                r = hs.Reading(r.cores, r.physical_mb, r.physical_mb, r.source, r.load1)
            return real_plan(r, cap_mb, want, reserve_mb)
        self._plan_mutant(guess)


def slot_violations(workers_fn=None) -> List[str]:
    """Gate 13's parallel slots fit the measured memory (each slot holds up to
    `-j` processes of the base run's peak) and the cores the load leaves; one
    slot is the old serial gate exactly (Targo's default -j)."""
    import verified_contracts as vc

    fn = workers_fn or vc.mutant_workers
    out = []
    for cores in (4, 14, 64):
        for phys_gib in (24, 128):
            for avail_frac in (0.1, 0.5, 0.9):
                for load in (0.0, cores / 2, cores * 3):
                    for peak_mib in (300, 750, 3000):
                        for cpu_ratio in (1.0, 2.5):
                            phys = phys_gib * 1024
                            reading = hs.Reading(cores, phys, int(phys * avail_frac), "t", load)
                            base = vc.LaneRun(1, "", peak_mib << 20, wall_s=100.0, cpu_s=100.0 * cpu_ratio)
                            with mock.patch.object(hs, "measure", lambda reading=reading: reading):
                                workers, jobs, _ = fn(18, base, None)
                            per_cpu = max(1, -(-int(100 * cpu_ratio) // 100))
                            if workers == 1:
                                if jobs != 0:
                                    out.append("one slot must keep Targo's default -j")
                                continue
                            margin = max(hs.MIN_MARGIN_MB, int(phys * hs.MARGIN_FRACTION))
                            if workers * jobs * peak_mib > int(phys * avail_frac) - margin:
                                out.append(f"{workers} slots x -j {jobs} x {peak_mib} MiB > room "
                                           f"({cores} cores, {phys_gib} GiB, {avail_frac}, load {load})")
                            if workers * per_cpu > max(1, int(cores - max(0.0, load - per_cpu))):
                                out.append(f"{workers} slots x {per_cpu} cores > free cores ({cores}, load {load})")
                            if workers > 18:
                                out.append("more slots than mutants")
    return out


class GateThirteenSlots(unittest.TestCase):
    def test_slots_fit(self):
        self.assertEqual(slot_violations(), [])

    def test_mutant_slots_ignore_inner_jobs(self):
        import verified_contracts as vc

        def per_process(n, base, data):
            # the mutant: a slot's cap is one process, though it builds with -j
            r = hs.measure()
            per_cpu = max(1, int(-(-base.cpu_s // base.wall_s)))
            free = max(1, int(r.cores - max(0.0, (r.load1 or 0) - per_cpu)))
            plan = hs.plan_jobs(r, base.rss_bound >> 20, want=max(1, min(n, free // per_cpu)))
            workers = plan.jobs if not plan.refused else 1
            return workers, (per_cpu if workers > 1 else 0), ""

        self.assertNotEqual(slot_violations(per_process), [])

    def test_mutant_slots_ignore_load(self):
        import verified_contracts as vc

        def ignore_load(n, base, data):
            r = hs.measure()
            with mock.patch.object(hs, "measure", lambda: hs.Reading(r.cores, r.physical_mb, r.available_mb,
                                                                    r.source, 0.0)):
                return vc.mutant_workers(n, base, data)

        self.assertNotEqual(slot_violations(ignore_load), [])


class FasterChecksSayTheSame(unittest.TestCase):
    """The gate-0 speedups are output-identical rewrites, held to the code
    they replaced."""

    EDGE = [
        'let a = "x\\"y"; // c "no"\n/* a /* b */ "no2" */ r#"raw "q" "#; br"b"; c"c";',
        "let c = '\"'; let l: &'a str = b'x'; let u = '\\u{1F600}'; 'outer: loop {}",
        "fn f() { let s = \"unterminated\n",
        "/* unterminated /* nested */",
        "r##\"two \"# hashes\"##; b\"\\\"\"; x/y; a//b\n",
        "",
    ]

    def test_mask_matches_the_reference_on_the_tree(self):
        import check_no_ignored_rust as c

        files = subprocess.run(["git", "-C", os.fspath(ROOT), "ls-files", "*.rs"],
                               capture_output=True, text=True, check=True).stdout.split()
        self.assertGreater(len(files), 100)
        for text in [(ROOT / f).read_text(encoding="utf-8", errors="surrogateescape") for f in files] + self.EDGE:
            self.assertEqual(c.mask_non_code(text), c._mask_non_code_reference(text))

    def test_a_broken_mask_is_seen(self):
        import check_no_ignored_rust as c

        broken = c._MASK_STOP
        try:
            c._MASK_STOP = __import__("re").compile(r"//|/\*|[bc]?\"")  # forgets raw strings and chars
            self.assertTrue(any(c.mask_non_code(t) != c._mask_non_code_reference(t) for t in self.EDGE))
        finally:
            c._MASK_STOP = broken

    def test_top_level_matches_its_definition(self):
        import check_enforcement_links as el

        def reference(text, needle):
            return [i for i, _, depth, quoted in el.lean_chars(text)
                    if not quoted and depth == 0 and text.startswith(needle, i)]

        samples = ["(a : Nat) : f (x := 1) = y := by simp", 'x := "a := b" | c', "| .I8 => (by simp)\n| .I16 => 1",
                   "{ a := 1, b := (2 : Nat) } = c"]
        for text in samples:
            for needle in (":=", ":", "|", ",", " = ", "=>"):
                self.assertEqual(el.top_level(text, needle), reference(text, needle))

    def test_memoized_scans_return_fresh_copies(self):
        import wire_alloc as wa

        src = (ROOT / "crates/trust-ir/src/binary.rs").read_text(encoding="utf-8")
        a, b = wa.scan_tag_spaces(src)
        a["mutated"] = 0
        b.append(-1)
        a2, b2 = wa.scan_tag_spaces(src)
        self.assertNotIn("mutated", a2)
        self.assertNotIn(-1, b2)
        self.assertEqual((a2, b2), wa._scan_tag_spaces(src))


class HostReading(unittest.TestCase):
    def test_admission_waits_then_refuses(self):
        tight = hs.Reading(4, 16384, 4096, "test", 0.0)
        cap = hs.Cap(512, 5200, "seed")
        with mock.patch.object(hs, "measure", lambda: tight), mock.patch.object(hs.time, "sleep", lambda s: None):
            plan, _ = hs.admit("probe", cap, None, 0.0)
        self.assertIsNone(plan)
        readings = iter([tight, tight, hs.Reading(4, 16384, 16384, "test", 0.0)])
        with mock.patch.object(hs, "measure", lambda: next(readings)), mock.patch.object(hs.time, "sleep", lambda s: None):
            plan, _ = hs.admit("probe", cap, None, 3600.0)
        self.assertIsNotNone(plan)
        self.assertLessEqual(plan.jobs * cap.share_mb + cap.reserve_mb, 16384 - plan.margin_mb)
        # one child that fits only without the margin runs alone, and says so
        snug = hs.Reading(4, 16384, 6000, "test", 0.0)
        with mock.patch.object(hs, "measure", lambda: snug):
            plan, _ = hs.admit("probe", cap, None, 0.0)
        self.assertEqual(plan.jobs, 1)
        self.assertIn("margin waived", plan.note)

    def test_vm_stat(self):
        text = (
            "Mach Virtual Memory Statistics: (page size of 16384 bytes)\n"
            "Pages free:                               1000.\n"
            "Pages active:                            50000.\n"
            "Pages inactive:                           2000.\n"
            "Pages speculative:                         500.\n"
            "Pages throttled:                             0.\n"
            "Pages wired down:                        90000.\n"
            "Pages purgeable:                           100.\n"
        )
        self.assertEqual(hs.parse_vm_stat(text), (1000 + 500 + 2000 + 100) * 16384 // (1 << 20))
        self.assertIsNone(hs.parse_vm_stat("Pages free: 3.\n"))  # no page size: refused

    def test_meminfo(self):
        self.assertEqual(hs.parse_meminfo("MemTotal: 100 kB\nMemAvailable:    2097152 kB\n"), 2048)
        self.assertIsNone(hs.parse_meminfo("MemTotal: 100 kB\n"))

    def test_margin_scales_with_the_host(self):
        small = hs.plan_jobs(hs.Reading(8, 8 * 1024, 8 * 1024, "t", 0.0), 512)
        large = hs.plan_jobs(hs.Reading(8, 512 * 1024, 512 * 1024, "t", 0.0), 512)
        self.assertEqual(small.margin_mb, max(hs.MIN_MARGIN_MB, int(8 * 1024 * hs.MARGIN_FRACTION)))
        self.assertGreater(large.margin_mb, small.margin_mb)

    def test_the_share_reproduces_the_measured_peak(self):
        # gate 0's tippy leg, measured: a 4855 MiB peak of a 3290 MiB
        # compiler and one neighbour
        share = hs.share_of(4855, 2, 3290, 3290)
        self.assertEqual(share, 1565)
        self.assertEqual(2 * share + (3290 - share), 4855)  # the plan's model at the measured jobs
        for tree, procs, largest in ((6547, 3, 5058), (7062, 14, 5179), (4338, 4, 3700)):
            share = hs.share_of(tree, procs, largest, largest)
            self.assertGreaterEqual(procs * share + (largest - share), tree)
        self.assertEqual(hs.share_of(900, 1, 880, 880), 0)  # no other live child: nothing measured
        self.assertEqual(hs.share_of(0, 0, 0, 700), 0)

    def test_a_job_is_never_charged_less_than_the_seed_share(self):
        # an incremental test build measured 66 MiB beside its compiler; a
        # cold one compiles many crates at once, so the plan floors the share
        with tempfile.TemporaryDirectory(prefix="host-scale-") as tmp:
            with mock.patch.dict(os.environ, {"TRUST_IR_GATE_CACHE": tmp}):
                hs.record("probe-leg", 66, 3619, 3636, 2)
                cap = hs.cap_for("probe-leg")
                self.assertEqual(cap.share_mb, hs.SEED["build"][0])
                self.assertEqual(cap.heavy_mb, 3619)
                hs.record("probe-leg", 900, 3000, 5000, 3)
                self.assertEqual(hs.cap_for("probe-leg").share_mb, 900)  # a larger measurement wins
                hs.record("verified-probe", 10, 700, 710, 2)
                self.assertEqual(hs.cap_for("verified-probe").share_mb, hs.SEED["verify"][0])

    def test_mutant_share_charges_every_job_the_heavy_child(self):
        # the first formula: tree / children, which charged each job a part
        # of the heavy one and planned 2428 MiB a job for the tippy leg
        self.assertNotEqual(-(-4855 // 2), hs.share_of(4855, 2, 3290, 3290))

    def test_caller_caps_are_honored(self):
        with mock.patch.dict(os.environ, {"TRUST_IR_TARGO_JOBS": "6", "CARGO_BUILD_JOBS": "4"}):
            self.assertEqual(hs.caller_cap(), 4)
            self.assertEqual(hs.caller_cap(3), 3)
        with mock.patch.dict(os.environ, {"CARGO_BUILD_JOBS": "-2"}, clear=False):
            os.environ.pop("TRUST_IR_TARGO_JOBS", None)
            self.assertIsNone(hs.caller_cap())  # Cargo's own spelling: not a cap here
        with mock.patch.dict(os.environ, {"TRUST_IR_TARGO_JOBS": "0"}):
            with self.assertRaises(ValueError):
                hs.caller_cap()

    def test_jobs_flag_goes_after_the_verb(self):
        self.assertEqual(hs.with_jobs(["run-targo.sh", "test", "--locked", "--", "x"], 3),
                         ["run-targo.sh", "test", "-j", "3", "--locked", "--", "x"])

    def test_run_learns_the_peak(self):
        with tempfile.TemporaryDirectory(prefix="host-scale-") as tmp:
            roomy = hs.Reading(4, 16384, 16384, "test", 0.0)
            with mock.patch.dict(os.environ, {"TRUST_IR_GATE_CACHE": tmp}), \
                    mock.patch.object(hs, "measure", lambda: roomy):
                code = hs.run("probe-leg", [sys.executable, "-c", "x = bytearray(32 << 20)"], None, False)
                self.assertEqual(code, 0)
                cap = hs.cap_for("probe-leg")
                self.assertIn("learned", cap.why)
                self.assertGreaterEqual(cap.heavy_mb, 32)
                self.assertGreaterEqual(cap.heavy_mb, cap.share_mb)


def _git_repo(root: Path, files: Dict[str, str]) -> None:
    """A committed git repository holding `files`."""
    subprocess.run(["git", "init", "-q", os.fspath(root)], check=True)
    for rel, text in files.items():
        (root / rel).parent.mkdir(parents=True, exist_ok=True)
        (root / rel).write_text(text)
    subprocess.run(["git", "-C", os.fspath(root), "add", "-A"], check=True)
    subprocess.run(["git", "-C", os.fspath(root), "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "t"],
                   check=True)


def lean_header_violations(closure=None) -> List[str]:
    """A Lean import hidden behind a block comment, or below the header, is
    still followed (gate 14's own reading of a file)."""
    out = []
    closure = closure or gs.lean_closure
    with tempfile.TemporaryDirectory(prefix="gate-lean-") as tmp:
        root = Path(tmp)
        _git_repo(root, {
            "pkg/Main.lean": "/-\nCopyright 2026\nAuthor\n-/\nimport Pkg.A\n-- a comment\nimport Lean.Data.Json\n",
            "pkg/Pkg/A.lean": "-- header\n\nimport Pkg.B\n",
            "pkg/Pkg/B.lean": "def b := 1\n",
            "pkg/Pkg/C.lean": "def c := 1\n",
        })
        got = closure(gs.Tree(root), "pkg", "Main")
        want = {"pkg/Main.lean", "pkg/Pkg/A.lean", "pkg/Pkg/B.lean"}
        if got != want:
            out.append(f"closure {sorted(got or [])} != {sorted(want)}")
    return out


def doc_read_violations(doc_reads=None) -> List[str]:
    """What a doctest can read is read from the doc comments themselves."""
    out = []
    with tempfile.TemporaryDirectory(prefix="gate-doc-") as tmp:
        root = Path(tmp)
        _git_repo(root, {
            "crates/a/src/lib.rs": "//! ```\n//! let t = std::fs::read_to_string(\"../../data/x.toml\").unwrap();\n"
                                   "//! ```\npub fn a() {}\n",
            "crates/b/src/lib.rs": "/// ```\n/// let p = std::path::Path::new(env!(\"CARGO_MANIFEST_DIR\"))\n"
                                   "///     .parent().unwrap().join(\"anything\");\n/// ```\npub fn b() {}\n",
            "crates/c/src/lib.rs": "/// A grammar: `theorems [\"..\", ..]` (prose, not a path).\npub fn c() {}\n",
            "data/x.toml": "x = 1\n",
        })
        tree = gs.Tree(root)
        pkgs = {f"crates/{n}": gs.Package(n, f"crates/{n}", "root", [],
                                          [gs.Target(n, "lib", n, f"crates/{n}/src/lib.rs", True)], True)
                for n in "abc"}
        g = gs.Graph(root, tree, pkgs)
        fn = doc_reads or gs.Graph.doc_reads
        if "data/x.toml" not in fn(g, "crates/a/src/lib.rs", "crates/a")[0]:
            out.append("a doctest's climbing read is not seen")
        if gs.EVERYTHING not in fn(g, "crates/b/src/lib.rs", "crates/b")[0]:
            out.append("a doctest climbing from CARGO_MANIFEST_DIR does not read everything")
        if fn(g, "crates/c/src/lib.rs", "crates/c")[0]:
            out.append("prose quoting `..` was read as a path (precision)")
        # and the doctest leg takes them: the lib's run-time inputs with docs
        pats, _ = g.target_inputs("crates/a", pkgs["crates/a"].targets[0], test_run=True, cfg_test=False, docs=True)
        if fn is gs.Graph.doc_reads and "data/x.toml" not in pats:
            out.append("target_inputs(docs=True) leaves the doc reads out")
    return out


class ReadsTheTestsCanMake(unittest.TestCase):
    def test_lean_header_comments_hide_no_import(self):
        self.assertEqual(lean_header_violations(), [])

    def test_mutant_lean_reader_stops_at_the_first_comment_line(self):
        def old_reader(tree, pkg, module):  # the reader this replaced: header ends at a non-comment line
            out, stack = set(), [module]
            while stack:
                m = stack.pop()
                f = f"{pkg}/{m.replace('.', '/')}.lean"
                if f in out:
                    continue
                text = tree.read_text(f)
                if text is None:
                    return None
                out.add(f)
                for line in text.splitlines():
                    s = line.strip()
                    if s.startswith("import "):
                        stack += [n for n in s[7:].split() if n.split(".")[0] not in gs.LEAN_CORE]
                    elif s and not s.startswith(("--", "/-", "prelude", "-", "/")):
                        break
            return out

        self.assertNotEqual(lean_header_violations(old_reader), [])

    def test_doctests_read_their_doc_comments(self):
        self.assertEqual(doc_read_violations(), [])

    def test_mutant_doc_comments_unread(self):
        self.assertNotEqual(doc_read_violations(lambda self, f, d: (set(), False)), [])

    def test_a_filtered_lib_test_reads_every_test_module(self):
        # libtest's filter is a substring of the whole test path, so
        # `--lib alloc_bound::` can run a test module anywhere in the crate:
        # every `-p trust-ir --features binary --lib <filter>` leg has the
        # same inputs (wire_census's declared reads included)
        units, _, _ = real()
        legs = ("wire-version-ledger", "allocation-bounds", "wire-allocation-census")
        self.assertEqual(len({frozenset(units[n].patterns) for n in legs}), 1)
        self.assertIn("wire-allocations.toml", units["allocation-bounds"].patterns)

    def test_an_existence_flip_selects_its_reader(self):
        units, pins, _ = real()
        # refuse_corpus asks whether docs/ and CLAUDE.md exist (public snapshot)
        sel = gs.select(units, ["CLAUDE.md"], pins)
        self.assertNotIn("refuse_corpus", targets(sel, "wire-format-goldens"))  # an edit: not read
        sel = gs.select(units, ["CLAUDE.md"], pins, flipped=["CLAUDE.md"])
        self.assertIn("refuse_corpus", targets(sel, "wire-format-goldens"))  # a deletion: read

    def test_existence_flips_are_computed_against_the_base(self):
        units = {"u": gs.Unit("u", {gs.EXISTS + "docs", gs.EXISTS + "CLAUDE.md", "crates/"})}
        before = {"docs": True, "CLAUDE.md": True}
        after = {"docs": True, "CLAUDE.md": False}
        self.assertEqual(gs.existence_flips(units, before.get, after.get), ["CLAUDE.md"])

    def test_the_survey_ledger_check_reads_every_file_a_row_names(self):
        units, _, graph = real()
        ledger, _ = graph.expand(["paths-in:scripts/gates/verified-survey-refutations.tsv"])
        self.assertTrue(ledger)
        self.assertLessEqual(ledger, units["verified-survey"].patterns)


class RecordAndFinish(unittest.TestCase):
    def setUp(self):
        self.identity = mock.patch.object(gs, "toolchain_identity", return_value=dict(FAKE_TOOLCHAIN))
        self.identity.start()
        self.addCleanup(self.identity.stop)

    def _plan(self, root: Path, cache: Path) -> Path:
        tree = gs.Tree(root)
        plan = {"schema": gs.PLAN_SCHEMA,
                "units": {"u": {"run": True, "reason": "r", "targets": [], "volatile": None, "keys": {},
                                "key": "ab" * 32, "required": True, "required_targets": [], "cached_keys": {}}},
                "cache": os.fspath(cache), "root": os.fspath(root), "base": "b", "mode": "selected",
                "cache_policy": "exact", "recovery": False,
                "why": "w", "changed": [], "identity": gs.current_identity(root, dict(os.environ)),
                "tree": tree.digest([gs.EVERYTHING])[0],
                "head": gs.git_text(root, "rev-parse", "HEAD"), "origin_main": None}
        ctx = gs.KeyContext(plan["identity"], gs.env_fingerprint(dict(os.environ)),
                            gs.outside_config_files(root, dict(os.environ)), [], {})
        plan["units"]["u"]["execution"] = gs.execution_binding("u", ctx)
        p = cache / "plan.json"
        p.write_text(__import__("json").dumps(plan))
        return p

    def test_a_pass_is_not_cached_once_the_tree_changed(self):
        with tempfile.TemporaryDirectory(prefix="gate-rec-") as tmp:
            root, cache = Path(tmp) / "r", Path(tmp) / "c"
            cache.mkdir()
            _git_repo(root, {"a.rs": "fn a() {}\n"})
            plan = self._plan(root, cache)
            (root / "a.rs").write_text("fn a() { }\n")  # edited during the run
            gs.main(["record", "--plan", os.fspath(plan), "--unit", "u"])
            self.assertIsNone(gs.cache_hit(cache, "ab" * 32))
            (root / "a.rs").write_text("fn a() {}\n")  # back to what was planned
            gs.main(["record", "--plan", os.fspath(plan), "--unit", "u"])
            self.assertIsNotNone(gs.cache_hit(cache, "ab" * 32))

    def test_a_pass_is_not_cached_once_head_moved(self):
        with tempfile.TemporaryDirectory(prefix="gate-rec-") as tmp:
            root, cache = Path(tmp) / "r", Path(tmp) / "c"
            cache.mkdir()
            _git_repo(root, {"a.rs": "fn a() {}\n"})
            plan = self._plan(root, cache)
            subprocess.run(["git", "-C", os.fspath(root), "-c", "user.name=t", "-c", "user.email=t@t", "commit",
                            "-q", "--allow-empty", "-m", "moved"], check=True)
            gs.main(["record", "--plan", os.fspath(plan), "--unit", "u"])
            self.assertIsNone(gs.cache_hit(cache, "ab" * 32))

    def test_only_a_green_run_records_the_identity(self):
        with tempfile.TemporaryDirectory(prefix="gate-fin-") as tmp:
            root, cache = Path(tmp) / "r", Path(tmp) / "c"
            cache.mkdir()
            _git_repo(root, {"a.rs": "fn a() {}\n"})
            plan = self._plan(root, cache)
            red = cache / "red.tsv"
            red.write_text("u\tFAIL\tr\t2\n")
            self.assertEqual(gs.main(["finish", "--plan", os.fspath(plan), "--results", os.fspath(red)]), 0)
            self.assertFalse((cache / "last-toolchain.json").exists())
            green = cache / "green.tsv"
            green.write_text("u\tPASS\tr\t1\n")
            self.assertEqual(gs.main(["finish", "--plan", os.fspath(plan), "--results", os.fspath(green)]), 0)
            self.assertTrue((cache / "last-toolchain.json").exists())

    def test_later_failure_invalidates_pass_and_fresh_pass_restores_it(self):
        with tempfile.TemporaryDirectory(prefix="gate-failure-") as tmp:
            root, cache = Path(tmp) / "r", Path(tmp) / "c"
            cache.mkdir()
            _git_repo(root, {"a.rs": "fn a() {}\n"})
            plan = self._plan(root, cache)
            args = ["record", "--plan", os.fspath(plan), "--unit", "u"]
            self.assertEqual(gs.main(args), 0)
            self.assertIsNotNone(gs.cache_hit(cache, "ab" * 32))
            self.assertEqual(gs.main(args + ["--result", "FAIL"]), 0)
            self.assertIsNone(gs.cache_hit(cache, "ab" * 32))
            self.assertEqual(gs.main(args), 0)
            self.assertIsNotNone(gs.cache_hit(cache, "ab" * 32))

    def test_malformed_or_non_object_cache_receipt_is_a_miss(self):
        with tempfile.TemporaryDirectory(prefix="gate-corrupt-") as tmp:
            cache, key = Path(tmp), "ab" * 32
            path = cache / "pass" / key[:2] / f"{key}.json"
            path.parent.mkdir(parents=True)
            for text in ("{", "null", "[]", "1", '"text"', '{"key":"wrong","result":"PASS"}'):
                with self.subTest(text=text):
                    path.write_text(text)
                    self.assertIsNone(gs.cache_hit(cache, key))

    def test_actual_runner_scoped_environment_does_not_change_finish_identity(self):
        source = (ROOT / "scripts/ci_gates.sh").read_text()
        lint = source[source.index("\nlint() {") + 1:source.index("\ngate workspace-clippy")]
        lean = source[source.index("\nlean_exec_differential() {") + 1:source.index("\ngate lean-exec-differential")]
        with tempfile.TemporaryDirectory(prefix="gate-env-") as tmp:
            home = Path(tmp)
            lake = home / ".elan/bin/lake"
            lake.parent.mkdir(parents=True)
            lake.write_text("#!/bin/sh\nexit 0\n")
            lake.chmod(0o755)
            # Run the exact maintained functions with their downstream heavy
            # commands stubbed, checking that both assignments were effective.
            program = ("set -e\n"
                       "stub_clippy() { test \"$CARGO_TARGET_DIR\" = /test-target/tippy; }\n"
                       "run_registry() { test \"$TRUST_IR_REQUIRE_LEAN\" = 1; }\n"
                       "TARGO_RUNNER=stub_clippy\nTARGET_DIR=/test-target\n"
                       + lint + "\n" + lean + "\nenv\nprintf '\\nGATE-ENV-END\\n'\nlint\nlean_exec_differential\nenv\n")
            env = dict(os.environ, HOME=str(home), CARGO_TARGET_DIR="/original-target")
            env.pop("TRUST_IR_REQUIRE_LEAN", None)
            proc = subprocess.run(["bash", "-c", program], env=env, text=True, capture_output=True)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
            before, after = proc.stdout.split("\nGATE-ENV-END\n")
            parse = lambda text: dict(line.split("=", 1) for line in text.splitlines() if "=" in line)
            self.assertEqual(gs.env_fingerprint(parse(before)), gs.env_fingerprint(parse(after)))

    def test_finish_rejects_missing_duplicate_unknown_or_skipped_results(self):
        for rows in ("", "u\tPASS\tr\t1\nu\tPASS\tr\t1\n",
                     "u\tPASS\tr\t1\nv\tPASS\tr\t1\n", "u\tSKIP\tr\t\n"):
            with self.subTest(rows=rows), tempfile.TemporaryDirectory(prefix="gate-incomplete-") as tmp:
                root, cache = Path(tmp) / "r", Path(tmp) / "c"
                cache.mkdir()
                _git_repo(root, {"a.rs": "fn a() {}\n"})
                plan = self._plan(root, cache)
                results = cache / "results.tsv"
                results.write_text(rows)
                self.assertEqual(gs.main(["finish", "--plan", str(plan), "--results", str(results)]), 2)
                self.assertFalse((cache / "last-toolchain.json").exists())

    def test_finish_rechecks_tree_head_origin_environment_configuration_and_toolchain(self):
        for what in ("tree", "head", "origin", "environment", "configuration", "toolchain"):
            with self.subTest(what=what), tempfile.TemporaryDirectory(prefix="gate-bookend-") as tmp:
                root, cache = Path(tmp) / "r", Path(tmp) / "c"
                cache.mkdir()
                _git_repo(root, {"a.rs": "fn a() {}\n"})
                plan = self._plan(root, cache)
                results = cache / "results.tsv"
                results.write_text("u\tPASS\tr\t1\n")
                with mock.patch.dict(os.environ), mock.patch.object(gs, "toolchain_identity", return_value=dict(FAKE_TOOLCHAIN)) as tool:
                    if what == "tree":
                        (root / "a.rs").write_text("fn b() {}\n")
                    elif what == "head":
                        subprocess.run(["git", "-C", str(root), "-c", "user.name=t", "-c", "user.email=t@t",
                                        "commit", "-q", "--allow-empty", "-m", "moved"], check=True)
                    elif what == "origin":
                        subprocess.run(["git", "-C", str(root), "update-ref", "refs/remotes/origin/main", "HEAD"], check=True)
                    elif what == "environment":
                        os.environ["RUSTFLAGS"] = "changed"
                    elif what == "configuration":
                        # Ignored Cargo configuration does not change Tree.digest.
                        (root / ".git/info/exclude").write_text(".cargo/\n")
                        (root / ".cargo").mkdir()
                        (root / ".cargo/config.toml").write_text("[build]\njobs=1\n")
                    else:
                        tool.return_value = dict(FAKE_TOOLCHAIN, targo="other")
                    self.assertEqual(gs.main(["finish", "--plan", str(plan), "--results", str(results)]), 2)
                self.assertFalse((cache / "last-toolchain.json").exists())

    def test_shell_completion_refusal_fails_the_gate(self):
        with tempfile.TemporaryDirectory(prefix="gate-shell-") as tmp:
            plan, results = Path(tmp) / "plan.json", Path(tmp) / "results.tsv"
            plan.write_text("{}")
            results.write_text("u\tPASS\tr\t1\n")
            # Execute the maintained shell summary, with only its Python call
            # replaced. No real compiler, gate or arbitrary source is run.
            summary = (ROOT / "scripts/ci_gates.sh").read_text().split("# --- Summary ", 1)[1]
            summary = summary[summary.index("\n") + 1:]
            env = dict(os.environ, PLAN=str(plan), RESULTS=str(results), ROOT=str(ROOT),
                       FAIL_COUNT="0", FAIL_NAMES="", RUN_STARTED="0")
            proc = subprocess.run(["bash", "-c", "python3() { return 2; }\n" + summary],
                                  env=env, text=True, capture_output=True)
            self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
            self.assertIn("gate-completion", proc.stderr)


class ExecutionInputs(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="gate-execution-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / "root"
        _git_repo(self.root, {"a.rs": "fn a() {}\n", "scripts/ci_gates.sh": "#!/bin/sh\n"})
        self.ident = dict(FAKE_TOOLCHAIN)
        self.env = {"TMPDIR": "/tmp/a", "TRUST_IR_LAKE": "/lake/a", "TRUST_TARGO_BIN": "/targo/a"}

    def ctx(self, ident=None, env=None, outside=None):
        return gs.KeyContext(self.ident if ident is None else ident,
                             gs.env_fingerprint(self.env if env is None else env),
                             {} if outside is None else outside, gs.global_patterns(set()), {})

    def key(self, name, ctx=None):
        return gs.unit_key(gs.Tree(self.root), name, "spec", {"a.rs"}, ctx or self.ctx(), False)

    def test_every_maintained_unit_has_a_reviewed_execution_profile(self):
        self.assertEqual(set(gs.gate_names(ROOT)), set(gs.EXECUTION_PROFILES))
        self.assertEqual(gs.execution_profile("new-unreviewed-unit"), "all")

    def test_temporary_and_python_inputs_move_every_profile(self):
        for name in ("enforcement-links", "internal-gate-tests", "lean-proofs", "lean-exec-differential", "unknown"):
            for variable in ("TMPDIR", "TMP", "TEMP", "PYTHONHASHSEED"):
                with self.subTest(unit=name, variable=variable):
                    self.assertNotEqual(self.key(name), self.key(name, self.ctx(env=dict(self.env, **{variable: "changed"}))))

    def test_lake_changes_only_units_that_execute_lean(self):
        changed = self.ctx(ident=dict(self.ident, lake="other-lake", lean="other-lean"),
                           env=dict(self.env, TRUST_IR_LAKE="/lake/b"))
        for name in ("enforcement-links", "internal-gate-tests", "validator-fail-closed"):
            self.assertEqual(self.key(name), self.key(name, changed), name)
        for name in ("lean-proofs", "lean-exec-differential", "unknown"):
            self.assertNotEqual(self.key(name), self.key(name, changed), name)

    def test_rust_wrapper_changes_only_units_that_execute_rust(self):
        changed = self.ctx(ident=dict(self.ident, targo="other-targo", **{"trustc-vV": "other-compiler"}),
                           env=dict(self.env, TRUST_TARGO_BIN="/targo/b"))
        for name in ("enforcement-links", "lean-proofs"):
            self.assertEqual(self.key(name), self.key(name, changed), name)
        for name in ("internal-gate-tests", "validator-fail-closed", "lean-exec-differential", "unknown"):
            self.assertNotEqual(self.key(name), self.key(name, changed), name)

    def test_cargo_config_and_unknown_inputs_stay_bound_where_needed(self):
        config = self.ctx(outside={"/outside/config.toml": "changed"})
        self.assertEqual(self.key("lean-proofs"), self.key("lean-proofs", config))
        self.assertNotEqual(self.key("internal-gate-tests"), self.key("internal-gate-tests", config))
        for name in ("enforcement-links", "lean-proofs", "internal-gate-tests"):
            self.assertNotEqual(self.key(name), self.key(name, self.ctx(ident=dict(self.ident, new_tool="new"))))
            self.assertNotEqual(self.key(name), self.key(name, self.ctx(env=dict(self.env, TRUST_NEW_POLICY="new"))))
        binding = json.dumps(gs.execution_binding("unknown", self.ctx(env={"TRUST_TOKEN": "secret-value"})))
        self.assertNotIn("secret-value", binding)

    def test_unknown_prefixed_variables_are_not_language_scoped(self):
        for name in ("enforcement-links", "lean-proofs", "validator-fail-closed", "unknown"):
            for variable in ("LEAN_FUTURE_POLICY", "LAKE_FUTURE_POLICY", "ELAN_FUTURE_POLICY",
                             "RUST_FUTURE_POLICY", "TARGO_FUTURE_POLICY", "CARGO_FUTURE_POLICY"):
                with self.subTest(unit=name, variable=variable):
                    self.assertNotEqual(self.key(name), self.key(name, self.ctx(env=dict(self.env, **{variable: "x"}))))

    def test_lean_library_input_of_rust_validator_remains_bound(self):
        # The real Rust validator selects its proof environment through this
        # variable without invoking a Lean executable.
        source = (ROOT / "crates/trust-ir-build/src/validate.rs").read_text()
        self.assertIn('std::env::var_os("LEAN_LIB_DIR")', source)
        first = self.ctx(env=dict(self.env, LEAN_LIB_DIR="/proof/one"))
        second = self.ctx(env=dict(self.env, LEAN_LIB_DIR="/proof/two"))
        self.assertNotEqual(self.key("validator-fail-closed", first), self.key("validator-fail-closed", second))

    def test_wrapper_bytes_are_bound_even_when_path_and_version_do_not_change(self):
        bindir = self.root / "bin"
        bindir.mkdir()
        for name in ("targo", "trustc", "lake", "lean", "python3", "cc", "git"):
            path = bindir / name
            path.write_text("#!/bin/sh\nexit 0\n")
            path.chmod(0o755)
        env = dict(self.env, PATH=str(bindir))
        env["TRUST_TARGO_BIN"] = str(bindir / "targo")
        env["TRUST_IR_LAKE"] = str(bindir / "lake")
        with mock.patch.object(gs, "_run_quiet", return_value="same-version"):
            before = gs.toolchain_identity(self.root, env)
            (bindir / "lake").write_text("#!/bin/sh\n# different dispatcher\nexit 0\n")
            after = gs.toolchain_identity(self.root, env)
        self.assertEqual(before["lake"], after["lake"])
        self.assertEqual(before["lean"], after["lean"])
        self.assertNotEqual(before["lake-file"], after["lake-file"])
        first, second = self.ctx(before, env), self.ctx(after, env)
        self.assertEqual(self.key("internal-gate-tests", first), self.key("internal-gate-tests", second))
        self.assertNotEqual(self.key("lean-proofs", first), self.key("lean-proofs", second))

    def test_unavailable_relevant_tool_identity_is_not_cacheable(self):
        ctx = self.ctx(ident=dict(self.ident, **{"lake-file": "unavailable: executable changed while hashing"}))
        self.assertTrue(gs.execution_binding("internal-gate-tests", ctx)["cacheable"])
        self.assertFalse(gs.execution_binding("lean-proofs", ctx)["cacheable"])
        self.assertFalse(gs.execution_binding("unknown", ctx)["cacheable"])

    def test_missing_required_identity_fields_are_not_complete(self):
        for field in ("trustc", "trustc-vV", "trustc-file"):
            ident = dict(self.ident)
            del ident[field]
            with self.subTest(field=field):
                ctx = self.ctx(ident=ident)
                self.assertFalse(gs.execution_binding("validator-fail-closed", ctx)["cacheable"])
                self.assertTrue(gs.execution_binding("enforcement-links", ctx)["cacheable"])

    def test_actual_resolver_records_missing_compiler_and_refuses_rust_reuse(self):
        bindir = self.root / "missing-compiler-bin"
        bindir.mkdir()
        for name in ("targo", "python3", "git", "cc"):
            path = bindir / name
            path.write_text("#!/bin/sh\nexit 0\n")
            path.chmod(0o755)
        env = dict(self.env, TRUST_TARGO_BIN=str(bindir / "targo"), TRUST_IR_LAKE="/absent/lake")
        def which(name, _env):
            return str(bindir / name) if name != "trustc" else None
        with mock.patch.object(gs, "_which", side_effect=which), mock.patch.object(gs, "_run_quiet", return_value="same"):
            ident = gs.toolchain_identity(self.root, env)
        self.assertEqual(ident["trustc"], "not found")
        self.assertEqual(ident["trustc-file"], "not found")
        ctx = self.ctx(ident=ident, env=env)
        self.assertFalse(gs.execution_binding("validator-fail-closed", ctx)["cacheable"])
        self.assertTrue(gs.execution_binding("enforcement-links", ctx)["cacheable"])


class ScopedExecutionPublication(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="gate-execution-publication-")
        self.addCleanup(self.tmp.cleanup)
        self.root, self.cache = Path(self.tmp.name) / "r", Path(self.tmp.name) / "c"
        self.cache.mkdir()
        _git_repo(self.root, {"a.rs": "fn a() {}\n", "scripts/ci_gates.sh": "gate x true\n"})
        self.env = dict(os.environ, TRUST_IR_GATE_CACHE=str(self.cache), TMPDIR="/tmp/planned",
                        TRUST_IR_LAKE="/lake/planned", TRUST_TARGO_BIN="/targo/planned")
        self.environment = mock.patch.dict(os.environ, self.env, clear=True)
        self.environment.start()
        self.addCleanup(self.environment.stop)
        self.tools = mock.patch.object(gs, "toolchain_identity", return_value=dict(FAKE_TOOLCHAIN))
        self.tools.start()
        self.addCleanup(self.tools.stop)
        for name, kwargs in (("pin_leg_paths", {"return_value": set()}),
                             ("resolve_base", {"return_value": (gs.git_text(self.root, "rev-parse", "HEAD"), "base")}),
                             ("changed_paths", {"return_value": []}),
                             ("load_metadata", {"return_value": {"fixture": object()}}),
                             ("Graph", {"return_value": mock.Mock(notes=[], decl_errors=[])}),
                             ("build_units", {"return_value": {
                                 "internal-gate-tests": gs.Unit("internal-gate-tests", {"a.rs"}),
                                 "lean-proofs": gs.Unit("lean-proofs", {"a.rs"}),
                             }})):
            patch = mock.patch.object(gs, name, **kwargs)
            patch.start()
            self.addCleanup(patch.stop)

    def plan(self):
        return gs.make_plan(self.root, None, False, dict(os.environ))

    def write_plan(self, plan):
        path = self.cache / "plan.json"
        path.write_text(json.dumps(plan))
        return path

    def test_canonical_recovery_reuses_only_complete_equivalent_unit_keys(self):
        first = self.plan()
        for name in first["units"]:
            gs.store_unit_result(first, name, "PASS")
        os.environ["TRUST_IR_LAKE"] = "/lake/changed"
        changed = self.plan()
        self.assertTrue(changed["recovery"])
        self.assertTrue(all(u["required"] for u in changed["units"].values()))
        self.assertFalse(changed["units"]["internal-gate-tests"]["run"])
        self.assertTrue(changed["units"]["lean-proofs"]["run"])
        os.environ["TMPDIR"] = "/tmp/changed"
        self.assertTrue(all(u["run"] for u in self.plan()["units"].values()))

    def test_record_allows_irrelevant_change_but_rejects_relevant_change(self):
        plan = self.plan()
        path = self.write_plan(plan)
        command = ["record", "--plan", str(path), "--unit", "internal-gate-tests"]
        os.environ["TRUST_IR_LAKE"] = "/lake/changed"
        self.assertEqual(gs.main(command), 0)
        key = plan["units"]["internal-gate-tests"]["key"]
        self.assertIsNotNone(gs.cache_hit(self.cache, key))
        os.environ["TMPDIR"] = "/tmp/changed"
        self.assertEqual(gs.main(command), 2)
        self.assertIsNone(gs.cache_hit(self.cache, key))

    def test_stale_finish_refuses_green_and_preserves_unaffected_passes(self):
        plan = self.plan()
        path = self.write_plan(plan)
        for name in plan["units"]:
            self.assertEqual(gs.main(["record", "--plan", str(path), "--unit", name]), 0)
        results = self.cache / "results.tsv"
        results.write_text("internal-gate-tests\tPASS\trun\t1\nlean-proofs\tPASS\trun\t1\n")
        os.environ["TRUST_IR_LAKE"] = "/lake/changed"
        self.assertEqual(gs.main(["finish", "--plan", str(path), "--results", str(results)]), 2)
        self.assertFalse((self.cache / "last-toolchain.json").exists())
        self.assertIsNotNone(gs.cache_hit(self.cache, plan["units"]["internal-gate-tests"]["key"]))
        self.assertIsNone(gs.cache_hit(self.cache, plan["units"]["lean-proofs"]["key"]))
        resumed = self.plan()
        self.assertFalse(resumed["units"]["internal-gate-tests"]["run"])
        self.assertTrue(resumed["units"]["lean-proofs"]["run"])
        gs.store_unit_result(resumed, "lean-proofs", "PASS")
        results.write_text("internal-gate-tests\tSKIP\tcached\t\nlean-proofs\tPASS\trun\t1\n")
        self.assertEqual(gs.main(["finish", "--plan", str(self.write_plan(resumed)), "--results", str(results)]), 0)
        self.assertTrue((self.cache / "last-toolchain.json").exists())

    def test_v2_plan_is_refused_without_publishing_a_new_pass(self):
        plan = self.plan()
        plan["schema"] = "trust-ir-gate-plan-v2"
        path = self.write_plan(plan)
        self.assertEqual(gs.main(["record", "--plan", str(path), "--unit", "internal-gate-tests"]), 2)
        self.assertIsNone(gs.cache_hit(self.cache, plan["units"]["internal-gate-tests"]["key"]))

    def test_receipt_without_execution_preimage_is_not_a_bridge(self):
        plan = self.plan()
        key = plan["units"]["internal-gate-tests"]["key"]
        path = self.cache / "pass" / key[:2] / f"{key}.json"
        path.parent.mkdir(parents=True)
        for extra in ({}, {"schema": "trust-ir-gate-plan-v2"}, {"schema": gs.PLAN_SCHEMA}):
            path.write_text(json.dumps(dict(extra, key=key, result="PASS")))
            self.assertIsNone(gs.cache_hit(self.cache, key))

    def test_repeated_unavailable_identity_never_records_or_reuses_pass(self):
        with mock.patch.object(gs, "toolchain_identity", return_value=dict(
                FAKE_TOOLCHAIN, **{"lake-file": "unavailable: persistent read error"})):
            plan = self.plan()
            self.assertTrue(plan["units"]["internal-gate-tests"]["execution"]["cacheable"])
            self.assertFalse(plan["units"]["lean-proofs"]["execution"]["cacheable"])
            self.assertIsNone(plan["units"]["lean-proofs"]["key"])
            path = self.write_plan(plan)
            for _ in range(2):
                self.assertEqual(gs.main(["record", "--plan", str(path), "--unit", "lean-proofs"]), 2)
                self.assertTrue(self.plan()["units"]["lean-proofs"]["run"])
            results = self.cache / "results.tsv"
            results.write_text("internal-gate-tests\tPASS\trun\t1\nlean-proofs\tPASS\trun\t1\n")
            self.assertEqual(gs.main(["finish", "--plan", str(path), "--results", str(results)]), 2)
            self.assertFalse((self.cache / "last-toolchain.json").exists())

    def test_missing_compiler_field_cannot_publish_a_pass(self):
        missing = dict(FAKE_TOOLCHAIN)
        del missing["trustc-file"]
        with mock.patch.object(gs, "toolchain_identity", return_value=missing):
            plan = self.plan()
            self.assertIsNone(plan["units"]["internal-gate-tests"]["key"])
            path = self.write_plan(plan)
            self.assertEqual(gs.main(["record", "--plan", str(path), "--unit", "internal-gate-tests"]), 2)
            self.assertTrue(self.plan()["units"]["internal-gate-tests"]["run"])


class RecoveryPlan(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="gate-recovery-")
        self.addCleanup(self.tmp.cleanup)
        self.root, self.cache = Path(self.tmp.name) / "r", Path(self.tmp.name) / "c"
        self.cache.mkdir()
        _git_repo(self.root, {"a.rs": "fn a() {}\n", "b.rs": "fn b() {}\n",
                              "scripts/ci_gates.sh": "gate pass true\ngate fail true\n"})
        self.head = gs.git_text(self.root, "rev-parse", "HEAD")
        self.env = dict(os.environ, TRUST_IR_GATE_CACHE=str(self.cache))
        self.patches = []
        for name, kwargs in (
            ("pin_leg_paths", {"return_value": set()}),
            ("resolve_base", {"return_value": (self.head, "test base")}),
            ("changed_paths", {"return_value": []}),
            ("load_metadata", {"return_value": {"synthetic": object()}}),
            ("Graph", {"return_value": mock.Mock(notes=[], decl_errors=[])}),
            ("build_units", {"side_effect": self.units}),
            ("toolchain_identity", {"return_value": dict(FAKE_TOOLCHAIN)}),
        ):
            patch = mock.patch.object(gs, name, **kwargs)
            self.patches.append(patch.start())
            self.addCleanup(patch.stop)

    def units(self, *_):
        return {"pass": gs.Unit("pass", {"a.rs"}), "fail": gs.Unit("fail", {"b.rs"}),
                "batch": gs.Unit("batch", {"a.rs", "b.rs"}, targets={"a": {"a.rs"}, "b": {"b.rs"}}),
                "live": gs.Unit("live", {"a.rs"}, volatile="external state", always=True)}

    def plan(self, all_=False):
        return gs.make_plan(self.root, self.head, all_, self.env)

    def seed_passes(self, plan):
        for name, unit in plan["units"].items():
            if name == "fail" or unit["volatile"]:
                continue
            gs.store_unit_result(plan, name, "PASS")

    def test_identity_recovery_keeps_all_required_and_only_reuses_exact_successes(self):
        first = self.plan()
        self.seed_passes(first)
        resumed = self.plan()
        self.assertEqual(resumed["mode"], "all")
        self.assertEqual(resumed["cache_policy"], "exact")
        self.assertTrue(resumed["recovery"])
        self.assertTrue(all(u["required"] for u in resumed["units"].values()))
        self.assertFalse(resumed["units"]["pass"]["run"])
        self.assertFalse(resumed["units"]["batch"]["run"])
        self.assertTrue(resumed["units"]["fail"]["run"])
        self.assertTrue(resumed["units"]["live"]["run"])

    def test_explicit_all_and_hard_fallbacks_never_reuse_even_without_identity(self):
        self.seed_passes(self.plan())
        plans = [self.plan(all_=True)]
        for changed in (["Cargo.lock"], ["some-new-root-file.cfg"]):
            with mock.patch.object(gs, "changed_paths", return_value=changed):
                plans.append(self.plan())
        with mock.patch.object(gs, "changed_paths", side_effect=gs.GitError("unreadable diff")):
            plans.append(self.plan())
        with mock.patch.object(gs, "resolve_base", return_value=(None, "missing")):
            plans.append(self.plan())
        with mock.patch.object(gs, "load_metadata", side_effect=RuntimeError("unreadable graph")):
            plans.append(self.plan())
        for plan in plans:
            with self.subTest(why=plan["why"]):
                self.assertEqual(plan["cache_policy"], "none")
                self.assertFalse(plan["recovery"])
                self.assertTrue(all(u["run"] for u in plan["units"].values()))

    def test_changed_toolchain_cannot_reuse_other_identity(self):
        self.seed_passes(self.plan())
        with mock.patch.object(gs, "toolchain_identity", return_value=dict(FAKE_TOOLCHAIN, targo="other")):
            plan = self.plan()
        self.assertEqual(plan["cache_policy"], "exact")
        self.assertTrue(all(u["run"] for u in plan["units"].values()))

    def test_failed_target_batch_invalidates_attempted_keys_and_whole_unit(self):
        first = self.plan()
        self.seed_passes(first)
        unit = first["units"]["batch"]
        gs.store_unit_result(first, "batch", "FAIL", ["b"])
        self.assertIsNone(gs.cache_hit(self.cache, unit["key"]))
        self.assertIsNotNone(gs.cache_hit(self.cache, unit["keys"]["a"]))
        self.assertIsNone(gs.cache_hit(self.cache, unit["keys"]["b"]))
        resumed = self.plan()
        self.assertEqual(resumed["units"]["batch"]["targets"], ["b"])
        self.assertEqual(resumed["units"]["batch"]["required_targets"], ["a", "b"])
        self.assertEqual(set(resumed["units"]["batch"]["cached_keys"]), {"a"})

    def test_required_consumer_runs_its_cached_producer(self):
        units = self.units()
        units["consumer"] = gs.Unit("consumer", {"b.rs"}, after=("pass",))
        with mock.patch.object(gs, "build_units", return_value=units):
            first = self.plan()
            self.seed_passes(first)
            gs.store_unit_result(first, "consumer", "FAIL")
            resumed = self.plan()
        self.assertTrue(resumed["units"]["pass"]["run"])
        self.assertFalse(resumed["units"]["pass"]["cached_keys"])

    def test_recovery_finish_requires_all_live_checks_and_rechecks_cached_keys(self):
        self.seed_passes(self.plan())
        for failure in ("none", "required-failure", "live-skipped", "cached-invalidated", "cached-missing", "coverage-lost"):
            with self.subTest(failure=failure):
                plan = self.plan()
                rows = "pass\tSKIP\tcached\t\nbatch\tSKIP\tcached\t\nfail\tPASS\trun\t1\nlive\tPASS\trun\t1\n"
                if failure == "required-failure":
                    rows = rows.replace("fail\tPASS", "fail\tFAIL")
                elif failure == "live-skipped":
                    rows = rows.replace("live\tPASS", "live\tSKIP")
                elif failure == "cached-invalidated":
                    gs.store_unit_result(plan, "pass", "FAIL")
                elif failure == "cached-missing":
                    key = plan["units"]["pass"]["key"]
                    (self.cache / "pass" / key[:2] / f"{key}.json").unlink()
                elif failure == "coverage-lost":
                    plan["units"]["batch"]["cached_keys"].pop("a")
                plan_path, results = self.cache / "finish.json", self.cache / "results.tsv"
                plan_path.write_text(json.dumps(plan))
                results.write_text(rows)
                with mock.patch.dict(os.environ, self.env, clear=True):
                    rc = gs.main(["finish", "--plan", str(plan_path), "--results", str(results)])
                self.assertEqual(rc, 0 if failure in ("none", "required-failure") else 2)
                self.assertEqual((self.cache / "last-toolchain.json").exists(), failure == "none")
                (self.cache / "last-toolchain.json").unlink(missing_ok=True)
                self.seed_passes(self.plan())


if __name__ == "__main__":
    unittest.main()
