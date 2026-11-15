"""Guards for the Lean-proofs gate (scripts/lean_proofs.py, gate 14).

The gate's red demonstrations (a `sorry` theorem, an `example` with a `sorry`,
an extra axiom, `native_decide` outside the fixture modules, a stale
`#guard_msgs` printout, a kernel bypass, an orphan file; then, for the kernel
replay, constants written into the environment without the kernel in a proof
module and in a fixture module, a forged `partial` definition with a user, and
a `native_decide`-shaped constant asserting the wrong evaluation) need `lake`
and were run by hand on a scratch copy; they are recorded in the commits that
added the gate and the replay. What runs here, without a Lean toolchain, is
the gate's BOOKKEEPING: the comment stripper, the import closure, the orphan
and kernel-bypass checks, the census-list reader, the log parsers, the replay
ledger, the no-lake verdict, and that ci_gates.sh really requires the gate
where gate 12 does.
"""

import io
import sys
import tempfile
import textwrap
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

import lean_proofs as lp  # noqa: E402

REAL_PACKAGE = ROOT / lp.PACKAGE


def package(files):
    tmp = tempfile.TemporaryDirectory()
    root = Path(tmp.name)
    for name, text in files.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(textwrap.dedent(text).lstrip("\n"), encoding="utf-8")
    return tmp, root


class CommentStripping(unittest.TestCase):
    def test_line_and_nested_block_comments_are_blanked_and_lines_kept(self):
        source = "a -- skipKernelTC\n/- outer /- inner -/ still -/ b\n/-\nimport X\n-/\nc"
        stripped = lp.strip_lean_comments(source)
        self.assertEqual(stripped.count("\n"), source.count("\n"))
        self.assertNotIn("skipKernelTC", stripped)
        self.assertNotIn("import X", stripped)
        self.assertEqual(stripped.split("\n")[1].strip(), "b")
        self.assertEqual(stripped.split("\n")[-1], "c")


class ImportClosure(unittest.TestCase):
    def test_the_closure_follows_package_imports_and_names_orphans(self):
        tmp, pkg = package(
            {
                "TrustIr.lean": "import Lean\nimport TrustIr.A TrustIr.B\n-- import TrustIr.C\n",
                "TrustIr/A.lean": "import TrustIr.Deep.D\n",
                "TrustIr/B.lean": "",
                "TrustIr/C.lean": "theorem nobody_builds_me : True := trivial\n",
                "TrustIr/Deep/D.lean": "",
            }
        )
        with tmp:
            closure = lp.import_closure(pkg)
            self.assertEqual(sorted(closure), ["TrustIr", "TrustIr.A", "TrustIr.B", "TrustIr.Deep.D"])
            self.assertEqual(lp.orphan_files(pkg, closure), ["TrustIr/C.lean"])

    def test_the_real_package_has_no_orphan_and_no_kernel_bypass(self):
        closure = lp.import_closure(REAL_PACKAGE)
        self.assertIn(lp.ROOT_MODULE, closure)
        self.assertEqual(lp.orphan_files(REAL_PACKAGE, closure), [])
        self.assertEqual(lp.runtime_model_leaks(lp.import_closure(REAL_PACKAGE, lp.FORMAL_ROOT_MODULE)), [])
        self.assertEqual(lp.kernel_bypasses(closure, REAL_PACKAGE), [])

    def test_a_kernel_bypass_is_found_outside_comments_only(self):
        tmp, pkg = package(
            {
                "TrustIr.lean": "import TrustIr.A\n",
                "TrustIr/A.lean": "-- skipKernelTC in a comment\nset_option debug.skipKernelTC true in\ntheorem t : True := trivial\n",
            }
        )
        with tmp:
            found = lp.kernel_bypasses(lp.import_closure(pkg), pkg)
            self.assertEqual(len(found), 1, found)
            self.assertTrue(found[0].startswith("TrustIr/A.lean:2:"), found)


class RuntimeBoundary(unittest.TestCase):
    def fixture(self, model="", runtime=""):
        return package({
            "TrustIr.lean": model,
            "TrustIrRuntime.lean": runtime,
            "TrustIrRuntime/Unused.lean": "",
            "TrustIr/Hidden.lean": "theorem hidden : True := trivial\n",
        })

    def test_runtime_build_coverage_does_not_hide_orphan_model_proofs(self):
        tmp, pkg = self.fixture(runtime="import TrustIr.Hidden\n")
        with tmp:
            model = lp.import_closure(pkg)
            runtime = lp.runtime_import_closure(pkg)
            self.assertEqual(lp.orphan_files(pkg, model),
                             ["TrustIr/Hidden.lean"])
            self.assertIn(lp.RUNTIME_ROOT_MODULE, runtime)
            self.assertNotIn(lp.RUNTIME_ROOT_MODULE, model)

    def test_a_runtime_helper_must_be_reached_from_the_built_root(self):
        tmp, pkg = self.fixture(model="import TrustIr.Hidden TrustIrRuntime\n",
                                runtime="import TrustIrRuntime.Unused\n")
        with tmp:
            self.assertEqual(lp.orphan_files(pkg, lp.import_closure(pkg)), [])
            self.assertEqual(lp.orphan_files(pkg, lp.runtime_import_closure(pkg), lp.RUNTIME_ROOT_MODULE), [])

    def test_runtime_imported_by_model_is_a_boundary_failure(self):
        tmp, pkg = self.fixture(model="import TrustIrRuntime\n")
        with tmp:
            self.assertEqual(lp.runtime_model_leaks(lp.import_closure(pkg)),
                             [lp.RUNTIME_ROOT_MODULE])

    def test_kernel_bypass_is_still_checked_in_runtime_sources(self):
        tmp, pkg = self.fixture(runtime="set_option debug.skipKernelTC true\n")
        with tmp:
            closure = {**lp.runtime_import_closure(pkg), **lp.import_closure(pkg)}
            self.assertTrue(lp.kernel_bypasses(closure, pkg))

    def test_a_complete_replay_ledger_does_not_waive_a_runtime_leak(self):
        tmp, pkg = package({"TrustIr.lean": "import TrustIr.Formal\n",
                            "TrustIr/Formal.lean": "import TrustIrRuntime\n",
                            "TrustIrRuntime.lean": ""})
        def accepted_runs(cmd, cwd, env):
            if cmd[-1] == "runtimePluginPath":
                return lp.subprocess.CompletedProcess(cmd, 0, stdout=str(Path(lp.__file__).resolve()) + "\n")
            out = ("lean-proofs census: safe-constants=1 imported-modules=3 "
                   "replayed=1 replay-skipped-partial=0\n") if cmd[-1] == lp.CENSUS_FILE else "Build completed successfully.\n"
            return lp.subprocess.CompletedProcess(cmd, 0, stdout=out)
        out, err = io.StringIO(), io.StringIO()
        with tmp, mock.patch.object(lp, "find_lake", return_value=Path(lp.__file__)), \
             mock.patch.object(lp, "run", side_effect=accepted_runs), \
             redirect_stdout(out), redirect_stderr(err):
            self.assertEqual(lp.main(["--package", str(pkg), "--require"]), 1)
        self.assertIn("runtime-boundary:", err.getvalue())

    def test_attachment_cannot_hide_proofs_outside_the_census_namespace(self):
        tmp, pkg = package({"TrustIr.lean": "import TrustIrNativeLink\n",
                            "TrustIrNativeLink.lean": "import Init\naxiom hidden : False\n"})
        with tmp:
            closure = lp.import_closure(pkg)
            self.assertEqual(lp.audited_module_count(closure), 1)
            self.assertEqual(lp.logical_attachment_problems(closure), ["TrustIrNativeLink"])
            (pkg / "TrustIrNativeLink.lean").write_text("-- native attachment\nimport Init\n")
            self.assertEqual(lp.logical_attachment_problems(lp.import_closure(pkg)), [])

    def test_a_missing_explicit_linker_is_not_silently_ignored(self):
        with self.assertRaises(ValueError):
            lp.lake_config_args({"TRUST_IR_NATIVE_LINKER": "/definitely/missing/trust-ir-ld"})

    def test_census_uses_loaded_lake_lean_and_retains_explicit_linker(self):
        calls = []
        def loaded_run(cmd, cwd, env):
            calls.append(cmd)
            return lp.subprocess.CompletedProcess(cmd, 0, stdout="Build completed successfully.\n")
        with mock.patch.object(lp, "find_lake", return_value=Path(lp.__file__)), \
             mock.patch.object(lp, "run", side_effect=loaded_run), \
             redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            self.assertEqual(lp.main(["--root", str(ROOT), "--require"]), 1)
        self.assertIn("lean", calls[-1])
        self.assertNotIn("env", calls[-1])
        self.assertEqual(calls[-1][-1], lp.CENSUS_FILE)
        self.assertIn("-R", calls[-1])

    def test_the_runtime_target_is_compiled_and_its_failure_refuses_the_gate(self):
        tmp, pkg = package({"TrustIr.lean": "import TrustIr.Formal TrustIrRuntime\n",
                            "TrustIr/Formal.lean": "", "TrustIrRuntime.lean": ""})
        calls = []
        def failed_runtime(cmd, cwd, env):
            calls.append(cmd)
            return lp.subprocess.CompletedProcess(cmd, 1,
                stdout="error: TrustIrRuntime.lean:1:1: runtime type error\n")
        with tmp, mock.patch.object(lp, "find_lake", return_value=Path(lp.__file__)), \
             mock.patch.object(lp, "run", side_effect=failed_runtime), \
             redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            self.assertEqual(lp.main(["--package", str(pkg), "--require"]), 1)
        self.assertEqual(len(calls), 1)
        self.assertIn("TrustIrRuntime", calls[0])



class TheFixtureListIsStatedOnce(unittest.TestCase):
    def test_the_census_list_is_read_and_a_comment_is_not_a_list(self):
        tmp, pkg = package(
            {
                lp.CENSUS_FILE: "-- def nativeDecideModules : List Name := [`Wrong]\n"
                "def nativeDecideModules : List Name :=\n  [`TrustIr.X, `TrustIr.Y.Z]\n"
            }
        )
        with tmp:
            self.assertEqual(lp.native_decide_modules(pkg), ["TrustIr.X", "TrustIr.Y.Z"])

    def test_an_unreadable_list_raises_and_a_missing_census_is_none(self):
        tmp, pkg = package({lp.CENSUS_FILE: "def somethingElse := 1\n"})
        with tmp:
            with self.assertRaises(ValueError):
                lp.native_decide_modules(pkg)
            (pkg / lp.CENSUS_FILE).unlink()
            self.assertIsNone(lp.native_decide_modules(pkg))

    def test_every_real_fixture_module_is_built_and_uses_native_decide(self):
        # The census admits `Lean.ofReduceBool` exactly where the fixtures are:
        # a listed module that stopped using `native_decide` would widen the
        # admission for nothing, and one outside the closure admits nothing.
        closure = lp.import_closure(REAL_PACKAGE)
        listed = lp.native_decide_modules(REAL_PACKAGE)
        self.assertTrue(listed)
        for module in listed:
            self.assertIn(module, closure)
            code = lp.strip_lean_comments(closure[module].read_text(encoding="utf-8"))
            self.assertIn("native_decide", code, module)


class LogParsing(unittest.TestCase):
    LOG = (
        "⚠ [47/53] Replayed TrustIr.Proofs.ArithProps\n"
        "warning: ././././TrustIr/Proofs/ArithProps.lean:165:8: declaration uses 'sorry'\n"
        "warning: ././././TrustIr/Proofs/ArithProps.lean:170:4: unused variable `x`\n"
        "error: ././././TrustIr/Proofs/AxiomAudit.lean:44:0: ❌ Docstring on `#guard_msgs` does not match\n"
        "error: build failed\n"
    )

    def test_a_replayed_sorry_warning_is_found_with_its_location(self):
        self.assertEqual(
            lp.sorry_warnings(self.LOG),
            ["warning: TrustIr/Proofs/ArithProps.lean:165:8: declaration uses 'sorry'"],
        )

    def test_errors_are_named_by_file_and_line(self):
        errors = lp.build_errors(self.LOG)
        self.assertEqual(errors[0].split(" ❌")[0], "error: TrustIr/Proofs/AxiomAudit.lean:44:0:")
        self.assertEqual(len(errors), 2)

    def test_the_census_line_and_its_fields_parse(self):
        out = "lean-proofs census: modules=50 safe-constants=6916 theorems=3147 imported-modules=52 cross-checked=197\n"
        line = lp.census_line(out)
        self.assertIsNotNone(line)
        self.assertEqual(lp.census_field(line, "imported-modules"), "52")
        self.assertEqual(lp.census_field(line, "modules"), "50")
        self.assertIsNone(lp.census_line("nothing here\n"))

    def test_a_field_is_not_read_off_the_tail_of_a_longer_key(self):
        line = "lean-proofs census: imported-modules=52 modules=50 replay-skipped-partial=3 replayed=9"
        self.assertEqual(lp.census_field(line, "modules"), "50")
        self.assertEqual(lp.census_field(line, "replayed"), "9")
        self.assertIsNone(lp.census_field("lean-proofs census: imported-modules=52", "modules"))


class ReplayLedger(unittest.TestCase):
    LINE = (
        "lean-proofs census: modules=50 safe-constants=6916 theorems=3147 imported-modules=52 "
        "cross-checked=197 replayed=6839 replay-evaluations=462 replay-skipped-partial=77"
    )

    def test_a_ledger_that_accounts_for_every_safe_constant_passes(self):
        self.assertEqual(lp.replay_ledger_problems(self.LINE), [])

    def test_a_constant_the_replay_did_not_account_for_fails(self):
        problems = lp.replay_ledger_problems(self.LINE.replace("replayed=6839", "replayed=6838"))
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("safe-constants=6916", problems[0])

    def test_a_census_line_without_the_replay_fails(self):
        line = self.LINE.split(" replayed=")[0]
        self.assertEqual(lp.replay_ledger_problems(line), ["replay: the census line has no numeric `replayed=` field"])

    def test_an_empty_replay_fails(self):
        line = "lean-proofs census: safe-constants=0 replayed=0 replay-skipped-partial=0"
        self.assertEqual(lp.replay_ledger_problems(line), ["replay: nothing was replayed"])

    def test_the_census_source_runs_the_replay_and_prints_the_ledger(self):
        # The ledger is only as good as the census that prints it: the replay
        # call, the evaluation premises and every ledger key must be in the
        # census source (outside comments).
        code = lp.strip_lean_comments((REAL_PACKAGE / lp.CENSUS_FILE).read_text(encoding="utf-8"))
        self.assertIn("import Lean.Replay", code)
        self.assertIn("Environment.replay", code)
        self.assertIn("evalBool env aux", code)
        for key in lp.REPLAY_LEDGER:
            self.assertIn(f"{key}={{", code)


class TheGateReadsTheLedger(unittest.TestCase):
    """`main` with lake and both Lean runs stubbed: a census that exits 0 but
    prints no replay ledger is refused, and a whole ledger passes."""

    def run_main(self, census_stdout):
        closure = lp.import_closure(REAL_PACKAGE)
        census_stdout = census_stdout.replace("IMPORTED", str(sum(name == lp.ROOT_MODULE or name.startswith(lp.ROOT_MODULE + ".") for name in closure)))

        def fake_run(cmd, cwd, env):
            if cmd[-1] == lp.CENSUS_FILE:
                # Fresh elaboration must receive Lake's precompiled-import
                # context; raw `lake env lean` loses required native wrappers.
                self.assertEqual(cmd[-2:], ["lean", lp.CENSUS_FILE])
                self.assertNotIn("env", cmd)
            out = census_stdout if cmd[-1] == lp.CENSUS_FILE else "Build completed successfully.\n"
            return lp.subprocess.CompletedProcess(cmd, 0, stdout=out)

        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(lp, "find_lake", return_value=Path(lp.__file__)), mock.patch.object(
            lp, "run", side_effect=fake_run
        ), redirect_stdout(out), redirect_stderr(err):
            code = lp.main(["--root", str(ROOT), "--require"])
        return code, out.getvalue() + err.getvalue()

    def test_a_census_without_the_replay_is_refused(self):
        code, text = self.run_main("lean-proofs census: modules=50 safe-constants=6916 imported-modules=IMPORTED\n")
        self.assertEqual(code, 1, text)
        self.assertIn("replay: the census line has no numeric `replayed=` field", text)

    def test_a_census_with_a_whole_ledger_passes(self):
        code, text = self.run_main(
            "lean-proofs census: modules=50 safe-constants=6916 imported-modules=IMPORTED "
            "replayed=6839 replay-evaluations=462 replay-skipped-partial=77\n"
        )
        self.assertEqual(code, 0, text)
        self.assertIn("lean-proofs: PASS", text)


class WithoutLake(unittest.TestCase):
    def run_main(self, *argv):
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(lp, "find_lake", return_value=None), mock.patch.dict(
            "os.environ", {"TRUST_IR_REQUIRE_LEAN": "0"}
        ), redirect_stdout(out), redirect_stderr(err):
            code = lp.main(["--root", str(ROOT), *argv])
        return code, out.getvalue() + err.getvalue()

    def test_a_missing_lake_is_a_loud_skip(self):
        code, text = self.run_main()
        self.assertEqual(code, 0, text)
        self.assertIn("SKIP", text)
        self.assertIn("no (lean-theorem) row", text)

    def test_a_missing_lake_fails_when_the_build_is_required(self):
        code, text = self.run_main("--require")
        self.assertEqual(code, 1, text)
        self.assertIn("required", text)


class TheGateIsWired(unittest.TestCase):
    def test_ci_gates_requires_the_build_where_gate_12_does(self):
        text = (ROOT / "scripts" / "ci_gates.sh").read_text(encoding="utf-8")
        self.assertRegex(text, r"(?m)^gate lean-proofs lean_proofs$")
        body = text[text.index("lean_proofs() {") :]
        body = body[: body.index("\n}\n")]
        self.assertIn('[[ -x "$HOME/.elan/bin/lake" ]]', body)
        required, _, optional = body.partition("else")
        self.assertIn("--require", required)
        self.assertNotIn("--require", optional)


if __name__ == "__main__":
    unittest.main()
