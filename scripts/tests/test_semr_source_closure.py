"""Source projection regressions; no compiler, publication service or credentials."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from scripts import check_semr_source_closure as closure


class ClosureTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for package in closure.PACKAGES:
            self.put(package + "/lean-toolchain", "leanprover/lean4:v4.30.0-rc2\n")
            self.put(package + "/lake-manifest.json", '{"packages": []}')
            self.put(package + "/lakefile.lean", "import Lake\n")
        self.put("lean/semr/lakefile.lean", "import Lake\nlean_lib SemR where\nlean_exe oracle where\n  root := `Main\n")
        self.put("lean/semr/SemR.lean", "import Init\n")
        self.put("lean/semr/Main.lean", "import SemR\n")
        self.put("lean/semr/FRAGMENT.tsv", "fixture\n")
        self.put("lean/semr/QUOTED_MODEL.tsv", "fixture\n")
        self.put("lean/semr/fixtures/input.bin", "bytes")
        self.put("lean/semr-memory/SemRFrameMemory.lean", "import SemR\n")
        self.put("lean/semr-memory/SemRFrameChecks.lean", "import SemRFrameMemory\n")
        self.put("lean/semr-memory/FrameAudit.lean", "import Lean\nimport SemRFrameChecks\n")
        self.put("lean/semr-memory/frame-audit-refusals.json", "{}")
        self.put("crates/probe/src/lib.rs", 'const B: &[u8] = include_bytes!("../../../lean/semr/fixtures/input.bin");\n')
        self.put("THIRD_PARTY.md", "fixture notices")
        self.put("NOTICE", "fixture notices")
        revision = "1" * 40
        self.put("lean/semr/MiniRust.lean", "-- from MiniRust " + revision + "\n")
        licenses = {}
        for name in ("MIT", "APACHE"):
            path = "LICENSES/MiniRust-" + name + ".txt"
            self.put(path, name)
            data = (self.root / path).read_bytes()
            licenses[path] = {"sha256": hashlib.sha256(data).hexdigest(),
                "git_blob_sha1": hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()}
        self.put("LICENSES/MiniRust.json", json.dumps({"schema": 1, "revision": revision,
            "translation": "lean/semr/MiniRust.lean", "translation_sha256": hashlib.sha256(
                (self.root / "lean/semr/MiniRust.lean").read_bytes()).hexdigest(), "license_files": licenses}))

    def put(self, path, text):
        file = self.root / path
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(text)

    def problems(self, excluded=()):
        return closure.check(self.root, closure.files(self.root) - set(excluded))["problems"]

    def test_complete_input_tree(self):
        self.assertEqual(self.problems(), [])

    def test_missing_compile_time_fixture_is_reported(self):
        self.assertIn("missing source input: lean/semr/fixtures/input.bin",
                      self.problems(["lean/semr/fixtures/input.bin"]))

    def test_raw_literal_include_is_checked(self):
        self.put("crates/probe/src/lib.rs", 'const B: &[u8] = include_bytes!(r#"../../../lean/semr/fixtures/missing.bin"#);')
        self.assertIn("missing source input: lean/semr/fixtures/missing.bin", self.problems())

    def test_examples_in_comments_and_strings_are_not_includes(self):
        self.put("crates/probe/src/lib.rs", '// include_bytes!("../../../lean/semr/missing.bin")\nconst S: &str = r#"include_str!("../../../lean/semr/missing.lean")"#;')
        self.assertEqual(self.problems(), [])

    def test_missing_import_is_reported(self):
        self.assertTrue(any("missing Lean import:" in p for p in
                            self.problems(["lean/semr-memory/SemRFrameMemory.lean"])))

    def test_unimported_declared_library_root_is_required(self):
        self.put("lean/semr/lakefile.lean", "import Lake\nlean_lib Optional where\n")
        self.assertIn("missing source input: lean/semr/Optional.lean", self.problems())

    def test_toml_target_root_is_required(self):
        (self.root / "lean/semr-memory/lakefile.lean").unlink()
        self.put("lean/semr-memory/lakefile.toml", 'name = "proofs"\n[[lean_lib]]\nname = "Absent"\n')
        self.assertIn("missing source input: lean/semr-memory/Absent.lean", self.problems())

    def test_local_dependency_cannot_escape_projection(self):
        self.put("lean/semr-memory/lake-manifest.json", json.dumps({"packages": [{
            "type": "path", "dir": "../../../outside", "configFile": "lakefile.lean"}]}))
        self.assertTrue(any("escaping Lean dependency:" in p for p in self.problems()))

    def test_changed_license_and_translation_are_reported(self):
        self.put("LICENSES/MiniRust-MIT.txt", "changed")
        self.put("lean/semr/MiniRust.lean", "changed")
        problems = self.problems()
        self.assertIn("upstream license bytes changed: LICENSES/MiniRust-MIT.txt", problems)
        self.assertIn("MiniRust translation identity changed", problems)
        self.assertIn("MiniRust revision marker disagrees with provenance", problems)

    def test_escaping_fixture_symlink_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            outside = Path(directory) / "outside.bin"
            outside.write_bytes(b"outside")
            file = self.root / "lean/semr/fixtures/input.bin"
            file.unlink()
            file.symlink_to(outside)
            self.assertIn("escaping source input: lean/semr/fixtures/input.bin", self.problems())

    def fixture_manifest(self, file="input.bin"):
        self.put("lean/semr/fixtures/model/MANIFEST.json", json.dumps({
            "schema": "trust.generic-scalar-model-fixtures.v1", "fixtures": [{
                "file": file, "bytes": 5, "sha256": hashlib.sha256(b"bytes").hexdigest()}]}))

    def test_fixture_manifest_binds_actual_bytes(self):
        self.fixture_manifest()
        self.assertEqual(self.problems(), [])
        self.put("lean/semr/fixtures/input.bin", "other")
        self.assertIn("SemR fixture bytes changed: lean/semr/fixtures/input.bin", self.problems())

    def test_fixture_manifest_cannot_escape_its_source_area(self):
        self.fixture_manifest("../../../NOTICE")
        self.assertTrue(any("escaping SemR fixture:" in p for p in self.problems()))

    def test_exclude_only_manifest_is_refused(self):
        manifest = self.root / "manifest.txt"
        manifest.write_text("!private/\n")
        with self.assertRaises(ValueError):
            closure.manifest_selection(self.root, manifest)

    def test_old_allowlist_omission_and_fixed_directory_selection(self):
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        manifest = self.root / "manifest.txt"
        manifest.write_text("crates/\nlean/trust_ir-semantics/\nLICENSES/\nNOTICE\nTHIRD_PARTY.md\n")
        self.assertTrue(closure.check(self.root, closure.manifest_selection(self.root, manifest))["problems"])
        manifest.write_text(manifest.read_text() + "lean/semr/\nlean/semr-memory/\n")
        self.assertEqual(closure.check(self.root, closure.manifest_selection(self.root, manifest))["problems"], [])


class RepositoryRegression(unittest.TestCase):
    def test_snapshot_or_source_policy_contains_semr_inputs(self):
        root = Path(__file__).resolve().parents[2]
        manifest = root / "publish/manifest.txt"
        selected = closure.manifest_selection(root, manifest) if manifest.exists() else closure.files(root)
        self.assertEqual(closure.check(root, selected)["problems"], [])


if __name__ == "__main__":
    unittest.main()
