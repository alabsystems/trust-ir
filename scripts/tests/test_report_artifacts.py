"""Artifact custody at a real Git history cut, through the public Store API.

The fixtures commit original binary bytes, then remove them from HEAD and
commit the locator catalog. These are functional transport/refusal tests;
they do not manufacture or replay a semantic proof.
"""

from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import os
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any, Dict, Optional

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from report_artifacts import ArtifactError, Store  # noqa: E402


CATALOG_REL = Path("reports/report-artifacts.json")
FIRST_PATH = "reports/pkg/chunk-000.bin"
SECOND_PATH = "reports/pkg/chunk-001.bin"
FIRST_BYTES = b"original\x00chunk\xff\x80\n"
SECOND_BYTES = b"second chunk\x00\x7f\n"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def clean_git_environment() -> Dict[str, str]:
    """Keep each temporary repo independent of inherited Git selectors."""
    env = dict(os.environ)
    for name in list(env):
        if name in {
            "GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR",
            "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES",
            "GIT_NAMESPACE", "GIT_GRAFT_FILE", "GIT_SHALLOW_FILE",
            "GIT_CONFIG", "GIT_CONFIG_PARAMETERS", "GIT_CONFIG_COUNT",
        } or name.startswith(("GIT_CONFIG_KEY_", "GIT_CONFIG_VALUE_")):
            env.pop(name)
    env.update(
        GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
        GIT_TERMINAL_PROMPT="0", GIT_NO_REPLACE_OBJECTS="1",
        GIT_GRAFT_FILE=os.devnull,
    )
    return env


class RealGitCut:
    """An original source commit followed by a catalog-only HEAD."""

    def __init__(self, root: Path) -> None:
        self.root = root
        root.mkdir()
        self.env = clean_git_environment()
        self.git("init", "-q", "--template=")
        self.git("config", "user.name", "Artifact transport fixture")
        self.git("config", "user.email", "artifact-fixture@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        self.git("config", "core.filemode", "true")
        self.payloads = {FIRST_PATH: FIRST_BYTES, SECOND_PATH: SECOND_BYTES}
        for name, payload in self.payloads.items():
            target = root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(payload)
            target.chmod(0o755 if name == FIRST_PATH else 0o644)
        self.git("add", "--", *self.payloads)
        self.git("commit", "-qm", "original immutable artifacts")
        self.source = self.git("rev-parse", "HEAD")
        self.tree = self.git("rev-parse", "HEAD^{tree}")
        self.records = [self.record(name, payload, self.source)
                        for name, payload in self.payloads.items()]
        self.catalog = {
            "schema": "trust-ir.report-artifacts.v1",
            "sources": [{
                "commit": self.source,
                "tree": self.tree,
                "repository": "example/repo",
            }],
            "artifacts": self.records,
            "inline_fixture": None,
        }
        self.git("rm", "-q", "--", *self.payloads)
        self.write_catalog(self.catalog)
        self.git("add", "--", str(CATALOG_REL))
        self.git("commit", "-qm", "remove generated artifacts from HEAD")
        self.cut = self.git("rev-parse", "HEAD")
        self.cut_tree = self.git("rev-parse", "HEAD^{tree}")

    def git(self, *arguments: str) -> str:
        done = subprocess.run(
            ["git", "-C", str(self.root), *arguments], env=self.env,
            capture_output=True, check=False,
        )
        if done.returncode:
            raise AssertionError((arguments, done.returncode, done.stderr))
        return done.stdout.decode().strip()

    def record(self, path: str, data: bytes, source: str) -> Dict[str, Any]:
        mode = "100755" if path == FIRST_PATH else "100644"
        return {
            "path": path, "source": source, "mode": mode,
            "git_blob": self.git("rev-parse", source + ":" + path),
            "bytes": len(data), "sha256": digest(data),
        }

    def write_catalog(self, value: Dict[str, Any]) -> None:
        target = self.root / CATALOG_REL
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")

    def add_second_source(self, data: bytes) -> str:
        target = self.root / FIRST_PATH
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        target.chmod(0o755)
        self.git("add", "--", FIRST_PATH)
        self.git("commit", "-qm", "a distinct immutable version")
        source = self.git("rev-parse", "HEAD")
        tree = self.git("rev-parse", "HEAD^{tree}")
        self.catalog["sources"].append({
            "commit": source, "tree": tree, "repository": "example/repo",
        })
        self.catalog["artifacts"].append(self.record(FIRST_PATH, data, source))
        self.git("rm", "-q", "--", FIRST_PATH)
        self.write_catalog(self.catalog)
        self.git("add", "--", str(CATALOG_REL))
        self.git("commit", "-qm", "retain both versions outside HEAD")
        return source


class ReportArtifactCustodyTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="report-artifact-api-")
        self.addCleanup(self.temporary.cleanup)
        self.work = Path(self.temporary.name)
        self.repo = RealGitCut(self.work / "repo")
        self.root = self.repo.root

    def read(self, path: str = FIRST_PATH, source: Optional[str] = None,
             root: Optional[Path] = None) -> bytes:
        with Store(root or self.root, fetch=False).open(path, source=source) as payload:
            self.assertTrue(payload.seekable())
            data = payload.read()
            payload.seek(0)
            self.assertEqual(payload.read(), data)
            return data

    def assert_catalog_refused(self, catalog: Dict[str, Any]) -> None:
        self.repo.write_catalog(catalog)
        with self.assertRaises(ArtifactError):
            self.read()

    def test_original_git_bytes_remain_seekable_after_head_deletion(self) -> None:
        self.assertNotEqual(self.repo.source, self.repo.cut)
        self.assertFalse((self.root / FIRST_PATH).exists())
        self.assertNotIn(FIRST_PATH, self.repo.git("ls-files").splitlines())
        self.assertEqual(self.read(), FIRST_BYTES)
        self.assertEqual(self.read(SECOND_PATH), SECOND_BYTES)
        self.assertIsInstance(Store(self.root, fetch=False).check_index(), dict)

    def test_another_valid_blob_cannot_impersonate_the_original_source_path(self) -> None:
        catalog = copy.deepcopy(self.repo.catalog)
        other = catalog["artifacts"][1]
        target = catalog["artifacts"][0]
        # A complete, internally consistent payload substitution must still
        # fail the independent source-tree/path association.
        for name in ("git_blob", "bytes", "sha256"):
            target[name] = other[name]
        self.assert_catalog_refused(catalog)

    def test_incorrect_payload_digest_is_refused(self) -> None:
        catalog = copy.deepcopy(self.repo.catalog)
        catalog["artifacts"][0]["sha256"] = "0" * 64
        self.assert_catalog_refused(catalog)

    def test_incorrect_payload_length_is_refused(self) -> None:
        catalog = copy.deepcopy(self.repo.catalog)
        catalog["artifacts"][0]["bytes"] += 1
        self.assert_catalog_refused(catalog)

    def test_a_real_commit_without_that_path_is_not_the_artifact_source(self) -> None:
        catalog = copy.deepcopy(self.repo.catalog)
        catalog["sources"][0].update(commit=self.repo.cut, tree=self.repo.cut_tree)
        for row in catalog["artifacts"]:
            row["source"] = self.repo.cut
        self.assert_catalog_refused(catalog)
        self.repo.write_catalog(self.repo.catalog)
        with self.assertRaises(ArtifactError):
            self.read(source="f" * 40)

    def test_a_real_but_wrong_tree_does_not_bind_the_source_commit(self) -> None:
        catalog = copy.deepcopy(self.repo.catalog)
        catalog["sources"][0]["tree"] = self.repo.cut_tree
        self.assert_catalog_refused(catalog)

    def test_missing_original_git_objects_refuse_with_fetch_disabled(self) -> None:
        empty = self.work / "empty-repository"
        empty.mkdir()
        subprocess.run(["git", "init", "-q", "--template=", str(empty)], check=True,
                       capture_output=True, env=clean_git_environment())
        path = empty / CATALOG_REL
        path.parent.mkdir(parents=True)
        path.write_text(json.dumps(self.repo.catalog))
        # This repository has the genuine locator but none of its object
        # authority. fetch=False cannot silently substitute other bytes.
        with self.assertRaises(ArtifactError):
            self.read(root=empty)

    def test_two_versions_are_ambiguous_until_the_original_source_is_selected(self) -> None:
        second_bytes = b"a genuinely different second version\x00"
        second_source = self.repo.add_second_source(second_bytes)
        with self.assertRaises(ArtifactError):
            self.read()
        self.assertEqual(self.read(source=self.repo.source), FIRST_BYTES)
        self.assertEqual(self.read(source=second_source), second_bytes)
        destination = self.work / "mixed-versions"
        with self.assertRaises(ArtifactError):
            Store(self.root, fetch=False).materialize("reports/pkg/", destination)
        self.assertFalse(destination.exists())
        selected = Store(self.root, fetch=False).materialize(
            "reports/pkg/", destination, source=second_source)
        self.assertEqual({row["path"] for row in selected["files"]}, {FIRST_PATH})
        self.assertTrue(all(row["source"] == second_source for row in selected["files"]))
        self.assertEqual((destination / FIRST_PATH).read_bytes(), second_bytes)
        self.assertFalse((destination / SECOND_PATH).exists())

    def test_catalog_schema_rejects_unknown_fields_and_wrong_typed_authority(self) -> None:
        mutations = [
            ("unknown header", lambda c: c.update(authority="Certified")),
            ("unknown source", lambda c: c["sources"][0].update(trusted=True)),
            ("unknown artifact", lambda c: c["artifacts"][0].update(verified=True)),
            ("Boolean byte count", lambda c: c["artifacts"][0].update(bytes=True)),
            ("negative byte count", lambda c: c["artifacts"][0].update(bytes=-1)),
            ("floating byte count", lambda c: c["artifacts"][0].update(bytes=1.0)),
            ("invalid mode", lambda c: c["artifacts"][0].update(mode="100600")),
            ("symbolic commit", lambda c: c["sources"][0].update(commit="HEAD")),
            ("missing source binding", lambda c: c["artifacts"][0].pop("source")),
            ("missing payload digest", lambda c: c["artifacts"][0].pop("sha256")),
            ("invalid blob digest", lambda c: c["artifacts"][0].update(git_blob="x" * 40)),
            ("non-list artifacts", lambda c: c.update(artifacts={})),
            ("non-object artifact", lambda c: c["artifacts"].__setitem__(0, None)),
        ]
        for name, mutate in mutations:
            with self.subTest(name=name):
                catalog = copy.deepcopy(self.repo.catalog)
                mutate(catalog)
                self.assert_catalog_refused(catalog)

    def test_duplicate_json_keys_sources_and_artifact_identities_are_refused(self) -> None:
        for name in ("source", "artifact"):
            with self.subTest(duplicate=name):
                catalog = copy.deepcopy(self.repo.catalog)
                key = "sources" if name == "source" else "artifacts"
                catalog[key].append(copy.deepcopy(catalog[key][0]))
                self.assert_catalog_refused(catalog)
        raw = json.dumps(self.repo.catalog)
        raw = '{"schema":"trust-ir.report-artifacts.v1",' + raw[1:]
        (self.root / CATALOG_REL).write_text(raw)
        with self.assertRaises(ArtifactError):
            self.read()

    def test_unknown_and_noncanonical_paths_do_not_alias_a_catalog_identity(self) -> None:
        for path in ("reports/missing.bin", "../" + FIRST_PATH,
                     "reports/../" + FIRST_PATH, "/" + FIRST_PATH,
                     "./" + FIRST_PATH):
            with self.subTest(request=path), self.assertRaises(ArtifactError):
                self.read(path)
        for path in ("../escape.bin", "reports/pkg/../chunk-000.bin"):
            with self.subTest(catalog_path=path):
                catalog = copy.deepcopy(self.repo.catalog)
                catalog["artifacts"][0]["path"] = path
                self.assert_catalog_refused(catalog)

    def test_exact_external_materialization_preserves_identity_mode_and_verified_reuse(self) -> None:
        # A sibling sharing the repository's string prefix is still external.
        destination = Path(str(self.root) + "-artifacts")
        store = Store(self.root, fetch=False)
        first = store.materialize(FIRST_PATH, destination)
        target = destination / FIRST_PATH
        self.assertEqual(target.read_bytes(), FIRST_BYTES)
        self.assertEqual(stat.S_IMODE(target.stat().st_mode), 0o755)
        first_stat = target.stat()
        second = store.materialize(FIRST_PATH, destination)
        self.assertEqual(target.read_bytes(), FIRST_BYTES)
        self.assertEqual(target.stat().st_ino, first_stat.st_ino)
        self.assertEqual(target.stat().st_mtime_ns, first_stat.st_mtime_ns)
        for receipt, reused in ((first, False), (second, True)):
            self.assertIsInstance(receipt, dict)
            self.assertEqual(len(receipt["files"]), 1)
            row = receipt["files"][0]
            for name, value in self.repo.records[0].items():
                self.assertEqual(row[name], value, name)
            self.assertIs(row["reused"], reused)

    def test_prefix_materialization_keeps_every_original_relative_name(self) -> None:
        destination = self.work / "full-prefix"
        receipt = Store(self.root, fetch=False).materialize("reports/pkg/", destination)
        self.assertEqual({row["path"] for row in receipt["files"]}, set(self.repo.payloads))
        self.assertEqual({q.relative_to(destination).as_posix()
                          for q in destination.rglob("*") if q.is_file()},
                         set(self.repo.payloads))
        for record in self.repo.records:
            target = destination / record["path"]
            self.assertEqual(target.read_bytes(), self.repo.payloads[record["path"]])
            self.assertEqual(stat.S_IMODE(target.stat().st_mode),
                             int(record["mode"][-3:], 8))

    def test_materialization_inside_source_or_its_physical_alias_refuses(self) -> None:
        alias = self.work / "repo-alias"
        alias.symlink_to(self.root, target_is_directory=True)
        for destination in (self.root / ".restored", self.root / "reports/restored",
                            alias / ".aliased-restore"):
            with self.subTest(destination=str(destination)), self.assertRaises(ArtifactError):
                Store(self.root, fetch=False).materialize(FIRST_PATH, destination)
            self.assertFalse(destination.exists())
        self.assertFalse((self.root / FIRST_PATH).exists())

    def test_symlink_destination_and_intermediate_redirect_refuse(self) -> None:
        outside = self.work / "outside"
        outside.mkdir()
        alias = self.work / "destination-alias"
        alias.symlink_to(outside, target_is_directory=True)
        with self.assertRaises(ArtifactError):
            Store(self.root, fetch=False).materialize(FIRST_PATH, alias)
        self.assertEqual(list(outside.iterdir()), [])
        destination = self.work / "redirected-prefix"
        (destination / "reports").mkdir(parents=True)
        (destination / "reports/pkg").symlink_to(outside, target_is_directory=True)
        with self.assertRaises(ArtifactError):
            Store(self.root, fetch=False).materialize(FIRST_PATH, destination)
        self.assertEqual(list(outside.iterdir()), [])
        self.assertTrue((destination / "reports/pkg").is_symlink())

    def test_mismatched_existing_destination_is_not_overwritten_or_repaired(self) -> None:
        destination = self.work / "existing"
        target = destination / FIRST_PATH
        target.parent.mkdir(parents=True)
        wrong = b"different evidence must remain visible"
        target.write_bytes(wrong)
        with self.assertRaises(ArtifactError):
            Store(self.root, fetch=False).materialize(FIRST_PATH, destination)
        self.assertEqual(target.read_bytes(), wrong)

    def test_corrupt_existing_source_file_is_not_silently_repaired_from_history(self) -> None:
        source = self.root / FIRST_PATH
        source.parent.mkdir(parents=True, exist_ok=True)
        wrong = b"uncommitted impostor\x00"
        source.write_bytes(wrong)
        source.chmod(0o755)
        with self.assertRaises(ArtifactError):
            self.read()
        self.assertEqual(source.read_bytes(), wrong)

    def test_current_index_guard_refuses_reintroduced_and_unregistered_archives(self) -> None:
        # The fixture's initial HEAD has no artifacts and check_index passes.
        self.assertIsInstance(Store(self.root, fetch=False).check_index(), dict)
        for path, data in ((FIRST_PATH, FIRST_BYTES),
                           ("reports/new/unregistered.bin", b"new generated payload")):
            with self.subTest(path=path):
                target = self.root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
                self.repo.git("add", "--", path)
                with self.assertRaises(ArtifactError):
                    Store(self.root, fetch=False).check_index()
                self.repo.git("rm", "-q", "--cached", "--", path)
                target.unlink()


    def _refusal_in_child(self, destination: Path) -> None:
        # A broken reader must not hang this focused control on a FIFO.
        program = """import sys
from pathlib import Path
sys.path.insert(0, sys.argv[1])
from report_artifacts import ArtifactError, Store
try:
    Store(Path(sys.argv[2]), fetch=False).materialize(sys.argv[3], Path(sys.argv[4]))
except ArtifactError:
    raise SystemExit(0)
raise SystemExit(9)
"""
        done = subprocess.run(
            [sys.executable, "-B", "-c", program,
             str(Path(__file__).resolve().parents[1]), str(self.root), FIRST_PATH, str(destination)],
            capture_output=True, timeout=3, check=False,
        )
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)

    def test_fifo_destination_refuses_without_waiting_for_a_writer(self) -> None:
        if not hasattr(os, "mkfifo"):
            self.skipTest("host has no FIFO filesystem primitive")
        destination = self.work / "fifo-destination"
        target = destination / FIRST_PATH
        target.parent.mkdir(parents=True)
        os.mkfifo(target, 0o755)
        self._refusal_in_child(destination)
        self.assertTrue(stat.S_ISFIFO(target.lstat().st_mode))

    def test_oversized_destination_refuses_without_overwrite(self) -> None:
        destination = self.work / "oversized-destination"
        target = destination / FIRST_PATH
        target.parent.mkdir(parents=True)
        with target.open("wb") as stream:
            stream.write(FIRST_BYTES)
            stream.truncate(256 * 1024 * 1024)
        target.chmod(0o755)
        self._refusal_in_child(destination)
        self.assertEqual(target.stat().st_size, 256 * 1024 * 1024)
        with target.open("rb") as stream:
            self.assertEqual(stream.read(len(FIRST_BYTES)), FIRST_BYTES)

    def test_catalog_cannot_rebind_the_standing_fixture_allowance(self) -> None:
        prefix = "reports/2026-09-17-two-language-proof-program/"
        payload = self.root / (prefix + "new.bin")
        payload.parent.mkdir(parents=True)
        payload.write_bytes(b"new generated binary, not the reviewed standing fixture")
        manifest = self.root / (prefix + "MANIFEST.sha256")
        manifest.write_text(digest(payload.read_bytes()) + "  new.bin\n")
        self.repo.git("add", "--", prefix)
        self.repo.git("commit", "-qm", "an alternate self-sealed fixture")
        source = self.repo.git("rev-parse", "HEAD")
        catalog = copy.deepcopy(self.repo.catalog)
        catalog["sources"].append({
            "commit": source, "tree": self.repo.git("rev-parse", "HEAD^{tree}"),
            "repository": "example/repo",
        })
        catalog["inline_fixture"] = {
            "prefix": prefix, "source": source,
            "manifest_path": prefix + "MANIFEST.sha256",
            "manifest_sha256": digest(manifest.read_bytes()),
            "manifest_git_blob": self.repo.git("rev-parse", source + ":" + prefix + "MANIFEST.sha256"),
            "files": 2, "bytes": payload.stat().st_size + manifest.stat().st_size,
        }
        self.repo.write_catalog(catalog)
        with self.assertRaises(ArtifactError):
            Store(self.root, fetch=False).check_index()


class CurrentReportTreePolicy(unittest.TestCase):
    def test_current_index_preserves_fixture_and_excludes_generated_archives(self):
        root = Path(__file__).resolve().parents[2]
        if not (root / "reports/report-artifacts.json").is_file():
            spec = importlib.util.spec_from_file_location(
                "report_artifact_snapshot_boundary", root / "scripts/check_enforcement_links.py"
            )
            if spec is None or spec.loader is None:
                self.fail("source artifact catalog and snapshot classifier are missing")
            classifier = importlib.util.module_from_spec(spec)
            sys.modules[spec.name] = classifier
            spec.loader.exec_module(classifier)
            if classifier.is_public_snapshot(root):
                self.skipTest("public snapshot: internal report/catalog data is not exported")
        result = Store(root, fetch=False).check_index()
        self.assertGreater(result["archive_files"], 0)
        self.assertEqual(result["inline_fixture_files"], 1349)
        # The obsolete helper is captured DATA, never an active absolute Cargo
        # dependency. Retrieve its exact historical manifest through public custody.
        captured = "reports/2026-11-08-source-value-operational/evidence/actual-clean-profile/inspector/Cargo.toml"
        self.assertFalse((root / captured).exists())
        with tempfile.TemporaryDirectory() as destination:
            receipt = Store(root, fetch=False).materialize(
                captured, Path(destination), "406f6856055038259ed6ae36981858eab540a574")
            self.assertEqual(len(receipt["files"]), 1)
            original = (Path(destination) / captured).read_bytes()
            self.assertEqual(len(original), 305)
            self.assertEqual(digest(original), "2730a54825ba8136546f01142dae59af12b6dad485d33033b4ea0e863ad53803")
            # The digest above pins the bytes. This states what they are (an
            # absolute dependency path under the producer's home) by shape,
            # so the test does not repeat that machine's account name.
            self.assertRegex(
                original.decode("utf-8"),
                r"/Users/[^/]+/trust-ir-worktrees/source-value-operational\.noindex/crates/trust-ir")



if __name__ == "__main__":
    unittest.main()
