"""WS8.1: the archived 2026-09-17 two-language proof program is a STANDING check.

`reports/2026-09-17-two-language-proof-program/check_archive.sh` holds the
archive to its three WS8.1 gates (manifest, row resolution, publish boundary)
and two supporting checks (no live pin, every cited cache path archived), each
with its twin. Until this file it ran only when someone remembered to: no
standing gate invoked it, so a re-collection, an edited evidence file or a
`publish/manifest.txt` that started exporting `reports/` would have gone
unnoticed. Gate 0's `internal-gate-tests` (`scripts/run_script_tests.sh`) runs
every `scripts/tests/test_*.py`, so this file puts the check on the standing
gate without a new `ci_gates.sh` step.

The cases:

* the live archive passes, every one of its gates and twins (the positive);
* the same archive with one byte flipped, in a scratch repository, FAILS with
  the manifest gate named (the negative twin: the wiring can go red), and so
  does a `publish/manifest.txt` that allowlists `reports/`;
* a checkout that is not a public snapshot but has no archive FAILS rather than
  skipping (the mutation control: deleting the archive is not a way to pass),
  and so does an archive copied out of any repository;
* a `*.md` glob in the allowlist, which reaches the archive's Markdown, FAILS
  the publish gate, while the same scratch tree reached under a differently
  cased path (a case-insensitive volume) PASSES rather than being refused.

The public snapshot never ships `reports/` (nor `docs/`), so there, and only
there, the live case is skipped. The snapshot test is the one
`check_enforcement_links.py` uses, so the two cannot disagree about what a
snapshot is.
"""

from __future__ import annotations

import importlib.util
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Tuple

ROOT = Path(__file__).resolve().parents[2]
ARCHIVE_REL = Path("reports") / "2026-09-17-two-language-proof-program"
CHECK = "check_archive.sh"
# The whole run takes about 6 s (measured 2026-10-01); a hung `shasum` or
# `git` must not hold gate 0 for ever.
TIMEOUT_SECONDS = 600

_SPEC = importlib.util.spec_from_file_location(
    "check_enforcement_links_for_archive", ROOT / "scripts" / "check_enforcement_links.py"
)
assert _SPEC is not None and _SPEC.loader is not None
_LINKS = importlib.util.module_from_spec(_SPEC)
sys.modules[_SPEC.name] = _LINKS
_SPEC.loader.exec_module(_LINKS)


def archive_verdict(root: Path) -> Tuple[str, str]:
    """`("skip", why)` in a public snapshot, else `("pass"|"fail", output)`.

    A missing archive or a missing checker in a non-snapshot tree is a
    FAILURE, never a skip."""
    if _LINKS.is_public_snapshot(root):
        return "skip", "public snapshot: reports/ is not exported, so there is no archive to check"
    check = root / ARCHIVE_REL / CHECK
    if not check.is_file():
        return "fail", f"{ARCHIVE_REL / CHECK} is missing from a development checkout"
    done = subprocess.run(
        ["bash", str(check)],
        cwd=root,
        capture_output=True,
        text=True,
        timeout=TIMEOUT_SECONDS,
        check=False,
    )
    output = done.stdout + done.stderr
    ok = done.returncode == 0 and "RESULT: PASS" in done.stdout and "FAIL  " not in output
    return ("pass" if ok else "fail"), output


def scratch_repository(tmp: Path) -> Path:
    """A minimal git work tree carrying what `check_archive.sh` reads: the
    archive, `scripts/pin_rewrite.py` (the pin rule), `publish/manifest.txt`
    and `Cargo.toml` (the export it computes), and a `docs/` marker so the
    tree is a development checkout, not a snapshot. Nothing is committed: the
    checker reads tracked AND untracked files.

    The tree is returned through a SYMLINK, on purpose: `git rev-parse
    --show-toplevel` answers the physical path, and before the checker
    resolved its own directory physically the archive's path never stripped
    against it, so the publish gate searched the export for an absolute path
    and passed vacuously (measured 2026-10-01 under macOS's /var ->
    /private/var). Every scratch case below runs through that shape."""
    real = tmp / "real-repo"
    subprocess.run(["git", "init", "-q", str(real)], check=True)
    dest = tmp / "repo"
    dest.symlink_to(real, target_is_directory=True)
    shutil.copytree(ROOT / ARCHIVE_REL, dest / ARCHIVE_REL, ignore=shutil.ignore_patterns("__pycache__"))
    for rel in ("scripts/pin_rewrite.py", "publish/manifest.txt", "Cargo.toml"):
        (dest / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / rel, dest / rel)
    (dest / "docs").mkdir()
    return dest


class TheArchiveIsAStandingCheck(unittest.TestCase):
    def test_the_archived_proof_program_passes_every_gate_and_twin(self) -> None:
        verdict, output = archive_verdict(ROOT)
        if verdict == "skip":
            self.skipTest(output)
        self.assertEqual(verdict, "pass", output)
        for gate in ("manifest:", "manifest twin:", "pins:", "rows:", "rows twin:", "paths:", "publish:", "publish twin:"):
            self.assertIn(f"PASS  {gate}", output, f"{gate} did not run\n{output}")

    def test_a_one_byte_edit_turns_the_standing_check_red(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = scratch_repository(Path(tmp))
            # The control: the unmutated scratch copy passes, so the red
            # below is the edit's doing and not the scratch layout's.
            verdict, output = archive_verdict(repo)
            self.assertEqual(verdict, "pass", output)
            self.assertRegex(output, r"PASS  publish: \d+ exported paths, none under reports/")
            target = repo / ARCHIVE_REL / "roadmap" / "FINDINGS.json"
            data = bytearray(target.read_bytes())
            data[len(data) // 3] ^= 0x01
            target.write_bytes(bytes(data))
            verdict, output = archive_verdict(repo)
            self.assertEqual(verdict, "fail", output)
            self.assertIn("FAIL  manifest: shasum -c failed", output)

    def test_publishing_reports_turns_the_standing_check_red(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = scratch_repository(Path(tmp))
            manifest = repo / "publish" / "manifest.txt"
            manifest.write_text(manifest.read_text(encoding="utf-8") + "\nreports/\n", encoding="utf-8")
            verdict, output = archive_verdict(repo)
            self.assertEqual(verdict, "fail", output)
            self.assertRegex(output, r"FAIL  publish: \d+ archived path\(s\) are in the public export")

    def test_a_differently_cased_path_is_checked_not_refused(self) -> None:
        # A case-insensitive volume (macOS's default) reaches the same tree
        # under another spelling of the path; git's top-level is canonically
        # cased. Stripping one spelling off the other used to leave the
        # archive's path absolute: a legitimate archive was refused as a bad
        # layout (and, before the refusal, the publish gate passed vacuously).
        with tempfile.TemporaryDirectory() as tmp:
            repo = scratch_repository(Path(tmp))
            recased = Path(tmp) / "REAL-REPO"
            if not recased.is_dir():
                self.skipTest("case-sensitive volume: no second spelling of the path exists")
            verdict, output = archive_verdict(recased)
            self.assertEqual(verdict, "pass", output)
            self.assertRegex(output, rf"PASS  publish: \d+ exported paths, none under {ARCHIVE_REL.as_posix()}/")
            self.assertTrue(repo.exists())

    def test_a_globbed_allowlist_that_reaches_the_archive_turns_it_red(self) -> None:
        # Not only a literal `reports/` line: git pathspec globs cross `/`,
        # so a `*.md` allowlist exports the archive's Markdown.
        with tempfile.TemporaryDirectory() as tmp:
            repo = scratch_repository(Path(tmp))
            manifest = repo / "publish" / "manifest.txt"
            manifest.write_text(manifest.read_text(encoding="utf-8") + "\n*.md\n", encoding="utf-8")
            verdict, output = archive_verdict(repo)
            self.assertEqual(verdict, "fail", output)
            self.assertRegex(output, r"FAIL  publish: \d+ archived path\(s\) are in the public export")

    def test_an_archive_outside_any_repository_fails(self) -> None:
        # The publish gate needs git's view of the tree; an archive copied out
        # of the repository cannot be placed, and that is a failure, not a pass.
        with tempfile.TemporaryDirectory() as tmp:
            loose = Path(tmp) / "loose"
            shutil.copytree(ROOT / ARCHIVE_REL, loose, ignore=shutil.ignore_patterns("__pycache__"))
            done = subprocess.run(
                ["bash", str(loose / CHECK)],
                cwd=tmp,
                capture_output=True,
                text=True,
                timeout=TIMEOUT_SECONDS,
                check=False,
                env={**os.environ, "GIT_CEILING_DIRECTORIES": tmp},
            )
            self.assertNotEqual(done.returncode, 0, done.stdout + done.stderr)
            self.assertNotIn("RESULT: PASS", done.stdout)

    def test_a_deleted_archive_fails_instead_of_skipping(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = scratch_repository(Path(tmp))
            shutil.rmtree(repo / ARCHIVE_REL)
            verdict, output = archive_verdict(repo)
            self.assertEqual(verdict, "fail", output)
            self.assertIn("is missing from a development checkout", output)

    def test_only_a_public_snapshot_skips(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            snapshot = Path(tmp)
            self.assertEqual(archive_verdict(snapshot)[0], "skip")
            (snapshot / "CLAUDE.md").write_text("", encoding="utf-8")
            self.assertEqual(archive_verdict(snapshot)[0], "fail")


if __name__ == "__main__":
    unittest.main()
