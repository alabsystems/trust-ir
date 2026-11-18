"""The object budget judges every commit a push uploads, not the tip tree.

Each case builds a real Git history and runs scripts/check_object_budget.py
(or the pre-push hook through a real `git push`) on it. The 2026-11-07/08
report archives were committed and later deleted from the tree; a check of
the tip could not see them, and every clone still downloads them.
"""

from __future__ import annotations

import hashlib
import importlib.util
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Dict, Optional

SCRIPTS = Path(__file__).resolve().parents[1]
ROOT = SCRIPTS.parent
CHECKER = SCRIPTS / "check_object_budget.py"
HOOKS = SCRIPTS / "hooks"
sys.path.insert(0, str(SCRIPTS))
import check_object_budget as budget  # noqa: E402

MIB = 1 << 20
FIXTURE = "reports/2026-09-17-two-language-proof-program/"


def noise(size: int, seed: str) -> bytes:
    """Incompressible, deterministic bytes."""
    out = bytearray()
    counter = 0
    while len(out) < size:
        out += hashlib.sha256(f"{seed}:{counter}".encode()).digest()
        counter += 1
    return bytes(out[:size])


def blob_id(data: bytes) -> str:
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def row(path: str, data: bytes) -> str:
    return f"{path}\t{blob_id(data)}\t{len(data)}"


def allowlist(files: Dict[str, bytes]) -> bytes:
    return ("# fixture allowlist\n" + "".join(row(p, d) + "\n" for p, d in sorted(files.items()))).encode()


def disclosing(message: str, *paths: str) -> str:
    return message + "\n\n" + "\n".join(f"{budget.TRAILER}: {p}: reviewed fixture payload" for p in paths) + "\n"


def git_environment() -> Dict[str, str]:
    env = dict(os.environ)
    for name in list(env):
        if name.startswith("GIT_"):
            env.pop(name)
    env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull, GIT_TERMINAL_PROMPT="0")
    return env


class History:
    def __init__(self, root: Path) -> None:
        self.root = root
        self.env = git_environment()
        root.mkdir()
        self.git("init", "-q", "--template=", "-b", "main")
        self.configure()

    def configure(self) -> None:
        self.git("config", "user.name", "Object budget fixture")
        self.git("config", "user.email", "object-budget@example.invalid")
        self.git("config", "commit.gpgsign", "false")

    def git(self, *args: str, check: bool = True) -> subprocess.CompletedProcess:
        done = subprocess.run(["git", "-C", str(self.root), *args], env=self.env, capture_output=True, check=False)
        if check and done.returncode:
            raise AssertionError((args, done.returncode, done.stderr.decode()))
        return done

    def out(self, *args: str) -> str:
        return self.git(*args).stdout.decode().strip()

    def stage(self, files: Dict[str, Optional[bytes]]) -> None:
        for path, data in files.items():
            target = self.root / path
            if data is None:
                target.unlink()
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
        self.git("add", "-A", "-f")

    def commit(self, files: Dict[str, Optional[bytes]], message: str) -> str:
        self.stage(files)
        self.git("commit", "-q", "--allow-empty", "-m", message)
        return self.out("rev-parse", "HEAD")

    def amend(self, files: Dict[str, Optional[bytes]], message: str) -> str:
        self.stage(files)
        self.git("commit", "-q", "--amend", "--allow-empty", "-m", message)
        return self.out("rev-parse", "HEAD")

    def check(self, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run([sys.executable, "-B", str(CHECKER), "--root", str(self.root), *args],
                              env=self.env, capture_output=True, text=True, check=False)


class Verdicts(unittest.TestCase):
    def assert_refused(self, done: subprocess.CompletedProcess, *needles: str) -> None:
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        for needle in needles:
            self.assertIn(needle, done.stderr)

    def assert_passes(self, done: subprocess.CompletedProcess) -> None:
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("OBJECT-BUDGET PASS", done.stdout)


class RangeRules(Verdicts):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="object-budget-")
        self.addCleanup(temporary.cleanup)
        self.work = Path(temporary.name)
        self.repo = History(self.work / "repo")
        self.big = noise(2 * MIB, "big")
        self.sealed = b"\x02sealed"
        self.base = self.repo.commit({
            "README.md": b"fixture\n",
            "data/big.json": self.big,
            "crates/x/tests/fixtures/golden.bin": b"\x00\x01golden",
            FIXTURE + "case.bin": self.sealed,
            budget.ALLOWLIST: allowlist({"data/big.json": self.big}),
        }, "base")
        self.fixture_tree = self.repo.out("rev-parse", f"{self.base}:{FIXTURE.rstrip('/')}")

    def range(self, base: Optional[str] = None) -> subprocess.CompletedProcess:
        return self.repo.check("--range", f"{base or self.base}..HEAD")

    def judged(self, base: Optional[str] = None):
        """The range judged in-process against this history's own sealed tree."""
        return budget.check(self.repo.root, "HEAD", [base or self.base], fixture_tree=self.fixture_tree)

    def test_a_seeded_2_mib_blob_is_refused_until_its_commit_discloses_it(self) -> None:
        new = noise(2 * MIB, "new")
        self.repo.commit({"data/new.json": new}, "add a 2 MiB blob")
        self.assert_refused(self.range(), "size: data/new.json", "2097152 bytes",
                            f"the row `{row('data/new.json', new)}`",
                            "the trailer `Object-Budget: data/new.json: <reason>`")
        self.repo.amend({budget.ALLOWLIST: allowlist({"data/big.json": self.big, "data/new.json": new})},
                        disclosing("add a 2 MiB blob", "data/new.json"))
        self.assert_passes(self.range())

    def test_a_blob_of_exactly_the_budget_passes(self) -> None:
        self.repo.commit({"data/edge.json": noise(MIB, "edge")}, "add exactly 1 MiB")
        self.assert_passes(self.range())

    def test_an_add_then_delete_inside_one_range_is_refused(self) -> None:
        added = self.repo.commit({
            "reports/pkt/chunks/chunk-000.bin": noise(4096, "chunk"),
            "reports/pkt/chunks/chunk-001.BIN": noise(4096, "upper"),
            "reports/pkt/notes.json": noise(2 * MIB, "notes"),
        }, "stage evidence chunks")
        self.repo.commit({"reports/pkt/chunks/chunk-000.bin": None, "reports/pkt/chunks/chunk-001.BIN": None,
                          "reports/pkt/notes.json": None}, "move evidence to custody")
        # The tip tree is the base's: only the commits show the payload.
        self.assertEqual(self.repo.out("rev-parse", "HEAD^{tree}"), self.repo.out("rev-parse", self.base + "^{tree}"))
        self.assert_refused(self.range(),
                            "archive: reports/pkt/chunks/chunk-000.bin", f"introduced by {added[:12]}",
                            "archive: reports/pkt/chunks/chunk-001.BIN", "size: reports/pkt/notes.json")

    def test_a_changed_allowlisted_file_needs_its_exact_row_and_trailer(self) -> None:
        grown = self.big + b"+"
        self.repo.commit({"data/big.json": grown}, "grow the allowlisted file")
        done = self.range()
        self.assert_refused(done, "size: data/big.json", f"is {2 * MIB + 1} bytes",
                            f"the row `{row('data/big.json', grown)}`", f"it has `{row('data/big.json', self.big)}`",
                            "the trailer `Object-Budget: data/big.json: <reason>`")
        self.assertNotIn("census:", done.stderr)
        # The exact row alone is not the disclosure.
        self.repo.amend({budget.ALLOWLIST: allowlist({"data/big.json": grown})}, "grow the allowlisted file")
        done = self.range()
        self.assert_refused(done, "size: data/big.json", "the trailer `Object-Budget: data/big.json: <reason>`")
        self.assertNotIn("the row", done.stderr)
        # A trailer with no reason is not one either.
        self.repo.amend({}, "grow the allowlisted file\n\nObject-Budget: data/big.json:\n")
        self.assert_refused(self.range(), "the trailer `Object-Budget: data/big.json: <reason>`")
        self.repo.amend({}, disclosing("grow the allowlisted file", "data/big.json"))
        self.assert_passes(self.range())

    def test_a_replacement_of_the_same_size_is_refused(self) -> None:
        other = noise(2 * MIB, "unrelated")
        self.repo.commit({"data/big.json": other}, "replace with unrelated 2 MiB")
        self.assert_refused(self.range(), "size: data/big.json", f"the row `{row('data/big.json', other)}`")

    def test_a_row_added_beside_its_payload_still_needs_the_trailer(self) -> None:
        evidence = noise(3 * MIB, "evidence")
        self.repo.commit({"data/evidence.json": evidence,
                          budget.ALLOWLIST: allowlist({"data/big.json": self.big, "data/evidence.json": evidence})},
                         "evidence and its own row")
        done = self.range()
        self.assert_refused(done, "size: data/evidence.json", "the trailer `Object-Budget: data/evidence.json: <reason>`")
        self.assertNotIn("the row", done.stderr)

    def test_every_commit_that_introduces_a_large_blob_discloses_it(self) -> None:
        first, second = self.big[:-1] + b"1", self.big[:-1] + b"2"
        one = self.repo.commit({"data/big.json": first, budget.ALLOWLIST: allowlist({"data/big.json": first})},
                               disclosing("first edit", "data/big.json"))
        two = self.repo.commit({"data/big.json": second, budget.ALLOWLIST: allowlist({"data/big.json": second})},
                               "second edit")
        self.assert_refused(self.range(), f"introduced by {two[:12]}")
        self.repo.amend({}, disclosing("second edit", "data/big.json"))
        self.assert_passes(self.range())
        # An undisclosed replacement that a later commit reverts is still uploaded.
        self.repo.git("reset", "-q", "--hard", self.base)
        hidden = self.repo.commit({"data/big.json": first, budget.ALLOWLIST: allowlist({"data/big.json": first})},
                                  "replace")
        self.repo.commit({"data/big.json": self.big, budget.ALLOWLIST: allowlist({"data/big.json": self.big})},
                         "and restore")
        self.assertEqual(self.repo.out("rev-parse", "HEAD^{tree}"), self.repo.out("rev-parse", self.base + "^{tree}"))
        self.assert_refused(self.range(), f"introduced by {hidden[:12]}")
        self.assertNotEqual(one, hidden)

    def test_the_allowlist_is_the_exact_census_of_the_tip(self) -> None:
        legacy = noise(2 * MIB, "legacy")
        cut = self.repo.commit({"data/legacy.json": legacy}, "a large file the allowlist did not know")
        # A row for a file the range does not introduce admits nothing: no trailer.
        self.repo.commit({budget.ALLOWLIST: allowlist({"data/big.json": self.big, "data/legacy.json": legacy})},
                         "the census catches up")
        self.assert_passes(self.range(cut))
        # When the range changes the allowlist, every row must describe the tip.
        self.repo.commit({budget.ALLOWLIST: allowlist({"data/big.json": self.big, "data/legacy.json": legacy,
                                                       "README.md": noise(2 * MIB, "not the readme")})},
                         "a row for a file the tip does not hold so")
        self.assert_refused(self.range(cut), "census:", "README.md", "within the budget: remove the row")
        self.repo.commit({budget.ALLOWLIST: allowlist({"data/big.json": legacy, "data/legacy.json": legacy})},
                         "a row naming another blob")
        self.assert_refused(self.range(cut), "census:", f"the row is `{row('data/big.json', self.big)}`")

    def test_a_row_the_range_leaves_behind_is_refused(self) -> None:
        self.repo.commit({"data/big.json": None}, "delete the large file")
        self.assert_refused(self.range(), "census:", "data/big.json", "the tip does not hold it: remove the row")
        self.repo.commit({budget.ALLOWLIST: allowlist({})}, "drop its row")
        self.assert_passes(self.range())
        self.repo.commit({"data/big.json": b"small now\n", budget.ALLOWLIST: allowlist({"data/big.json": self.big})},
                         "a small file under a kept row")
        self.assert_refused(self.range("HEAD~1"), "census:", "the tip holds 10 bytes, within the budget")

    def test_a_large_file_the_range_touches_needs_a_row_at_the_tip(self) -> None:
        self.repo.commit({budget.ALLOWLIST: allowlist({})}, "drop the row of an unchanged large file")
        self.assert_refused(self.range(), "census: data/big.json is 2097152 bytes at the tip and has no row",
                            f"add `{row('data/big.json', self.big)}`")

    def test_history_before_the_range_is_not_judged(self) -> None:
        self.repo.commit({"reports/old/archive.tar.gz": noise(4096, "old")}, "a legacy archive")
        cut = self.repo.commit({"reports/old/archive.tar.gz": None}, "the legacy archive leaves the tree")
        self.repo.commit({"src/lib.rs": b"pub fn f() {}\n"}, "ordinary work")
        self.assert_passes(self.range(cut))
        self.assert_refused(self.range(), "archive: reports/old/archive.tar.gz")

    def test_a_merge_of_the_base_judges_only_its_own_resolution(self) -> None:
        self.repo.git("checkout", "-q", "-b", "feature")
        self.repo.commit({"src/feature.rs": b"pub fn g() {}\n"}, "feature work")
        self.repo.git("checkout", "-q", "main")
        # Main still carries a legacy archive in its tree (before the guard).
        main = self.repo.commit({"reports/legacy/kept.gz": noise(2048, "legacy")}, "legacy archive on main")
        self.repo.git("checkout", "-q", "feature")
        self.repo.git("merge", "-q", "--no-edit", "main")
        self.assert_passes(self.range(main))
        # An evil merge: the resolution itself introduces an archive.
        self.repo.git("checkout", "-q", "-b", "evil", "HEAD~1")
        self.repo.git("merge", "-q", "--no-commit", "main")
        (self.repo.root / "reports/legacy/resolution.zip").write_bytes(noise(512, "evil"))
        self.repo.git("add", "-f", "reports/legacy/resolution.zip")
        self.repo.git("commit", "-q", "--no-edit")
        merge = self.repo.out("rev-parse", "HEAD")
        self.assert_refused(self.range(main), "archive: reports/legacy/resolution.zip", f"introduced by {merge[:12]}")

    def test_only_the_sealed_fixture_members_are_exempt(self) -> None:
        self.repo.commit({FIXTURE + "case.bin": None}, "the fixture member leaves")
        self.repo.commit({
            FIXTURE + "case.bin": self.sealed,
            "crates/x/tests/fixtures/golden.bin": b"\x00\x02golden",
            "docs/decisions/x.evidence/run.log.gz": noise(700, "log"),
        }, "and returns byte-identical, beside binary fixtures outside reports/")
        refusals, summary = self.judged()
        self.assertEqual(refusals, [], summary)
        # Without the sealed tree here, nothing under the prefix is exempt.
        self.assert_refused(self.range(), f"archive: {FIXTURE}case.bin")
        for name, files in (
            ("a changed member", {FIXTURE + "case.bin": b"\x03resealed"}),
            ("a new member", {FIXTURE + "smuggled.tar.gz": noise(900, "smuggled")}),
            ("a member's bytes under another name", {FIXTURE + "copy.bin": self.sealed}),
        ):
            with self.subTest(name):
                self.repo.git("reset", "-q", "--hard", self.base)
                self.repo.commit(files, "stage")
                self.repo.commit({p: None for p in files if p != FIXTURE + "case.bin"}
                                 or {FIXTURE + "case.bin": self.sealed}, "unstage")
                refusals, _ = self.judged()
                self.assertEqual([r.split(":", 1)[0] for r in refusals], ["archive"], refusals)
                self.assertIn(next(iter(files)), refusals[0])

    def test_an_unresolved_base_is_not_judged_and_nothing_else_reads_so(self) -> None:
        done = self.repo.check("--range", "origin/main..HEAD")
        self.assertEqual(done.returncode, budget.NOT_JUDGED, done.stderr)
        self.assertIn("OBJECT-BUDGET NOT JUDGED", done.stderr)
        # A usage error is Python's 2, never the NOT JUDGED status.
        done = self.repo.check("--range", "origin/main...HEAD")
        self.assertEqual(done.returncode, 2, done.stderr)
        self.assertNotIn("NOT JUDGED", done.stderr)

    def test_a_malformed_allowlist_is_refused(self) -> None:
        good = blob_id(self.big)
        for text, needle in (
            (b"data/big.json\t2097152\n", "a row is `path<TAB>blob<TAB>bytes`"),
            (f"data/big.json\t{good}\t2097152\textra\n".encode(), "a row is `path<TAB>blob<TAB>bytes`"),
            (f"data/big.json\t{good[:12]}\t2097152\n".encode(), "a row is `path<TAB>blob<TAB>bytes`"),
            (f"data/big.json\t{good}\t+2097152\n".encode(), "a row is `path<TAB>blob<TAB>bytes`"),
            (f"data/small.json\t{good}\t1048576\n".encode(), "within the 1048576-byte budget"),
            (f"/data/big.json\t{good}\t2097152\n".encode(), "not a canonical repository path"),
            (f"data/../big.json\t{good}\t2097152\n".encode(), "not a canonical repository path"),
            (f"data/big.json\t{good}\t2097152\ndata/big.json\t{good}\t2097152\n".encode(), "has a second row"),
        ):
            with self.subTest(text=text):
                self.repo.git("reset", "-q", "--hard", self.base)
                edit = self.repo.commit({budget.ALLOWLIST: text}, "edit the allowlist")
                self.assert_refused(self.range(), f"{budget.ALLOWLIST}:", needle, f"(in {edit[:12]})")

    def test_a_blobless_clone_judges_its_own_commits_and_refuses_unmeasured_ones(self) -> None:
        self.repo.commit({"notes/draft.txt": noise(4096, "draft")}, "a blob the tip drops")
        fetched = self.repo.commit({"notes/draft.txt": None}, "drop it")
        self.repo.git("config", "uploadpack.allowFilter", "true")
        clone = self.work / "blobless"
        subprocess.run(["git", "clone", "-q", "--filter=blob:none", "file://" + str(self.repo.root), str(clone)],
                       env=self.repo.env, check=True, capture_output=True)
        local = History.__new__(History)
        local.root, local.env = clone, self.repo.env
        local.configure()
        local.commit({"src/own.rs": b"pub fn own() {}\n"}, "own work")
        self.assert_passes(local.check("--range", f"{fetched}..HEAD"))
        # Fetched commits whose blobs this clone never received cannot be sized.
        self.assert_refused(local.check("--range", f"{self.base}..HEAD"), "unmeasured: notes/draft.txt")

    def test_the_pack_budget_measures_what_the_push_uploads(self) -> None:
        self.repo.commit({f"data/part-{i}.dat": noise(200 * 1024, f"part{i}") for i in range(3)}, "incompressible")
        refusals, summary = budget.check(self.repo.root, "HEAD", [self.base], max_pack=256 * 1024)
        self.assertEqual([r.split(":", 1)[0] for r in refusals], ["pack"], refusals)
        self.assertIn("over 262144 bytes", summary)
        compressible = self.repo.commit({f"data/zero-{i}.dat": bytes([i + 1]) + bytes(200 * 1024) for i in range(3)},
                                        "compressible")
        refusals, summary = budget.check(self.repo.root, "HEAD", [compressible + "~1"], max_pack=256 * 1024)
        self.assertEqual(refusals, [], summary)
        self.assertNotIn("bounded", summary)
        refusals, summary = budget.check(self.repo.root, "HEAD", [compressible + "~1"])
        self.assertEqual(refusals, [], summary)
        self.assertIn("bounded by raw size", summary)

    def test_an_advertisement_excludes_exactly_the_commits_it_names(self) -> None:
        new = noise(2 * MIB, "pushed")
        self.repo.commit({"data/new.json": new}, "a 2 MiB blob")
        listing = self.work / "advertised"
        absent = "f" * 40
        listing.write_text(f"{self.base}\trefs/heads/main\n{absent}\trefs/heads/elsewhere\n")
        self.assert_refused(self.repo.check("--tip", "HEAD", "--advertised", str(listing)), "size: data/new.json")
        listing.write_text(f"{self.repo.out('rev-parse', 'HEAD')}\trefs/heads/main\n")
        done = self.repo.check("--tip", "HEAD", "--advertised", str(listing))
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertIn("no new commits", done.stdout)
        listing.write_text("not an advertisement\n")
        self.assert_refused(self.repo.check("--tip", "HEAD", "--advertised", str(listing)), "advertisement line 1")

    def test_update_allowlist_writes_the_census_of_the_index(self) -> None:
        new = noise(3 * MIB, "staged")
        self.repo.stage({"data/big.json": None, "data/new.json": new})
        done = self.repo.check("--update-allowlist")
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertIn(f"- {row('data/big.json', self.big)}", done.stdout)
        self.assertIn(f"+ {row('data/new.json', new)}", done.stdout)
        text = (self.repo.root / budget.ALLOWLIST).read_text()
        self.assertTrue(text.startswith("# fixture allowlist\n"), text)
        self.assertEqual(budget.parse_allowlist(text), {"data/new.json": (blob_id(new), len(new))})


class PrePushHook(Verdicts):
    """The hook runs the same check on what `git push` would upload: the local
    commits minus what the remote advertises, never remote-tracking refs."""

    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="object-budget-push-")
        self.addCleanup(temporary.cleanup)
        self.work = Path(temporary.name)
        self.remote = self.work / "remote.git"
        subprocess.run(["git", "init", "-q", "--bare", "--template=", str(self.remote)],
                       env=git_environment(), check=True, capture_output=True)
        self.repo = History(self.work / "repo")
        self.base = self.repo.commit({"README.md": b"fixture\n"}, "base")
        self.repo.git("remote", "add", "origin", "file://" + str(self.remote))
        self.repo.git("push", "-q", "origin", "HEAD:refs/heads/main")
        self.repo.git("config", "core.hooksPath", str(HOOKS))

    def push(self, *refspecs: str) -> subprocess.CompletedProcess:
        return self.repo.git("push", "origin", *refspecs, check=False)

    def remote_ref(self, ref: str) -> Optional[str]:
        done = subprocess.run(["git", "--git-dir", str(self.remote), "rev-parse", "--verify", "--quiet", ref],
                              env=git_environment(), capture_output=True, check=False)
        return done.stdout.decode().strip() or None

    def payload_branch(self) -> str:
        self.repo.git("checkout", "-q", "-b", "old")
        payload = self.repo.commit({"data/payload.json": noise(2 * MIB, "payload")}, "old-line payload")
        self.repo.git("checkout", "-q", "main")
        return payload

    def assert_push_refused(self, done: subprocess.CompletedProcess, needle: str) -> None:
        self.assertNotEqual(done.returncode, 0)
        self.assertIn(needle, done.stderr.decode())

    def test_a_push_of_an_oversized_blob_is_refused(self) -> None:
        self.repo.commit({"data/new.json": noise(2 * MIB, "push")}, "a 2 MiB blob")
        self.assert_push_refused(self.push("HEAD:refs/heads/main"), "OBJECT-BUDGET REFUSED size: data/new.json")
        self.assertEqual(self.remote_ref("refs/heads/main"), self.base)

    def test_a_new_ref_carrying_an_added_then_deleted_archive_is_refused(self) -> None:
        self.repo.commit({"reports/pkt/chunk-000.bin": noise(1024, "c")}, "stage")
        self.repo.commit({"reports/pkt/chunk-000.bin": None}, "unstage")
        self.assert_push_refused(self.push("HEAD:refs/heads/lane"),
                                 "OBJECT-BUDGET REFUSED archive: reports/pkt/chunk-000.bin")
        self.assertIsNone(self.remote_ref("refs/heads/lane"))

    def test_an_ordinary_push_and_a_deletion_pass(self) -> None:
        tip = self.repo.commit({"src/lib.rs": b"pub fn f() {}\n"}, "ordinary work")
        done = self.push("HEAD:refs/heads/main", "HEAD:refs/heads/lane")
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(self.remote_ref("refs/heads/main"), tip)
        done = self.push(":refs/heads/lane")
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertIsNone(self.remote_ref("refs/heads/lane"))

    def test_a_disclosed_blob_is_pushed_and_what_the_remote_has_is_not_judged_again(self) -> None:
        big = noise(2 * MIB, "disclosed")
        self.repo.commit({"data/big.json": big, budget.ALLOWLIST: allowlist({"data/big.json": big})},
                         disclosing("a reviewed large file", "data/big.json"))
        done = self.push("HEAD:refs/heads/main")
        self.assertEqual(done.returncode, 0, done.stderr)
        # A new lane on top uploads only its own commit: the remote advertises main.
        lane = self.repo.commit({"src/lib.rs": b"pub fn f() {}\n"}, "lane work")
        done = self.push("HEAD:refs/heads/lane")
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(self.remote_ref("refs/heads/lane"), lane)

    def test_a_stale_remote_tracking_ref_does_not_hide_a_payload(self) -> None:
        payload = self.payload_branch()
        # What an old clone keeps after the remote deleted or rewrote the branch.
        self.repo.git("update-ref", "refs/remotes/origin/lane-deleted-on-remote", payload)
        self.assert_push_refused(self.push("old:refs/heads/revived"), "OBJECT-BUDGET REFUSED size: data/payload.json")
        self.assertIsNone(self.remote_ref("refs/heads/revived"))

    def test_another_remotes_refs_do_not_hide_a_payload(self) -> None:
        payload = self.payload_branch()
        mirror = self.work / "mirror.git"
        subprocess.run(["git", "init", "-q", "--bare", "--template=", str(mirror)],
                       env=git_environment(), check=True, capture_output=True)
        self.repo.git("push", "-q", "--no-verify", "file://" + str(mirror), "old:refs/heads/main")
        self.repo.git("remote", "add", "mirror", "file://" + str(mirror))
        self.repo.git("fetch", "-q", "mirror")
        self.assertEqual(self.repo.out("rev-parse", "refs/remotes/mirror/main"), payload)
        self.assert_push_refused(self.push("old:refs/heads/main"), "OBJECT-BUDGET REFUSED size: data/payload.json")
        self.assertEqual(self.remote_ref("refs/heads/main"), self.base)


def public_snapshot() -> bool:
    spec = importlib.util.spec_from_file_location("object_budget_snapshot_boundary", SCRIPTS / "check_enforcement_links.py")
    if spec is None or spec.loader is None:
        raise AssertionError("the snapshot classifier is missing")
    classifier = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = classifier
    spec.loader.exec_module(classifier)
    return bool(classifier.is_public_snapshot(ROOT))


class LiveAllowlist(unittest.TestCase):
    """The committed allowlist is the exact census of HEAD's files over the
    budget: one `path<TAB>blob<TAB>bytes` row each, and no other row."""

    def test_the_allowlist_is_the_exact_census_of_head(self) -> None:
        env = git_environment()
        text = subprocess.run(["git", "-C", str(ROOT), "show", "HEAD:" + budget.ALLOWLIST],
                              env=env, capture_output=True, check=True).stdout.decode("utf-8")
        rows = budget.parse_allowlist(text)
        listing = subprocess.run(["git", "-C", str(ROOT), "ls-tree", "-r", "-l", "-z", "HEAD"],
                                 env=env, capture_output=True, check=True).stdout
        over, present = {}, set()
        for entry in listing.split(b"\0"):
            if not entry:
                continue
            header, name = entry.split(b"\t", 1)
            mode, kind, oid, size = header.decode().split()
            present.add(os.fsdecode(name))
            if kind == "blob" and int(size) > budget.MAX_BLOB_BYTES:
                over[os.fsdecode(name)] = (oid, int(size))
        if public_snapshot():
            # The snapshot ships scripts/ whole but not reports/: rows for
            # unexported files describe the development tree.
            rows = {p: r for p, r in rows.items() if p in present}
        self.assertEqual(rows, over, "run `python3 scripts/check_object_budget.py --update-allowlist` on the "
                                     "staged tree and commit " + budget.ALLOWLIST)


if __name__ == "__main__":
    unittest.main()
