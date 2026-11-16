#!/usr/bin/env python3
"""Retrieve original report bytes without putting generated archives in source.

The catalog is transport custody, never a proof receipt. Every lookup names an
immutable source commit, original path, Git blob, byte count and SHA-256. Local
Git objects are preferred. Network access requires explicit --fetch and uses
Agh. Missing or ambiguous inputs refuse; no latest-main or missing-file skip.
"""
from __future__ import annotations

import argparse
import base64
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import sys
import tempfile

SCHEMA = "trust-ir.report-artifacts.v1"
CATALOG = "reports/report-artifacts.json"
INLINE_FIXTURE = "reports/2026-09-17-two-language-proof-program/"
# This allowance is the independently reviewed original standing fixture.
# A mutable transport catalog cannot grant itself a new source exception.
REVIEWED_FIXTURE_SOURCE = "61d9c366cd92420f78fc86f43c376d83b01ac238"
REVIEWED_FIXTURE_TREE = "81f37bdd14ab20f8c78ac52d8f93e1c082f24019"
REVIEWED_INLINE_FIXTURE = {
    "prefix": INLINE_FIXTURE,
    "source": REVIEWED_FIXTURE_SOURCE,
    "manifest_path": INLINE_FIXTURE + "MANIFEST.sha256",
    "manifest_sha256": "713568eea4e05a24a43efbb33a2e2c618fc14e461a2b9a635b8f9b90c1a9ccac",
    "manifest_git_blob": "ec1efbdf72a667585a9dacdb3038a97922cb662f",
    "files": 1349,
    "bytes": 14246466,
}
ARCHIVE_SUFFIXES = (".bin", ".gz", ".xz", ".zst", ".zip", ".tar", ".tgz", ".bz2", ".7z", ".olean", ".ilean")
HEX40 = re.compile(r"[0-9a-f]{40}\Z")
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
REPOSITORY = re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+\Z")


class ArtifactError(RuntimeError):
    """Artifact identity, custody, availability or destination refusal."""


def _unique_pairs(pairs):
    value = {}
    for key, item in pairs:
        if key in value:
            raise ArtifactError(f"duplicate catalog key: {key}")
        value[key] = item
    return value


def _fields(value, required, optional=()):
    if not isinstance(value, dict) or not set(required) <= set(value) or set(value) - set(required) - set(optional):
        raise ArtifactError("unknown or missing catalog fields")


def _path(value):
    if not isinstance(value, str) or not value or "\\" in value or any(ord(c) < 32 for c in value):
        raise ArtifactError("invalid original artifact path")
    try:
        value.encode("utf-8")
    except UnicodeError as error:
        raise ArtifactError("artifact path is not UTF-8") from error
    if value.startswith("/") or any(p in {"", ".", ".."} for p in value.split("/")) or str(PurePosixPath(value)) != value:
        raise ArtifactError("artifact path traversal or alias")
    if value != "reports" and not value.startswith("reports/"):
        raise ArtifactError("artifact path is outside reports")
    return value


def _integer(value):
    if type(value) is not int or value < 0 or value > (1 << 63) - 1:
        raise ArtifactError("invalid artifact byte count")
    return value


def _hex(value, pattern, label):
    if not isinstance(value, str) or pattern.fullmatch(value) is None:
        raise ArtifactError(f"invalid {label}")
    return value


ARTIFACT_OBJECTS_ENV = "TRUST_IR_ARTIFACT_OBJECTS"


def _git_environment():
    env = dict(os.environ)
    for key in list(env):
        if key in {"GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR", "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_REPLACE_REF_BASE", "GIT_NAMESPACE", "GIT_SHALLOW_FILE", "GIT_GRAFT_FILE"} or key.startswith("GIT_CONFIG"):
            del env[key]
    env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1", GIT_NO_REPLACE_OBJECTS="1", GIT_GRAFT_FILE=os.devnull, GIT_NO_LAZY_FETCH="1", GIT_TERMINAL_PROMPT="0")
    # The 2026-11-15 history rewrite removed the archive payloads and their
    # original source commits from this repository. A machine that holds the
    # custody mirror names its object directory here; every byte read through
    # it is still bound to the catalog's commit, tree, blob and SHA-256.
    archive = os.environ.get(ARTIFACT_OBJECTS_ENV, "")
    if archive and Path(archive).is_dir():
        env["GIT_ALTERNATE_OBJECT_DIRECTORIES"] = archive
    return env


class Store:
    def __init__(self, root: Path, catalog_path=None, fetch=False):
        self.root = Path(root).resolve(strict=True)
        self.fetch = fetch is True
        if type(fetch) is not bool:
            raise ArtifactError("fetch must be an explicit Boolean")
        self.catalog_path = Path(catalog_path) if catalog_path is not None else self.root / CATALOG
        if self.catalog_path.is_symlink():
            raise ArtifactError("catalog must be a regular file")
        try:
            value = json.loads(self.catalog_path.read_text(encoding="utf-8"), object_pairs_hook=_unique_pairs)
        except (OSError, ValueError) as error:
            raise ArtifactError(f"cannot read artifact catalog: {error}") from error
        _fields(value, {"schema", "sources", "artifacts", "inline_fixture"}, {"archive_suffixes", "scope"})
        if value["schema"] != SCHEMA or not isinstance(value["sources"], list) or not isinstance(value["artifacts"], list):
            raise ArtifactError("unsupported artifact catalog schema")
        self.sources = {}
        for source in value["sources"]:
            _fields(source, {"commit", "tree", "repository"})
            commit = _hex(source["commit"], HEX40, "source commit")
            _hex(source["tree"], HEX40, "source tree")
            repo = source["repository"]
            if not isinstance(repo, str) or REPOSITORY.fullmatch(repo) is None or any(p in {".", ".."} for p in repo.split("/")):
                raise ArtifactError("invalid authenticated repository locator")
            if commit in self.sources:
                raise ArtifactError("duplicate immutable source")
            self.sources[commit] = source
        if not self.sources:
            raise ArtifactError("artifact catalog has no source")
        self.records = {}
        for row in value["artifacts"]:
            _fields(row, {"path", "source", "mode", "git_blob", "bytes", "sha256"})
            path = _path(row["path"])
            _hex(row["source"], HEX40, "artifact source")
            if row["source"] not in self.sources or not isinstance(row["mode"], str) or row["mode"] not in {"100644", "100755"}:
                raise ArtifactError("unknown source or nonregular artifact mode")
            _hex(row["git_blob"], HEX40, "Git blob")
            _hex(row["sha256"], HEX64, "SHA-256")
            _integer(row["bytes"])
            key = row["source"], path
            if key in self.records:
                raise ArtifactError("duplicate artifact identity")
            self.records[key] = dict(row)
        self.fixture = value["inline_fixture"]
        if self.fixture is not None:
            _fields(self.fixture, {"prefix", "source", "manifest_path", "manifest_sha256", "manifest_git_blob", "files", "bytes"})
            fixture = self.fixture
            _hex(fixture["source"], HEX40, "fixture source")
            if fixture["prefix"] != INLINE_FIXTURE or fixture["manifest_path"] != INLINE_FIXTURE + "MANIFEST.sha256" or fixture["source"] not in self.sources:
                raise ArtifactError("unknown inline fixture")
            _hex(fixture["manifest_sha256"], HEX64, "fixture manifest SHA-256")
            _hex(fixture["manifest_git_blob"], HEX40, "fixture manifest Git blob")
            _integer(fixture["files"])
            _integer(fixture["bytes"])
            if fixture != REVIEWED_INLINE_FIXTURE or self.sources[REVIEWED_FIXTURE_SOURCE]["tree"] != REVIEWED_FIXTURE_TREE:
                raise ArtifactError("standing fixture differs from the independently reviewed original seal")
        self._trees = {}
        self._api_trees = {}
        self._api_commits = set()

    def sources_available(self):
        """True when every original source commit can be read without the network."""
        return all(self._git("cat-file", "-e", source + "^{commit}").returncode == 0 for source in self.sources)

    def _git(self, *args):
        command = ["git", "--no-replace-objects", "--literal-pathspecs", "-C", str(self.root), *args]
        return subprocess.run(command, capture_output=True, env=_git_environment())

    def _source_rows(self, source):
        if source in self._trees:
            return self._trees[source]
        tree = self._git("rev-parse", source + "^{tree}")
        if tree.returncode or tree.stdout.decode().strip() != self.sources[source]["tree"]:
            raise ArtifactError("original immutable source commit/tree is unavailable or differs")
        result = self._git("ls-tree", "-r", "-l", "-z", source, "--", "reports")
        if result.returncode:
            raise ArtifactError("cannot read original report tree")
        rows = {}
        for raw in result.stdout.split(b"\0"):
            if not raw:
                continue
            header, path = raw.split(b"\t", 1)
            mode, kind, oid, size = header.decode("ascii").split()
            name = _path(os.fsdecode(path))
            if name in rows or kind != "blob" or mode not in {"100644", "100755"}:
                raise ArtifactError("original report has duplicate or unsupported entries")
            rows[name] = {"path": name, "source": source, "mode": mode, "git_blob": oid, "bytes": int(size)}
        self._trees[source] = rows
        return rows

    def _api(self, source, endpoint):
        if not self.fetch:
            raise ArtifactError("original Git object unavailable; network requires explicit --fetch")
        executable = Path.home() / ".local/bin/agh"
        selected = str(executable) if executable.is_file() else shutil.which("agh")
        if selected is None:
            raise ArtifactError("authenticated Agh is unavailable")
        repository = self.sources[source]["repository"]
        result = subprocess.run([selected, "api", "repos/" + repository + "/git/" + endpoint], capture_output=True)
        if result.returncode:
            raise ArtifactError("authenticated artifact retrieval failed: " + result.stderr.decode(errors="backslashreplace")[:500])
        try:
            return json.loads(result.stdout, object_pairs_hook=_unique_pairs)
        except ValueError as error:
            raise ArtifactError("malformed authenticated artifact response") from error

    def _remote_tree(self, source, oid):
        key = source, oid
        if key in self._api_trees:
            return self._api_trees[key]
        if source not in self._api_commits:
            commit = self._api(source, "commits/" + source)
            if commit.get("sha") != source or commit.get("tree", {}).get("sha") != self.sources[source]["tree"]:
                raise ArtifactError("remote immutable commit/tree mismatch")
            self._api_commits.add(source)
        value = self._api(source, "trees/" + oid)
        if value.get("sha") != oid or value.get("truncated") is not False or not isinstance(value.get("tree"), list):
            raise ArtifactError("incomplete original Git tree response")
        rows = {}
        encoded = []
        for row in value["tree"]:
            name = row.get("path")
            if not isinstance(name, str) or not name or "/" in name or name in {".", ".."} or "\0" in name or name in rows:
                raise ArtifactError("invalid original Git tree member")
            mode = row.get("mode")
            kind = row.get("type")
            if (mode, kind) not in {("040000", "tree"), ("100644", "blob"), ("100755", "blob"), ("120000", "blob"), ("160000", "commit")}:
                raise ArtifactError("invalid original Git tree mode")
            blob = _hex(row.get("sha"), HEX40, "Git tree child")
            raw_name = name.encode("utf-8")
            encoded.append((raw_name + (b"/" if kind == "tree" else b""), mode.lstrip("0").encode() + b" " + raw_name + b"\0" + bytes.fromhex(blob)))
            rows[name] = row
        data = b"".join(row for _, row in sorted(encoded))
        if hashlib.sha1(b"tree " + str(len(data)).encode() + b"\0" + data).hexdigest() != oid:
            raise ArtifactError("original Git tree digest mismatch")
        self._api_trees[key] = rows
        return rows

    def _remote_row(self, source, path):
        oid = self.sources[source]["tree"]
        parts = path.split("/")
        for i, part in enumerate(parts):
            row = self._remote_tree(source, oid).get(part)
            if row is None:
                raise ArtifactError("artifact path is missing from original tree")
            if i < len(parts) - 1:
                if row["type"] != "tree":
                    raise ArtifactError("artifact parent is not an original tree")
                oid = row["sha"]
        if row["type"] != "blob" or row["mode"] not in {"100644", "100755"}:
            raise ArtifactError("artifact is not an original regular file")
        return {"path": path, "source": source, "mode": row["mode"], "git_blob": row["sha"], "bytes": _integer(row.get("size"))}

    def _remote_rows(self, source, selector):
        oid = self.sources[source]["tree"]
        parts = selector.split("/")
        for i, part in enumerate(parts):
            row = self._remote_tree(source, oid).get(part)
            if row is None:
                raise ArtifactError("report prefix is missing from original tree")
            if i < len(parts) - 1:
                if row["type"] != "tree":
                    raise ArtifactError("report parent is not a tree")
                oid = row["sha"]
        if row["type"] != "tree":
            return {selector: self._remote_row(source, selector)}
        rows = {}
        stack = [(row["sha"], selector, 0)]
        while stack:
            tree, prefix, depth = stack.pop()
            if depth > 128:
                raise ArtifactError("report tree depth exceeds retrieval bound")
            for name, child in self._remote_tree(source, tree).items():
                path = _path(prefix + "/" + name)
                if child["type"] == "tree":
                    stack.append((child["sha"], path, depth + 1))
                elif child["type"] == "blob" and child["mode"] in {"100644", "100755"}:
                    if path in rows or len(rows) >= 100000:
                        raise ArtifactError("duplicate or oversized report member namespace")
                    rows[path] = {"path": path, "source": source, "mode": child["mode"], "git_blob": child["sha"], "bytes": _integer(child.get("size"))}
                else:
                    raise ArtifactError("report contains a nonregular original member")
        return rows

    def _bound(self, row):
        try:
            actual = self._source_rows(row["source"]).get(row["path"])
        except ArtifactError:
            if not self.fetch:
                raise
            actual = self._remote_row(row["source"], row["path"])
        if actual is None or any(actual[k] != row[k] for k in ("path", "source", "mode", "git_blob", "bytes")):
            raise ArtifactError("artifact path/blob/size/mode differs from original source")

    def _record(self, path, source=None):
        path = _path(path)
        rows = [r for (s, p), r in self.records.items() if p == path and (source is None or s == source)]
        if len(rows) != 1:
            raise ArtifactError("artifact is missing or ambiguous; name its immutable source")
        return rows[0]

    def _existing(self, path):
        cursor = self.root
        for part in path.split("/"):
            cursor /= part
            try:
                info = cursor.lstat()
            except FileNotFoundError:
                return None
            if stat.S_ISLNK(info.st_mode):
                raise ArtifactError("artifact source path contains a symlink")
        if not stat.S_ISREG(info.st_mode):
            raise ArtifactError("artifact source is not regular")
        return cursor

    def _copy_verified(self, row, out):
        self._bound(row)
        existing = self._existing(row["path"])
        process = None
        if existing is not None:
            stream = existing.open("rb")
        else:
            command = ["git", "--no-replace-objects", "-C", str(self.root), "cat-file", "blob", row["git_blob"]]
            process = subprocess.Popen(command, env=_git_environment(), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            stream = process.stdout
        digest = hashlib.sha256()
        blob = hashlib.sha1(b"blob " + str(row["bytes"]).encode() + b"\0")
        count = 0
        try:
            while True:
                data = stream.read(1024 * 1024)
                if not data:
                    break
                count += len(data)
                if count > row["bytes"]:
                    raise ArtifactError("artifact byte count mismatch")
                digest.update(data)
                blob.update(data)
                out.write(data)
            if process is not None:
                _, error = process.communicate()
                if process.returncode:
                    if self.fetch:
                        out.seek(0)
                        out.truncate()
                        value = self._api(row["source"], "blobs/" + row["git_blob"])
                        if value.get("sha") != row["git_blob"] or type(value.get("size")) is not int or value["size"] != row["bytes"] or value.get("encoding") != "base64":
                            raise ArtifactError("remote blob identity mismatch")
                        try:
                            payload = base64.b64decode("".join(value["content"].split()), validate=True)
                        except (KeyError, ValueError) as error:
                            raise ArtifactError("malformed remote blob content") from error
                        count = len(payload)
                        digest = hashlib.sha256(payload)
                        blob = hashlib.sha1(b"blob " + str(count).encode() + b"\0" + payload)
                        out.write(payload)
                    else:
                        raise ArtifactError("original Git blob unavailable: " + error.decode(errors="backslashreplace")[:500])
        finally:
            stream.close()
            if process is not None and process.poll() is None:
                process.terminate()
                process.communicate()
        if count != row["bytes"] or blob.hexdigest() != row["git_blob"] or ("sha256" in row and digest.hexdigest() != row["sha256"]):
            raise ArtifactError("artifact size/Git blob/SHA-256 mismatch")
        return {**row, "sha256": digest.hexdigest()}

    @contextmanager
    def open(self, path, source=None):
        row = self._record(path, source)
        with tempfile.TemporaryFile(mode="w+b") as stream:
            self._copy_verified(row, stream)
            stream.seek(0)
            yield stream

    def _outside(self, destination):
        destination = Path(destination)
        if not destination.is_absolute():
            raise ArtifactError("destination must be an explicit absolute external directory")
        # samefile includes differently-cased aliases on case-insensitive hosts.
        for p in [destination, *destination.parents]:
            try:
                if p.samefile(self.root):
                    raise ArtifactError("artifact destination is inside the source tree")
            except FileNotFoundError:
                pass
        if destination.is_symlink():
            raise ArtifactError("artifact destination is a symlink")
        result = destination.resolve()
        if result == self.root or self.root in result.parents:
            raise ArtifactError("artifact destination is inside the source tree")
        return result

    def _destination_parent(self, destination, path):
        # Traverse directory FDs without following links; never overwrite a file.
        destination.mkdir(parents=True, exist_ok=True)
        descriptor = os.open(destination, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        try:
            parts = path.split("/")
            for name in parts[:-1]:
                try:
                    os.mkdir(name, 0o755, dir_fd=descriptor)
                except FileExistsError:
                    pass
                following = os.open(name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=descriptor)
                os.close(descriptor)
                descriptor = following
            return descriptor, parts[-1]
        except BaseException:
            os.close(descriptor)
            raise

    def _materialize_one(self, destination, row):
        descriptor, name = self._destination_parent(destination, row["path"])
        mode = 0o755 if row["mode"] == "100755" else 0o644
        try:
            try:
                existing = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=descriptor)
            except FileNotFoundError:
                existing = None
            if existing is not None:
                with os.fdopen(existing, "rb") as stream:
                    info = os.fstat(stream.fileno())
                    if not stat.S_ISREG(info.st_mode) or stat.S_IMODE(info.st_mode) != mode or info.st_size != row["bytes"]:
                        raise ArtifactError("existing destination differs; no overwrite")
                    digest = hashlib.sha256()
                    blob = hashlib.sha1(b"blob " + str(info.st_size).encode() + b"\0")
                    count = 0
                    for data in iter(lambda: stream.read(1024 * 1024), b""):
                        count += len(data)
                        if count > row["bytes"]:
                            raise ArtifactError("existing destination grew; no overwrite")
                        digest.update(data)
                        blob.update(data)
                    if count != row["bytes"] or blob.hexdigest() != row["git_blob"] or ("sha256" in row and digest.hexdigest() != row["sha256"]):
                        raise ArtifactError("existing destination differs; no overwrite")
                    self._bound(row)
                    return {**row, "sha256": digest.hexdigest(), "reused": True}
            temporary = ".artifact-" + os.urandom(16).hex()
            fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600, dir_fd=descriptor)
            try:
                with os.fdopen(fd, "wb") as stream:
                    record = self._copy_verified(row, stream)
                    stream.flush()
                    os.fsync(stream.fileno())
                    os.fchmod(stream.fileno(), mode)
                os.link(temporary, name, src_dir_fd=descriptor, dst_dir_fd=descriptor, follow_symlinks=False)
                os.fsync(descriptor)
                return {**record, "reused": False}
            finally:
                os.unlink(temporary, dir_fd=descriptor)
        finally:
            os.close(descriptor)

    def materialize(self, selector, destination, source=None, report=False):
        selector = _path(selector.rstrip("/"))
        destination = self._outside(destination)
        if report:
            selected_source = source
            if selected_source is None:
                if len(self.sources) != 1:
                    raise ArtifactError("report source is ambiguous; name its immutable source")
                selected_source = next(iter(self.sources))
            if selected_source not in self.sources:
                raise ArtifactError("unknown report source")
            try:
                rows = self._source_rows(selected_source)
            except ArtifactError:
                if not self.fetch:
                    raise
                rows = self._remote_rows(selected_source, selector)
            selected = [self.records.get((selected_source, path), row) for path, row in rows.items() if path == selector or path.startswith(selector + "/")]
        else:
            selected = [row for (s, path), row in self.records.items() if (source is None or s == source) and (path == selector or path.startswith(selector + "/"))]
            if len({row["source"] for row in selected}) > 1:
                raise ArtifactError("artifact prefix is ambiguous; name its immutable source")
        if not selected:
            raise ArtifactError("artifact selector has no original members")
        try:
            return {"files": [self._materialize_one(destination, row) for row in sorted(selected, key=lambda r: r["path"])]}
        except OSError as error:
            raise ArtifactError(f"artifact destination refused: {error}") from error

    def check_index(self):
        result = self._git("ls-files", "--stage", "-z", "--", "reports")
        if result.returncode:
            raise ArtifactError("cannot inspect current report index")
        index = {}
        for entry in result.stdout.split(b"\0"):
            if not entry:
                continue
            header, raw = entry.split(b"\t", 1)
            mode, oid, stage = header.decode().split()
            path = _path(os.fsdecode(raw))
            if stage != "0" or path in index:
                raise ArtifactError("unmerged or duplicate report index")
            index[path] = (mode, oid)
        generated = [p for p in index if p.endswith(ARCHIVE_SUFFIXES) and not p.startswith(INLINE_FIXTURE)]
        if generated:
            raise ArtifactError("generated report archives remain in source: " + ", ".join(generated[:8]))
        fixture_paths = {p for p in index if p.startswith(INLINE_FIXTURE)}
        # Synthetic isolated repositories need no fixture. In this actual
        # history, removing the seal from the catalog cannot erase its duty.
        known = self._git("cat-file", "-t", REVIEWED_FIXTURE_SOURCE)
        if known.returncode == 0:
            ancestor = self._git("merge-base", "--is-ancestor", REVIEWED_FIXTURE_SOURCE, "HEAD")
            if ancestor.returncode not in (0, 1):
                raise ArtifactError("cannot establish original standing fixture ancestry")
            if ancestor.returncode == 0 and self.fixture is None:
                raise ArtifactError("original standing fixture has no independent seal; never skipped")
        if self.fixture is None and any(any(p.startswith(INLINE_FIXTURE) for p in self._source_rows(source)) for source in self.sources):
            raise ArtifactError("original standing fixture has no seal; never skipped")
        if fixture_paths:
            if self.fixture is None:
                raise ArtifactError("standing fixture has no original seal")
            f = self.fixture
            original = {p: row for p, row in self._source_rows(f["source"]).items() if p.startswith(INLINE_FIXTURE)}
            if set(original) != fixture_paths or len(original) != f["files"] or sum(r["bytes"] for r in original.values()) != f["bytes"]:
                raise ArtifactError("standing fixture member denominator differs")
            if any(index[p] != (row["mode"], row["git_blob"]) for p, row in original.items()):
                raise ArtifactError("standing fixture source bytes differ")
            manifest = original[f["manifest_path"]]
            if manifest["git_blob"] != f["manifest_git_blob"]:
                raise ArtifactError("standing fixture manifest identity differs")
            with tempfile.TemporaryFile() as stream:
                actual = self._copy_verified({**manifest, "sha256": f["manifest_sha256"]}, stream)
                assert actual["sha256"] == f["manifest_sha256"]
        elif self.fixture is not None:
            raise ArtifactError("standing fixture is missing; never skipped")
        # Validate transport structure/path binding without rehashing historical GB.
        for row in self.records.values():
            self._bound(row)
        return {"archive_files": len(self.records), "archive_bytes": sum(r["bytes"] for r in self.records.values()), "inline_fixture_files": len(fixture_paths), "scope": "Source-tree/custody check only, no proof or release grade"}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--catalog", type=Path)
    parser.add_argument("--fetch", action="store_true", help="explicit authenticated Agh retrieval when original Git objects are unavailable")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("check-index", help="refuse generated archives and preserve the exact standing fixture")
    for name in ("materialize", "restore-report"):
        item = sub.add_parser(name)
        item.add_argument("selector")
        item.add_argument("--source", help="immutable source commit; required for ambiguous versions")
        item.add_argument("--destination", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        store = Store(args.root, args.catalog, args.fetch)
        if args.command == "check-index":
            result = store.check_index()
        else:
            result = store.materialize(args.selector, args.destination, args.source, report=args.command == "restore-report")
        print(json.dumps(result, sort_keys=True, indent=2))
        return 0
    except (ArtifactError, OSError, ValueError) as error:
        print(f"REPORT-ARTIFACT REFUSED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
