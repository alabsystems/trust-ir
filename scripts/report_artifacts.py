#!/usr/bin/env python3
"""Retrieve original report bytes without putting generated archives in source.

The catalog is transport custody, never a proof receipt. Every lookup names an
immutable source commit, original path, Git blob, byte count and SHA-256. Local
Git objects are preferred. Network access requires explicit --fetch and uses
Agh. Missing or ambiguous inputs refuse; no latest-main or missing-file skip.

`check-index` (gate 0) is local: it reads the current index, the catalog and
the standing fixture's current blobs, never a historical object, so it passes
in a blobless or shallow clone. `audit` is the explicit history check: every
catalog row against its original source tree, the fixture seal against its
source's prefix tree, and no unsealed catalog whose sources hold the fixture
(local objects, or Agh with --fetch). The standing test
`CurrentReportTreePolicy` runs `audit` wherever the sources are present.
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
# `tree` is the Git tree of the prefix at the reviewed source
# (`git rev-parse 61d9c366…:reports/2026-09-17-two-language-proof-program`):
# one digest over every member's name, mode and blob, so the current index can
# be held to the seal without reading the source commit.
REVIEWED_INLINE_FIXTURE = {
    "prefix": INLINE_FIXTURE,
    "source": REVIEWED_FIXTURE_SOURCE,
    "tree": "4d9b82c5ef7458c3988220e3041a03f162a3d233",
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


def is_archive(path):
    """An archive name in any letter case: `chunk-000.BIN` is one."""
    return path.lower().endswith(ARCHIVE_SUFFIXES)


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


def _tree_oid(entries):
    """The Git tree id of {relative path: (mode, blob)}, computed in memory:
    the same digest `git write-tree` would give, without writing an object."""
    root = {}
    for path, (mode, oid) in entries.items():
        node = root
        parts = path.split("/")
        for part in parts[:-1]:
            node = node.setdefault(part, {})
            if not isinstance(node, dict):
                raise ArtifactError("standing fixture path is both a file and a directory")
        if parts[-1] in node:
            raise ArtifactError("standing fixture path is both a file and a directory")
        node[parts[-1]] = (mode, _hex(oid, HEX40, "fixture member Git blob"))

    def digest(node):
        rows = []
        for name, value in node.items():
            raw = os.fsencode(name)
            if isinstance(value, dict):
                rows.append((raw + b"/", b"40000 " + raw + b"\0" + bytes.fromhex(digest(value))))
            else:
                rows.append((raw, value[0].lstrip("0").encode("ascii") + b" " + raw + b"\0" + bytes.fromhex(value[1])))
        data = b"".join(row for _, row in sorted(rows))
        return hashlib.sha1(b"tree " + str(len(data)).encode() + b"\0" + data).hexdigest()

    return digest(root)


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


def _read_catalog(path):
    if not stat.S_ISREG(path.lstat().st_mode):
        raise ArtifactError("catalog must be a regular file")
    flags = os.O_RDONLY
    for name in ("O_NOFOLLOW", "O_NONBLOCK", "O_BINARY"):
        flags |= getattr(os, name, 0)
    descriptor = os.open(path, flags)
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise ArtifactError("catalog must be a regular file")
        with os.fdopen(descriptor, "r", encoding="utf-8", closefd=False) as stream:
            return json.load(stream, object_pairs_hook=_unique_pairs)
    finally:
        os.close(descriptor)


class Store:
    def __init__(self, root: Path, catalog_path=None, fetch=False):
        self.root = Path(root).resolve(strict=True)
        self.fetch = fetch is True
        if type(fetch) is not bool:
            raise ArtifactError("fetch must be an explicit Boolean")
        self.catalog_path = Path(catalog_path) if catalog_path is not None else self.root / CATALOG
        try:
            value = _read_catalog(self.catalog_path)
        except (OSError, ValueError) as error:
            raise ArtifactError(f"cannot read artifact catalog: {error}") from error
        # An immutable snapshot of the decoded JSON, retaining value types
        # while ignoring presentation such as CRLF and object-key ordering.
        self._catalog_snapshot = json.dumps(value, sort_keys=True)
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
            _fields(self.fixture, {"prefix", "source", "tree", "manifest_path", "manifest_sha256", "manifest_git_blob", "files", "bytes"})
            fixture = self.fixture
            _hex(fixture["source"], HEX40, "fixture source")
            _hex(fixture["tree"], HEX40, "fixture tree")
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
            if not size.isdigit():
                # A blobless clone has the tree but not the blob, so ls-tree
                # cannot size it (it prints BAD); never guess a byte count.
                raise ArtifactError("original report blob is unavailable locally: " + name)
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

    def _index(self):
        """path -> (mode, blob) of the current index under reports/."""
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
        return index

    def _current_blob(self, oid):
        """A blob the current index names, read from local objects only."""
        result = self._git("cat-file", "blob", oid)
        if result.returncode:
            raise ArtifactError("current indexed blob is unavailable: " + result.stderr.decode(errors="backslashreplace")[:500])
        return result.stdout

    def _check_fixture(self, index):
        """The standing fixture in `index` equals its independent seal: the Git
        tree of its prefix, its member count and bytes, and its manifest's
        identity and SHA-256. Reads only index rows and current blobs."""
        fixture_paths = sorted(p for p in index if p.startswith(INLINE_FIXTURE))
        if self.fixture is None:
            # Synthetic isolated repositories need no fixture. A catalog that
            # carries the reviewed source cannot drop the seal to erase its duty.
            if REVIEWED_FIXTURE_SOURCE in self.sources:
                raise ArtifactError("original standing fixture has no independent seal; never skipped")
            if fixture_paths:
                raise ArtifactError("standing fixture has no original seal")
            return 0
        if not fixture_paths:
            raise ArtifactError("standing fixture is missing; never skipped")
        f = self.fixture
        members = {p[len(INLINE_FIXTURE):]: index[p] for p in fixture_paths}
        if len(members) != f["files"] or _tree_oid(members) != f["tree"]:
            raise ArtifactError("standing fixture members differ from the sealed tree")
        oids = sorted({oid for _, oid in members.values()})
        result = subprocess.run(
            ["git", "--no-replace-objects", "-C", str(self.root), "cat-file", "--batch-check=%(objectname) %(objectsize)"],
            input=("\n".join(oids) + "\n").encode(), capture_output=True, env=_git_environment())
        measured = {}
        for line in result.stdout.decode().splitlines():
            oid, size = line.split()
            if size == "missing":
                raise ArtifactError("current standing fixture blob is unavailable")
            measured[oid] = int(size)
        if result.returncode or set(measured) != set(oids):
            raise ArtifactError("cannot measure the standing fixture")
        if sum(measured[oid] for _, oid in members.values()) != f["bytes"]:
            raise ArtifactError("standing fixture member bytes differ from the seal")
        manifest = index.get(f["manifest_path"])
        if manifest is None or manifest[1] != f["manifest_git_blob"]:
            raise ArtifactError("standing fixture manifest identity differs")
        if hashlib.sha256(self._current_blob(manifest[1])).hexdigest() != f["manifest_sha256"]:
            raise ArtifactError("standing fixture manifest digest differs")
        return len(members)

    def check_index(self):
        """Local custody check of the current index (gate 0). It reads no
        historical object: `audit` binds the catalog to its source trees."""
        index = self._index()
        catalog = index.get(CATALOG)
        if catalog is None or catalog[0] not in {"100644", "100755"}:
            raise ArtifactError("artifact catalog must be a regular file in the current index")
        # Bind the data that was parsed, not a fresh working-file read: a
        # later edit cannot make this Store's rules match a different index.
        try:
            indexed = json.loads(self._current_blob(catalog[1]).decode("utf-8"), object_pairs_hook=_unique_pairs)
        except ValueError as error:
            raise ArtifactError(f"cannot read indexed artifact catalog: {error}") from error
        if json.dumps(indexed, sort_keys=True) != self._catalog_snapshot:
            raise ArtifactError("parsed artifact catalog differs from the current index; stage the intended catalog")
        generated = [p for p in index if is_archive(p) and not p.startswith(INLINE_FIXTURE)]
        if generated:
            raise ArtifactError("generated report archives remain in source: " + ", ".join(generated[:8]))
        returned = sorted({path for _, path in self.records} & set(index))
        if returned:
            raise ArtifactError("cataloged artifacts are back in source: " + ", ".join(returned[:8]))
        fixture_files = self._check_fixture(index)
        return {"archive_files": len(self.records), "archive_bytes": sum(r["bytes"] for r in self.records.values()), "inline_fixture_files": fixture_files, "scope": "Current-index custody check from local index rows and current blobs; `audit` binds every row to its original source tree. No proof or release grade"}

    def _holds_fixture(self, source):
        """Whether an original source tree has the standing fixture's prefix."""
        try:
            return any(p.startswith(INLINE_FIXTURE) for p in self._source_rows(source))
        except ArtifactError:
            if not self.fetch:
                raise
        reports = self._remote_tree(source, self.sources[source]["tree"]).get("reports")
        if reports is None or reports["type"] != "tree":
            return False
        return INLINE_FIXTURE.split("/")[1] in self._remote_tree(source, reports["sha"])

    def audit(self):
        """Every catalog row equals its original source tree (path, mode, Git
        blob, bytes); the fixture seal equals its source's prefix tree, and no
        source holds the fixture while the catalog has no seal. Reads
        historical commits: local objects, or Agh with --fetch."""
        for row in self.records.values():
            self._bound(row)
        fixture_files = 0
        if self.fixture is None:
            # A catalog whose original sources hold the standing fixture
            # cannot erase its duty by dropping the seal (check-index holds
            # only the reviewed source's case, the one it can see locally).
            if any(self._holds_fixture(source) for source in self.sources):
                raise ArtifactError("original standing fixture has no seal; never skipped")
        else:
            f = self.fixture
            try:
                rows = {p: r for p, r in self._source_rows(f["source"]).items() if p.startswith(INLINE_FIXTURE)}
            except ArtifactError:
                if not self.fetch:
                    raise
                rows = self._remote_rows(f["source"], INLINE_FIXTURE.rstrip("/"))
            members = {p[len(INLINE_FIXTURE):]: (r["mode"], r["git_blob"]) for p, r in rows.items()}
            if len(members) != f["files"] or sum(r["bytes"] for r in rows.values()) != f["bytes"] or _tree_oid(members) != f["tree"]:
                raise ArtifactError("standing fixture seal differs from its original source tree")
            manifest = rows.get(f["manifest_path"])
            if manifest is None or manifest["git_blob"] != f["manifest_git_blob"]:
                raise ArtifactError("standing fixture manifest identity differs from its original source tree")
            with tempfile.TemporaryFile() as stream:
                self._copy_verified({**manifest, "sha256": f["manifest_sha256"]}, stream)
            fixture_files = len(members)
        return {"audited_files": len(self.records), "audited_bytes": sum(r["bytes"] for r in self.records.values()), "sources": len(self.sources), "inline_fixture_files": fixture_files, "scope": "Every catalog row and the fixture seal equal their original source trees; transport custody only, no proof or release grade"}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--catalog", type=Path)
    parser.add_argument("--fetch", action="store_true", help="explicit authenticated Agh retrieval when original Git objects are unavailable")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("check-index", help="refuse generated archives and preserve the exact standing fixture (local: reads no historical object)")
    sub.add_parser("audit", help="bind every catalog row and the fixture seal to the original source trees (reads history; --fetch for Agh)")
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
        elif args.command == "audit":
            result = store.audit()
        else:
            result = store.materialize(args.selector, args.destination, args.source, report=args.command == "restore-report")
        print(json.dumps(result, sort_keys=True, indent=2))
        return 0
    except (ArtifactError, OSError, ValueError) as error:
        print(f"REPORT-ARTIFACT REFUSED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
