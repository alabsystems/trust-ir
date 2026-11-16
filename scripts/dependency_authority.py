#!/usr/bin/env python3
"""Owner-routed immutable dependency bytes; no direct GitHub Git fallback."""
from __future__ import annotations
import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

MAX_MANIFEST = 1024 * 1024
# Each dependency repository by its full GitHub slug, spelled as a literal so
# the publication engine's owner rewrite maps it to the public owner in the
# exported tree (an f-string owner would ship the development owner).
REPOSITORIES = {"clean": "alabsystems/clean", "ay": "alabsystems/ay"}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def git_environment() -> dict[str, str]:
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1",
               GIT_GRAFT_FILE=os.devnull, GIT_NO_REPLACE_OBJECTS="1",
               GIT_NO_LAZY_FETCH="1", GIT_TERMINAL_PROMPT="0")
    return env


def exact_revision(revision: str) -> None:
    require(re.fullmatch(r"[0-9a-f]{40}", revision) is not None, "expected exact commit SHA")


def invoke(arguments: list[str]) -> bytes:
    agh = shutil.which("agh")
    require(agh is not None, "native Agh required; no direct Git or anonymous API fallback")
    return subprocess.check_output([agh, "--no-anonymous-api", *arguments])


def remote(repository: str, revision: str) -> None:
    require(repository in REPOSITORIES, "unsupported dependency repository")
    exact_revision(revision)
    actual = invoke(["rev", f"{REPOSITORIES[repository]}@{revision}", "--jq", ".sha"])
    require(actual.strip() == revision.encode("ascii"), "Agh resolved a different commit")


def api(repository: str, suffix: str) -> dict:
    require(repository in REPOSITORIES, "unsupported dependency repository")
    result = json.loads(invoke(["api", f"repos/{REPOSITORIES[repository]}/{suffix}"]))
    require(isinstance(result, dict), "expected GitHub object")
    return result


class MissingManifest(ValueError):
    """An authenticated complete tree has no requested path entry."""


class ManifestAuthority:
    """Read exact dependency manifests through one authenticated commit tree.

    Package versions can be independent of the workspace version. Resolve
    their manifests from the same immutable revision, never checkout bytes.
    Cached trees and blobs are data for this instance's fixed revision only.
    """

    def __init__(self, repository: str, revision: str) -> None:
        remote(repository, revision)
        commit = api(repository, f"git/commits/{revision}")
        require(commit.get("sha") == revision, "commit response identity mismatch")
        self.root = commit.get("tree", {}).get("sha", "")
        exact_revision(self.root)
        self.repository = repository
        self.revision = revision
        self.trees: dict[str, list[dict]] = {}
        self.manifests: dict[str, tuple[bytes, str]] = {}
        self.absent: set[str] = set()

    def tree(self, oid: str) -> list[dict]:
        exact_revision(oid)
        if oid not in self.trees:
            tree = api(self.repository, f"git/trees/{oid}")
            require(tree.get("sha") == oid and tree.get("truncated") is False,
                    "incomplete or mismatched root tree")
            entries = tree.get("tree")
            require(isinstance(entries, list) and all(isinstance(e, dict) for e in entries),
                    "invalid manifest tree entries")
            self.trees[oid] = entries
        return self.trees[oid]

    def read(self, path: str) -> tuple[bytes, str]:
        require(isinstance(path, str) and len(path) <= 4096,
                "invalid manifest path")
        parts = path.split("/")
        require(1 <= len(parts) <= 32 and parts[-1] == "Cargo.toml"
                and all(p not in ("", ".", "..") and "\\" not in p
                        and not any(ord(c) < 32 or ord(c) == 127 for c in p) for p in parts),
                "expected canonical repository-relative Cargo.toml path")
        if path in self.manifests:
            return self.manifests[path]
        if path in self.absent:
            raise MissingManifest("missing authority manifest: " + path)
        tree = self.root
        for index, part in enumerate(parts):
            entries = [e for e in self.tree(tree) if e.get("path") == part]
            if not entries:
                self.absent.add(path)
                raise MissingManifest("missing authority manifest: " + path)
            require(len(entries) == 1, "expected one authority manifest path entry: " + path)
            entry = entries[0]
            oid = entry.get("sha", "")
            exact_revision(oid)
            if index < len(parts) - 1:
                require(entry.get("type") == "tree" and entry.get("mode") == "040000",
                        "authority manifest ancestor must be a tracked directory")
                tree = oid
                continue
            require(entry.get("type") == "blob" and entry.get("mode") == "100644",
                    "authority manifest must be an ordinary tracked file")
            blob = api(self.repository, f"git/blobs/{oid}")
            size = blob.get("size")
            require(blob.get("sha") == oid and blob.get("encoding") == "base64"
                    and type(size) is int and 0 <= size <= MAX_MANIFEST,
                    "invalid manifest blob metadata")
            content = blob.get("content")
            require(isinstance(content, str), "missing raw blob content")
            data = base64.b64decode("".join(content.split()), validate=True)
            require(len(data) == size, "manifest byte length mismatch")
            require(hashlib.sha1(b"blob " + str(size).encode("ascii") + b"\0" + data).hexdigest() == oid,
                    "manifest Git blob digest mismatch")
            self.manifests[path] = data, oid
        return self.manifests[path]

    def optional(self, path: str) -> tuple[bytes, str] | None:
        """Workspace discovery may skip absence, never malformed authority."""
        try:
            return self.read(path)
        except MissingManifest:
            return None


def manifest(repository: str, revision: str) -> bytes:
    return ManifestAuthority(repository, revision).read("Cargo.toml")[0]


def offline_manifest(cache: Path, revision: str) -> bytes:
    # Explicit offline preparation retains its old local-only scope. It never
    # establishes remote availability and is not an online fallback.
    exact_revision(revision)
    return subprocess.check_output(
        ["git", "-C", str(cache), "show", f"{revision}:Cargo.toml"], env=git_environment())


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("operation", choices=("remote", "manifest", "offline-manifest"))
    parser.add_argument("repository")
    parser.add_argument("revision")
    args = parser.parse_args()
    if args.operation == "remote":
        remote(args.repository, args.revision)
    else:
        data = offline_manifest(Path(args.repository), args.revision) if args.operation == "offline-manifest" else manifest(args.repository, args.revision)
        sys.stdout.buffer.write(data)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as error:
        print(f"dependency authority refused: {error}", file=sys.stderr)
        sys.exit(1)
