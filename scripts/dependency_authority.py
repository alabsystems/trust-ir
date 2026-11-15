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


def manifest(repository: str, revision: str) -> bytes:
    remote(repository, revision)
    commit = api(repository, f"git/commits/{revision}")
    require(commit.get("sha") == revision, "commit response identity mismatch")
    root = commit.get("tree", {}).get("sha", "")
    exact_revision(root)
    tree = api(repository, f"git/trees/{root}")
    require(tree.get("sha") == root and tree.get("truncated") is False,
            "incomplete or mismatched root tree")
    entries = [e for e in tree.get("tree", []) if e.get("path") == "Cargo.toml"]
    require(len(entries) == 1, "expected one root Cargo.toml")
    entry = entries[0]
    require(entry.get("type") == "blob" and entry.get("mode") == "100644",
            "authority manifest must be an ordinary tracked file")
    oid = entry.get("sha", "")
    exact_revision(oid)
    blob = api(repository, f"git/blobs/{oid}")
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
    return data


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
