#!/usr/bin/env python3
"""Which legs of scripts/ci_gates.sh a change can reach, and which of those a
recorded PASS already covers.

ci_gates.sh asks this script for a PLAN before it runs anything. A plan names,
for every leg (`gate <name> ...` in ci_gates.sh) and for every test target of
the target-list legs, one of:

  run                      its inputs intersect the change, and no PASS is
                           recorded for its complete input key;
  skip: unchanged          none of its inputs changed since the base;
  skip: cached PASS        a PASS is recorded for exactly this input key.

THE INPUTS OF A LEG are read from the real build graph, never from a hand list:

  * Rust: `targo metadata --no-deps` for the workspace and for the excluded
    `frontend/` package gives every package, its targets and its PATH
    dependencies by kind. A test run of a target reaches its package's direct
    dependencies of every kind (dev included) and their normal/build closure;
    a build of a lib or bin reaches the normal/build closure. Every file under
    a reached package's directory is an input (fixtures included).
  * Rust files OUTSIDE the target's package: the target's module closure
    (`mod`, `#[path]`, `include!`/`include_str!`/`include_bytes!`), followed
    across crate boundaries, so a test that `#[path]`-includes another crate's
    file has that file as an input.
  * Runtime reads outside the package ("escapes"): every string literal of
    every file of the target's module closure, and of the lib closure of every
    package it reaches, that climbs out of its package (`"../.."`,
    `concat!(env!("CARGO_MANIFEST_DIR"), "/../x")`) is resolved to the repo
    path it names. A file that climbs to the REPO ROOT (or uses
    `.parent()`/`.ancestors()`/`current_dir` beside `CARGO_MANIFEST_DIR`) can
    read anything: its reads are EVERYTHING unless scripts/gates/test-reads.tsv
    declares them, and a declaration must cover every path literal of the file
    that names a repo path (checked here; an uncovered literal makes the reads
    EVERYTHING again). An `exists:` declaration is a read of a path's
    existence: its bit is in the key, and a change that adds or removes the
    path (against the base tree) selects the reader. A file that runs `git`
    reads history: its key carries HEAD, the merge-base and origin/main.
  * Name-filtered lib tests (`--lib alloc_bound::`) read EVERY `#[cfg(test)]`
    module of their crate: libtest's filter is a substring of the whole test
    path, so a test module anywhere can run under it.
  * Doctests: the doc comments of the crate (and any document it includes as
    its docs) are read for climbing paths; a climb from the package anchor
    in doc text reads EVERYTHING.
  * Lean: `import` lines (read as gate 14 reads them: comments stripped,
    every line), closed from the root a leg builds (`lean:` patterns).
  * Python legs: the paths their scripts read (UNITS below).

FAIL-CLOSED. The plan runs EVERY leg, with no cache, when:
  * the base cannot be resolved or the diff cannot be read;
  * the Rust graph cannot be read;
  * a changed path is a build or gate input (GLOBAL): any Cargo.toml or
    Cargo.lock, rust-toolchain*, .cargo/, build.rs, Lean package
    configuration, rustfmt/clippy configuration, .gitattributes/.gitignore,
    a dependency-pin leg (scripts/pin_rewrite.py LEGS), or anything under
    scripts/ (the gate scripts, their registries and their tests);
  * a changed path is UNMAPPED: no leg with a specific input pattern claims it
    and it is not documentation (DOC);
When only the toolchain identity or environment differs from the last GREEN
run on this host (or none is recorded), every leg is required, but a matching
complete-input PASS may be reused. Failed and unmeasured inputs run again.
This recovery never uses the diff to skip an unchanged leg, and a run with
a failure still records no green identity. The hard fallbacks above and an
explicit --all remain uncached, including when an identity change also occurs.
A documentation-only change (DOC paths no compiled leg reads) runs only the
legs whose inputs are the whole tree: the link and enforcement checks, the
gate tooling's tests, and the wire-allocation owners audit.

THE CACHE. A PASS is recorded per leg (and per test target) under a key that
hashes the COMPLETE input set: the blob of every input file and of every
GLOBAL file (so every gate script), the leg's own command, its reviewed
execution identity (tool paths, versions and wrapper bytes), and the
environment (including temporary roots and Python startup settings). Only
the exact launcher selectors explicitly irrelevant to that unit are omitted;
unknown units retain all tools and variables. The aggregate toolchain and
environment remain the whole-run completion guard. Any Cargo
configuration file outside the tree (an uncommitted `.cargo/config.toml` patch
changes a Cargo unit without changing the tree), the existence bit of each
`exists:` read, and — for a leg that reads history — HEAD, the merge-base and
origin/main. A PASS is recorded only while the planned inputs still match.
A later FAIL replaces a PASS of the same key, including attempted targets.
Completion checks every required result or reused key and the input bookends
before it can record a green identity. A leg with an input outside the tree that no key can
name (origin's branches, the toolchain's file modes) is never cached. The
cache lives in the git common directory, so every worktree of one clone
shares it. Override with TRUST_IR_GATE_CACHE. Version-2 receipts lack these
execution preimages and are not migrated or relabeled as version-3 passes.

Usage:
  gate_select.py plan   [--root R] [--base REV | --all] --out PLAN.json
  gate_select.py action --plan PLAN.json --unit NAME         # run|skip TAB reason TAB targets
  gate_select.py record --plan PLAN.json --unit NAME [--targets T...] [--result PASS|FAIL]
  gate_select.py finish --plan PLAN.json --results RESULTS.tsv          # the run record
  gate_select.py replay [--root R] [--ref origin/main] [--count 50]      # history, no builds
  gate_select.py audit  [--root R]                                      # escapes and declarations
"""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import os
import platform
import posixpath
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Dict, Iterable, List, Optional, Sequence, Set, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent

PLAN_SCHEMA = "trust-ir-gate-plan-v3"
EVERYTHING = "*"
EXISTS = "exists:"  # a read pattern naming a path read for its existence only
READS_FILE = "scripts/gates/test-reads.tsv"

# --------------------------------------------------------------------------
# Path classes
# --------------------------------------------------------------------------

# A change to any of these runs EVERYTHING (build, toolchain, pin and gate
# inputs). `fnmatch` patterns: `*` matches across `/`.
GLOBAL_EXACT = frozenset(
    {
        "Cargo.toml",
        "Cargo.lock",
        "rust-toolchain",
        "rust-toolchain.toml",
        "build.rs",
        ".gitattributes",
        ".gitignore",
        "rustfmt.toml",
        ".rustfmt.toml",
        "clippy.toml",
        ".clippy.toml",
    }
)
GLOBAL_GLOBS = (
    "*/Cargo.toml",
    "*/Cargo.lock",
    "*/build.rs",
    "*/rust-toolchain",
    "*/rust-toolchain.toml",
    ".cargo/*",
    "*/.cargo/*",
    "*/rustfmt.toml",
    "*/.rustfmt.toml",
    "*/clippy.toml",
    "*/.clippy.toml",
    "*/lakefile.lean",
    "*/lakefile.toml",
    "*/lean-toolchain",
    "*/lake-manifest.json",
    "scripts/*",
)

# Documentation and publication data: read by no compiled leg unless a test
# declares (or literally names) the file, so a change here alone runs only the
# whole-tree legs and the targets that read it.
DOC_PREFIXES = ("docs/", "designs/", "reports/", "publish/")
DOC_ROOT_GLOBS = ("*.md", "LICENSE*", "NOTICE*")


def is_global(path: str, pin_legs: Set[str]) -> bool:
    if path in GLOBAL_EXACT or path in pin_legs:
        return True
    return any(fnmatch.fnmatchcase(path, g) for g in GLOBAL_GLOBS)


def is_doc(path: str) -> bool:
    if path.startswith(DOC_PREFIXES):
        return True
    return "/" not in path and any(fnmatch.fnmatchcase(path, g) for g in DOC_ROOT_GLOBS)


def pattern_matches(pattern: str, path: str) -> bool:
    """A pattern is EVERYTHING, a directory prefix ending in `/`, an fnmatch
    glob (contains `*`, `?` or `[`), or an exact path."""
    if pattern == EVERYTHING:
        return True
    if pattern.endswith("/"):
        return path.startswith(pattern)
    if any(c in pattern for c in "*?["):
        return fnmatch.fnmatchcase(path, pattern)
    return path == pattern


def any_match(patterns: Iterable[str], path: str) -> bool:
    return any(pattern_matches(p, path) for p in patterns)


# --------------------------------------------------------------------------
# git
# --------------------------------------------------------------------------


class GitError(RuntimeError):
    pass


def git(root: Path, *args: str, check: bool = True, input_bytes: Optional[bytes] = None) -> bytes:
    proc = subprocess.run(
        ["git", "-C", os.fspath(root), *args],
        input=input_bytes,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if check and proc.returncode != 0:
        raise GitError(f"git {' '.join(args)}: {proc.stderr.decode(errors='replace').strip()}")
    return proc.stdout


def git_text(root: Path, *args: str) -> Optional[str]:
    try:
        return git(root, *args).decode().strip() or None
    except GitError:
        return None


def zsplit(data: bytes) -> List[str]:
    return [p.decode("utf-8", "surrogateescape") for p in data.split(b"\0") if p]


class Tree:
    """The working tree as git sees it — tracked files plus untracked files
    that are not ignored — with a blob id per path. Nothing is written to the
    object store (`hash-object` without -w)."""

    def __init__(self, root: Path, files: Optional[Dict[str, str]] = None):
        self.root = root
        self.files: Dict[str, str] = files if files is not None else self._read(root)

    @staticmethod
    def _read(root: Path) -> Dict[str, str]:
        files: Dict[str, str] = {}
        for raw in git(root, "ls-files", "-s", "-z").split(b"\0"):
            if not raw:
                continue
            meta, path = raw.split(b"\t", 1)
            mode, blob, _stage = meta.decode().split()
            if mode == "160000":  # a submodule: its commit is the identity
                files[path.decode("utf-8", "surrogateescape")] = "commit:" + blob
                continue
            files[path.decode("utf-8", "surrogateescape")] = blob
        dirty = set(zsplit(git(root, "diff", "--name-only", "-z")))
        dirty |= set(zsplit(git(root, "ls-files", "--others", "--exclude-standard", "-z")))
        present = sorted(p for p in dirty if (root / p).is_file())
        for p in dirty - set(present):
            files.pop(p, None)  # deleted in the working tree
        if present:
            out = git(root, "hash-object", "--stdin-paths", input_bytes="\n".join(present).encode() + b"\n")
            for p, blob in zip(present, out.decode().split()):
                files[p] = blob
        return files

    def top_level(self) -> Set[str]:
        if not hasattr(self, "_tops"):
            self._tops = {p.split("/", 1)[0] for p in self.files}
        return self._tops

    def paths(self) -> List[str]:
        if not hasattr(self, "_sorted"):
            self._sorted = sorted(self.files)
        return self._sorted

    def read_text(self, path: str) -> Optional[str]:
        try:
            return (self.root / path).read_text(encoding="utf-8", errors="replace")
        except OSError:
            return None

    def exists(self, path: str) -> bool:
        """A file or a directory (some file lies under it)."""
        if path in ("", "."):
            return True
        if path in self.files:
            return True
        prefix = path.rstrip("/") + "/"
        return any(p.startswith(prefix) for p in self._sorted_from(prefix))

    def is_dir(self, path: str) -> bool:
        prefix = path.rstrip("/") + "/"
        return path in ("", ".") or any(True for _ in self._sorted_from(prefix))

    def _sorted_from(self, prefix: str) -> Iterable[str]:
        if not hasattr(self, "_sorted"):
            self._sorted = sorted(self.files)
        import bisect

        i = bisect.bisect_left(self._sorted, prefix)
        while i < len(self._sorted) and self._sorted[i].startswith(prefix):
            yield self._sorted[i]
            i += 1

    def select_paths(self, patterns: Iterable[str]) -> List[str]:
        """Every tree path some pattern matches (prefixes by range, exact
        paths by lookup, globs by scan)."""
        pats = set(patterns)
        if EVERYTHING in pats:
            return self.paths()
        out: Set[str] = set()
        globs = []
        for p in pats:
            if p.endswith("/"):
                out.update(self._sorted_from(p))
            elif any(c in p for c in "*?["):
                globs.append(p)
            elif p in self.files:
                out.add(p)
        for g in globs:
            out.update(self.glob(g))
        return sorted(out)

    def glob(self, pattern: str) -> Set[str]:
        """Every tree path an fnmatch pattern matches (memoized: the GLOBAL
        globs are part of every key)."""
        if not hasattr(self, "_globs"):
            self._globs: Dict[str, Set[str]] = {}
        if pattern not in self._globs:
            rx = re.compile(fnmatch.translate(pattern))
            self._globs[pattern] = {q for q in self.paths() if rx.match(q)}
        return self._globs[pattern]

    def digest(self, patterns: Iterable[str]) -> Tuple[str, int]:
        h = hashlib.sha256()
        paths = self.select_paths(patterns)
        for p in paths:
            h.update(p.encode("utf-8", "surrogateescape") + b"\0" + self.files[p].encode() + b"\n")
        return h.hexdigest(), len(paths)


def changed_paths(root: Path, base: str) -> List[str]:
    """Every path that differs between `base` and the working tree (tracked,
    staged or not, both sides of a rename) plus every untracked, unignored
    file."""
    out = set(zsplit(git(root, "diff", "--name-only", "-z", "--no-renames", base, "--")))
    out |= set(zsplit(git(root, "ls-files", "--others", "--exclude-standard", "-z")))
    return sorted(out)


def exists_at(root: Path, rev: str, path: str) -> bool:
    """Whether `path` (a file or a directory) exists in commit `rev`."""
    return bool(git(root, "ls-tree", "--name-only", rev, "--", path).strip())


def existence_flips(units: Dict[str, "Unit"], before: Callable[[str], bool], after: Callable[[str], bool]) -> List[str]:
    """The `exists:` reads of every unit whose answer differs between two
    trees."""
    paths = {p[len(EXISTS):] for u in units.values()
             for pats in [u.patterns, *u.targets.values()] for p in pats if p.startswith(EXISTS)}
    return sorted(p for p in paths if before(p) != after(p))


def resolve_base(root: Path, explicit: Optional[str]) -> Tuple[Optional[str], str]:
    """(commit, how). The merge-base of HEAD with origin/main (else main)."""
    if explicit:
        sha = git_text(root, "rev-parse", "--verify", f"{explicit}^{{commit}}")
        return sha, f"--base {explicit}"
    for ref in ("origin/main", "main"):
        if git_text(root, "rev-parse", "--verify", f"{ref}^{{commit}}"):
            sha = git_text(root, "merge-base", "HEAD", ref)
            if sha:
                return sha, f"merge-base(HEAD, {ref})"
    return None, "no origin/main or main to take a merge-base with"


# --------------------------------------------------------------------------
# Rust graph
# --------------------------------------------------------------------------


@dataclass
class Target:
    package: str
    kind: str  # lib | bin | test | example | bench | custom-build | proc-macro
    name: str
    src: str  # repo-relative
    test: bool  # `cargo test` runs it


@dataclass
class Package:
    name: str
    dir: str  # repo-relative, no trailing slash
    workspace: str  # "root" | "frontend"
    deps: List[Tuple[str, str]]  # (dep dir, kind: normal | dev | build), PATH deps only
    targets: List[Target]
    default_member: bool = False


def _rel(root: Path, p: str) -> Optional[str]:
    try:
        return Path(p).resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return None


def parse_metadata(root: Path, data: dict, workspace: str) -> Dict[str, Package]:
    default = set(data.get("workspace_default_members") or data.get("workspace_members") or [])
    members = set(data.get("workspace_members") or [])
    out: Dict[str, Package] = {}
    for p in data["packages"]:
        if p["id"] not in members:
            continue
        pdir = _rel(root, str(Path(p["manifest_path"]).parent))
        if pdir is None:
            raise ValueError(f"package {p['name']} lies outside the repository")
        deps = []
        for d in p.get("dependencies", []):
            if d.get("path"):
                ddir = _rel(root, d["path"])
                if ddir is None:
                    raise ValueError(f"{p['name']}: path dependency {d['name']} lies outside the repository")
                deps.append((ddir, d.get("kind") or "normal"))
        targets = []
        for t in p["targets"]:
            src = _rel(root, t["src_path"])
            if src is None:
                raise ValueError(f"{p['name']}: target {t['name']} lies outside the repository")
            kind = t["kind"][0] if t["kind"] else "lib"
            if kind in ("rlib", "dylib", "cdylib", "staticlib"):
                kind = "lib"
            targets.append(Target(p["name"], kind, t["name"], src, bool(t.get("test", kind != "custom-build"))))
        out[pdir] = Package(p["name"], pdir, workspace, deps, targets, p["id"] in default)
    return out


def load_metadata(root: Path) -> Dict[str, Package]:
    """Both Cargo graphs: the workspace and the excluded frontend package."""
    runner = root / "scripts" / "run-targo.sh"
    packages: Dict[str, Package] = {}
    for workspace, manifest in (("root", root / "Cargo.toml"), ("frontend", root / "frontend" / "Cargo.toml")):
        if not manifest.is_file():
            continue
        proc = subprocess.run(
            [os.fspath(runner), "metadata", "--no-deps", "--format-version", "1", "--offline",
             "--manifest-path", os.fspath(manifest)],
            cwd=os.fspath(root), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        )
        if proc.returncode != 0:
            raise RuntimeError(f"targo metadata ({workspace}) failed: {proc.stderr.decode(errors='replace')[-400:]}")
        packages.update(parse_metadata(root, json.loads(proc.stdout), workspace))
    return packages


def closure_dirs(packages: Dict[str, Package], pdir: str, test_run: bool) -> Set[str]:
    """Package dirs a build of `pdir` reaches (normal + build edges,
    transitively); a test run also takes its own dev edges (not theirs)."""
    seen: Set[str] = {pdir}
    stack = [d for d, kind in packages[pdir].deps if kind != "dev" or test_run]
    while stack:
        d = stack.pop()
        if d in seen:
            continue
        seen.add(d)
        if d in packages:
            stack.extend(dd for dd, kind in packages[d].deps if kind != "dev")
    return seen


# --------------------------------------------------------------------------
# Rust sources: literals, modules, escapes
# --------------------------------------------------------------------------

_TOKEN = re.compile(
    r"""(?P<lc>//[^\n]*)"""
    r"""|(?P<bc>/\*)"""
    r"""|(?P<raw>(?<![A-Za-z0-9_])(?:br|cr|r)(?P<h>\#*)")"""
    r"""|(?P<str>(?:(?<![A-Za-z0-9_])[bc])?"(?:[^"\\]|\\.)*")"""
    r"""|(?P<chr>'(?:[^'\\\n]|\\[^\n]{1,10}?)')""",
    re.S,
)


_NEUTRAL = str.maketrans({"{": " ", "}": " ", ";": " ", "(": " ", ")": " "})


def lex_rust3(
    text: str, ctx: Optional[List[str]] = None, masked: Optional[List[str]] = None
) -> Tuple[List[str], str, str]:
    """(string literal contents, code with comments removed and literals
    blanked to `""`, text with comments removed and literals kept). With
    `ctx`, the 48 characters of comment-free text before each literal are
    appended to it (what the literal is an argument of). With `masked`, the
    comment-free text with every `{ } ; ( )` INSIDE a literal blanked is
    appended to it (so braces and statements can be matched)."""
    lits: List[str] = []
    code: List[str] = []
    keep: List[str] = []
    pos, n = 0, len(text)
    while pos < n:
        m = _TOKEN.search(text, pos)
        if m is None:
            code.append(text[pos:])
            keep.append(text[pos:])
            if masked is not None:
                masked.append(text[pos:])
            break
        code.append(text[pos:m.start()])
        keep.append(text[pos:m.start()])
        if masked is not None:
            masked.append(text[pos:m.start()])
        kind = m.lastgroup if m.lastgroup != "h" else "raw"
        if m.group("lc") is not None:
            pos = m.end()
        elif m.group("bc") is not None:
            depth, j = 1, m.end()
            while j < n and depth:
                k = text.find("/*", j)
                e = text.find("*/", j)
                if e < 0:
                    j = n
                    break
                if 0 <= k < e:
                    depth, j = depth + 1, k + 2
                else:
                    depth, j = depth - 1, e + 2
            code.append(" ")
            keep.append(" ")
            if masked is not None:
                masked.append(" ")
            pos = j
        elif m.group("raw") is not None:
            term = '"' + m.group("h")
            j = text.find(term, m.end())
            j = n if j < 0 else j
            lits.append(text[m.end():j])
            if ctx is not None:
                ctx.append("".join(keep[-8:])[-48:])
            code.append('""')
            keep.append(text[m.start():j + len(term)])
            if masked is not None:
                masked.append(text[m.start():j + len(term)].translate(_NEUTRAL))
            pos = j + len(term)
        elif m.group("str") is not None:
            body = m.group("str")
            q = body.index('"')
            lits.append(body[q + 1:-1])
            if ctx is not None:
                ctx.append("".join(keep[-8:])[-48:])
            code.append('""')
            keep.append(body)
            if masked is not None:
                masked.append(body.translate(_NEUTRAL))
            pos = m.end()
        else:  # a char literal
            code.append("' '")
            keep.append(m.group(0))
            if masked is not None:
                masked.append(m.group(0).translate(_NEUTRAL))
            pos = m.end()
        del kind
    return lits, "".join(code), "".join(keep)


def lex_rust(text: str) -> Tuple[List[str], str]:
    lits, code, _ = lex_rust3(text)
    return lits, code


_MOD_DECL = re.compile(
    r"(?P<attrs>(?:#\s*\[[^\]]*\]\s*)*)(?:pub(?:\s*\([^)]*\))?\s+)?mod\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*;"
)
_MOD_NAME = re.compile(r"\bmod\s+([A-Za-z_][A-Za-z0-9_]*)\s*;")
_PATH_ATTR = re.compile(r'#\s*\[\s*path\s*=\s*"(?P<p>[^"]+)"\s*\]')
# `#[cfg(test)]` / `#[cfg(all(test, ...))]`: compiled only into the crate's own
# test harness, never when the crate is a dependency.
_CFG_TEST = re.compile(r"#\s*\[\s*cfg\s*\((?:\s*all\s*\()?\s*test\b")
_INCLUDE = re.compile(r'\binclude(?:_str|_bytes)?\s*!\s*\(\s*"(?P<p>[^"]+)"\s*\)')


@dataclass
class SourceFile:
    path: str
    literals: List[str]
    code: str
    mods: List[Tuple[str, Optional[str], bool]]  # (name, #[path] value, cfg(test) only)
    includes: List[str]
    text_nc: str  # comments removed, literals kept
    lit_ctx: List[str]  # the code just before each literal
    text_mask: str  # text_nc with `{ } ; ( )` inside literals blanked


class Sources:
    """Parsed Rust files of the tree, memoized."""

    def __init__(self, tree: Tree):
        self.tree = tree
        self._cache: Dict[str, Optional[SourceFile]] = {}

    def get(self, path: str) -> Optional[SourceFile]:
        if path not in self._cache:
            text = self.tree.read_text(path) if path in self.tree.files else None
            if text is None:
                self._cache[path] = None
            else:
                ctx: List[str] = []
                mask: List[str] = []
                lits, code, nc = lex_rust3(text, ctx, mask)
                mods = []
                for m in _MOD_NAME.finditer(nc):
                    m_name = m.group(1)
                    # the attributes are what precedes `mod` back to the end of
                    # the previous item (`;`, `{` or `}`)
                    start = max(nc.rfind(";", 0, m.start()), nc.rfind("{", 0, m.start()),
                                nc.rfind("}", 0, m.start()))
                    attrs = nc[start + 1:m.start()]
                    pa = _PATH_ATTR.search(attrs)
                    mods.append((m_name, pa.group("p") if pa else None, bool(_CFG_TEST.search(attrs))))
                includes = [m.group("p") for m in _INCLUDE.finditer(nc)]
                self._cache[path] = SourceFile(path, lits, code, mods, includes, nc, ctx, "".join(mask))
        return self._cache[path]


def norm(path: str) -> str:
    p = posixpath.normpath(path)
    return "" if p == "." else p


def module_closure(src: Sources, root_file: str, cfg_test: bool = True) -> Tuple[List[str], bool]:
    """Every file compiled into the crate rooted at `root_file` (mod tree,
    #[path], include*!), and whether some module could not be found.
    `cfg_test=False` leaves out `#[cfg(test)]` modules: the closure of a lib
    as a DEPENDENCY of another crate. A name-filtered lib-test run
    (`--lib alloc_bound::`) keeps EVERY `#[cfg(test)]` module: libtest's
    filter is a substring match on the whole test path, so a test module
    anywhere in the crate can run under it."""
    seen: List[str] = []
    unresolved = False
    stack: List[Tuple[str, bool, str]] = [(root_file, True, "")]
    visited: Set[str] = set()
    while stack:
        f, is_root, modpath = stack.pop()
        if f in visited:
            continue
        visited.add(f)
        sf = src.get(f)
        if sf is None:
            unresolved = True
            continue
        seen.append(f)
        fdir = posixpath.dirname(f)
        stem = posixpath.splitext(posixpath.basename(f))[0]
        mod_dir = fdir if (is_root or stem == "mod") else posixpath.join(fdir, stem)
        for name, pattr, test_only in sf.mods:
            child = f"{modpath}::{name}" if modpath else name
            if test_only and not cfg_test:
                continue
            if pattr is not None:
                cand = [norm(posixpath.join(fdir, pattr))]
            else:
                cand = [posixpath.join(mod_dir, name + ".rs"), posixpath.join(mod_dir, name, "mod.rs")]
            hit = next((c for c in cand if c in src.tree.files), None)
            if hit is None:
                # An inline `mod a { mod b; }` nests the path; look one level down.
                hit = next(
                    (p for p in src.tree._sorted_from(mod_dir + "/")
                     if p.endswith("/" + name + ".rs") or p.endswith("/" + name + "/mod.rs")),
                    None,
                )
            if hit is None:
                unresolved = True
                continue
            # A `#[path]` file owns its directory, like a mod.rs (rustc's
            # directory ownership); a plain `mod x;` file nests under x/.
            stack.append((hit, pattr is not None, child))
        for inc in sf.includes:
            p = norm(posixpath.join(fdir, inc))
            if p in src.tree.files:
                if inc.endswith(".rs"):
                    stack.append((p, True, modpath))
                else:
                    seen.append(p)
            # an include of a missing file fails the build; nothing to add
    return seen, unresolved


_CLIMB = re.compile(r"\.\s*(?:parent|ancestors)\s*\(\s*\)")
_ANCHOR = re.compile(r'"CARGO_MANIFEST_DIR"|\benv::current_dir\s*\(|\bcurrent_dir\s*\(\s*\)|\bfile!\s*\(|"CARGO_WORKSPACE_DIR"')
# The code a bare `..` literal is a PATH in: an argument of a path
# constructor, join, include, read or open. Elsewhere (`split_once("..")`,
# `== ".."`, `contains("..")`) it is text.
_PATH_CTX = re.compile(
    r"(?:\bjoin|\bnew|\bfrom|\bpush|\binclude(?:_str|_bytes)?!|\bconcat!|\bread_to_string|\bread_dir|\bread|\bopen|"
    r"\bexists|\bis_file|\bis_dir|\bcanonicalize|\bmetadata|\bwith_file_name|\bset_file_name|\bpath\s*=|,)\s*\(?\s*&?\s*$"
)


def _blocks(nc: str) -> List[Tuple[str, str]]:
    """(fn name, body) for every `fn` with a body, outermost first (a nested
    fn is also inside its parent's body)."""
    out = []
    for m in re.finditer(r"\bfn\s+([A-Za-z_]\w*)\b[^;{]*\{", nc):
        depth, j = 1, m.end()
        while j < len(nc) and depth:
            c = nc[j]
            depth += 1 if c == "{" else -1 if c == "}" else 0
            j += 1
        out.append((m.group(1), nc[m.end():j - 1]))
    return out


def anchored_climb(nc: str) -> Optional[str]:
    """A statement that climbs (`.parent()` / `.ancestors()`) from a path
    anchored at the package (CARGO_MANIFEST_DIR, the test's current dir,
    file!()), directly or through a `let`, a `const`/`static`, or a fn that
    returns one. Text before each `;`/`{`/`}` is one statement; bindings are
    tracked per fn body, constants and anchored fns per file."""
    anchors = set()
    for m in re.finditer(r"\b(?:const|static)\s+([A-Za-z_]\w*)\s*:[^=;]*=\s*([^;]*);", nc):
        if _ANCHOR.search(m.group(2)):
            anchors.add(m.group(1))
    blocks = _blocks(nc)
    changed = True
    while changed:  # an anchored fn anchors its callers' bindings
        changed = False
        for name, body in blocks:
            if name + "()" not in anchors and _mentions_anchor(body, anchors) and re.search(r"\bfn\b", body) is None:
                tail = body.strip().rsplit(";", 1)[-1]
                if _mentions_anchor(tail, anchors) or re.search(r"\breturn\b[^;]*", body) and _mentions_anchor(body, anchors):
                    anchors.add(name + "()")
                    changed = True
    # Bindings are tracked per fn body: two fns' `path`s are different
    # values. (A Rust file has no statements outside fns but consts/statics.)
    scopes = [b for _, b in blocks]
    for body in scopes:
        local = set(anchors)
        grew = True
        while grew:
            grew = False
            for m in re.finditer(r"\blet\s+(?:mut\s+)?([A-Za-z_]\w*)\s*(?::[^=;]*)?=\s*([^;]*);", body):
                if m.group(1) not in local and _mentions_anchor(m.group(2), local):
                    local.add(m.group(1))
                    grew = True
        for stmt in re.split(r"[;{}]", body):
            if _CLIMB.search(stmt) and _mentions_anchor(stmt, local):
                return " ".join(stmt.split())[:120]
    return None


def _mentions_anchor(text: str, anchors: Set[str]) -> bool:
    if _ANCHOR.search(text):
        return True
    for a in anchors:
        if a.endswith("()"):
            if re.search(r"\b" + re.escape(a[:-2]) + r"\s*\(\s*\)", text):
                return True
        elif re.search(r"(?<![\w.])" + re.escape(a) + r"\b", text):
            return True
    return False


_GIT_SPAWN = re.compile(r'Command::new\s*\(\s*(?:"git"|GIT)\s*\)')
# Doc comments: `///` and `//!` lines (not `////`), `/** */` and `/*! */`
# blocks. Over-approximate: a `///` inside a string literal counts too.
_DOC_LINE = re.compile(r"^[ \t]*//(?:/(?!/)|!)(.*)$", re.M)
_DOC_BLOCK = re.compile(r"/\*[*!](?![*/])(.*?)\*/", re.S)
_DOC_PATH_TOKEN = re.compile(r"[A-Za-z0-9_./-]+")


def doc_text(path: str, text: str) -> str:
    """The text rustdoc can run as doctests: a Rust file's doc comments; all
    of a document a crate includes as its docs (`#![doc = include_str!(..)]`)."""
    if not path.endswith(".rs"):
        return text
    return "\n".join([m.group(1) for m in _DOC_LINE.finditer(text)] + [m.group(1) for m in _DOC_BLOCK.finditer(text)])
_EXT = re.compile(r"\.(?:rs|toml|lock|tsv|md|json|msgpack|tmbc|lean|txt|py|sh|hex|bin|trust_ir)$")


@dataclass
class Escape:
    reads: Set[str] = field(default_factory=set)
    root: bool = False  # can reach anything
    why_root: str = ""
    git: bool = False
    literals: List[Tuple[str, str]] = field(default_factory=list)  # (literal, resolved repo path)


def file_escape(tree: Tree, sf: SourceFile, crate_dir: str) -> Escape:
    """What `sf` can read outside `crate_dir` at run time (or include)."""
    e = Escape()
    fdir = posixpath.dirname(sf.path)
    crate_prefix = crate_dir + "/"
    climbs_to_root = False
    anchor_dirs: List[str] = []  # directories outside the package a literal reaches
    for idx, lit in enumerate(sf.literals):
        if "\n" in lit or len(lit) > 400:
            continue
        s = lit[1:] if lit.startswith("/..") else lit
        if not (s == ".." or s.startswith("../") or "/../" in s or s.endswith("/..")):
            continue
        if s in ("..", "../") and not _PATH_CTX.search(sf.lit_ctx[idx] if idx < len(sf.lit_ctx) else ","):
            continue  # a bare `..` compared or split on, not joined
        # Run time resolves against the package (cargo's cwd for tests,
        # CARGO_MANIFEST_DIR); include!/#[path] against the file's directory.
        # A resolution that names an existing path wins over one that does not.
        res = []
        for base in (crate_dir, fdir):
            if s.startswith("/"):
                continue  # an absolute path: not a tree input
            r = norm(posixpath.join(base, s))
            if r.startswith("../") or r == "..":
                continue  # outside the repository (a sibling checkout): not a tree input
            if r not in res:
                res.append(r)
        existing = [r for r in res if r == "" or r in tree.files or tree.is_dir(r)]
        for r in existing or res:
            if r == "" or crate_prefix.startswith(r + "/"):
                climbs_to_root = True  # an anchor, not a read: what it reads is named by other literals
                continue
            if r == crate_dir or r.startswith(crate_prefix):
                continue
            e.literals.append((lit, r))
            if tree.is_dir(r):
                e.reads.add(r + "/")
                anchor_dirs.append(r)
            elif r in tree.files:
                e.reads.add(r)
            else:
                # names nothing that exists: take the nearest existing ancestor
                a = posixpath.dirname(r)
                while a not in ("", "/") and not tree.is_dir(a):
                    a = posixpath.dirname(a)
                a = a.strip("/")
                if a and not crate_prefix.startswith(a + "/"):
                    e.reads.add(a + "/")
                else:
                    climbs_to_root = True
    if climbs_to_root:
        e.root, e.why_root = True, "a literal climbs to the repository root"
    if _CLIMB.search(sf.text_mask) and _ANCHOR.search(sf.text_mask):
        stmt = anchored_climb(sf.text_mask)
        if stmt:
            e.root, e.why_root = True, f"climbs from the package directory: `{stmt}`"
    if _GIT_SPAWN.search(sf.text_nc):
        e.git = True
    # Every path-like literal may be relative to a directory a climbing
    # literal reached (`lean_dir().join("Inst.lean")`); in a file that reaches
    # the root, to the root or any ancestor of the package
    # (`manifest.join("..").join("x/src")`), and a bare top-level name
    # (`root.join("lean")`) is a path too. These resolutions are what a
    # declaration must cover; derived reads already hold the directories.
    bases: List[str] = list(dict.fromkeys(anchor_dirs))
    tops: Set[str] = set()
    if e.root:
        tops = tree.top_level()
        bases.append("")
        a = crate_dir
        while "/" in a:
            a = posixpath.dirname(a)
            bases.append(a)
    if bases:
        bases += [crate_dir, fdir]
        for lit in sf.literals:
            s = lit.strip("/")
            if not s or "\n" in s or len(s) > 200:
                continue
            if not ("/" in s or _EXT.search(s) or s in tops):
                continue
            if ".." in s.split("/"):
                continue  # a climbing literal: resolved above
            for base in bases:
                r = norm(posixpath.join(base, s))
                if not r or r.startswith(".."):
                    continue
                if (r in tree.files or tree.is_dir(r)) and not (r == crate_dir or r.startswith(crate_prefix)):
                    e.literals.append((lit, r))
    return e


# --------------------------------------------------------------------------
# Declared reads (scripts/gates/test-reads.tsv)
# --------------------------------------------------------------------------


@dataclass
class Declaration:
    file: str
    patterns: List[str]
    why: str
    line: int


def load_declarations(tree: Tree) -> Tuple[Dict[str, Declaration], List[str]]:
    text = tree.read_text(READS_FILE)
    if text is None:
        return {}, [f"{READS_FILE} is missing"]
    out: Dict[str, Declaration] = {}
    errors: List[str] = []
    for n, raw in enumerate(text.splitlines(), 1):
        line = raw.split("#", 1)[0].rstrip() if not raw.lstrip().startswith("#") else ""
        if not line.strip():
            continue
        parts = line.split("\t")
        if len(parts) != 3 or not parts[1].strip():
            errors.append(f"{READS_FILE}:{n}: expected `file<TAB>patterns<TAB>why`")
            continue
        f, pats, why = parts[0].strip(), parts[1].split(), parts[2].strip()
        if f in out:
            errors.append(f"{READS_FILE}:{n}: {f} declared twice")
        if f not in tree.files:
            errors.append(f"{READS_FILE}:{n}: {f} does not exist")
        out[f] = Declaration(f, pats, why, n)
    return out, errors


def literal_covered(tree: Tree, resolved: str, patterns: Iterable[str], exists_only: Iterable[str] = ()) -> bool:
    """Whether a declaration's expanded patterns account for a path literal:
    the path is matched, or (a walked directory) something declared lies
    under it, or it is declared as read for its existence only."""
    if resolved == ".":
        return True  # the root itself: what is read under it is what the literals name
    if resolved in set(exists_only):
        return True
    for p in patterns:
        if pattern_matches(p, resolved) or pattern_matches(p, resolved + "/"):
            return True
        if tree.is_dir(resolved):
            under = resolved.rstrip("/") + "/"
            if p.startswith(under) or (any(c in p for c in "*?[") and fnmatch.fnmatchcase(under + "x", p)):
                return True
    return False


_PATHISH = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_./-]*")


# --------------------------------------------------------------------------
# Lean graph
# --------------------------------------------------------------------------

LEAN_CORE = ("Init", "Lean", "Std", "Lake")


def lean_imports(text: str) -> List[str]:
    """Every module an `import` line of a Lean file names, with comments
    (`--` lines, nested `/- -/` blocks) removed first. The reading is gate
    14's own (`lean_proofs.strip_lean_comments`, `IMPORT_LINE`), and like it
    every line is read, not only the header: a comment above the imports, or
    a stray `import` further down, never hides one."""
    sys.path.insert(0, os.fspath(SCRIPT_DIR))
    try:
        import lean_proofs  # noqa: E402
    finally:
        sys.path.pop(0)
    names: List[str] = []
    for line in lean_proofs.strip_lean_comments(text).split("\n"):
        m = lean_proofs.IMPORT_LINE.match(line)
        if m:
            names.extend(n for n in m.group(1).split() if n != "runtime")
    return names


def lean_closure(tree: Tree, pkg: str, module: str) -> Optional[Set[str]]:
    """Files of the import closure of `module` inside the Lean package `pkg`
    (srcDir "."), or None when an import cannot be resolved."""
    out: Set[str] = set()
    stack = [module]
    while stack:
        m = stack.pop()
        f = f"{pkg}/{m.replace('.', '/')}.lean"
        if f in out:
            continue
        text = tree.read_text(f) if f in tree.files else None
        if text is None:
            return None
        out.add(f)
        stack.extend(name for name in lean_imports(text) if name.split(".")[0] not in LEAN_CORE)
    return out


# --------------------------------------------------------------------------
# Units: one per `gate <name>` in ci_gates.sh
# --------------------------------------------------------------------------


@dataclass
class Unit:
    name: str
    patterns: Set[str] = field(default_factory=set)
    volatile: Optional[str] = None  # an input outside the tree no key names: never cached
    history: bool = False  # reads git history: HEAD and merge-base join the key
    spec: str = ""
    targets: Dict[str, Set[str]] = field(default_factory=dict)  # test target -> its patterns
    target_history: Set[str] = field(default_factory=set)
    compiles: bool = False
    after: Tuple[str, ...] = ()  # units that must run first when this one runs
    whole_tree: bool = False
    always: bool = False  # its verdict follows an input outside the tree: runs on every plan


class Graph:
    """Everything the selector reads from the tree, computed once."""

    def __init__(self, root: Path, tree: Tree, packages: Dict[str, Package]):
        self.root = root
        self.tree = tree
        self.packages = packages
        self.sources = Sources(tree)
        self.decls, self.decl_errors = load_declarations(tree)
        self.notes: List[str] = []
        self._file_reads: Dict[str, Tuple[Set[str], bool]] = {}
        self._lib_reads: Dict[str, Tuple[Set[str], bool]] = {}

    # -- reads of one file (escapes, declared or derived) ---------------------
    def file_reads(self, f: str, crate_dir: str) -> Tuple[Set[str], bool]:
        key = f + "\0" + crate_dir
        if key in self._file_reads:
            return self._file_reads[key]
        sf = self.sources.get(f)
        reads: Set[str] = set()
        hist = False
        if sf is not None:
            dirs = {crate_dir}
            owner = self.owner_package(f)
            if owner:
                dirs.add(owner)
            for d in sorted(dirs):
                e = file_escape(self.tree, sf, d)
                hist = hist or e.git
                decl = self.decls.get(f)
                if decl is not None:
                    pats, exists_only = self.expand(decl.patterns)
                    uncovered = [r for _, r in e.literals if not literal_covered(self.tree, r, pats, exists_only)]
                    if uncovered:
                        self.notes.append(
                            f"{f}: declared reads do not cover {sorted(set(uncovered))[:4]}: reads EVERYTHING")
                        reads.add(EVERYTHING)
                    else:
                        # an existence-only read is an input too: its key
                        # carries the bit, and a change that flips it selects
                        reads |= pats | {EXISTS + p for p in exists_only}
                elif e.root:
                    self.notes.append(f"{f}: undeclared ({e.why_root}): reads EVERYTHING; declare it in {READS_FILE}")
                    reads.add(EVERYTHING)
                else:
                    reads |= e.reads
        self._file_reads[key] = (reads, hist)
        return reads, hist

    def doc_reads(self, f: str, crate_dir: str) -> Tuple[Set[str], bool]:
        """What the doc comments of `f` (or a document it includes) can read
        when rustdoc runs them as doctests. The lexer drops comments, so this
        reads the doc text on its own, coarsely: every path token in it that
        climbs out of the package (`../x`) is a read; a quoted bare `..` in a
        path context (as in code: an argument of a join, read, ...), or a
        climb (`.parent()` / `.ancestors()`) beside a package anchor anywhere
        in the text, reads EVERYTHING (doctests have no
        declarations); a `git` spawn reads history."""
        text = self.tree.read_text(f) if f in self.tree.files else None
        if not text:
            return set(), False
        doc = doc_text(f, text)
        if not doc:
            return set(), False
        hist = bool(_GIT_SPAWN.search(doc))
        bare_climb = any(_PATH_CTX.search(doc[max(0, m.start() - 48):m.start()])
                         for m in re.finditer(r'"\.\./?"', doc))
        if bare_climb or (_CLIMB.search(doc) and _ANCHOR.search(doc)):
            self.notes.append(f"{f}: its doc comments climb from the package: the doctests read EVERYTHING")
            return {EVERYTHING}, hist
        lits = [t for t in _DOC_PATH_TOKEN.findall(doc) if "../" in t or "/.." in t]
        if not lits:
            return set(), hist
        sf = SourceFile(f, lits, "", [], [], doc, [","] * len(lits), doc)
        e = file_escape(self.tree, sf, crate_dir)
        if e.root:
            self.notes.append(f"{f}: its doc comments climb to the repository root: the doctests read EVERYTHING")
            return {EVERYTHING}, hist
        return set(e.reads), hist

    def expand(self, patterns: Sequence[str]) -> Tuple[Set[str], Set[str]]:
        """(read patterns, existence-only paths) of a declaration.
        `lean:<Module>@<pkg>`: the Lean import closure; `paths-in:<file>`: the
        file and every existing repository path it names (data-driven reads);
        `exists:<path>`: read for its existence only."""
        out: Set[str] = set()
        exists: Set[str] = set()
        for p in patterns:
            if p.startswith("lean:"):
                body = p[len("lean:"):]
                module, _, pkg = body.partition("@")
                files = lean_closure(self.tree, pkg, module) if pkg else None
                if files is None:
                    self.notes.append(f"{p}: the Lean import closure could not be read: the whole package")
                    out.add((pkg or "lean") + "/")
                else:
                    out |= files
            elif p.startswith("paths-in:"):
                f = p[len("paths-in:"):]
                out.add(f)
                text = self.tree.read_text(f) if f in self.tree.files else None
                if text is None:
                    self.notes.append(f"{p}: {f} is missing: EVERYTHING")
                    out.add(EVERYTHING)
                    continue
                for tok in _PATHISH.findall(text):
                    t = tok.rstrip("./")
                    if t in self.tree.files:
                        out.add(t)
                    elif "/" in t and self.tree.is_dir(t):
                        out.add(t + "/")
            elif p.startswith("exists:"):
                exists.add(p[len("exists:"):].rstrip("/"))
            else:
                out.add(p)
        return out, exists

    def owner_package(self, f: str) -> Optional[str]:
        best = None
        for d in self.packages:
            if f.startswith(d + "/") and (best is None or len(d) > len(best)):
                best = d
        return best

    # -- inputs of one crate root (lib/bin/test target) -----------------------
    def crate_inputs(
        self, pdir: str, src_file: str, run: bool, cfg_test: bool, docs: bool = False
    ) -> Tuple[Set[str], bool]:
        """Files OUTSIDE `pdir` that compiling the crate rooted at `src_file`
        reads (its module closure across crate boundaries, include*! targets)
        and, when the crate RUNS (`run`), what its sources read at run time.
        With `docs` (a doctest run), the doc comments of those files, and
        any document they include, are read as code too: a doctest runs them.
        Returns (patterns, reads git history)."""
        files, unresolved = module_closure(self.sources, src_file, cfg_test)
        if unresolved:
            # a module we could not place: every .rs file of the package may be in it
            files = files + [p for p in self.tree.files if p.startswith(pdir + "/") and p.endswith(".rs")]
        pats = {f for f in files if not f.startswith(pdir + "/")}
        hist = False
        if run:
            for f in files:
                if f.endswith(".rs"):
                    r, h = self.file_reads(f, pdir)
                    pats |= r
                    hist = hist or h
                if docs:
                    r, h = self.doc_reads(f, pdir)
                    pats |= r
                    hist = hist or h
        return pats, hist

    def lib_inputs(self, pdir: str, run: bool) -> Tuple[Set[str], bool]:
        """The lib of `pdir` as a DEPENDENCY: `#[cfg(test)]` modules left out."""
        key = f"{pdir}\0{run}"
        if key not in self._lib_reads:
            pkg = self.packages.get(pdir)
            lib = next((t for t in pkg.targets if t.kind in ("lib", "proc-macro")), None) if pkg else None
            self._lib_reads[key] = self.crate_inputs(pdir, lib.src, run, cfg_test=False) if lib else (set(), False)
        return self._lib_reads[key]

    def target_inputs(
        self, pdir: str, target: Target, test_run: bool, run: bool = True,
        cfg_test: Optional[bool] = None, docs: bool = False,
    ) -> Tuple[Set[str], bool]:
        """Every input of building (`run=False`) or running (`run=True`)
        `target`; `test_run` compiles it as a test (dev edges, and cfg(test)
        unless `cfg_test` says otherwise: a doctest links the plain lib);
        `docs` runs its doc comments (a doctest)."""
        reach = closure_dirs(self.packages, pdir, test_run)
        pats = {d + "/" for d in reach}
        own, hist = self.crate_inputs(pdir, target.src, run, cfg_test=test_run if cfg_test is None else cfg_test,
                                      docs=docs)
        pats |= own
        for d in reach:
            if d == pdir and target.kind == "lib":
                continue  # the lib itself is `own`
            r, h = self.lib_inputs(d, run)
            pats |= r
            hist = hist or h
        return pats, hist

    def test_targets_named(self, name: str, workspace: str = "root") -> List[Tuple[str, Target]]:
        return [
            (d, t) for d, p in self.packages.items() if p.workspace == workspace
            for t in p.targets if t.kind == "test" and t.name == name
        ]

    def package_by_name(self, name: str) -> Optional[str]:
        return next((d for d, p in self.packages.items() if p.name == name), None)


def registry_targets(tree: Tree, gate: str) -> Dict[str, List[str]]:
    """{registry file: [targets]} of scripts/gates/<gate>.*.tests."""
    out: Dict[str, List[str]] = {}
    prefix = f"scripts/gates/{gate}."
    for p in tree.paths():
        if p.startswith(prefix) and p.endswith(".tests"):
            names = []
            for line in (tree.read_text(p) or "").splitlines():
                s = re.sub(r"\s+", "", line.split("#", 1)[0])
                if s:
                    names.append(s)
            out[p] = names
    return out


CLI_FIXTURES = (
    "crates/trust-ir-conformance/tests/fixtures/chc_batch.tmbc",
    "crates/trust-ir-conformance/tests/fixtures/proof_annotations.tmbc",
    "crates/trust-ir-conformance/tests/fixtures/proof_diagnostics.tmbc",
)


def build_units(g: Graph, env: Dict[str, str]) -> Dict[str, Unit]:
    """Every leg of ci_gates.sh with its inputs. The names are ci_gates.sh's
    `gate <name>` names (test_gate_select holds the two lists equal)."""
    P = g.packages
    members = [d for d, p in P.items() if p.workspace == "root"]
    units: Dict[str, Unit] = {}

    def add(u: Unit) -> Unit:
        units[u.name] = u
        return u

    def target_unit(name: str, targets: Iterable[Tuple[str, str]], spec: str, after: Tuple[str, ...] = ()) -> Unit:
        """targets: (test target name, workspace)."""
        u = Unit(name, spec=spec, compiles=True, after=after)
        for tname, ws in targets:
            pats: Set[str] = set()
            found = g.test_targets_named(tname, ws)
            if not found:
                g.notes.append(f"{name}: no test target named {tname!r}: runs on every change")
                pats.add(EVERYTHING)
            for d, t in found:
                r, h = g.target_inputs(d, t, test_run=True)
                pats |= r
                if h:
                    u.target_history.add(tname)
            u.targets[tname] = pats
            u.patterns |= pats
        return u

    def lib_test_unit(name: str, pkg_name: str, spec: str) -> Unit:
        d = g.package_by_name(pkg_name)
        u = Unit(name, spec=spec, compiles=True)
        if d is None:
            u.patterns.add(EVERYTHING)
            return u
        lib = next(t for t in P[d].targets if t.kind == "lib")
        r, h = g.target_inputs(d, lib, test_run=True)
        u.patterns |= r
        u.history = h
        return u

    def build_unit(name: str, roots: Iterable[str], kinds: Tuple[str, ...], spec: str) -> Unit:
        u = Unit(name, spec=spec, compiles=True)
        for d in roots:
            for t in P[d].targets:
                if t.kind in kinds:
                    u.patterns |= g.target_inputs(d, t, test_run=False, run=False)[0]
        return u

    # --- gate 0 --------------------------------------------------------------
    add(Unit("zero-ignored-rust", {"*.rs"}, spec="check_no_ignored_rust.py"))
    add(Unit("trust-default-authority", {"rust-toolchain.toml", "rust-toolchain"},
             volatile="the installed toolchain's trees and launchers (ownership, modes, links)",
             spec="check_trust_default_authority.py"))
    add(Unit("dependency-pin-census", {"*.toml", "*.lock", "*.rs"}, spec="pin_rewrite.py census+static-guard"))
    # `check` also holds every pinned owner to a commit in HEAD's history
    add(Unit("wire-allocation-registry", {"wire-allocations.toml", "*.rs", "*.tsv"}, history=True,
             spec="wire_alloc.py check"))
    add(Unit("wire-allocation-owners", {EVERYTHING}, volatile="origin's branch list", spec="wire_alloc.py owners",
             whole_tree=True, always=True))
    add(Unit("enforcement-links", {EVERYTHING}, history=True, spec="check_enforcement_links.py check",
             whole_tree=True))
    add(Unit("internal-gate-tests", {EVERYTHING}, spec="run_script_tests.sh", whole_tree=True))
    add(Unit("workspace-format", {f"{d}/*.rs" for d in members}, spec="targo fmt --check --all"))
    lint = add(Unit("workspace-clippy", {d + "/" for d in members},
                    spec="targo tippy --locked --workspace --all-targets --all-features -- -D warnings",
                    compiles=True))
    for d in members:
        for t in P[d].targets:
            # --all-targets compiles every target, tests as tests; nothing runs
            lint.patterns |= g.target_inputs(d, t, test_run=t.kind != "custom-build", run=False)[0]
    # --- gate 1 --------------------------------------------------------------
    add(target_unit("lean-schema-parity", [("lean_schema_parity", "root")], "--test lean_schema_parity"))
    # --- gate 2 (and the CLI binary legs 4-6 that run what it builds) --------
    defaults = [d for d, p in P.items() if p.workspace == "root" and p.default_member]
    add(build_unit("workspace-build", defaults, ("lib", "bin", "proc-macro", "custom-build"), "targo build --locked"))
    minimal = add(build_unit("minimal-feature-build", ["crates/trust-ir"], ("lib", "custom-build"),
                            "targo check --locked -p trust-ir --lib --no-default-features; repeat with binary,fmt; "
                            "targo test --locked -p trust-ir --lib --no-default-features --no-run"))
    for target in P["crates/trust-ir"].targets:
        if target.kind == "lib":
            minimal.patterns |= g.target_inputs("crates/trust-ir", target, test_run=True, run=False)[0]
    cli = g.package_by_name("trust-ir-cli")
    cli_pats: Set[str] = set()
    if cli is not None:
        for t in P[cli].targets:
            if t.kind == "bin":
                cli_pats |= g.target_inputs(cli, t, test_run=False, run=True)[0]
    else:
        cli_pats.add(EVERYTHING)
    # --- gate 3 --------------------------------------------------------------
    u3 = Unit("cli-gate-tests", spec="crate_tests trust-ir-cli trust-ir", compiles=True)
    if cli is not None:
        for t in P[cli].targets:
            if t.kind in ("bin", "test") and t.test:
                key = ("bin:" + t.name) if t.kind == "bin" else t.name
                r, h = g.target_inputs(cli, t, test_run=True)
                u3.targets[key] = r
                u3.patterns |= r
                if h:
                    u3.target_history.add(key)
    else:
        u3.patterns.add(EVERYTHING)
    add(u3)
    for name, fixture in (
        ("zero-trusted-census-green", CLI_FIXTURES[0]),
        ("zero-trusted-census-red", CLI_FIXTURES[1]),
        ("lineage-closure-red", CLI_FIXTURES[0]),
        ("failed-obligation-census-green", CLI_FIXTURES[0]),
        ("failed-obligation-census-red", CLI_FIXTURES[2]),
    ):
        add(Unit(name, set(cli_pats) | {fixture}, spec=f"trust-ir validate ({name})",
                 compiles=True, after=("workspace-build",)))
    # --- gate 7 --------------------------------------------------------------
    add(target_unit("dependency-pin-coherence", [("dependency_pin_coherence", "root")],
                    "--test dependency_pin_coherence"))
    add(target_unit("import-verification", [("verify_import", "root")], "--test verify_import"))

    # --- registry gates --------------------------------------------------------
    def registry_unit(name: str, extra: str = "") -> Unit:
        regs = registry_targets(g.tree, name)
        targets = sorted({t for names in regs.values() for t in names})
        u = target_unit(name, [(t, "root") for t in targets], f"registry {name} {extra}".strip())
        if not regs:
            u.patterns.add(EVERYTHING)
        return u

    add(registry_unit("wire-format-goldens", "--skip native_request_bundle"))
    add(lib_test_unit("wire-version-ledger", "trust-ir",
                      "-p trust-ir --features binary --lib binary::wire_version_ledger::"))
    add(registry_unit("validator-fail-closed"))
    docs = add(Unit("trust-ir-doctests", spec="--workspace --doc", compiles=True))
    for d in members:
        for t in P[d].targets:
            if t.kind == "lib":
                # doctests link the plain lib (no cfg(test)) and may use dev-deps
                r, h = g.target_inputs(d, t, test_run=True, cfg_test=False, docs=True)
                docs.patterns |= r
                docs.history = docs.history or h
    add(lib_test_unit("allocation-bounds", "trust-ir", "-p trust-ir --features binary --lib alloc_bound::"))
    fd = registry_unit("formula-dag")
    contract = lib_test_unit("formula-dag-lib", "trust-ir-contract", "-p trust-ir-contract --lib formula_dag::")
    fd.patterns |= contract.patterns
    fd.history = fd.history or contract.history
    fd.targets = {}  # the leg runs as a whole (registry + lib filter)
    fd.spec += " + " + contract.spec
    add(fd)
    add(lib_test_unit("wire-allocation-census", "trust-ir",
                      "-p trust-ir --features binary --lib binary::wire_census"))
    add(registry_unit("two-language-ratchets"))
    lean = registry_unit("lean-exec-differential")
    add(lean)
    # --- gate 13 -------------------------------------------------------------
    laws = g.package_by_name("trust-ir-laws")
    u13 = add(Unit("verified-contracts", spec="verified_contracts.py", compiles=True))
    if laws is None:
        u13.patterns.add(EVERYTHING)
    else:
        lib = next(t for t in P[laws].targets if t.kind == "lib")
        u13.patterns |= g.target_inputs(laws, lib, test_run=False, run=False)[0]
    # --- gate 14 -------------------------------------------------------------
    add(Unit("lean-proofs", {"lean/trust_ir-semantics/"}, spec="lean_proofs.py"))
    # --- gate 15 -------------------------------------------------------------
    survey = env.get("TRUST_IR_VERIFIED_SURVEY") == "1"
    # the ledger check reads every member and every file a ledger row names
    # (a row's site may lie outside crates/); the survey compiles the members
    ledger, _ = g.expand(["paths-in:scripts/gates/verified-survey-refutations.tsv"])
    add(Unit("verified-survey", {d + "/" for d in members} | {"crates/"} | ledger,
             spec=f"verified_survey.py {'survey' if survey else '--check-ledger'}", compiles=survey))
    # --- gate 16: one target per row (crate.lib / crate.bins) ----------------
    u16 = add(Unit("verified-ready", spec="verified_ready.py", compiles=True))
    rows_text = g.tree.read_text("scripts/gates/verified-ready.tsv") or ""
    for line in rows_text.splitlines():
        if not line.strip() or line.startswith("#") or line.startswith("crate\t"):
            continue
        cols = line.split("\t")
        if len(cols) < 2:
            continue
        crate, kind = cols[0], cols[1]
        d = g.package_by_name(crate)
        pats: Set[str] = set()
        if d is None:
            pats.add(EVERYTHING)
        else:
            for t in P[d].targets:
                if (kind == "lib" and t.kind == "lib") or (kind == "bins" and t.kind == "bin"):
                    pats |= g.target_inputs(d, t, test_run=False, run=False)[0]
        u16.targets[f"{crate}.{kind}"] = pats
        u16.patterns |= pats
    if not u16.targets:
        u16.patterns.add(EVERYTHING)
    # --- gate 17 -------------------------------------------------------------
    regs = registry_targets(g.tree, "frontend-lowering")
    names = sorted({t for v in regs.values() for t in v})
    add(target_unit("frontend-lowering", [(t, "frontend") for t in names], "frontend-lowering registry"))
    return units


def unit_after_closure(units: Dict[str, Unit]) -> None:
    for u in units.values():
        if u.history or u.target_history:
            u.history = True


# --------------------------------------------------------------------------
# Toolchain identity, environment, keys
# --------------------------------------------------------------------------

ENV_PREFIXES = ("CARGO", "RUST", "TARGO", "TRUST", "LEAN", "LAKE", "ELAN", "PYTHON")
# PATH is not here: what it resolves to is (targo, trustc, lake, python3).
ENV_EXACT = ("SDKROOT", "MACOSX_DEPLOYMENT_TARGET", "CC", "CXX", "AR", "LD",
             "TMPDIR", "TEMP", "TMP", "HOME", "PATH")
ENV_IGNORED = ("TRUST_IR_GATE_CACHE", "TRUST_IR_GATES_BASE", "TRUST_IR_TARGO_JOBS", "CARGO_TARGET_DIR",
               "CARGO_BUILD_JOBS", "TRUST_IR_GATES", "TRUST_IR_ADMISSION_WAIT_S")

# Reviewed execution contracts of ci_gates.sh, not guesses from a file suffix.
# All units execute the Python gate/host wrapper and may run git. Rust units
# additionally use run-targo.sh and its compiler/linker; Lean units use lake.
# The internal script tests run real targo metadata but mock their Lean runners.
# A new/unknown unit retains the complete identity and environment until its
# execution contract is reviewed here. Changes to this table are gate inputs.
EXECUTION_SCHEMA = "trust-ir-unit-execution-v1"
EXECUTION_PROFILES = {
    **dict.fromkeys(("zero-ignored-rust", "dependency-pin-census", "wire-allocation-registry",
                     "wire-allocation-owners", "enforcement-links"), "python"),
    **dict.fromkeys(("internal-gate-tests", "workspace-format", "workspace-clippy", "lean-schema-parity",
                     "workspace-build", "minimal-feature-build", "cli-gate-tests", "zero-trusted-census-green",
                     "zero-trusted-census-red", "lineage-closure-red", "failed-obligation-census-green",
                     "failed-obligation-census-red", "dependency-pin-coherence", "import-verification",
                     "wire-format-goldens", "wire-version-ledger", "validator-fail-closed", "trust-ir-doctests",
                     "allocation-bounds", "formula-dag", "wire-allocation-census", "two-language-ratchets",
                     "verified-contracts", "verified-survey", "verified-ready", "frontend-lowering"), "rust"),
    "lean-exec-differential": "rust-lean",
    "lean-proofs": "lean",
    "trust-default-authority": "all",  # volatile, independently audits the installation
}
RUST_TOOL_KEYS = frozenset(("targo", "targo-version", "targo-file", "trustc", "trustc-vV", "trustc-file"))
LEAN_TOOL_KEYS = frozenset(("lake", "lake-file", "lean", "lean-file"))
COMMON_TOOL_KEYS = frozenset(("host", "python3", "python3-file", "git", "git-file"))
COMPILER_TOOL_KEYS = frozenset(("cc", "cc-file"))
AGGREGATE_IDENTITY_KEYS = frozenset(("env", "outside-config", "execution-schema"))
# Only these exact launcher selectors have been shown irrelevant to the
# corresponding runner contracts. Do not drop a namespace: a Rust validator
# consumes LEAN_LIB_DIR without executing lake, and a future variable may be
# read by any unit. All other selected environment values remain bound.
PROFILE_ENV_OMISSIONS = {
    "python": frozenset(("TRUST_IR_LAKE", "TRUST_TARGO_BIN")),
    "rust": frozenset(("TRUST_IR_LAKE",)),
    "lean": frozenset(("TRUST_TARGO_BIN",)),
    "rust-lean": frozenset(),
    "all": frozenset(),
}


def execution_profile(name: str) -> str:
    return EXECUTION_PROFILES.get(name, "all")


def execution_binding(name: str, ctx: "KeyContext") -> dict:
    """Complete execution inputs of the reviewed unit, with no credential values.

    Unknown identity fields and unclassified environment variables remain
    bound. Only positively classified tool families are omitted from units
    whose maintained runner does not use them. Temporary-root and Python
    startup inputs are bound for every profile, including pure script tests.
    """
    profile = execution_profile(name)
    rust = profile in ("rust", "rust-lean", "all")
    lean = profile in ("lean", "rust-lean", "all")
    known = RUST_TOOL_KEYS | LEAN_TOOL_KEYS | COMMON_TOOL_KEYS | COMPILER_TOOL_KEYS | AGGREGATE_IDENTITY_KEYS
    keep = COMMON_TOOL_KEYS | (RUST_TOOL_KEYS if rust else set()) | (LEAN_TOOL_KEYS if lean else set())
    if rust or lean:
        keep |= COMPILER_TOOL_KEYS
    identity = {k: v for k, v in ctx.ident.items() if k in keep or k not in known}
    unavailable = sorted({f"missing:{k}" for k in keep if k not in identity}
                         | {k for k, v in identity.items()
                            if isinstance(v, str) and (v.startswith("unavailable:") or v == "not found")})
    environment = {}
    for k, v in ctx.env.items():
        if k not in PROFILE_ENV_OMISSIONS[profile]:
            environment[k] = v
    digest = lambda value: hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()
    return {"schema": EXECUTION_SCHEMA, "profile": profile, "tools": identity,
            "cacheable": not unavailable, "unavailable": unavailable,
            "environment": digest(environment), "outside-config": digest(ctx.outside if rust else {})}


def env_fingerprint(env: Dict[str, str]) -> Dict[str, str]:
    """Environment that reaches a build or a test. Job counts and target
    directories are excluded: they change scheduling, not verdicts."""
    out = {}
    for k, v in env.items():
        if k in ENV_IGNORED:
            continue
        if k.startswith(ENV_PREFIXES) or k in ENV_EXACT:
            out[k] = v
    return out


def outside_config_files(root: Path, env: Dict[str, str]) -> Dict[str, str]:
    """Cargo configuration files Cargo reads that the tree hash cannot see:
    every `.cargo/config(.toml)` in an ancestor of the root (and inside the
    root, ignored ones included) and in CARGO_HOME."""
    out: Dict[str, str] = {}
    dirs = [root] + list(root.parents)
    home = Path(env.get("CARGO_HOME") or (Path(env.get("HOME", "~")).expanduser() / ".cargo"))
    for d in dirs:
        for name in ("config.toml", "config"):
            p = d / ".cargo" / name
            if p.is_file():
                out[os.fspath(p)] = hashlib.sha256(p.read_bytes()).hexdigest()
    for name in ("config.toml", "config"):
        p = home / name
        if p.is_file():
            out[os.fspath(p)] = hashlib.sha256(p.read_bytes()).hexdigest()
    return out


def _run_quiet(cmd: Sequence[str], cwd: Optional[Path] = None, env: Optional[Dict[str, str]] = None) -> str:
    try:
        proc = subprocess.run(list(cmd), cwd=os.fspath(cwd) if cwd else None, env=env,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
        return f"exit {proc.returncode}: " + proc.stdout.decode(errors="replace").strip()
    except (OSError, subprocess.TimeoutExpired) as e:
        return f"unavailable: {e}"


def executable_identity(path: str) -> str:
    """Bind wrapper bytes as well as their reported version and resolved path."""
    try:
        real = Path(path).resolve(strict=True)
        before = real.stat()
        h = hashlib.sha256()
        with real.open("rb") as stream:
            for block in iter(lambda: stream.read(1024 * 1024), b""):
                h.update(block)
        after = real.stat()
        if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns) != (
                after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns):
            return "unavailable: executable changed while hashing"
        return json.dumps({"sha256": h.hexdigest(), "mode": before.st_mode,
                           "uid": before.st_uid, "gid": before.st_gid}, sort_keys=True)
    except OSError as error:
        return f"unavailable: {error}"


def toolchain_identity(root: Path, env: Dict[str, str]) -> Dict[str, str]:
    """What compiles and checks: Trust's targo/trustc (resolved the way
    run-targo.sh resolves them), the elan-pinned Lean, and the programs the
    legs run from PATH (python3, cc, git)."""
    ident: Dict[str, str] = {}
    targo = env.get("TRUST_TARGO_BIN") or _which("targo", env)
    if targo:
        real = os.path.realpath(targo)
        ident["targo"] = real
        ident["targo-file"] = executable_identity(targo)
        ident["targo-version"] = _run_quiet([targo, "--unverified", "--version"], root, env)
        trustc = Path(real).with_name("trustc")
        cand = os.fspath(trustc) if trustc.exists() else _which("trustc", env)
        if cand:
            ident["trustc"] = os.path.realpath(cand)
            ident["trustc-file"] = executable_identity(cand)
            ident["trustc-vV"] = _run_quiet([cand, "-vV"], root, env)
        else:
            ident.update({"trustc": "not found", "trustc-file": "not found", "trustc-vV": "not found"})
    else:
        ident["targo"] = "not found"
    lake = env.get("TRUST_IR_LAKE") or os.path.join(env.get("HOME", ""), ".elan", "bin", "lake")
    if os.path.exists(lake):
        pkg = root / "lean" / "trust_ir-semantics"
        ident["lake"] = os.path.realpath(lake)
        ident["lake-file"] = executable_identity(lake)
        lean = os.path.join(os.path.dirname(lake), "lean")
        ident["lean"] = _run_quiet([lean, "--version"], pkg, env)
        ident["lean-file"] = executable_identity(lean)
    else:
        ident["lake"] = "not found"
    ident["host"] = f"{platform.system()} {platform.machine()}"
    # The other programs a leg runs from PATH: the gate scripts' interpreter,
    # the C driver rustc links test binaries with, and git (history readers).
    for name, version in (("python3", "--version"), ("cc", "--version"), ("git", "--version")):
        exe = _which(name, env)
        ident[name] = (os.path.realpath(exe) + " " + _run_quiet([exe, version], root, env)) if exe else "not found"
        if exe:
            ident[name + "-file"] = executable_identity(exe)
    return ident


def _which(name: str, env: Dict[str, str]) -> Optional[str]:
    for d in env.get("PATH", "").split(os.pathsep):
        p = os.path.join(d, name)
        if os.path.isfile(p) and os.access(p, os.X_OK):
            return p
    return None


def global_patterns(pin_legs: Set[str]) -> List[str]:
    return sorted(GLOBAL_EXACT | pin_legs) + list(GLOBAL_GLOBS)


def unit_key(
    tree: Tree, unit_name: str, spec: str, patterns: Set[str], ctx: "KeyContext", history: bool,
    target: Optional[str] = None,
) -> str:
    """A complete source and reviewed execution-input key for one unit.

    v2 receipts lack these execution preimages and are never translated into
    v3 passes. Their original evidence remains intact under its original key.
    """
    h = hashlib.sha256()
    tree_digest, n = tree.digest(sorted(patterns) + ctx.globals)
    record = {
        "schema": PLAN_SCHEMA,
        "unit": unit_name,
        "target": target,
        "spec": spec,
        "inputs": tree_digest,
        "input-files": n,
        "execution": execution_binding(unit_name, ctx),
        "history": ctx.history if history else None,
        "exists": {p: tree.exists(p[len(EXISTS):]) for p in sorted(patterns) if p.startswith(EXISTS)},
    }
    h.update(json.dumps(record, sort_keys=True).encode())
    return h.hexdigest()


@dataclass
class KeyContext:
    ident: Dict[str, str]
    env: Dict[str, str]
    outside: Dict[str, str]
    globals: List[str]
    history: Dict[str, Optional[str]]


# --------------------------------------------------------------------------
# Cache
# --------------------------------------------------------------------------


def cache_dir(root: Path, env: Dict[str, str]) -> Path:
    if env.get("TRUST_IR_GATE_CACHE"):
        return Path(env["TRUST_IR_GATE_CACHE"])
    common = git_text(root, "rev-parse", "--path-format=absolute", "--git-common-dir")
    if not common:
        return root / "target" / "gate-cache"
    return Path(common) / "trust-ir-gates"


def cache_hit(cdir: Path, key: str) -> Optional[dict]:
    p = cdir / "pass" / key[:2] / f"{key}.json"
    try:
        rec = json.loads(p.read_text())
    except (OSError, ValueError):
        return None
    if not isinstance(rec, dict) or rec.get("key") != key or rec.get("result") != "PASS":
        return None
    execution = rec.get("execution")
    if (rec.get("schema") != PLAN_SCHEMA or not isinstance(execution, dict)
            or execution.get("schema") != EXECUTION_SCHEMA or execution.get("cacheable") is not True):
        return None  # no inferred bridge from receipts without execution preimages
    return rec


def cache_store(cdir: Path, key: str, record: dict) -> None:
    d = cdir / "pass" / key[:2]
    d.mkdir(parents=True, exist_ok=True)
    tmp = d / f".{key}.{os.getpid()}.tmp"
    if record.get("result") not in ("PASS", "FAIL") or record.get("schema") != PLAN_SCHEMA:
        raise ValueError("a cache record requires an explicit current-schema result")
    tmp.write_text(json.dumps(dict(record, key=key), sort_keys=True) + "\n")
    os.replace(tmp, d / f"{key}.json")


def current_identity(root: Path, env: Dict[str, str]) -> dict:
    """The same complete identity at planning and result publication.

    Store environment/configuration digests, not credentials from their values.
    """
    ident = toolchain_identity(root, env)
    ident["env"] = hashlib.sha256(json.dumps(env_fingerprint(env), sort_keys=True).encode()).hexdigest()
    ident["outside-config"] = hashlib.sha256(
        json.dumps(outside_config_files(root, env), sort_keys=True).encode()).hexdigest()
    ident["execution-schema"] = EXECUTION_SCHEMA
    return ident


def input_changes(plan: dict, units: Optional[Sequence[str]] = None) -> Tuple[List[str], List[str], bool]:
    """Separate shared source changes from per-unit execution changes."""
    root = Path(plan["root"])
    moved = []
    if Tree(root).digest([EVERYTHING])[0] != plan.get("tree"):
        moved.append("the tree")
    if git_text(root, "rev-parse", "HEAD") != plan.get("head"):
        moved.append("HEAD")
    if git_text(root, "rev-parse", "--verify", "origin/main^{commit}") != plan.get("origin_main"):
        moved.append("origin/main")
    env = dict(os.environ)
    ctx = KeyContext(current_identity(root, env), env_fingerprint(env), outside_config_files(root, env), [], {})
    execution = []
    for name in units if units is not None else plan["units"]:
        if execution_binding(name, ctx) != plan["units"][name].get("execution"):
            execution.append(name)
    return moved, execution, ctx.ident != plan.get("identity")


def moved_inputs(plan: dict, units: Optional[Sequence[str]] = None) -> List[str]:
    shared, execution, identity_moved = input_changes(plan, units)
    if units is None and identity_moved:
        shared.append("the global execution context")
    return shared + [f"execution inputs for {name}" for name in execution]


# --------------------------------------------------------------------------
# Planning
# --------------------------------------------------------------------------


def pin_leg_paths() -> Set[str]:
    sys.path.insert(0, os.fspath(SCRIPT_DIR))
    try:
        import pin_rewrite  # noqa: E402

        out = {leg.relpath for legs in pin_rewrite.LEGS.values() for leg in legs}
        out.add(pin_rewrite.GUARD_TEST)
        return out
    finally:
        sys.path.pop(0)


@dataclass
class Selection:
    mode: str  # "all" | "selected"
    why: str
    units: Dict[str, dict]
    unmapped: List[str]
    global_hits: List[str]


def mapping_claims(units: Dict[str, Unit]) -> List[str]:
    """The patterns that MAP a path to a leg: names, directories and exact
    files. Extension-wide globs (`*.rs`) and EVERYTHING claim without owning."""
    return sorted({q for u in units.values() for q in u.patterns
                   if q != EVERYTHING and not q.startswith("*") and not q.startswith(EXISTS)})


def select(
    units: Dict[str, Unit], changed: Optional[List[str]], pin_legs: Set[str], why_all: Optional[str] = None,
    flipped: Sequence[str] = (),
) -> Selection:
    """The pure part of planning: which units (and targets) the change
    reaches. No cache, no keys. `flipped` are the `exists:<path>` reads
    whose answer the change flips (a path added or removed)."""
    out: Dict[str, dict] = {}
    if changed is None or why_all is not None:
        why = why_all or "no diff"
        for u in units.values():
            out[u.name] = {"run": True, "reason": f"everything runs: {why}", "targets": sorted(u.targets)}
        return Selection("all", why, out, [], [])
    global_hits = [p for p in changed if is_global(p, pin_legs)]
    # A path is MAPPED when a leg claims it by name, directory or exact file.
    # The extension-wide globs of the source scanners (`*.rs`, `*.toml`, ...)
    # and EVERYTHING do not map a path: a file only they claim is one no
    # compiled leg was shown to own.
    claims = mapping_claims(units)
    unmapped = [p for p in changed if p not in global_hits and not is_doc(p) and not any_match(claims, p)]
    if global_hits or unmapped:
        why = (
            f"build or gate input changed: {', '.join(global_hits[:5])}" if global_hits
            else f"unmapped path(s): {', '.join(unmapped[:5])}"
        )
        sel = select(units, None, pin_legs, why)
        return Selection("all", why, sel.units, unmapped, global_hits)
    reached = list(changed) + [EXISTS + p for p in flipped]
    for u in units.values():
        if u.targets:
            hit = sorted(t for t, pats in u.targets.items() if any(any_match(pats, p) for p in reached))
            run = bool(hit)
            reason = (f"inputs changed ({len(hit)} of {len(u.targets)} targets)" if run
                      else "inputs unchanged since the base")
            out[u.name] = {"run": run, "reason": reason, "targets": hit}
        else:
            touched = [p for p in reached if any_match(u.patterns, p)]
            run = bool(touched) or u.always
            reason = (f"inputs changed: {', '.join(touched[:3])}{' ...' if len(touched) > 3 else ''}" if touched
                      else f"its verdict follows {u.volatile}: runs on every plan" if u.always
                      else "inputs unchanged since the base")
            out[u.name] = {"run": run, "reason": reason, "targets": []}
    # dependencies: what a unit needs run first, and the compile preflight
    for u in units.values():
        if out[u.name]["run"]:
            for dep in u.after:
                if not out[dep]["run"]:
                    out[dep] = {"run": True, "reason": f"needed by {u.name}", "targets": out[dep]["targets"]}
    if any(out[u.name]["run"] for u in units.values() if u.compiles) and "trust-default-authority" in out:
        if not out["trust-default-authority"]["run"]:
            out["trust-default-authority"] = {
                "run": True, "reason": "a selected leg compiles: the toolchain preflight runs", "targets": []}
    return Selection("selected", "the change's reverse-dependency closure", out, [], [])


def make_plan(root: Path, base_arg: Optional[str], run_all: bool, env: Dict[str, str]) -> dict:
    t0 = time.monotonic()
    tree = Tree(root)
    pin_legs = pin_leg_paths()
    why_all: Optional[str] = None
    if run_all:
        why_all = "--all"
    base, how = resolve_base(root, base_arg)
    changed: Optional[List[str]] = None
    if base is None and why_all is None:
        why_all = f"no base ({how})"
    elif base is not None:
        try:
            changed = changed_paths(root, base)
        except GitError as e:
            why_all = why_all or f"the diff could not be read ({e})"
    try:
        packages = load_metadata(root)
    except (RuntimeError, ValueError, KeyError, json.JSONDecodeError) as e:
        packages = {}
        why_all = why_all or f"the Rust graph could not be read ({e})"
    g = Graph(root, tree, packages)
    units = build_units(g, env) if packages else {}
    if not units:
        # no graph: every leg of ci_gates.sh runs; the names come from the script
        units = {n: Unit(n, {EVERYTHING}) for n in gate_names(root)}
    unit_after_closure(units)
    cdir = cache_dir(root, env)
    ident = current_identity(root, env)
    flipped: List[str] = []
    if changed is not None and base is not None and why_all is None:
        try:
            flipped = existence_flips(units, lambda p: exists_at(root, base, p), tree.exists)
        except GitError as e:
            why_all = f"the base tree could not be read ({e})"
    sel = select(units, changed, pin_legs, why_all, flipped)
    # Resolve hard fallbacks FIRST. A missing identity must not conceal an
    # unreadable graph/diff or a global/unmapped edit and enable cache reuse.
    recovery = False
    if sel.mode != "all":
        last = _read_json(cdir / "last-toolchain.json")
        identity_reason = None
        if last is None:
            identity_reason = "no green run is recorded on this host (first run, or a new cache)"
        elif last.get("identity") != ident:
            changed_keys = sorted(k for k in set(ident) | set(last.get("identity", {}))
                                  if ident.get(k) != last.get("identity", {}).get(k))
            identity_reason = ("the toolchain identity or environment changed since the last green run "
                               f"({', '.join(changed_keys)})")
        if identity_reason is not None:
            sel = select(units, changed, pin_legs, identity_reason, flipped)
            recovery = True
    cache_policy = "exact" if sel.mode == "selected" or recovery else "none"
    last_failures = _last_run_failures(cdir)
    # A leg that reads history (enforcement-links' ratchet, the must-refuse
    # allowlist's shrink rule, `trust-ir --version`) judges HEAD against the
    # merge-base with origin/main, and the shrink rule also asks origin/main
    # itself: all three join its key.
    history = {
        "HEAD": git_text(root, "rev-parse", "HEAD"),
        "origin-merge-base": git_text(root, "merge-base", "HEAD", "origin/main"),
        "origin/main": git_text(root, "rev-parse", "--verify", "origin/main^{commit}"),
    }
    ctx = KeyContext(ident, env_fingerprint(env), outside_config_files(root, env), global_patterns(pin_legs), history)
    plan_units: Dict[str, dict] = {}
    for name, u in units.items():
        s = sel.units[name]
        entry = {"run": s["run"], "reason": s["reason"], "targets": list(s["targets"]), "volatile": u.volatile,
                 "required": s["run"], "required_targets": list(s["targets"]), "cached_keys": {},
                 "execution": execution_binding(name, ctx),
                 "keys": {}, "key": None}
        if u.volatile is None and entry["execution"]["cacheable"]:
            entry["key"] = unit_key(tree, name, u.spec, u.patterns, ctx, u.history)
            for t, pats in u.targets.items():
                entry["keys"][t] = unit_key(tree, name, u.spec, pats, ctx, u.history or t in u.target_history,
                                            target=t)
        if cache_policy == "exact" and s["run"] and u.volatile is None and entry["execution"]["cacheable"]:
            if u.targets:
                todo = [t for t in s["targets"] if cache_hit(cdir, entry["keys"][t]) is None]
                entry["cached_keys"] = {t: entry["keys"][t] for t in s["targets"] if t not in todo}
                cached = len(s["targets"]) - len(todo)
                if not todo:
                    entry["run"], entry["reason"] = False, f"cached PASS for all {cached} selected targets"
                elif cached:
                    entry["reason"] += f"; {cached} cached PASS"
                entry["targets"] = todo
            elif cache_hit(cdir, entry["key"]) is not None:
                entry["run"], entry["reason"] = False, "cached PASS for this exact input key"
                entry["cached_keys"] = {"": entry["key"]}
        plan_units[name] = entry
    # a unit forced by `after` must still run even when its own key is cached
    for name, u in units.items():
        if plan_units[name]["run"]:
            for dep in u.after:
                if not plan_units[dep]["run"]:
                    plan_units[dep]["run"] = True
                    plan_units[dep]["required"] = True
                    plan_units[dep]["targets"] = sorted(units[dep].targets)
                    plan_units[dep]["required_targets"] = sorted(units[dep].targets)
                    plan_units[dep]["cached_keys"] = {}
                    plan_units[dep]["reason"] = f"needed by {name} (its output is this run's input)"
    return {
        "schema": PLAN_SCHEMA,
        "root": os.fspath(root),
        "mode": sel.mode,
        "cache_policy": cache_policy,
        "recovery": recovery,
        "why": sel.why,
        "base": base,
        "base_how": how,
        "head": history["HEAD"],
        "origin_main": history["origin/main"],
        "changed": changed if changed is not None else None,
        "unmapped": sel.unmapped,
        "global_hits": sel.global_hits,
        "notes": sorted(set(g.notes)) + g.decl_errors + last_failures
        + ([f"existence flipped since the base: {', '.join(flipped)}"] if flipped else []),
        "identity": ident,
        # what every recorded PASS was planned against: `record` refuses to
        # store a PASS once the tree differs from it (edited during the run)
        "tree": tree.digest([EVERYTHING])[0],
        "cache": os.fspath(cdir),
        "units": plan_units,
        "unit_order": list(units),
        "planned_in_s": round(time.monotonic() - t0, 2),
    }


def _last_run_failures(cdir: Path) -> List[str]:
    """What FAILED in the newest run record on this host, so a skipped leg's
    red state stays visible (the cache records PASS only)."""
    runs = sorted((cdir / "runs").glob("*.json")) if (cdir / "runs").is_dir() else []
    if not runs:
        return []
    rec = _read_json(runs[-1]) or {}
    bad = [r["unit"] for r in rec.get("results", []) if r.get("result") == "FAIL"]
    return [f"the last recorded run ({rec.get('head', '?')[:10]}, {rec.get('at', '?')}) FAILED: {', '.join(bad)}"] if bad else []


def gate_names(root: Path) -> List[str]:
    text = (root / "scripts" / "ci_gates.sh").read_text(encoding="utf-8")
    return re.findall(r"(?m)^\s*gate\s+([a-z0-9-]+)\b", text)


def _read_json(p: Path) -> Optional[dict]:
    try:
        value = json.loads(p.read_text())
        return value if isinstance(value, dict) else None
    except (OSError, ValueError):
        return None


def print_plan(plan: dict, out=sys.stdout) -> None:
    w = out.write
    w(f"gate plan: mode {plan['mode']} — {plan['why']}\n")
    w(f"  cache policy: {plan['cache_policy']}"
      + ("; every leg remains required during identity recovery" if plan["recovery"] else "") + "\n")
    w(f"  base {plan['base'] or '-'} ({plan['base_how']}); head {plan['head']}\n")
    ch = plan["changed"]
    if ch is not None:
        w(f"  {len(ch)} changed path(s){': ' + ', '.join(ch[:8]) if ch else ''}{' ...' if len(ch) > 8 else ''}\n")
    for n in plan["notes"]:
        w(f"  note: {n}\n")
    for name in plan["unit_order"]:
        u = plan["units"][name]
        tag = "RUN " if u["run"] else "SKIP"
        tl = f" [{len(u['targets'])} target(s)]" if u["targets"] else ""
        w(f"  {tag} {name}{tl}: {u['reason']}\n")
    w(f"  planned in {plan['planned_in_s']} s; cache {plan['cache']}\n")


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


def cmd_plan(args) -> int:
    root = Path(args.root).resolve()
    env = dict(os.environ)
    base = args.base or env.get("TRUST_IR_GATES_BASE") or None
    run_all = args.all or env.get("TRUST_IR_GATES") == "all"
    plan = make_plan(root, base, run_all, env)
    Path(args.out).write_text(json.dumps(plan, indent=1, sort_keys=True) + "\n")
    # The shell's view: unit TAB run|skip TAB reason TAB targets.
    rows = []
    for name in plan["unit_order"]:
        u = plan["units"][name]
        reason = " ".join(str(u["reason"]).split())
        rows.append(f"{name}\t{'run' if u['run'] else 'skip'}\t{reason}\t{' '.join(u['targets'])}")
    Path(args.out + ".tsv").write_text("\n".join(rows) + "\n")
    print_plan(plan)
    return 0


def cmd_action(args) -> int:
    plan = json.loads(Path(args.plan).read_text())
    u = plan["units"].get(args.unit)
    if u is None:
        # a leg the planner does not know runs (fail closed)
        print(f"run\tnot in the plan: runs\t")
        return 0
    print(f"{'run' if u['run'] else 'skip'}\t{u['reason']}\t{' '.join(u['targets'])}")
    return 0


def store_unit_result(plan: dict, name: str, result: str, targets=None) -> None:
    """FAIL replaces old PASS; a failed target batch invalidates every attempted target."""
    u = plan["units"][name]
    if u.get("volatile"):
        return
    cdir = Path(plan["cache"])
    rec = {"unit": name, "head": plan["head"], "at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
           "root": plan["root"], "result": result, "schema": PLAN_SCHEMA,
           "execution": u.get("execution")}
    ran = targets if targets is not None else u["targets"]
    if u["keys"]:
        for t in ran:
            cache_store(cdir, u["keys"][t], dict(rec, target=t))
        # the unit key covers every target: record it only when all ran
        # A failed subset also invalidates an older whole-unit PASS.
        if result == "FAIL" or set(ran) >= set(u["keys"]):
            cache_store(cdir, u["key"], rec)
    elif u["key"]:
        cache_store(cdir, u["key"], rec)


def cmd_record(args) -> int:
    plan = json.loads(Path(args.plan).read_text())
    if plan.get("schema") != PLAN_SCHEMA:
        print("refusing a result for an unsupported gate plan", file=sys.stderr)
        return 2
    u = plan["units"].get(args.unit)
    if u is None or not u["run"]:
        print(f"refusing an unplanned result for {args.unit}", file=sys.stderr)
        return 2
    if args.targets is not None and (len(set(args.targets)) != len(args.targets)
                                    or not set(args.targets) <= set(u["targets"])):
        print(f"refusing unplanned targets for {args.unit}", file=sys.stderr)
        return 2
    result = args.result
    if result == "PASS":
        if not u.get("execution", {}).get("cacheable"):
            print(f"refusing PASS of {args.unit}: execution identity unavailable", file=sys.stderr)
            return 2
        moved = moved_inputs(plan, [args.unit])
        if moved:
            # A changed-input run must not leave an earlier same-key PASS usable.
            store_unit_result(plan, args.unit, "FAIL", args.targets)
            print(f"refusing PASS of {args.unit}: {' and '.join(moved)} changed since the plan",
                  file=sys.stderr)
            return 2
    store_unit_result(plan, args.unit, result, args.targets)
    return 0


def cmd_finish(args) -> int:
    plan = json.loads(Path(args.plan).read_text())
    if plan.get("schema") != PLAN_SCHEMA:
        print("refusing completion of an unsupported gate plan", file=sys.stderr)
        return 2
    cdir = Path(plan["cache"])
    results = []
    errors = []
    if args.results and Path(args.results).is_file():
        for line in Path(args.results).read_text().splitlines():
            parts = line.split("\t")
            if len(parts) not in (3, 4) or parts[1] not in ("PASS", "FAIL", "SKIP"):
                errors.append("malformed result row")
                continue
            try:
                wall = float(parts[3]) if len(parts) > 3 and parts[3] else None
            except ValueError:
                errors.append(f"malformed timing for {parts[0]}")
                continue
            results.append({"unit": parts[0], "result": parts[1], "detail": parts[2], "wall_s": wall})
    by_name = {}
    for row in results:
        if row["unit"] in by_name:
            errors.append(f"duplicate result for {row['unit']}")
        by_name[row["unit"]] = row
        if row["unit"] not in plan["units"]:
            errors.append(f"unplanned result for {row['unit']}")
    for name, u in plan["units"].items():
        row = by_name.get(name)
        if row is None:
            errors.append(f"missing result for {name}")
            continue
        expected = {t: u["keys"][t] for t in u["required_targets"]} if u["keys"] else {"": u["key"]}
        cached = u["cached_keys"]
        attempted = set(u["targets"]) if u["keys"] else ({""} if u["run"] else set())
        if u["required"]:
            if not u.get("execution", {}).get("cacheable"):
                errors.append(f"execution identity unavailable for {name}")
            if u["keys"] and attempted & set(cached):
                errors.append(f"overlapping cached and attempted targets for {name}")
            if u["volatile"]:
                if not u["run"] or cached:
                    errors.append(f"volatile check {name} was not run")
            elif attempted | set(cached) != set(expected) or any(expected.get(t) != k for t, k in cached.items()):
                errors.append(f"incomplete target coverage for {name}")
            for target, key in cached.items():
                if cache_hit(cdir, key) is None:
                    errors.append(f"cached PASS no longer holds for {name}:{target}")
            if u["run"]:
                if row["result"] not in ("PASS", "FAIL"):
                    errors.append(f"required check {name} did not run")
                elif row["result"] == "FAIL":
                    store_unit_result(plan, name, "FAIL")
            elif row["result"] != "SKIP" or not cached:
                errors.append(f"required check {name} has no checked result")
        elif u["run"] or cached or row["result"] != "SKIP":
            errors.append(f"result disagrees with the selection for {name}")
    shared_moved, execution_moved, identity_moved = input_changes(plan)
    moved = shared_moved + [f"execution inputs for {name}" for name in execution_moved]
    if identity_moved:
        moved.append("the global execution context")
    if moved:
        errors.append(f"{' and '.join(moved)} changed since the plan")
        for name, u in plan["units"].items():
            if u["run"] and (shared_moved or name in execution_moved):
                store_unit_result(plan, name, "FAIL")
    record = {
        "schema": PLAN_SCHEMA, "at": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "root": plan["root"],
        "head": plan["head"], "base": plan["base"], "mode": plan["mode"], "why": plan["why"],
        "changed": plan["changed"], "results": results, "identity": plan["identity"],
        "execution": {name: unit["execution"] for name, unit in plan["units"].items()},
        "cache_policy": plan["cache_policy"], "complete": not errors, "errors": errors,
    }
    (cdir / "runs").mkdir(parents=True, exist_ok=True)
    name = time.strftime("%Y%m%dT%H%M%S") + f"-{os.getpid()}.json"
    (cdir / "runs" / name).write_text(json.dumps(record, indent=1, sort_keys=True) + "\n")
    failed = [r for r in results if r["result"] == "FAIL"]
    # The identity that judged the base: written only by a run with no
    # failure. After a toolchain or environment change, every plan runs
    # everything until one such run is green here; a red full run proves
    # nothing about what an "unchanged" leg would say on the new toolchain.
    if results and not failed and not errors:
        tmp = cdir / f".last-toolchain.{os.getpid()}.tmp"
        tmp.write_text(json.dumps({"identity": plan["identity"], "head": plan["head"], "at": record["at"]}) + "\n")
        os.replace(tmp, cdir / "last-toolchain.json")
    ran = sum(1 for r in results if r["result"] in ("PASS", "FAIL"))
    skipped = sum(1 for r in results if r["result"] == "SKIP")
    print(f"run record: {cdir / 'runs' / name} ({ran} leg(s) ran, {skipped} skipped, {len(failed)} failed)")
    for error in errors:
        print(f"completion refused: {error}", file=sys.stderr)
    return 2 if errors else 0


def replay(root: Path, ref: str, count: int, env: Dict[str, str]) -> dict:
    """The selector over the diffs of the last `count` first-parent commits of
    `ref` (no builds, no cache): each commit against its first parent, with
    the units of the CURRENT tree (the graph moves rarely; said in the doc)."""
    tree = Tree(root)
    packages = load_metadata(root)
    g = Graph(root, tree, packages)
    units = build_units(g, env)
    pin_legs = pin_leg_paths()
    commits = git(root, "rev-list", "--first-parent", f"--max-count={count}", ref).decode().split()
    rows = []
    for c in commits:
        subject = git_text(root, "log", "-1", "--format=%s", c) or ""
        parents = (git_text(root, "rev-list", "--parents", "-n", "1", c) or "").split()[1:]
        if not parents:
            continue
        changed = sorted(set(zsplit(git(root, "diff", "--name-only", "-z", "--no-renames", parents[0], c))))
        flipped = existence_flips(units, lambda p: exists_at(root, parents[0], p), lambda p: exists_at(root, c, p))
        sel = select(units, changed, pin_legs, flipped=flipped)
        ran = [n for n, u in sel.units.items() if u["run"]]
        rows.append({
            "commit": c[:10], "subject": subject[:72], "changed": len(changed), "mode": sel.mode,
            "why": sel.why, "selected": ran,
            "targets": {n: len(u["targets"]) for n, u in sel.units.items() if u["run"] and u["targets"]},
        })
    per_unit = {n: sum(1 for r in rows if n in r["selected"]) for n in units}
    return {"ref": ref, "count": len(rows), "units": list(units), "rows": rows, "per_unit": per_unit,
            "notes": sorted(set(g.notes)) + g.decl_errors}


def cmd_replay(args) -> int:
    root = Path(args.root).resolve()
    data = replay(root, args.ref, args.count, dict(os.environ))
    if args.json:
        Path(args.json).write_text(json.dumps(data, indent=1) + "\n")
    n = data["count"]
    total = len(data["units"])
    legs_before = n * total
    legs_after = sum(len(r["selected"]) for r in data["rows"])
    print(f"replay of {n} first-parent commits of {data['ref']} (legs selected; before = every leg, every commit)")
    for r in data["rows"]:
        print(f"  {r['commit']} {len(r['selected']):2d}/{total} {r['mode']:8s} {r['subject'][:60]}")
    print("\nper leg: commits selecting it (before: all)")
    for name in data["units"]:
        print(f"  {name:34s} {data['per_unit'][name]:3d}/{n}")
    print(f"\nlegs selected: before {legs_before}, after {legs_after} "
          f"({100.0 * legs_after / max(legs_before, 1):.0f}%); "
          f"mode all: {sum(1 for r in data['rows'] if r['mode'] == 'all')}/{n}; "
          f"docs-only-shaped (no compiled leg): "
          f"{sum(1 for r in data['rows'] if not set(r['selected']) - {'enforcement-links', 'internal-gate-tests', 'wire-allocation-owners'})}/{n}")
    for note in data["notes"]:
        print(f"note: {note}")
    return 0


def cmd_audit(args) -> int:
    root = Path(args.root).resolve()
    tree = Tree(root)
    packages = load_metadata(root)
    g = Graph(root, tree, packages)
    build_units(g, dict(os.environ))
    problems = list(g.decl_errors)
    # every declared file must still escape (else the row is stale)
    for f, d in sorted(g.decls.items()):
        sf = g.sources.get(f)
        owner = g.owner_package(f)
        if sf is None or owner is None:
            problems.append(f"{READS_FILE}:{d.line}: {f} is not a Rust file of a package")
            continue
        e = file_escape(tree, sf, owner)
        if not e.root and not e.reads and not e.literals:
            problems.append(f"{READS_FILE}:{d.line}: {f} reads nothing outside its package: drop the row")
    for n in sorted(set(g.notes)):
        print(f"note: {n}")
    for p in problems:
        print(f"problem: {p}")
    print(f"audit: {len(g.decls)} declaration(s), {len(set(g.notes))} note(s), {len(problems)} problem(s)")
    return 1 if problems else 0


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("plan")
    p.add_argument("--root", default=os.fspath(SCRIPT_DIR.parent))
    p.add_argument("--base")
    p.add_argument("--all", action="store_true")
    p.add_argument("--out", required=True)
    p.set_defaults(fn=cmd_plan)
    p = sub.add_parser("action")
    p.add_argument("--plan", required=True)
    p.add_argument("--unit", required=True)
    p.set_defaults(fn=cmd_action)
    p = sub.add_parser("record")
    p.add_argument("--plan", required=True)
    p.add_argument("--unit", required=True)
    p.add_argument("--targets", nargs="*")
    p.add_argument("--result", choices=("PASS", "FAIL"), default="PASS")
    p.set_defaults(fn=cmd_record)
    p = sub.add_parser("finish")
    p.add_argument("--plan", required=True)
    p.add_argument("--results")
    p.set_defaults(fn=cmd_finish)
    p = sub.add_parser("replay")
    p.add_argument("--root", default=os.fspath(SCRIPT_DIR.parent))
    p.add_argument("--ref", default="origin/main")
    p.add_argument("--count", type=int, default=50)
    p.add_argument("--json")
    p.set_defaults(fn=cmd_replay)
    p = sub.add_parser("audit")
    p.add_argument("--root", default=os.fspath(SCRIPT_DIR.parent))
    p.set_defaults(fn=cmd_audit)
    args = ap.parse_args(argv)
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
