#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Refuse a commit range that would put report archives or oversized blobs in Git.

Git keeps every blob any pushed commit reaches, so a check of the tip tree
cannot bound what a push costs: a payload added in one commit and deleted in
the next is absent from HEAD and is still downloaded by every clone. That is
how the 2026-11-07/08 report archives grew this repository to 17.4 GiB
(docs/report-artifact-custody.md). This check reads every commit of the range
instead (reachable from the tip, not from the base) and refuses:

  archive  a path under reports/ whose name ends, in any letter case, in an
           archive suffix (report_artifacts.ARCHIVE_SUFFIXES) and that a
           commit of the range introduces, unless the (path, blob) pair is a
           member of the sealed standing fixture's Git tree
           (report_artifacts.REVIEWED_INLINE_FIXTURE["tree"]; no file of the
           range can widen it);
  size     a blob over 1 MiB that a commit of the range introduces, unless that
           commit discloses it twice: its own scripts/gates/object-budget.tsv
           holds the exact row `path<TAB>blob<TAB>bytes`, and its message
           carries the trailer `Object-Budget: <path>: <reason>`;
  census   at the range's tip, a row that is not exactly the tip's file (path,
           blob, bytes), or a file over 1 MiB without a row, for every path the
           range touches (and every row when the range changes the allowlist);
  pack     new objects that pack to more than 64 MiB.

A commit introduces a (path, blob) pair when its tree has the pair and none of
its parents' trees does (the combined diff of a merge). History before the
range is therefore never judged, and a merge of the base judges only its own
resolution. Binary test fixtures outside reports/ are judged by size alone.

The allowlist is the exact census of the files over the budget and grants
nothing by itself: a replacement under an old row, or a row added beside its
payload, still needs the introducing commit's trailer. A row for a file the
range does not introduce (a census catching up) admits no object, so it needs
no trailer. A refusal prints the row and the trailer that would admit it;
`--update-allowlist` rewrites the rows to the census of the index.

Usage:
  check_object_budget.py --root R --range BASE..TIP                        (gate 0)
  check_object_budget.py --root R --tip SHA [--not REV]... [--advertised FILE]   (pre-push)
  check_object_budget.py --root R --update-allowlist                (before a commit)

--advertised is `git ls-remote` output of the remote the push goes to (`-`:
standard input). Every advertised commit present here is excluded, and nothing
else: a remote-tracking ref records what this clone once saw of some remote,
not what the remote the push goes to holds.

Exit 0: within budget. 1: refused, or the range cannot be judged (a missing
object, a malformed allowlist or advertisement). 3: a base does not resolve,
so there is no range to judge (printed as `OBJECT-BUDGET NOT JUDGED: ...`).
Every other status, Python's 2 for a usage error or a missing script
included, is a failure.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple

sys.path.insert(0, str(Path(__file__).resolve().parent))
from report_artifacts import INLINE_FIXTURE, REVIEWED_INLINE_FIXTURE, _git_environment, is_archive  # noqa: E402

ALLOWLIST = "scripts/gates/object-budget.tsv"
TRAILER = "Object-Budget"
REPORTS = "reports/"
SEALED_FIXTURE_TREE = REVIEWED_INLINE_FIXTURE["tree"]
MAX_BLOB_BYTES = 1 << 20
MAX_PACK_BYTES = 64 << 20
NOT_JUDGED = 3
OID = re.compile(r"[0-9a-f]{40}(?:[0-9a-f]{24})?\Z")
NULL_OID = re.compile(r"0+\Z")
BYTES = re.compile(r"[1-9][0-9]*\Z")
GITLINK = "160000"
FILE_MODES = {"100644", "100755", "120000"}
SHOWN_PER_RULE = 40  # refusals printed per rule; the count names the rest

Row = Tuple[str, int]  # (blob, bytes)


class BudgetError(RuntimeError):
    """The range cannot be judged: refuse."""


class NoBase(BudgetError):
    """A base revision does not resolve: there is no range to judge."""


def _entry_bound(size: int) -> int:
    # A pack entry is a varint header and the zlib stream of the object. Deflate
    # never expands input by more than its stored-block framing (5 bytes per
    # 16 KiB block plus the zlib header and checksum), so this bounds an entry.
    return size + size // 1024 + 64


class Repo:
    def __init__(self, root: Path) -> None:
        self.root = Path(root).resolve(strict=True)
        self.env = _git_environment()

    def command(self, *args: str) -> List[str]:
        return ["git", "--no-replace-objects", "--literal-pathspecs", "-C", str(self.root), *args]

    def run(self, *args: str, data: Optional[bytes] = None) -> bytes:
        done = subprocess.run(self.command(*args), input=data, capture_output=True, env=self.env)
        if done.returncode:
            detail = done.stderr.decode(errors="backslashreplace").strip()[:500]
            raise BudgetError(f"git {args[0]} failed: {detail}")
        return done.stdout

    def commit(self, rev: str) -> Optional[str]:
        done = subprocess.run(self.command("rev-parse", "--verify", "--quiet", "--end-of-options", rev + "^{commit}"),
                              capture_output=True, env=self.env)
        oid = done.stdout.decode().strip()
        return oid if done.returncode == 0 and OID.fullmatch(oid) else None

    def sizes(self, oids: Iterable[str]) -> Dict[str, Tuple[str, int]]:
        """oid -> (type, size); a missing object is absent from the result."""
        oids = sorted(set(oids))
        if not oids:
            return {}
        out = self.run("cat-file", "--batch-check=%(objectname) %(objecttype) %(objectsize)",
                       data=("\n".join(oids) + "\n").encode())
        found: Dict[str, Tuple[str, int]] = {}
        for line in out.decode().splitlines():
            fields = line.split()
            if len(fields) == 3 and fields[1] != "missing":
                found[fields[0]] = (fields[1], int(fields[2]))
        return found

    def blobs(self, oids: Iterable[str]) -> Dict[str, bytes]:
        """oid -> content of each blob; a missing or non-blob object refuses."""
        oids = sorted(set(oids))
        if not oids:
            return {}
        out = self.run("cat-file", "--batch", data=("\n".join(oids) + "\n").encode())
        found: Dict[str, bytes] = {}
        at = 0
        for oid in oids:
            end = out.index(b"\n", at)
            fields = out[at:end].decode(errors="backslashreplace").split()
            at = end + 1
            if len(fields) != 3 or fields[0] != oid or fields[1] != "blob":
                raise BudgetError(f"blob {oid[:12]} is not available here ({' '.join(fields[1:])})")
            size = int(fields[2])
            found[oid] = out[at:at + size]
            at += size + 1
        return found

    def tree(self, rev: str) -> Dict[str, str]:
        """path -> blob of every file (not gitlink) in rev's tree."""
        files: Dict[str, str] = {}
        for entry in self.run("ls-tree", "-r", "-z", rev).split(b"\0"):
            if entry:
                header, name = entry.split(b"\t", 1)
                mode, kind, oid = header.decode().split()
                if kind == "blob":
                    files[os.fsdecode(name)] = oid
        return files

    def allowlist_blob(self, rev: str) -> Optional[str]:
        """The allowlist's blob in rev's tree (None: rev has no allowlist)."""
        entries = [e for e in self.run("ls-tree", "-z", rev, "--", ALLOWLIST).split(b"\0") if e]
        if not entries:
            return None
        mode, kind, oid = entries[0].split(b"\t", 1)[0].decode().split()
        if kind != "blob" or mode not in {"100644", "100755"}:
            raise BudgetError(f"{ALLOWLIST} at {rev[:12]} is not a regular file")
        return oid

    def trailers(self, commits: Iterable[str]) -> Dict[str, List[str]]:
        """commit -> the values of its `Object-Budget:` trailers, as Git parses them."""
        commits = sorted(set(commits))
        if not commits:
            return {}
        out = self.run("log", "--no-walk=unsorted", "--stdin",
                       f"--format=%x01%H%x02%(trailers:key={TRAILER},valueonly,unfold,separator=%x1e)%x03",
                       data=("\n".join(commits) + "\n").encode())
        found = {commit: [] for commit in commits}
        for commit, values in re.findall(r"\x01([0-9a-f]+)\x02(.*?)\x03", out.decode("utf-8", "surrogateescape"), re.S):
            found[commit] = [v.strip() for v in values.split("\x1e") if v.strip()]
        return found


def _canonical(path: str) -> bool:
    return (bool(path) and not path.startswith("/") and "\\" not in path
            and not any(ord(c) < 32 for c in path)
            and all(p not in {"", ".", ".."} for p in path.split("/"))
            and str(PurePosixPath(path)) == path)


def parse_allowlist(text: str) -> Dict[str, Row]:
    """path -> (blob, bytes): one exact row per file over the budget."""
    rows: Dict[str, Row] = {}
    for number, line in enumerate(text.splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("\t")
        where = f"{ALLOWLIST}:{number}"
        if len(fields) != 3 or OID.fullmatch(fields[1]) is None or BYTES.fullmatch(fields[2]) is None:
            raise BudgetError(f"{where}: a row is `path<TAB>blob<TAB>bytes`")
        path, blob, size = fields[0], fields[1], int(fields[2])
        if not _canonical(path):
            raise BudgetError(f"{where}: {path!r} is not a canonical repository path")
        if path in rows:
            raise BudgetError(f"{where}: {path} has a second row")
        if size <= MAX_BLOB_BYTES:
            raise BudgetError(f"{where}: {path} is within the {MAX_BLOB_BYTES}-byte budget; remove the row")
        rows[path] = (blob, size)
    return rows


def format_row(path: str, blob: str, size: int) -> str:
    return f"{path}\t{blob}\t{size}"


def introduced(repo: Repo, commits: Sequence[str]):
    """((path, blob) -> (mode, [commits]) for every pair a commit introduces,
    path -> [commits] for every path a commit changes)."""
    pairs: Dict[Tuple[str, str], Tuple[str, List[str]]] = {}
    touched: Dict[str, List[str]] = {}
    if not commits:
        return pairs, touched
    out = repo.run("diff-tree", "--stdin", "-r", "-c", "--root", "--no-renames", "--raw", "-z",
                   data=("\n".join(commits) + "\n").encode())
    tokens = out.split(b"\0")
    commit = ""
    i = 0
    while i < len(tokens):
        token = tokens[i]
        i += 1
        if not token:
            continue
        if not token.startswith(b":"):
            commit = token.decode("ascii")
            if not OID.fullmatch(commit):
                raise BudgetError(f"unexpected diff-tree header {commit[:80]!r}")
            continue
        parents = len(token) - len(token.lstrip(b":"))
        fields = token[parents:].decode("ascii").split()
        if len(fields) != 2 * parents + 3 or i >= len(tokens):
            raise BudgetError("unexpected diff-tree record")
        mode, blob = fields[parents], fields[2 * parents + 1]
        path = os.fsdecode(tokens[i])
        i += 1
        touched.setdefault(path, []).append(commit)
        if NULL_OID.fullmatch(blob) or mode == GITLINK:
            continue
        pairs.setdefault((path, blob), (mode, []))[1].append(commit)
    return pairs, touched


def sealed_members(repo: Repo, tree: str) -> Set[Tuple[str, str]]:
    """(path, blob) of every member of the sealed fixture tree; none when this
    clone lacks the tree, so nothing under the prefix is exempt."""
    if repo.sizes([tree]).get(tree, ("", 0))[0] != "tree":
        return set()
    members = set()
    for entry in repo.run("ls-tree", "-r", "-z", tree).split(b"\0"):
        if entry:
            header, name = entry.split(b"\t", 1)
            members.add((INLINE_FIXTURE + os.fsdecode(name), header.decode().split()[2]))
    return members


def pack_bytes(repo: Repo, revs: Sequence[str], limit: int) -> int:
    """Bytes of the pack of the range's new objects, stopping once past limit."""
    process = subprocess.Popen(repo.command("pack-objects", "--revs", "--stdout", "-q"), env=repo.env,
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    assert process.stdin is not None and process.stdout is not None
    process.stdin.write(("\n".join(revs) + "\n").encode())
    process.stdin.close()
    total = 0
    stopped = False
    while True:
        data = process.stdout.read(1 << 20)
        if not data:
            break
        total += len(data)
        if total > limit:
            stopped = True
            process.kill()
            break
    process.stdout.close()
    assert process.stderr is not None
    error = process.stderr.read()
    process.stderr.close()
    process.wait()
    if process.returncode and not stopped:
        raise BudgetError("git pack-objects failed: " + error.decode(errors="backslashreplace").strip()[:500])
    return total


def advertised_commits(repo: Repo, text: str) -> List[str]:
    """The commits of a `git ls-remote` listing that this clone has."""
    oids = []
    for number, line in enumerate(text.splitlines(), 1):
        if not line:
            continue
        fields = line.split("\t")
        if len(fields) != 2 or OID.fullmatch(fields[0]) is None or not fields[1]:
            raise BudgetError(f"advertisement line {number} is not `<oid><TAB><ref>` (git ls-remote output)")
        oids.append(fields[0])
    return sorted(oid for oid, (kind, _) in repo.sizes(oids).items() if kind == "commit")


def disclosed(path: str, values: Sequence[str]) -> bool:
    return any(v.startswith(path + ":") and v[len(path) + 1:].strip() for v in values)


def check(root: Path, tip: str, bases: Sequence[str] = (), advertised: Optional[str] = None,
          max_blob: int = MAX_BLOB_BYTES, max_pack: int = MAX_PACK_BYTES, label: str = "",
          fixture_tree: str = SEALED_FIXTURE_TREE) -> Tuple[List[str], str]:
    """(refusals, summary) for the commits reachable from tip and from no base
    and no advertised commit."""
    repo = Repo(root)
    head = repo.commit(tip)
    if head is None:
        raise BudgetError(f"tip {tip!r} is not a commit here")
    excluded = []
    for base in bases:
        oid = repo.commit(base)
        if oid is None:
            raise NoBase(f"base {base!r} does not resolve to a commit here")
        excluded.append(oid)
    if advertised is not None:
        excluded += advertised_commits(repo, advertised)
    revs = [head, "--not", *sorted(set(excluded))]
    commits = repo.run("rev-list", *revs).decode().split()
    if not commits:
        return [], f"object budget: {label or tip}: no new commits"
    pairs, touched = introduced(repo, commits)
    # A partial clone may lack blobs of commits it fetched; every new blob is
    # an introduced one, so a blob left out here is refused as unmeasured.
    new_objects = repo.run("rev-list", "--objects", "--no-object-names", "--missing=allow-promisor",
                           *revs).decode().split()
    known = repo.sizes([*new_objects, *(blob for _, blob in pairs)])
    refusals: List[str] = []

    large: Dict[Tuple[str, str], Tuple[int, List[str]]] = {}
    sealed: Optional[Set[Tuple[str, str]]] = None
    for (path, blob), (_, by) in sorted(pairs.items()):
        at = f"{path} (blob {blob[:12]}, introduced by {by[0][:12]})"
        if blob not in known:
            refusals.append(f"unmeasured: {at}: the blob is not in this clone (a partial clone of commits "
                            "it did not make?), so its size cannot be judged; fetch it or judge the range "
                            "where it is")
            continue
        size = known[blob][1]
        if path.startswith(REPORTS) and is_archive(path):
            if sealed is None and path.startswith(INLINE_FIXTURE):
                sealed = sealed_members(repo, fixture_tree)
            if (path, blob) not in (sealed or set()):
                refusals.append(f"archive: {at}, {size} bytes: generated report archives belong in the "
                                "external evidence store, never in Git history; only the sealed standing "
                                "fixture's own members are exempt (docs/report-artifact-custody.md)")
        if size > max_blob:
            large[(path, blob)] = (size, by)

    # Each commit that introduces a large blob carries its own row and trailer;
    # a commit that edits the allowlist puts its parents' rows under the census.
    editors = touched.get(ALLOWLIST, [])
    parents: List[str] = []
    if editors:
        for line in repo.run("rev-list", "--no-walk=unsorted", "--parents", *editors).decode().splitlines():
            parents += line.split()[1:]
    lists_at = sorted({c for _, by in large.values() for c in by} | {head} | set(parents))
    list_blob = {c: repo.allowlist_blob(c) for c in lists_at}
    texts = repo.blobs(b for b in list_blob.values() if b is not None)
    parsed: Dict[str, Dict[str, Row]] = {}
    for commit, blob in list_blob.items():
        if blob is not None and blob not in parsed:
            try:
                parsed[blob] = parse_allowlist(texts[blob].decode("utf-8"))
            except BudgetError as error:
                raise BudgetError(f"{error} (in {commit[:12]})") from None
    rows_at = {c: parsed[b] if b is not None else {} for c, b in list_blob.items()}
    values_at = repo.trailers(c for _, by in large.values() for c in by)
    refused_large: Set[Tuple[str, str]] = set()
    for (path, blob), (size, by) in sorted(large.items()):
        for commit in by:
            have = rows_at[commit].get(path)
            needs = []
            if have != (blob, size):
                held = f"; it has `{format_row(path, *have)}`" if have is not None else ""
                needs.append(f"the row `{format_row(path, blob, size)}` in that commit's {ALLOWLIST}{held}")
            if not disclosed(path, values_at.get(commit, [])):
                needs.append(f"the trailer `{TRAILER}: {path}: <reason>` in its message")
            if needs:
                refused_large.add((path, blob))
                refusals.append(f"size: {path} (blob {blob[:12]}, introduced by {commit[:12]}) is {size} bytes, "
                                f"over the {max_blob}-byte budget; a reviewed exception needs "
                                + " and ".join(needs))

    # The allowlist at the tip is the exact census of what the range touches.
    allow = rows_at[head]
    watched = set(touched)
    if editors:
        watched |= set(allow).union(*(rows_at[p] for p in parents))
    tip = repo.tree(head)
    tip_sizes = repo.sizes(tip[p] for p in watched if p in tip)
    for path in sorted(watched):
        row, blob = allow.get(path), tip.get(path)
        if (path, blob) in refused_large:
            continue  # its size refusal already names the row it needs
        if blob is not None and blob not in tip_sizes:
            refusals.append(f"unmeasured: {path} at the tip (blob {blob[:12]}) is not available here")
            continue
        size = tip_sizes[blob][1] if blob is not None else 0
        if row is not None and row != (blob, size):
            if blob is None:
                fix = "the tip does not hold it: remove the row"
            elif size <= max_blob:
                fix = f"the tip holds {size} bytes, within the budget: remove the row"
            else:
                fix = f"the tip holds blob {blob[:12]} of {size} bytes: the row is `{format_row(path, blob, size)}`"
            refusals.append(f"census: {ALLOWLIST} has `{format_row(path, *row)}`, but {fix}")
        elif row is None and blob is not None and size > max_blob:
            refusals.append(f"census: {path} is {size} bytes at the tip and has no row in {ALLOWLIST}: "
                            f"add `{format_row(path, blob, size)}`")

    missing = [o for o in new_objects if o not in known]
    raw = sum(known[o][1] for o in new_objects if o in known)
    bound = 32 + sum(_entry_bound(known[o][1]) for o in new_objects if o in known)
    if missing:
        refusals.append(f"unmeasured: {len(missing)} new objects are not available here (first {missing[0]})")
        packed = "not measured (objects missing)"
    elif bound <= max_pack:
        packed = f"at most {bound} bytes (bounded by raw size)"
    elif refusals:
        packed = "not measured (the range is already refused)"
    else:
        size = pack_bytes(repo, revs, max_pack)
        packed = f"{size} bytes" if size <= max_pack else f"over {max_pack} bytes"
        if size > max_pack:
            refusals.append(f"pack: the range's {len(new_objects)} new objects pack to more than the {max_pack}-byte "
                            "budget; split the change or move generated output to the evidence store")
    summary = (f"object budget: {label or tip}: {len(commits)} commits, {len(pairs)} introduced paths, "
               f"{len(large)} over the budget, {len(new_objects)} new objects ({raw} raw bytes), pack {packed}")
    return refusals, summary


def index_census(root: Path, max_blob: int = MAX_BLOB_BYTES) -> Dict[str, Row]:
    """path -> (blob, bytes) of every staged file over the budget."""
    repo = Repo(root)
    staged: Dict[str, str] = {}
    for entry in repo.run("ls-files", "--stage", "-z").split(b"\0"):
        if entry:
            header, name = entry.split(b"\t", 1)
            mode, oid, stage = header.decode().split()
            if stage != "0":
                raise BudgetError("the index has unmerged entries")
            if mode in FILE_MODES:
                staged[os.fsdecode(name)] = oid
    sizes = repo.sizes(staged.values())
    absent = sorted(p for p, oid in staged.items() if oid not in sizes)
    if absent:
        raise BudgetError(f"staged blob of {absent[0]} is not available here")
    return {p: (oid, sizes[oid][1]) for p, oid in staged.items() if sizes[oid][1] > max_blob}


def update_allowlist(root: Path) -> Tuple[List[str], List[str]]:
    """Rewrite the allowlist's rows to the census of the index, keeping its
    leading comment. (rows removed, rows added), as `path<TAB>blob<TAB>bytes`."""
    target = Path(root) / ALLOWLIST
    lines = target.read_text(encoding="utf-8").splitlines() if target.exists() else []
    try:
        old = parse_allowlist("\n".join(lines))
    except BudgetError:
        old = {}  # a conflicted or malformed file: its rows are rewritten whole
    header = []
    for line in lines:
        if line.strip() and not line.startswith("#"):
            break
        header.append(line)
    new = index_census(root)
    target.parent.mkdir(parents=True, exist_ok=True)
    rows = [format_row(p, *new[p]) for p in sorted(new)]
    target.write_text("\n".join(header + rows) + "\n", encoding="utf-8")
    removed = [format_row(p, *old[p]) for p in sorted(old) if new.get(p) != old[p]]
    added = [format_row(p, *new[p]) for p in sorted(new) if old.get(p) != new[p]]
    return removed, added


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--range", help="BASE..TIP: the commits reachable from TIP and not from BASE")
    mode.add_argument("--tip", help="judge the commits reachable from this revision ...")
    mode.add_argument("--update-allowlist", action="store_true",
                      help=f"rewrite the rows of {ALLOWLIST} to the staged files over the budget")
    parser.add_argument("--not", dest="exclude", action="append", default=[], metavar="REV",
                        help="... and from none of these (repeatable; with --tip)")
    parser.add_argument("--advertised", metavar="FILE",
                        help="... and from no commit of this `git ls-remote` listing ('-': stdin; with --tip)")
    args = parser.parse_args(argv)
    if args.tip is None and (args.exclude or args.advertised is not None):
        parser.error("--not and --advertised go with --tip")
    try:
        if args.update_allowlist:
            removed, added = update_allowlist(args.root)
            for row in removed:
                print(f"- {row}")
            for row in added:
                print(f"+ {row}")
            print(f"{ALLOWLIST}: {len(added)} rows added or changed, {len(removed)} removed or changed. A commit "
                  f"that introduces a blob over the budget also carries `{TRAILER}: <path>: <reason>`.")
            return 0
        advertised = None
        if args.range is not None:
            match = re.fullmatch(r"(.+?)\.\.(.+)", args.range)
            if match is None or "..." in args.range:
                parser.error("--range is BASE..TIP")
            bases, tip, label = [match.group(1)], match.group(2), args.range
        else:
            bases, tip = args.exclude, args.tip
            if args.advertised is not None:
                advertised = sys.stdin.read() if args.advertised == "-" else Path(args.advertised).read_text("utf-8")
            label = " ".join([tip] + [f"^{b}" for b in bases] + (["^advertised"] if advertised is not None else []))
        refusals, summary = check(args.root, tip, bases, advertised, label=label)
    except NoBase as error:
        print(f"OBJECT-BUDGET NOT JUDGED: {error}", file=sys.stderr)
        return NOT_JUDGED
    except (BudgetError, OSError, UnicodeError, ValueError) as error:
        print(f"OBJECT-BUDGET REFUSED: {error}", file=sys.stderr)
        return 1
    print(summary)
    shown: Dict[str, int] = {}
    for refusal in refusals:
        rule = refusal.split(":", 1)[0]
        shown[rule] = shown.get(rule, 0) + 1
        if shown[rule] <= SHOWN_PER_RULE:
            print(f"OBJECT-BUDGET REFUSED {refusal}", file=sys.stderr)
    if refusals:
        counts = ", ".join(f"{n} {rule}" for rule, n in sorted(shown.items()))
        hidden = sum(max(0, n - SHOWN_PER_RULE) for n in shown.values())
        print(f"{len(refusals)} refusal(s) ({counts}){f', {hidden} not shown' if hidden else ''}. Generated "
              "evidence goes to the external evidence store (docs/report-artifact-custody.md); history keeps "
              "every blob a pushed commit reaches.", file=sys.stderr)
        return 1
    print("OBJECT-BUDGET PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
