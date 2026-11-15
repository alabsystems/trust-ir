#!/usr/bin/env python3
"""Size the gates to the machine they run on, at the moment they run.

The one host-scaling helper of this repository. Nothing here is sized for one
host: every number is MEASURED when a leg starts (cores, physical memory, the
memory available right now) or LEARNED from this host's own earlier runs (the
peak resident size of the largest child a leg spawned), and every run prints
what it measured and what it chose.

  available memory   macOS: vm_stat's free + speculative + inactive + purgeable
                     pages (the kernel's free count plus what it reclaims
                     without paging anything out; ay's scripts/_oom_guard.py
                     reads the same four rows); Linux: /proc/meminfo
                     MemAvailable. Unreadable is refused, never guessed.
  margin             max(1 GiB, 10% of physical memory): room for the other
                     processes on the host to grow after the reading.
  per-child cap      the SHARE one child of this leg takes beside its heavy
                     one: over its last runs here, the most the sampled peak
                     of its process tree held per live child other than the
                     largest ((tree RSS - largest process) / (processes above
                     64 MiB - 1), sampled every 0.5 s; `share_of`), never
                     below the seed share of the leg's class (`cap_for`),
                     and the HEAVY child: the largest single process
                     (`wait4`'s ru_maxrss). Cargo's children
                     are not alike: one compiler of the stack's largest crate
                     reached 5.2 GiB while the whole -j14 test build peaked
                     at 7.1 GiB (measured, docs/gates-inventory.md), so a cap
                     of "the largest child" for every job would serialize
                     every build, and "the average" alone could not hold the
                     heavy one.
  jobs               min(the leg's wanted parallelism (capped by
                     TRUST_IR_TARGO_JOBS and a positive CARGO_BUILD_JOBS), cores,
                     floor((available - margin - (heavy - share)) / share)):
                     the heavy child's excess is reserved first, so
                     jobs x share + (heavy - share) <= available - margin.
                     When that is below one but the heavy child fits in
                     what is available, ONE job (the margin is waived and
                     the log says so: nothing is left to scale down).
  admission          a heavy child larger than the available memory: the
                     leg waits for room, re-measuring every 5 s, up to
                     TRUST_IR_ADMISSION_WAIT_S (600 s), then is refused
                     (exit 75, COULD NOT RUN). A busy host gets fewer jobs.

The cap is a planning number, not a kill switch: a compiler that grows past
it is not stopped (that would fail a build the host can still carry). No leg
of this repository had a memory-pressure watch before this helper; the
verified lanes keep Trust's own verification memory ceiling (gate 13's THE
RULE), and the operating system's compressor and swap remain the host's last
line.

SEEDS: the share and the heavy child measured on this workspace when this
helper was written (docs/gates-inventory.md): properties of this code base's
compilation units, not of any host. A leg's own learned values replace them
after one run.

Usage:
  host_scale.py measure                         # print the reading
  host_scale.py plan --per-child-mb N [--want N] [--reserve-mb N] [--label L]
  host_scale.py run --leg L [--want N] [--jobs-flag] -- CMD ARGS...
      Plans, inserts `-j N` after CMD's first argument (the targo verb) when
      --jobs-flag is given, runs CMD while sampling its process tree, records
      the leg's share and heavy child, prints wall time, CPU time and peaks,
      and exits with CMD's status.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import threading
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

MIB = 1 << 20
MIN_MARGIN_MB = 1024
MARGIN_FRACTION = 0.10
EX_TEMPFAIL = 75
LEARN_WINDOW = 5  # learned values are the max over this many most recent runs of a leg
BIG_CHILD_MB = 64  # a process below this is bookkeeping (cargo, shells), not a job

# Seeds (MiB) per leg class until this host has recorded a run of the leg.
# Measured on this workspace, before-cold run of 2026-10-14 (-j14, load ~45):
# the test builds' tree peaked at 7062 MiB over 14 compilers (~505 MiB per
# child); the largest single compiler (the Clean kernel / trust-ir stack) at
# 5179 MiB. A verified lane's base run peaked at 0.75 GiB (gate 13's
# docstring, 2026-09-29).
SEED: Dict[str, Tuple[int, int]] = {  # class -> (share, heavy)
    "build": (512, 5200),
    "verify": (1024, 1024),
}


@dataclass
class Reading:
    cores: int
    physical_mb: int
    available_mb: Optional[int]
    source: str
    load1: Optional[float]


def _sysctl(name: str) -> Optional[str]:
    try:
        return subprocess.check_output(["sysctl", "-n", name], text=True, stderr=subprocess.DEVNULL).strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def physical_mb() -> int:
    if sys.platform == "darwin":
        v = _sysctl("hw.memsize")
        if v and v.isdigit():
            return int(v) // MIB
    try:
        return os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES") // MIB
    except (ValueError, OSError, AttributeError):
        return 0


def parse_vm_stat(text: str) -> Optional[int]:
    """MiB of free + speculative + inactive + purgeable pages, or None."""
    m = re.search(r"page size of (\d+) bytes", text)
    if not m:
        return None
    page = int(m.group(1))
    rows = {}
    for line in text.splitlines():
        k, _, v = line.partition(":")
        v = v.strip().rstrip(".")
        if v.isdigit():
            rows[k.strip()] = int(v)
    need = ("Pages free", "Pages speculative", "Pages inactive", "Pages purgeable")
    if not all(k in rows for k in need):
        return None
    return sum(rows[k] for k in need) * page // MIB


def parse_meminfo(text: str) -> Optional[int]:
    m = re.search(r"^MemAvailable:\s+(\d+) kB", text, re.M)
    return int(m.group(1)) // 1024 if m else None


def available_mb() -> (Optional[int], str):
    if sys.platform == "darwin":
        try:
            out = subprocess.check_output(["vm_stat"], text=True, stderr=subprocess.DEVNULL)
        except (OSError, subprocess.CalledProcessError) as e:
            return None, f"vm_stat failed: {e}"
        return parse_vm_stat(out), "vm_stat free+speculative+inactive+purgeable"
    try:
        return parse_meminfo(Path("/proc/meminfo").read_text()), "/proc/meminfo MemAvailable"
    except OSError as e:
        return None, f"/proc/meminfo unreadable: {e}"


def measure() -> Reading:
    avail, source = available_mb()
    try:
        load1 = os.getloadavg()[0]
    except OSError:
        load1 = None
    return Reading(os.cpu_count() or 1, physical_mb(), avail, source, load1)


@dataclass
class Plan:
    jobs: int
    cap_mb: int
    margin_mb: int
    room_mb: int
    refused: Optional[str]
    note: Optional[str] = None


def plan_jobs(r: Reading, cap_mb: int, want: Optional[int] = None, reserve_mb: int = 0) -> Plan:
    """The largest job count whose caps fit in the measured room.

    The margin is room left for the host's other processes to grow; it sizes
    PARALLELISM. When not even one job fits beside the margin but the one
    child (its share plus the heavy reserve) fits in what is available, the
    plan is one job and says the margin is waived: there is nothing left to
    scale down, and the child fits. Only a child that does not fit in the
    available memory at all is refused."""
    if cap_mb <= 0:
        raise ValueError("a per-child cap must be positive")
    margin = max(MIN_MARGIN_MB, int(r.physical_mb * MARGIN_FRACTION))
    if r.available_mb is None:
        return Plan(0, cap_mb, margin, 0, f"available memory could not be measured ({r.source})")
    room = r.available_mb - margin - reserve_mb
    limit = max(1, min(want if want else r.cores, r.cores))
    fit = room // cap_mb if room > 0 else 0
    jobs = min(limit, fit)
    if jobs >= 1:
        return Plan(jobs, cap_mb, margin, room, None)
    if cap_mb + reserve_mb <= r.available_mb:
        return Plan(1, cap_mb, margin, room, None, (
            f"margin waived: one child ({cap_mb + reserve_mb} MiB with the heavy reserve) fits in the "
            f"{r.available_mb} MiB available but not beside the {margin} MiB margin; one job"))
    return Plan(0, cap_mb, margin, room, (
        f"not even one child fits: {cap_mb + reserve_mb} MiB (share {cap_mb} + heavy reserve {reserve_mb}) "
        f"> {r.available_mb} MiB available"))


# --------------------------------------------------------------------------
# Learned peaks (host-local, beside the gate cache)
# --------------------------------------------------------------------------


def state_dir() -> Path:
    if os.environ.get("TRUST_IR_GATE_CACHE"):
        return Path(os.environ["TRUST_IR_GATE_CACHE"])
    root = Path(__file__).resolve().parents[1]
    try:
        common = subprocess.check_output(
            ["git", "-C", os.fspath(root), "rev-parse", "--path-format=absolute", "--git-common-dir"],
            text=True, stderr=subprocess.DEVNULL).strip()
        return Path(common) / "trust-ir-gates"
    except (OSError, subprocess.CalledProcessError):
        return root / "target" / "gate-cache"


def _learned_file() -> Path:
    return state_dir() / "learned.json"


def load_learned() -> Dict[str, List[Dict[str, int]]]:
    try:
        data = json.loads(_learned_file().read_text())
        return {k: [dict(x) for x in v] for k, v in data.items() if isinstance(v, list)}
    except (OSError, ValueError, TypeError):
        return {}


def record(leg: str, share_mb: int, heavy_mb: int, tree_mb: int = 0, procs: int = 0) -> None:
    """Remember one run of `leg` (host-local, beside the gate cache)."""
    data = load_learned()
    entry = {"share": int(share_mb), "heavy": int(max(heavy_mb, share_mb)), "tree": int(tree_mb),
             "procs": int(procs)}
    data[leg] = (data.get(leg, []) + [entry])[-LEARN_WINDOW:]
    p = _learned_file()
    p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_name(f".learned.{os.getpid()}.tmp")
    tmp.write_text(json.dumps(data, sort_keys=True) + "\n")
    os.replace(tmp, p)


def share_of(tree_mb: int, procs: int, largest_mb: int, heavy_mb: int) -> int:
    """MiB one job of a leg takes BESIDE its heavy child, from the sampled
    peak of its process tree: the tree minus its largest process, over the
    other live children (processes above BIG_CHILD_MB). The plan charges
    jobs x share + (heavy - share), i.e. the heavy child plus (jobs - 1)
    shares, which then reproduces the measured peak at the measured number
    of live children. Dividing the whole tree by the children instead
    charged every job a part of the heavy one: a 4855 MiB peak of a 3290 MiB
    compiler and one 1565 MiB neighbour planned 2428 MiB a job. With no
    other live child at the peak nothing was measured beside the heavy one:
    0, and the plan's floor (`cap_for`) applies. `heavy_mb` is unused: the
    heavy child is reserved on its own."""
    del heavy_mb
    if procs > 1:
        return max(0, -(-(tree_mb - largest_mb) // (procs - 1)))
    return 0


def leg_class(leg: str) -> str:
    return "verify" if leg.startswith("verified-") else "build"


@dataclass
class Cap:
    share_mb: int
    heavy_mb: int
    why: str

    @property
    def reserve_mb(self) -> int:
        return max(0, self.heavy_mb - self.share_mb)


def cap_for(leg: str) -> Cap:
    """The leg's planning numbers. Learned values are the max over its last
    runs here, and a job is never charged less than the seed share of its
    class: a run that compiled little (an incremental test build: one large
    compiler and one small neighbour at the peak, measured 66 MiB beside it)
    says nothing about what each job of a run that compiles many crates
    takes. The heavy child is the leg's own measurement."""
    cls = leg_class(leg)
    seed_share, seed_heavy = SEED[cls]
    seen = load_learned().get(leg)
    if seen:
        share = max(max(e["share"] for e in seen), seed_share)
        return Cap(share, max(max(e["heavy"] for e in seen), share),
                   f"learned: max over this leg's last {len(seen)} run(s) here, share at least the "
                   f"`{cls}` seed {seed_share} MiB")
    return Cap(seed_share, seed_heavy, f"seed for a `{cls}` leg (no run of it recorded here)")


class TreeSampler:
    """Samples the RSS of a process tree every `interval` seconds (`ps`):
    the largest total seen, and how many processes above BIG_CHILD_MB were
    live at that moment. A sampler sees no spike shorter than its interval;
    the heavy child comes from `wait4`, which does."""

    def __init__(self, pid: int, interval: float = 0.5):
        self.pid = pid
        self.interval = interval
        self.peak_tree_mb = 0
        self.procs_at_peak = 0
        self.largest_at_peak_mb = 0
        self._stop = threading.Event()
        self._thread = threading.Thread(target=self._run, daemon=True)

    def __enter__(self) -> "TreeSampler":
        self._thread.start()
        return self

    def __exit__(self, *exc) -> None:
        self._stop.set()
        self._thread.join()

    def sample(self) -> Tuple[int, int, int]:
        out = subprocess.run(["ps", "-A", "-o", "pid=,ppid=,rss="], stdout=subprocess.PIPE,
                             stderr=subprocess.DEVNULL, text=True).stdout
        kids: Dict[int, List[int]] = {}
        rss: Dict[int, int] = {}
        for line in out.splitlines():
            parts = line.split()
            if len(parts) != 3 or not all(x.isdigit() for x in parts):
                continue
            pid, ppid, kb = map(int, parts)
            kids.setdefault(ppid, []).append(pid)
            rss[pid] = kb
        total, big, largest, stack = 0, 0, 0, [self.pid]
        while stack:
            p = stack.pop()
            if p in rss:
                total += rss[p]
                big += rss[p] >= BIG_CHILD_MB * 1024
                largest = max(largest, rss[p])
            stack.extend(kids.get(p, ()))
        return total // 1024, big, largest // 1024

    def _run(self) -> None:
        while not self._stop.is_set():
            try:
                total, big, largest = self.sample()
            except OSError:
                total, big, largest = 0, 0, 0
            if total > self.peak_tree_mb:
                self.peak_tree_mb, self.procs_at_peak, self.largest_at_peak_mb = total, big, largest
            self._stop.wait(self.interval)


def describe(label: str, r: Reading, p: Plan, why_cap: str, reserve_mb: int = 0) -> str:
    load = "?" if r.load1 is None else f"{r.load1:.1f}"
    head = (f"host-scale [{label}]: measured {r.cores} cores, {r.physical_mb} MiB physical, "
            f"{r.available_mb if r.available_mb is not None else '?'} MiB available ({r.source}), load1 {load}; "
            f"per-child cap {p.cap_mb} MiB, {reserve_mb} MiB reserved for the heavy child ({why_cap}); "
            f"margin {p.margin_mb} MiB; room {p.room_mb} MiB")
    if p.refused:
        return head + f" -> COULD NOT RUN: {p.refused}"
    if p.note:
        return head + f" -> {p.jobs} job ({p.note})"
    return head + f" -> {p.jobs} job(s) ({p.jobs * p.cap_mb} MiB planned <= {p.room_mb} MiB room)"


# --------------------------------------------------------------------------
# run: plan, run, measure, learn
# --------------------------------------------------------------------------


def maxrss_mb(ru_maxrss: int) -> int:
    return (ru_maxrss if sys.platform == "darwin" else ru_maxrss * 1024) // MIB


def with_jobs(cmd: List[str], jobs: int) -> List[str]:
    """`<runner> <verb> ...` -> `<runner> <verb> -j N ...` (Cargo/Targo take
    -j after the verb and before `--`)."""
    if len(cmd) < 2:
        return cmd
    return cmd[:2] + ["-j", str(jobs)] + cmd[2:]


def admit(leg: str, cap: Cap, want: Optional[int], wait_s: float) -> Tuple[Optional[Plan], Reading]:
    """Plan now; when not even one child fits, re-measure every 5 s for up to
    `wait_s` (peers finish and give memory back; there is no portable event
    for "memory became available" to block on), then refuse."""
    deadline = time.monotonic() + wait_s
    announced = 0.0
    while True:
        r = measure()
        p = plan_jobs(r, cap.share_mb, want, cap.reserve_mb)
        if not p.refused:
            return p, r
        now = time.monotonic()
        if now >= deadline:
            print(describe(leg, r, p, cap.why, cap.reserve_mb), file=sys.stderr, flush=True)
            return None, r
        if now - announced >= 60:
            print(f"host-scale [{leg}]: waiting for room ({p.refused}); "
                  f"{deadline - now:.0f} s left", file=sys.stderr, flush=True)
            announced = now
        time.sleep(5)


def run(leg: str, cmd: List[str], want: Optional[int], jobs_flag: bool, wait_s: float = 600.0) -> int:
    cap = cap_for(leg)
    p, r = admit(leg, cap, want, wait_s)
    if p is None:
        return EX_TEMPFAIL
    print(describe(leg, r, p, cap.why, cap.reserve_mb), file=sys.stderr, flush=True)
    argv = with_jobs(cmd, p.jobs) if jobs_flag else cmd
    t0 = time.monotonic()
    proc = subprocess.Popen(argv)
    with TreeSampler(proc.pid) as sampler:
        _, status, usage = os.wait4(proc.pid, 0)
    wall = time.monotonic() - t0
    code = os.waitstatus_to_exitcode(status)
    proc.returncode = code
    heavy = maxrss_mb(usage.ru_maxrss)
    tree, procs = sampler.peak_tree_mb, sampler.procs_at_peak
    share = share_of(tree, procs, sampler.largest_at_peak_mb, heavy)
    if code == 0:
        record(leg, share, heavy, tree, procs)
    print(f"host-scale [{leg}]: exit {code}; wall {wall:.1f} s; cpu {usage.ru_utime + usage.ru_stime:.1f} s; "
          f"peak tree {tree} MiB over {procs} live child(ren) (share {share} MiB); heavy child {heavy} MiB "
          f"(planned share {cap.share_mb}, heavy {cap.heavy_mb})", file=sys.stderr, flush=True)
    return code


def admission_wait_s() -> float:
    """TRUST_IR_ADMISSION_WAIT_S (default 600): how long a leg waits for room
    before it is refused. Malformed is refused (ValueError)."""
    wait = os.environ.get("TRUST_IR_ADMISSION_WAIT_S", "600")
    if not re.fullmatch(r"[0-9]+", wait):
        raise ValueError(f"TRUST_IR_ADMISSION_WAIT_S must be a whole number of seconds, got {wait!r}")
    return float(wait)


def caller_cap(want: Optional[int] = None) -> Optional[int]:
    """The job count the caller allows: `want`, capped by TRUST_IR_TARGO_JOBS
    and by a positive CARGO_BUILD_JOBS (the `-j` this helper passes would
    otherwise override a cap the caller set for Cargo). A malformed
    TRUST_IR_TARGO_JOBS is refused (ValueError); CARGO_BUILD_JOBS is Cargo's
    to validate, so only a positive integer there caps."""
    caps = [want] if want else []
    mine = os.environ.get("TRUST_IR_TARGO_JOBS")
    if mine:
        if not re.fullmatch(r"[1-9][0-9]*", mine):
            raise ValueError(f"TRUST_IR_TARGO_JOBS must be a positive integer, got {mine!r}")
        caps.append(int(mine))
    cargo = os.environ.get("CARGO_BUILD_JOBS", "")
    if re.fullmatch(r"[1-9][0-9]*", cargo):
        caps.append(int(cargo))
    return min(caps) if caps else None


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("measure")
    p = sub.add_parser("plan")
    p.add_argument("--per-child-mb", type=int, required=True)
    p.add_argument("--heavy-mb", type=int, default=0)
    p.add_argument("--want", type=int)
    p.add_argument("--reserve-mb", type=int, default=0)
    p.add_argument("--label", default="plan")
    p = sub.add_parser("run")
    p.add_argument("--leg", required=True)
    p.add_argument("--want", type=int)
    p.add_argument("--jobs-flag", action="store_true")
    p.add_argument("command", nargs=argparse.REMAINDER)
    args = ap.parse_args(argv)
    if args.cmd == "measure":
        r = measure()
        print(json.dumps(r.__dict__, sort_keys=True))
        return 0 if r.available_mb is not None else 1
    if args.cmd == "plan":
        r = measure()
        reserve = args.reserve_mb + max(0, args.heavy_mb - args.per_child_mb)
        pl = plan_jobs(r, args.per_child_mb, args.want, reserve)
        print(describe(args.label, r, pl, "given", reserve), file=sys.stderr)
        if pl.refused:
            return EX_TEMPFAIL
        print(f"HOST_JOBS={pl.jobs}")
        return 0
    cmd = list(args.command)
    if cmd and cmd[0] == "--":
        cmd = cmd[1:]
    if not cmd:
        ap.error("run needs a command after --")
    try:
        want = caller_cap(args.want)
        wait = admission_wait_s()
    except ValueError as e:
        print(e, file=sys.stderr)
        return 2
    return run(args.leg, cmd, want, args.jobs_flag, wait)


if __name__ == "__main__":
    sys.exit(main())
