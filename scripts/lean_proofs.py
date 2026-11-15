#!/usr/bin/env python3
"""The Lean proofs as a standing gate (gate 14 of scripts/ci_gates.sh, `lean-proofs`).

WHY THIS EXISTS
---------------
Measured 2026-09-29: no standing gate ran `lake build` of
lean/trust_ir-semantics. Gate 12 (`lean-exec-differential`) builds only the
`trustir_eval` executable, which imports the executable semantics and not the
proofs, so every `(lean-theorem)` enforcement row and the `AxiomAudit.lean`
`#guard_msgs` axiom gate (which CLAUDE.md called "part of the build") rested on
somebody running the build by hand. And the build alone is not enough: a
proof placeholder is a WARNING in Lean, so a theorem with one builds green, and
`AxiomAudit.lean` pins the axiom printout of a CURATED list only, so a theorem
not on it could rest on a placeholder, on `native_decide` or on a new axiom
and nothing would say so.

WHAT IT CHECKS, in order, all fail-closed
-----------------------------------------
  1. ORPHANS   every `.lean` under `TrustIr/` must be imported by the
               checked `TrustIr` aggregate; every `TrustIrRuntime/` source
               must be reached by its separately built runtime root. The pure
               `TrustIr.Formal` root must not import runtime or native fixtures.
               The unproved provider stays outside the logical census; the
               separate runtime-boundary guard inventories its obligations.
  2. SOURCES   no `debug.skipKernelTC` in either checked closure (outside comments): an
               option that admits a declaration WITHOUT the kernel check. A
               tripwire that names the cause early (Lean 4.8.0 has no such
               option); the REPLAY (step 6) is what refuses a constant the
               kernel never admitted, however it got into the environment.
  3. BUILD     `lake build TrustIr` and the runtime's native library exit 0.
               Lake preloads runtime symbols for native fixture elaboration.
               A failing `#guard_msgs` (every
               axiom printout in `AxiomAudit.lean`) and every elaboration error
               land here, named by file and line.
  4. SORRY     no "declaration uses 'sorry'" in the build log. Lake replays a
               cached module's log, so a warm build still shows it; this is the
               only check that sees a placeholder inside an `example`, which
               never enters the environment.
  5. CENSUS    `lake lean ProofCensus.lean`: for EVERY safe constant of a
               `TrustIr.*` module, the axioms its kernel term depends on (the
               `#print axioms` relation) are the Lean-core trio plus
               `TrustIr.ay_sound_unsat`, with `Lean.ofReduceBool`
               (`native_decide`) admitted only in the executable-fixture
               modules; the only safe `axiom` declared is
               `TrustIr.ay_sound_unsat`. Refusals name each declaration and
               axiom. The census line must be present and must agree with the
               orphan check on the number of `TrustIr.*` modules imported.
  6. REPLAY    in the same run, `Lean.Environment.replay` (Lean core's
               `Lean/Replay.lean`, the engine of lean4checker) re-sends EVERY
               safe `TrustIr.*` constant to the kernel on top of the
               library's exact external import closure (including `Init` and
               its pinned Lean library dependencies), so each one is admitted
               again from the term the `.olean` stores; an inductive's
               constructors and recursors must equal the regenerated ones.
               The census and the build read what the environment RECORDS, and
               a meta-program can record a constant without the kernel
               (measured 2026-09-29: a module calling the private
               `Environment.add` through `evalConst` planted
               `theorem review_forged_false : False := Nat.zero` and both
               passed; the replay refuses it, "declaration type mismatch,
               'TrustIr.review_forged_false' has type Nat but it is expected to
               have type False"). A `native_decide` site
               (`Lean.ofReduceBool aux b h`, admitted in the fixture modules
               only) is replayed with `h` replaced by a premise
               `Lean.reduceBool aux = b` that exists only after running
               `aux`'s compiled code gives `b`; so the kernel re-checks all of
               such a proof except the evaluation, and the evaluation is re-run.
               Not replayed: the `_unsafe_rec` bodies of `partial` definitions,
               which no safe constant may name (the kernel refuses it). The
               census line's `replayed` and `replay-skipped-partial` must add up
               to `safe-constants` (checked here).

WHAT IT DOES NOT DO
-------------------
* It trusts the Lean kernel (TRUST.md item 1). The replay runs the SAME
  kernel a second time, over the stored terms: it closes admission WITHOUT the
  kernel, not a kernel bug. Lean 4.8.0 ships no `leanchecker` executable and
  no independent checker is run.
* A green run means each THEOREM's stored proof was admitted by that kernel,
  twice, from the admitted axioms (a `native_decide` fixture's modulo the
  evaluation, which is re-run). Whether a statement says what a
  document claims is the reader's judgement, and so is whether the Lean model
  means what the interpreter does (TRUST.md item 3, the known gap).
* The 462 `native_decide` fixture theorems (at 2026-09-29) are EVALUATIONS:
  `Lean.ofReduceBool` trusts the Lean compiler and runtime, not only the
  kernel, and the replay re-runs that same compiled code rather than checking
  it. They are tests, and check_enforcement_links.py counts them as such.
* `TrustIrEval` (the execution oracle) is gate 12's, not audited here.

Without lake: ci_gates.sh passes `--require` whenever `$HOME/.elan/bin/lake`
exists (gate 12's condition). Elsewhere this prints SKIP, says that no
`(lean-theorem)` row is checked on this machine, and exits 0; with `--require`
(or TRUST_IR_REQUIRE_LEAN=1) a missing lake is a failure.

Measured 2026-09-29 (Lean 4.8.0, this machine): warm 9.5 s wall (the build
replays in 0.2 s; the census and the kernel replay of 6,839 constants with
462 re-run evaluations take 8.9 s); cold 2 min 1 s wall (112.0 s to
elaborate all 52 modules from an empty `.lake`, then the same census and
replay in 9.0 s).

Usage: lean_proofs.py [--root DIR] [--package DIR] [--require]
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Set

PACKAGE = Path("lean") / "trust_ir-semantics"
ROOT_MODULE = "TrustIr"
RUNTIME_ROOT_MODULE = "TrustIrRuntime"
FORMAL_ROOT_MODULE = "TrustIr.Formal"
CENSUS_FILE = "ProofCensus.lean"
# The elan toolchain links with its own bundled libc stubs; an inherited
# SDKROOT (Apple's xcrun shims export it into every child) redirects clang.
# `lake build TrustIr` links nothing today, but it is the same toolchain as
# gate 12's `trustir_eval` build, so it gets the same scrubbed environment.
SCRUBBED_ENV = ("SDKROOT",)
SORRY_WARNING = "declaration uses 'sorry'"
CENSUS_LINE = re.compile(r"lean-proofs census: .*")
KERNEL_BYPASS = re.compile(r"\bskipKernelTC\b")
IMPORT_LINE = re.compile(r"^\s*import\s+(.+)$")
NATIVE_DECIDE_DEF = re.compile(r"def\s+nativeDecideModules\s*:\s*List\s+Name\s*:=\s*\[(.*?)\]", re.S)
NAME_LITERAL = re.compile(r"`+([A-Za-z_][\w.]*)")


def strip_lean_comments(source: str) -> str:
    """Blank `--` line comments and (nested) `/- -/` block comments, keeping
    line numbers. String literals are left alone: the tokens this gate looks
    for are option and module names, never text inside a string."""
    out: List[str] = []
    i, depth, n = 0, 0, len(source)
    while i < n:
        two = source[i : i + 2]
        if depth == 0 and two == "--":
            j = source.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif two == "/-":
            depth += 1
            out.append("  ")
            i += 2
        elif depth > 0 and two == "-/":
            depth -= 1
            out.append("  ")
            i += 2
        elif depth > 0:
            out.append("\n" if source[i] == "\n" else " ")
            i += 1
        else:
            out.append(source[i])
            i += 1
    return "".join(out)


def module_path(package: Path, module: str) -> Path:
    return package.joinpath(*module.split(".")).with_suffix(".lean")


def import_closure(package: Path, root_module: str = ROOT_MODULE) -> Dict[str, Path]:
    """Module name -> file for every package module `root_module` imports,
    transitively (itself included). Imports that name no file in the package
    (`Lean`, `Init`) are the toolchain's, not ours."""
    closure: Dict[str, Path] = {}
    todo = [root_module]
    while todo:
        module = todo.pop()
        if module in closure:
            continue
        path = module_path(package, module)
        if not path.is_file():
            continue
        closure[module] = path
        for line in strip_lean_comments(path.read_text(encoding="utf-8")).split("\n"):
            match = IMPORT_LINE.match(line)
            if match:
                todo.extend(match.group(1).split())
    return closure


def audited_module_count(closure: Dict[str, Path]) -> int:
    """Match ProofCensus.isAuditedModule's exact Lean Name root test."""
    return sum(name == ROOT_MODULE or name.startswith(ROOT_MODULE + ".") for name in closure)


def logical_attachment_problems(closure: Dict[str, Path]) -> List[str]:
    """Our one native attachment is outside the census namespace. Keep it
    declaration-free, so it cannot become an inherited proof authority."""
    return [name for name, path in closure.items()
            if not (name == ROOT_MODULE or name.startswith(ROOT_MODULE + "."))
            and (name != "TrustIrNativeLink"
                 or strip_lean_comments(path.read_text(encoding="utf-8")).strip() != "import Init")]


def runtime_import_closure(package: Path) -> Dict[str, Path]:
    """Runtime sources are compiled as a separate native dependency. Their
    unproved obligations are inventoried by check_lean_runtime_boundary.py."""
    return import_closure(package, RUNTIME_ROOT_MODULE)


def runtime_model_leaks(closure: Dict[str, Path]) -> List[str]:
    return sorted(name for name in closure if name == "TrustIrRuntime" or name.startswith("TrustIrRuntime.")
                  or name == "TrustIr.Runtime" or name.startswith("TrustIr.Runtime."))


def orphan_files(package: Path, closure: Dict[str, Path], root_module: str = ROOT_MODULE) -> List[str]:
    """Every source under the specified root directory must be reached by
    that root. Logical and runtime roots are checked separately."""
    built = {p.resolve() for p in closure.values()}
    directory = package / root_module
    if not directory.is_dir():
        return []
    return sorted(os.fspath(p.relative_to(package)) for p in directory.rglob("*.lean")
                  if p.resolve() not in built)


def lake_config_args(environ: Dict[str, str]) -> List[str]:
    """An explicit native linker is a build input, recorded by Lake's traces."""
    linker = environ.get("TRUST_IR_NATIVE_LINKER")
    if not linker:
        return ["-R"]
    path = Path(linker).expanduser().absolute()
    if not path.is_file() or not os.access(path, os.X_OK):
        raise ValueError(f"native linker is not executable: {path}")
    return ["-R", f"-KnativeLinker={path}"]


def native_decide_modules(package: Path) -> Optional[List[str]]:
    """The module names `ProofCensus.lean` admits `Lean.ofReduceBool` in (its
    `nativeDecideModules`), read from the census source so the list is stated
    once. `None` when the census file is absent; a census file whose list
    cannot be read raises, never reads as empty."""
    census = package / CENSUS_FILE
    if not census.is_file():
        return None
    match = NATIVE_DECIDE_DEF.search(strip_lean_comments(census.read_text(encoding="utf-8")))
    if not match:
        raise ValueError(f"{census}: no `def nativeDecideModules : List Name := [...]` to read")
    names = NAME_LITERAL.findall(match.group(1))
    if not names:
        raise ValueError(f"{census}: `nativeDecideModules` names no module")
    return names


def kernel_bypasses(closure: Dict[str, Path], package: Path) -> List[str]:
    found = []
    for path in sorted(closure.values()):
        for number, line in enumerate(strip_lean_comments(path.read_text(encoding="utf-8")).split("\n"), 1):
            if KERNEL_BYPASS.search(line):
                found.append(f"{os.fspath(path.relative_to(package))}:{number}: {line.strip()}")
    return found


def clean_location(line: str) -> str:
    """Lake prints `././././TrustIr/X.lean:1:2:`; keep `TrustIr/X.lean:1:2:`."""
    return re.sub(r"(?:\./)+(?=\S+\.lean:)", "", line)


def sorry_warnings(log: str) -> List[str]:
    return [clean_location(l.strip()) for l in log.split("\n") if SORRY_WARNING in l]


def build_errors(log: str) -> List[str]:
    return [clean_location(l.strip()) for l in log.split("\n") if l.lstrip().startswith("error")]


def census_line(output: str) -> Optional[str]:
    match = CENSUS_LINE.search(output)
    return match.group(0).strip() if match else None


def census_field(line: str, key: str) -> Optional[str]:
    match = re.search(rf"(?<![\w-]){re.escape(key)}=(\S+)", line)
    return match.group(1) if match else None


REPLAY_LEDGER = ("safe-constants", "replayed", "replay-skipped-partial")


def replay_ledger_problems(line: str) -> List[str]:
    """The kernel replay must account for every safe constant: `replayed`
    plus `replay-skipped-partial` equals `safe-constants`, and something was
    replayed. A census line without the replay's fields is a failure, never a
    pass: it would mean the replay did not run."""
    values: Dict[str, int] = {}
    for key in REPLAY_LEDGER:
        raw = census_field(line, key)
        if raw is None or not raw.isdigit():
            return [f"replay: the census line has no numeric `{key}=` field"]
        values[key] = int(raw)
    if values["replayed"] == 0:
        return ["replay: nothing was replayed"]
    accounted = values["replayed"] + values["replay-skipped-partial"]
    if accounted != values["safe-constants"]:
        return [
            f"replay: replayed={values['replayed']} + replay-skipped-partial={values['replay-skipped-partial']}"
            f" = {accounted}, but safe-constants={values['safe-constants']}"
        ]
    return []


def find_lake(environ: Dict[str, str]) -> Optional[Path]:
    """TRUST_IR_LAKE, then $HOME/.elan/bin/lake, then `lake` on PATH (the
    order gate 12's harness uses)."""
    explicit = environ.get("TRUST_IR_LAKE")
    if explicit:
        return Path(explicit)
    home = environ.get("HOME")
    if home:
        elan = Path(home) / ".elan" / "bin" / "lake"
        if elan.is_file() and os.access(elan, os.X_OK):
            return elan
    found = shutil.which("lake", path=environ.get("PATH"))
    return Path(found) if found else None


def lake_environment(lake: Path, environ: Dict[str, str]) -> Dict[str, str]:
    env = {k: v for k, v in environ.items() if k not in SCRUBBED_ENV}
    # `lake` needs `lean` beside it on PATH.
    env["PATH"] = os.pathsep.join([os.fspath(lake.parent), environ.get("PATH", "")])
    return env


def run(cmd: Sequence[str], cwd: Path, env: Dict[str, str]) -> subprocess.CompletedProcess:
    return subprocess.run(list(cmd), cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--package", type=Path, help=f"the Lean package (default: <root>/{PACKAGE})")
    parser.add_argument("--require", action="store_true", help="a missing lake is a failure")
    args = parser.parse_args(argv)
    # Progress lines (stdout) and the refusal list (stderr) interleave in order.
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(line_buffering=True)
    package = (args.package or args.root / PACKAGE).resolve()
    require = args.require or os.environ.get("TRUST_IR_REQUIRE_LEAN") == "1"
    failures: List[str] = []

    closure = import_closure(package)
    if ROOT_MODULE not in closure:
        print(f"FAIL: {module_path(package, ROOT_MODULE)} is missing", file=sys.stderr)
        return 1
    runtime = runtime_import_closure(package)
    for module in logical_attachment_problems(closure):
        failures.append(f"logical-attachment: unreviewed declarations/imports outside census: {module}")
    orphans = orphan_files(package, closure) + orphan_files(package, runtime, RUNTIME_ROOT_MODULE)
    for orphan in orphans:
        failures.append(f"orphan: {orphan} is not imported by the checked aggregate root")
    formal = import_closure(package, FORMAL_ROOT_MODULE)
    if FORMAL_ROOT_MODULE not in formal:
        failures.append(f"formal-root: {FORMAL_ROOT_MODULE} is missing")
    for leak in runtime_model_leaks(formal):
        failures.append(f"runtime-boundary: {leak} is imported by the pure formal root")
    for bypass in kernel_bypasses({**runtime, **closure}, package):
        failures.append(f"kernel-bypass: {bypass}")
    try:
        fixtures = native_decide_modules(package) or []
        for module in fixtures:
            if module in formal:
                failures.append(f"fixture-boundary: {module} is imported by the pure formal root")
    except ValueError as err:
        failures.append(f"census-source: {err}")
    print(f"lean-proofs: {len(closure)} modules in the {ROOT_MODULE} import closure, {len(orphans)} orphan file(s)")

    lake = find_lake(dict(os.environ))
    if lake is None or not lake.exists():
        if require:
            print("FAIL: no lake (TRUST_IR_LAKE, $HOME/.elan/bin/lake, PATH) and the Lean build is required", file=sys.stderr)
            return 1
        print(
            "SKIP: no lake on this machine, so the Lean proofs are NOT built here: no (lean-theorem) row, "
            "no AxiomAudit printout and no axiom census is checked by this run"
        )
        return 1 if failures else 0
    env = lake_environment(lake, dict(os.environ))

    try:
        config = lake_config_args(dict(os.environ))
    except ValueError as err:
        print(f"FAIL: {err}", file=sys.stderr)
        return 1
    targets = [ROOT_MODULE]
    if runtime:
        targets.append(RUNTIME_ROOT_MODULE)
        print("lean-proofs: pure formal root is isolated; runtime native symbols "
              "loaded through the native attachment; logical safe constants remain audited")
    started = time.monotonic()
    build = run([os.fspath(lake), *config, "build", *targets], package, env)
    build_seconds = time.monotonic() - started
    if build.returncode != 0:
        errors = build_errors(build.stdout) or build.stdout.strip().split("\n")[-20:]
        failures.append(f"build: `lake build {' '.join(targets)}` exited {build.returncode}")
        failures.extend(f"  {e}" for e in errors)
    for warning in sorry_warnings(build.stdout):
        failures.append(f"sorry: {warning}")
    print(f"lean-proofs: lake build {' '.join(targets)}: exit {build.returncode} in {build_seconds:.1f}s")

    if build.returncode == 0:
        started = time.monotonic()
        census = run([os.fspath(lake), *config, "lean", CENSUS_FILE], package, env)
        census_seconds = time.monotonic() - started
        line = census_line(census.stdout)
        if census.returncode != 0:
            failures.append(f"census: `lake lean {CENSUS_FILE}` exited {census.returncode}")
            failures.extend(f"  {clean_location(l)}" for l in census.stdout.strip().split("\n") if l.strip())
        elif line is None:
            failures.append(f"census: exit 0 but no `lean-proofs census:` line:\n{census.stdout}")
        else:
            imported = census_field(line, "imported-modules")
            if imported != str(audited_module_count(closure)):
                failures.append(
                    f"census: the environment imports {imported} {ROOT_MODULE}.* modules, the audited source closure has {audited_module_count(closure)}"
                )
            failures.extend(replay_ledger_problems(line))
        if line:
            print(line)
        print(f"lean-proofs: census and kernel replay in {census_seconds:.1f}s")

    if failures:
        print("lean-proofs REFUSED:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1
    print("lean-proofs: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
