"""The public-clone gate's wall-clock bound must outlast the bounds of the steps it runs.

`publish/config.sh` commits the gate (`CHECK_CMD_DEFAULT`) and its bound
(`CHECK_TIMEOUT_SECONDS_DEFAULT`, which the publication engine applies to the
whole `&&` chain; 7200 when absent). The chain's first step is the verified
`targo trust check`, and targo holds that step to its OWN ceiling, `[trust]
compiler_timeout_secs` (the toolchain default, 8 h, when Cargo.toml declares
none; under Cargo it bounds the whole driver).

An engine bound at or under that ceiling stops the gate before targo can say
why (the engine's clock starts first), records a working gate as a FAILURE
with nothing refuted, and signals the whole process tree. The measurements
behind the numbers are in publish/DECISIONS.md (2026-09-30).

A chain with no verified step has no such ceiling. Its bound needs only the
allowance for the steps that carry no proof claim.
"""

from __future__ import annotations

import re
import unittest
from pathlib import Path
from typing import List

ROOT = Path(__file__).resolve().parents[2]
CONFIG = ROOT / "publish" / "config.sh"
MANIFEST = ROOT / "Cargo.toml"

# publication/bin/pub: DEFAULT_CHECK_TIMEOUT_SECONDS, MAX_CHECK_TIMEOUT_SECONDS.
ENGINE_DEFAULT = 7200
ENGINE_MIN, ENGINE_MAX = 60, 86400
# targo-trust/src/config.rs `default_compiler_timeout_secs`: the absolute
# ceiling of a verified Cargo run whose manifest declares none.
TARGO_DEFAULT_CEILING = 8 * 60 * 60
# What the chain needs after its verified step: `targo --unverified test`
# (worst measured 39m49s) and `targo metadata` (0 s), at about 3x -- the
# engine's own default for a whole ordinary gate.
AFTER_THE_VERIFIED_STEP = 2 * 60 * 60
VERIFIED_STEP = re.compile(r"\btargo\s+trust\s+")


def committed(config: str, key: str) -> str | None:
    """The value the engine reads (`load_config`'s `committed`): one
    double-quoted literal with nothing after the closing quote.  None when
    the key is absent; a spelling the engine would die on is a problem below."""
    match = re.search(rf'^{key}_DEFAULT="([^"]*)"\s*$', config, re.M)
    if match:
        return match.group(1)
    if re.search(rf"^{key}_DEFAULT=", config, re.M):
        return "<unparseable>"
    return None


CEILING_KEY = "compiler_timeout_secs"
CEILING_ROW = re.compile(rf"{CEILING_KEY}\s*=\s*([0-9]+)")


def ceiling(manifest: str) -> int:
    """targo's own ceiling for the verified step: the root manifest's
    `[trust] compiler_timeout_secs`, else the toolchain default.

    Read WITHOUT `tomllib`. Gate 0 runs this file under `python3`, and the
    gate tooling's supported Python is 3.9 (`scripts/pin_rewrite.py`), which
    predates it. The reader is narrow and fails closed, as that one is. Every
    line that mentions the key must be a whole-line comment, or the one row
    `compiler_timeout_secs = <decimal>` directly under a `[trust]` header.
    Any other spelling raises instead of defaulting: a dotted key, another
    table, an inline table, a trailing comment, or a second row. A ceiling
    this reader missed would let a bound that is too short pass.
    """
    table = None
    declared = []
    for number, raw in enumerate(manifest.splitlines(), 1):
        line = raw.strip()
        if line.startswith("#"):
            continue
        if line.startswith("["):
            table = line
        if CEILING_KEY not in line:
            continue
        row = CEILING_ROW.fullmatch(line)
        if table != "[trust]" or row is None:
            raise ValueError(
                f"Cargo.toml line {number}: `{line}` is not the one `{CEILING_KEY} = <decimal>` row of a "
                "`[trust]` table this reader accepts; widen the reader before relying on this spelling"
            )
        declared.append(int(row.group(1)))
    if len(declared) > 1:
        raise ValueError(f"Cargo.toml declares `{CEILING_KEY}` {len(declared)} times")
    return declared[0] if declared else TARGO_DEFAULT_CEILING


def problems(config: str, manifest: str) -> List[str]:
    found: List[str] = []
    command = committed(config, "CHECK_CMD") or ""
    steps = [step.strip() for step in command.split("&&")]
    verified = [index for index, step in enumerate(steps) if VERIFIED_STEP.search(step)]
    if verified not in ([0], []):
        found.append(
            f"the bound below assumes ONE verified step, run first; CHECK_CMD has verified steps at {verified}: "
            "re-derive the bound for this chain before changing this test"
        )
    raw = committed(config, "CHECK_TIMEOUT_SECONDS")
    if raw is None:
        found.append(f"CHECK_TIMEOUT_SECONDS_DEFAULT is absent, so the engine applies {ENGINE_DEFAULT}")
        bound = ENGINE_DEFAULT
    elif not re.fullmatch(r"[1-9][0-9]*", raw):
        found.append(f"CHECK_TIMEOUT_SECONDS_DEFAULT `{raw}` is not one positive integer the engine can read")
        return found
    else:
        bound = int(raw)
        if not ENGINE_MIN <= bound <= ENGINE_MAX:
            found.append(f"CHECK_TIMEOUT_SECONDS_DEFAULT {bound} is outside the engine's {ENGINE_MIN}..{ENGINE_MAX}")
    if not verified:
        # An unverified chain has no targo ceiling to outlast: what is left is
        # the allowance for the steps that carry no proof claim.
        if bound < AFTER_THE_VERIFIED_STEP:
            found.append(
                f"the gate's bound {bound} s is under the {AFTER_THE_VERIFIED_STEP} s an unverified chain's "
                "build and test steps are allowed"
            )
        return found
    needed = ceiling(manifest) + AFTER_THE_VERIFIED_STEP
    if bound < needed:
        found.append(
            f"the gate's bound {bound} s does not outlast the verified step's own ceiling "
            f"({ceiling(manifest)} s, `[trust] compiler_timeout_secs`) plus {AFTER_THE_VERIFIED_STEP} s for the "
            f"rest of the chain ({needed} s): the engine would stop a working gate before targo could say why"
        )
    return found


BOUND = 'CHECK_CMD_DEFAULT="rustup run trust targo trust check --workspace && rustup run trust targo --unverified test"\n'
BUDGET_ONLY = "[trust]\nfunction_budget_ms = 3000\n"


class TheGateOutlastsItsSteps(unittest.TestCase):
    def test_the_committed_bound_outlasts_the_verified_steps_ceiling(self) -> None:
        if not CONFIG.is_file():
            self.skipTest("public snapshot: publish/ is not exported, so there is no committed gate here")
        self.assertEqual(problems(CONFIG.read_text(encoding="utf-8"), MANIFEST.read_text(encoding="utf-8")), [])

    def test_no_bound_is_refused(self) -> None:
        # main before this test: no key, so the engine applied its 7200.
        self.assertIn("is absent, so the engine applies 7200", "\n".join(problems(BOUND, BUDGET_ONLY)))

    def test_the_bound_equal_to_the_ceiling_is_refused(self) -> None:
        # The gate branch's 28800 (92352968): equal to targo's default ceiling.
        found = problems(BOUND + 'CHECK_TIMEOUT_SECONDS_DEFAULT="28800"\n', BUDGET_ONLY)
        self.assertTrue(any("does not outlast" in problem for problem in found), found)

    def test_the_relation_follows_a_declared_ceiling(self) -> None:
        config = BOUND + 'CHECK_TIMEOUT_SECONDS_DEFAULT="36000"\n'
        self.assertEqual(problems(config, BUDGET_ONLY), [])
        raised = BUDGET_ONLY + "compiler_timeout_secs = 72000\n"
        self.assertTrue(any("does not outlast" in problem for problem in problems(config, raised)))
        self.assertEqual(problems(BOUND + 'CHECK_TIMEOUT_SECONDS_DEFAULT="79200"\n', raised), [])

    def test_the_engine_limits_and_spelling_are_held(self) -> None:
        for line, why in (
            ('CHECK_TIMEOUT_SECONDS_DEFAULT="86401"', "outside the engine's"),
            ('CHECK_TIMEOUT_SECONDS_DEFAULT="036000"', "not one positive integer"),
            ('CHECK_TIMEOUT_SECONDS_DEFAULT="36000" # ten hours', "not one positive integer"),
        ):
            found = problems(BOUND + line + "\n", BUDGET_ONLY)
            self.assertTrue(any(why in problem for problem in found), (line, found))

    def test_the_ceiling_reader_fails_closed_on_spellings_it_does_not_read(self) -> None:
        self.assertEqual(ceiling(BUDGET_ONLY), TARGO_DEFAULT_CEILING)
        self.assertEqual(ceiling(BUDGET_ONLY + "compiler_timeout_secs = 72000\n"), 72000)
        self.assertEqual(ceiling("# compiler_timeout_secs = 1\n" + BUDGET_ONLY), TARGO_DEFAULT_CEILING)
        for manifest in (
            "trust.compiler_timeout_secs = 72000\n",
            "[workspace]\ncompiler_timeout_secs = 72000\n",
            "trust = { compiler_timeout_secs = 72000 }\n",
            BUDGET_ONLY + "compiler_timeout_secs = 72000 # twenty hours\n",
            BUDGET_ONLY + 'compiler_timeout_secs = "72000"\n',
            BUDGET_ONLY + "compiler_timeout_secs = 72000\ncompiler_timeout_secs = 72000\n",
        ):
            with self.assertRaises(ValueError, msg=manifest):
                ceiling(manifest)

    def test_an_unverified_chain_needs_only_the_allowance_for_its_own_steps(self) -> None:
        chain = (
            'CHECK_CMD_DEFAULT="rustup run trust targo --unverified build --workspace && '
            'rustup run trust targo --unverified test"\n'
        )
        self.assertEqual(problems(chain + 'CHECK_TIMEOUT_SECONDS_DEFAULT="7200"\n', BUDGET_ONLY), [])
        found = problems(chain + 'CHECK_TIMEOUT_SECONDS_DEFAULT="7199"\n', BUDGET_ONLY)
        self.assertTrue(any("an unverified chain's" in problem for problem in found), found)
        self.assertIn("is absent, so the engine applies 7200", "\n".join(problems(chain, BUDGET_ONLY)))

    def test_a_second_verified_step_needs_a_new_derivation(self) -> None:
        config = (
            'CHECK_CMD_DEFAULT="rustup run trust targo --unverified test && rustup run trust targo trust check"\n'
            'CHECK_TIMEOUT_SECONDS_DEFAULT="36000"\n'
        )
        self.assertTrue(any("ONE verified step, run first" in problem for problem in problems(config, BUDGET_ONLY)))


if __name__ == "__main__":
    unittest.main()
