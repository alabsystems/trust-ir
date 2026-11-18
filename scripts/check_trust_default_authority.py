#!/usr/bin/env python3
"""Fail-closed preflight for a Trust-pinned repository default.

An upstream toolchain is an honest, unverified default and passes unless
``--require-verified-default`` is requested. A ``channel = "trust"`` pin is
held to two bars, the same two tiers Trust's own launcher reports on every
``targo trust`` run:

* RAMP (default): the pin and the Targo lane resolve to ONE caller-owned Trust
  compiler (same 40-hex commit, a real ``targo``, no other principal can write
  either tree or the lane's launchers, no symlinked artifact in a tree, a
  symlinked launcher followed hop by hop to the file that runs, never an x.py
  build tree), no unit is switched off, and that compiler's no-flag default
  refuses a deliberate refutation. An explicit Cargo-config policy is optional here, because the
  canary measures the default the pin actually gets.
* DESTINATION (``--require-verified-default``): additionally an explicit
  strict/certify policy and ONE sealed, read-only ``trust-<commit>`` sysroot
  named by ``TRUST_SEALED_SYSROOT`` that the pin AND the lane resolve to.

In both tiers an explicit policy line governs rustup-proxied builds only:
``targo trust`` ignores it and selects its own lane (``POLICY_SCOPE``; the
checker prints that scope beside every configured policy). Every ``-Ztrust-*``
flag in the configuration is held to a closed table
(``AUDITED_STRENGTHENING_FLAGS``). Native Targo is resolved first and its
actual companion trustc is probed; rustup is not required for a complete native
lane. Legacy proxy discovery is used only without that native lane.

This checker does not turn verification on; it prevents configuration text
from claiming authority that the installed toolchain cannot supply.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Optional, Sequence

try:
    import tomllib
except ModuleNotFoundError:
    from _vendor import tomli as tomllib

# Any x.py build tree (`build/host/stage2`, `build/<triple>/stage1`, ...): a
# compiler a rebuild can replace underneath the checked name. Paths are
# resolved first, so the `host` symlink resolves to the triple it names.
MUTABLE_BUILD_TREE_RE = re.compile(r'(?:^|/)build(?:\.noindex)?/[^/]+/stage[0-9]+(?:-[^/]+)?(?:/|$)')
COMMIT_HASH_RE = re.compile(r'^[0-9a-f]{40}$')
RUSTC_OVERRIDE_RE = re.compile(
    r'^\s*(?:(?:build|env)\s*\.\s*)?'
    r'(?:rustc-wrapper|rustc-workspace-wrapper|rustc|RUSTC|RUSTC_WRAPPER|'
    r'RUSTC_WORKSPACE_WRAPPER|CARGO_BUILD_RUSTC|CARGO_BUILD_RUSTC_WRAPPER|'
    r'CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER)\s*=',
    re.MULTILINE,
)
AMBIENT_RUSTC_OVERRIDES = {
    "RUSTC",
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "CARGO_BUILD_RUSTC",
    "CARGO_BUILD_RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
}


@dataclass(frozen=True)
class LaneToolchain:
    """The compiler the Targo lane actually runs.

    ``targo`` compiles with the canonical ``trustc`` beside it, not with
    whatever rustup's pin resolves, so the pin is only honest if both name the
    same compiler. ``discriminated`` records ``targo --unverified --version``
    succeeding: upstream Cargo installed under the name ``targo`` rejects that
    flag, and it is the one discriminator Trust's CLAUDE.md says has held.
    """

    targo: Optional[Path]
    discriminated: bool
    rustc: Optional[Path]
    sysroot: Optional[Path]
    commit_hash: Optional[str]


@dataclass(frozen=True)
class ResolvedToolchain:
    rustc: Optional[Path]
    sysroot: Optional[Path]
    rustup_link: Optional[Path]
    sealed_root: Optional[Path]
    host: Optional[str]
    commit_hash: Optional[str]
    lane: Optional[LaneToolchain] = None
    # The ONE reason the native lane or compatibility pin could not be resolved,
    # reported instead of the four per-field
    # failures it would otherwise cascade into.
    resolution_error: Optional[str] = None
    # Native Targo owns compiler selection; rustup is optional compatibility.
    native: bool = False


def toolchain_channel(text: str) -> Optional[str]:
    """Read the actual TOML pin; parse/type errors must never mean unpinned."""
    document = tomllib.loads(text)
    if not document:
        return None
    toolchain = document.get("toolchain")
    if not isinstance(toolchain, dict):
        raise ValueError("toolchain must be a TOML table")
    channel = toolchain.get("channel")
    if channel is not None and not isinstance(channel, str):
        raise ValueError("toolchain.channel must be a string")
    return channel


def _toml_strings_and_normalized(text: str) -> tuple[list[str], str, list[str]]:
    """Lex enough Cargo TOML to decode strings and erase comments.

    Trust flags are collected from every string, rather than from a short list
    of table layouts. That is deliberately fail-closed: Cargo accepts flags in
    target, build, and ``[env]`` tables, including dotted and quoted keys.
    Multiline strings are not useful Cargo flag values and are rejected instead
    of being incompletely audited.
    """
    strings: list[str] = []
    normalized: list[str] = []
    issues: list[str] = []
    index = 0
    while index < len(text):
        char = text[index]
        if char == "#":
            newline = text.find("\n", index)
            if newline < 0:
                break
            normalized.append("\n")
            index = newline + 1
            continue
        if char not in {'"', "'"}:
            normalized.append(char)
            index += 1
            continue

        quote = char
        if text.startswith(quote * 3, index):
            issues.append("verified Cargo configuration cannot use multiline strings")
            closing = text.find(quote * 3, index + 3)
            if closing < 0:
                return strings, "".join(normalized), issues
            index = closing + 3
            continue

        end = index + 1
        escaped = False
        while end < len(text):
            current = text[end]
            if quote == '"' and current == "\\" and not escaped:
                escaped = True
                end += 1
                continue
            if current == quote and not escaped:
                break
            escaped = False
            if current == "\n":
                issues.append("verified Cargo configuration contains an unterminated string")
                return strings, "".join(normalized), issues
            end += 1
        if end >= len(text):
            issues.append("verified Cargo configuration contains an unterminated string")
            return strings, "".join(normalized), issues

        token = text[index : end + 1]
        try:
            if quote == '"':
                # JSON and TOML share the single-line basic-string escapes used
                # by Cargo. Expand TOML's eight-hex-digit form before JSON.
                token = re.sub(
                    r"\\U([0-9A-Fa-f]{8})",
                    lambda match: "\\u" + match.group(1)[4:]
                    if int(match.group(1), 16) <= 0xFFFF
                    else chr(int(match.group(1), 16)),
                    token,
                )
                value = json.loads(token)
            else:
                value = token[1:-1]
        except (ValueError, json.JSONDecodeError):
            issues.append("verified Cargo configuration contains an unauditable string escape")
            value = token[1:-1]
        strings.append(value)
        # Decoding quoted keys closes Unicode-escape evasions in names such as
        # ``RUSTC_WRAPPER``. Escaping a quote may only create a conservative
        # false positive in this fail-closed authority preflight.
        normalized.append(value)
        index = end + 1
    return strings, "".join(normalized), issues


def _canonical_trust_flags(values: Iterable[str]) -> Iterable[str]:
    tokens = []
    for value in values:
        tokens.extend(value.replace("\x1f", " ").split())
    index = 0
    while index < len(tokens):
        token = tokens[index]
        if token == "-Z" and index + 1 < len(tokens):
            value = tokens[index + 1]
            if value.startswith("trust-"):
                yield f"-Z{value}"
                index += 2
                continue
        if token.startswith("-Ztrust-"):
            yield token
        index += 1


def configured_flags(config_text: str) -> Iterable[str]:
    """Yield canonical Trust flags from all decoded Cargo string values."""
    strings, _, _ = _toml_strings_and_normalized(config_text)
    yield from _canonical_trust_flags(strings)


# The RAMP and the DESTINATION are different bars, and both are real.
#
# DESTINATION (`--require-verified-default`): strict or certify, nothing
# switched off anywhere. That is "all batteries included" and it does not move.
#
# RAMP (default): `-Ztrust-policy=advisory` is additionally accepted, because it
# is the only rung that exists today — `targo trust check` ignores advisory and
# always runs strict, and on Trust's own README example (`midpoint`, four lines)
# strict reports `Gate: FAIL`, 4 proved / 6 unknown. A bar nothing can clear is
# not a bar; it is a way of having no verification at all while sounding strict,
# which is exactly what the fleet's blanket `-Ztrust-verify=off` already was.
#
# Advisory does NOT mean verification is off: activation is the compiler default
# and every obligation is still checked and reported. What advisory changes is
# whether a refutation fails the build. The ratchet is what makes that
# non-ceremonial — proved counts may not regress — and the destination above is
# what it ratchets TOWARD.
#
# This function therefore reports a ramp posture as a RAMP, never as a verified
# default. Nothing here weakens the destination; it just stops pretending the
# fleet is already standing on it.
#
# ABSENT POLICY ON THE RAMP (2026-09-28, owner directive "we need to use Trust
# compiler for all ALab systems"): the pin selects the compiler, and the Targo
# lane selects the policy — `targo trust check` ran STRICT with
# `-Ztrust-policy=advisory` in `[build] rustflags` and ADVISORY with
# `--allow-l0-gaps` over a `strict` one (measured on trustc 321aaeda7), so a
# Cargo-config policy is not what a verified run obeys. What a policy-less
# config leaves in force is the compiler's own default, and `check()` never
# accepts that without `behavioral_issues` proving the default refuses a
# deliberate refutation — i.e. it is at least strict, which is a higher bar
# than the advisory rung this ramp already admits. The destination still
# demands an EXPLICIT strict/certify selection.
ADVISORY_RAMP_POLICY = "-Ztrust-policy=advisory"
DESTINATION_POLICIES = {"-Ztrust-policy=strict", "-Ztrust-policy=certify"}

# The one activation spelling. trustc documents `-Ztrust-verify=<on|off>` as
# "the sole verification activation control"; `-Ztrust-verify-level=`,
# `-Ztrust-verify-profile=`, ... are separate knobs that merely share the
# prefix, so a knob is never read as an activation (that misreading refused
# ay's live config nine times as "disables verification").
ACTIVATION_ON = "-Ztrust-verify=on"

# Every other `-Ztrust-*` flag a Trust-pinned default may carry, by exact
# spelling: each only ADDS obligations or strictness (trustc 321aaeda7
# `-Z help`). The table is CLOSED. trustc keeps growing `-Ztrust-*` knobs and
# some of them hand away authority: `-Ztrust-verify-ay-path=` runs an
# arbitrary executable as the solver, and `-Ztrust-dump=mir-only:` "skips
# solver/certifier dispatch". A flag this checker has not read is refused, not
# assumed harmless; admit one by adding its row here with the reason.
AUDITED_STRENGTHENING_FLAGS = {
    # The highest proof level trustc documents (0 safety, 1 functional,
    # 2 domain). A lower explicit level is refused: the compiled-in default is
    # not measured here, so a lower value could lower it.
    "-Ztrust-verify-level=2",
    # The registered hardened profiles "additionally emit fail-closed hardened
    # boundary verification conditions".
    "-Ztrust-verify-profile=hardened",
    "-Ztrust-verify-profile=unix_hardened",
    "-Ztrust-verify-profile=coreutils_hardened",
    # Widens the verified scope to authenticated dependency MIR.
    "-Ztrust-verify-include-dependencies=yes",
    # A body the producer cannot fully lower becomes a compile error.
    "-Ztrust-ir-lower=strict",
}

# What an explicit policy line in Cargo configuration governs, stated with
# every verdict that involves one. Measured on trustc 321aaeda7 (2026-09-29):
# `targo trust check` ran its `strict lane` with a configured advisory and its
# `advisory lane` under `--allow-l0-gaps` with a configured strict, so the line
# never reaches the verified lane.
POLICY_SCOPE = (
    "an explicit -Ztrust-policy line binds rustup-proxied builds only "
    "(`rustup run trust ...`, trust-analyzer, cargo through the rustup proxy); "
    "`targo trust` ignores it and selects its own lane (strict, or advisory "
    "under --allow-l0-gaps), measured on trustc 321aaeda7"
)


def policy_issues(
    toolchain_text: str,
    config_text: str,
    environment: Optional[dict[str, str]] = None,
    destination: bool = False,
) -> list[str]:
    try:
        channel = toolchain_channel(toolchain_text)
    except ValueError as error:
        return [f"invalid rust-toolchain.toml: {error}"]
    if channel != "trust":
        return []

    strings, normalized, lexical_issues = _toml_strings_and_normalized(config_text)
    issues = list(lexical_issues)
    if RUSTC_OVERRIDE_RE.search(normalized):
        issues.append("verified default cannot use a rustc wrapper or alternate rustc path")
    flags = list(_canonical_trust_flags(strings))
    # DISTINCT values: the same policy repeated for the host, target and
    # rustdoc units (ay's live config) is one policy. Two different values are
    # the ambiguity, whichever units carry them.
    policies = sorted({flag for flag in flags if flag.startswith("-Ztrust-policy")})
    accepted = DESTINATION_POLICIES if destination else (
        DESTINATION_POLICIES | {ADVISORY_RAMP_POLICY}
    )
    if not policies:
        if destination:
            issues.append(
                "a verified trust-channel default must explicitly select a Trust policy "
                f"({', '.join(sorted(accepted))}); {POLICY_SCOPE}"
            )
    elif len(policies) > 1:
        issues.append(
            "multiple distinct Trust policies make the authority claim ambiguous: "
            + ", ".join(policies)
        )
    for policy in policies:
        if policy not in accepted:
            if destination:
                issues.append(f"Trust policy is not strict or certify: {policy}")
            else:
                issues.append(f"unknown Trust policy: {policy}")
    for flag in sorted(set(flags)):
        if flag.startswith("-Ztrust-policy"):
            continue
        if flag == "-Ztrust-verify" or flag.startswith("-Ztrust-verify="):
            if flag != ACTIVATION_ON:
                issues.append(
                    f"at least one host, target, or rustdoc unit disables verification: {flag}"
                )
        elif flag not in AUDITED_STRENGTHENING_FLAGS:
            issues.append(
                f"unaudited Trust flag in a verified default: {flag} (admitted: "
                f"{ACTIVATION_ON}, a Trust policy, "
                + ", ".join(sorted(AUDITED_STRENGTHENING_FLAGS))
                + ")"
            )

    if environment is not None:
        overrides = sorted(key for key in AMBIENT_RUSTC_OVERRIDES if environment.get(key))
        if overrides:
            issues.append(
                "verified default cannot inherit an ambient rustc override: "
                + ", ".join(overrides)
            )
        flag_values = [
            value
            for key, value in environment.items()
            if value
            and (
                key in {"RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_ENCODED_RUSTFLAGS"}
                or (key.startswith("CARGO_") and key.endswith(("_RUSTFLAGS", "_RUSTDOCFLAGS")))
            )
        ]
        if list(_canonical_trust_flags(flag_values)):
            issues.append("verified default cannot inherit ambient Trust compiler flags")
    return issues


def _is_read_only(path: Path) -> bool:
    write_bits = stat.S_IWUSR | stat.S_IWGRP | stat.S_IWOTH
    return path.exists() and path.stat().st_mode & write_bits == 0


def _is_caller_owned(path: Path) -> bool:
    """Only the invoking user (or root) owns and can write ``path``."""
    if not path.exists():
        return False
    info = path.lstat()
    if stat.S_ISLNK(info.st_mode):
        # A link's own mode bits grant nothing (re-pointing it needs write on
        # its directory, which the chain checks) and Linux reports every link
        # as 0777, so only its owner counts.
        return info.st_uid in {os.getuid(), 0}
    foreign_write = stat.S_IWGRP | stat.S_IWOTH
    return info.st_uid in {os.getuid(), 0} and info.st_mode & foreign_write == 0


# More hops than any real install uses; the OS itself gives up near 32-40.
_MAX_LAUNCHER_HOPS = 40


def _launcher_chain(launcher: Path) -> Optional[list[Path]]:
    """Every path the OS walks to reach the file ``launcher`` executes.

    That is the launcher itself, each symlink hop in order, and the fully
    resolved file (which also undoes any symlinked DIRECTORY on the way).
    ``None`` means a symlink loop or a chain too long to trust.
    """
    chain = [launcher]
    current = launcher
    for _ in range(_MAX_LAUNCHER_HOPS):
        if not current.is_symlink():
            break
        target = Path(os.readlink(current))
        current = target if target.is_absolute() else current.parent / target
        chain.append(current)
    else:
        return None
    try:
        final = launcher.resolve(strict=True)
    except (OSError, RuntimeError):
        return None
    if final not in chain:
        chain.append(final)
    return chain


def _replacement_path_issue(path: Path) -> Optional[str]:
    """Check every actual component, including paths introduced by symlinks.

    A trusted sticky directory protects a trusted owner's entry from foreign
    replacement; it does not make a foreign-owned directory or symlink safe.
    Resolve incrementally: normalizing ``..`` first would hide the directory
    the kernel visits, and resolving only the final path would hide link owners
    and lexical ancestors. This is an authority check, not a race-proof handle
    to an executable: the invoking user and root remain trusted mutators.
    """
    absolute = path if path.is_absolute() else Path.cwd() / path
    current = Path(absolute.anchor)
    pending = list(reversed(absolute.parts[1:]))
    trusted = {os.getuid(), 0}
    hops = 0
    try:
        while True:
            parent = current.lstat()
            if not stat.S_ISDIR(parent.st_mode) or parent.st_uid not in trusted:
                return f"directory {current} is not caller-owned"
            if parent.st_mode & 0o022 and not parent.st_mode & stat.S_ISVTX:
                return f"directory {current} is foreign-writable without sticky protection"
            if not pending:
                return None
            component = pending.pop()
            if component == "..":
                current = current.parent
                continue
            candidate = current / component
            info = candidate.lstat()
            if info.st_uid not in trusted:
                return f"path component {candidate} is not caller-owned"
            if stat.S_ISLNK(info.st_mode):
                hops += 1
                if hops > _MAX_LAUNCHER_HOPS:
                    return f"path {path} has too many symlink hops"
                target = Path(os.readlink(candidate))
                after = candidate.lstat()
                if (info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_ctime_ns) != (
                    after.st_dev, after.st_ino, after.st_mode, after.st_uid, after.st_ctime_ns
                ):
                    return f"symlink {candidate} changed during inspection"
                if target.is_absolute():
                    current = Path(target.anchor)
                    parts = target.parts[1:]
                else:
                    parts = target.parts
                pending.extend(reversed(parts))
            elif stat.S_ISDIR(info.st_mode):
                current = candidate
            elif pending or not stat.S_ISREG(info.st_mode) or info.st_mode & 0o022:
                return f"file {candidate} is not a protected regular file"
            else:
                return None
    except (OSError, RuntimeError, ValueError) as error:
        return f"cannot inspect path {path}: {error}"


def _launcher_issue(label: str, launcher: Path) -> Optional[str]:
    """Protect the file and every lexical/resolved replacement ancestor."""
    issue = _replacement_path_issue(launcher)
    if issue is not None:
        return (
            f"the lane's {label} launcher {launcher} is not caller-owned: "
            f"another principal can replace it ({issue})"
        )
    try:
        chain = _launcher_chain(launcher)
    except (OSError, RuntimeError, ValueError):
        chain = None
    if chain is None:
        return (
            f"the lane's {label} launcher {launcher} is a symlink loop or does not "
            "resolve to an existing file"
        )
    for hop in chain:
        issue = _replacement_path_issue(hop)
        if issue is not None:
            return (
                f"the lane's {label} launcher {launcher} is not caller-owned: "
                f"another principal can replace it ({issue})"
            )
    return None


def _tree_issues(root: Path, label: str, *, sealed: bool) -> list[str]:
    """Reject one symlinked or under-protected artifact anywhere below ``root``.

    ``sealed`` (the destination) demands every entry read-only. Otherwise (the
    ramp) every entry must be CALLER-OWNED: no other principal can write it,
    which is the tier ``targo trust`` itself reports for an unsealed launcher.
    """
    guarded = _is_read_only if sealed else _is_caller_owned
    issues = []
    if not guarded(root):
        issues.append(
            f"{label} root retains write bits"
            if sealed
            else f"{label} root is not caller-owned (another principal can write it)"
        )

    first_symlink = None
    first_writable = None
    for directory, dirnames, filenames in os.walk(root, followlinks=False):
        parent = Path(directory)
        for name in list(dirnames):
            candidate = parent / name
            if candidate.is_symlink():
                first_symlink = first_symlink or candidate
                dirnames.remove(name)
            elif not guarded(candidate):
                first_writable = first_writable or candidate
        for name in filenames:
            candidate = parent / name
            if candidate.is_symlink():
                first_symlink = first_symlink or candidate
            elif not guarded(candidate):
                first_writable = first_writable or candidate
    if first_symlink is not None:
        issues.append(f"{label} contains a symlinked artifact: {first_symlink}")
    if first_writable is not None:
        issues.append(
            f"{label} contains a writable artifact: {first_writable}"
            if sealed
            else f"{label} contains an artifact another principal can write: {first_writable}"
        )
    return issues


def _sealed_tree_issues(root: Path) -> list[str]:
    """Reject one mutable or symlinked artifact anywhere below ``root``."""
    return _tree_issues(root, "sealed sysroot", sealed=True)


def _lane_presence_issues(lane: Optional[LaneToolchain]) -> list[str]:
    if lane is None or lane.targo is None:
        return [
            "Trust targo was not found (TRUST_TARGO_BIN, targo on PATH, or rustup's "
            "trust toolchain); the pin cannot be checked against the lane that builds"
        ]
    issues = []
    if not lane.discriminated:
        issues.append(
            f"`{lane.targo} --unverified --version` failed: that is not Trust's targo "
            "(upstream Cargo under the name targo rejects the flag)"
        )
    if (
        lane.rustc is None
        or lane.sysroot is None
        or not lane.sysroot.is_dir()
        or lane.commit_hash is None
        or COMMIT_HASH_RE.fullmatch(lane.commit_hash) is None
    ):
        issues.append(
            "the trustc beside targo did not report an existing sysroot and a "
            "canonical 40-hex commit-hash"
        )
    return issues


def _has_host_std(sysroot: Path, host: str) -> bool:
    return any((sysroot / "lib" / "rustlib" / host / "lib").glob("libstd-*"))


def resolved_issues(resolved: ResolvedToolchain, require_seal: bool = False) -> list[str]:
    """Check what the pin and the Targo lane resolve to.

    The SEALED tier applies at the destination (``require_seal``) and whenever
    ``TRUST_SEALED_SYSROOT`` names a seal: the pin and the lane must both
    resolve to that one read-only ``trust-<commit>`` directory. Otherwise the
    CALLER-OWNED ramp tier applies: both trees protected from every other
    principal, and one compiler identity across them.
    """
    if resolved.resolution_error is not None:
        # One cause, stated once: every per-field check below would fail for
        # it and name a symptom instead.
        return [resolved.resolution_error] + _lane_presence_issues(resolved.lane)
    sealed_tier = require_seal or resolved.sealed_root is not None
    issues = []
    if resolved.rustc is None or not resolved.rustc.is_file() or not os.access(resolved.rustc, os.X_OK):
        issues.append("Trust did not resolve an executable compiler")
    if resolved.sysroot is None or not resolved.sysroot.is_dir():
        issues.append("Trust rustc did not resolve an existing sysroot")
    if not resolved.native and (resolved.rustup_link is None or not resolved.rustup_link.exists()):
        issues.append("rustup Trust toolchain link is missing")
    if sealed_tier and (resolved.sealed_root is None or not resolved.sealed_root.is_dir()):
        issues.append("TRUST_SEALED_SYSROOT does not name an existing directory")
    if resolved.commit_hash is None or COMMIT_HASH_RE.fullmatch(resolved.commit_hash) is None:
        issues.append("Trust rustc did not report a canonical 40-hex commit-hash")
    issues.extend(_lane_presence_issues(resolved.lane))

    if issues:
        return issues

    assert resolved.rustc is not None
    assert resolved.sysroot is not None
    assert resolved.native or resolved.rustup_link is not None
    assert resolved.commit_hash is not None
    assert resolved.lane is not None and resolved.lane.sysroot is not None

    # Protect the spellings before resolve() discards lexical directories and
    # intermediate symlink owners. A read-only tree can still be substituted by
    # renaming a writable ancestor, so this applies to BOTH authority tiers.
    roots = [
        ("pinned rustc", resolved.rustc),
        ("Trust sysroot", resolved.sysroot),
        ("Targo lane sysroot", resolved.lane.sysroot),
    ]
    if resolved.rustup_link is not None:
        roots.append(("rustup Trust toolchain link", resolved.rustup_link))
    if resolved.sealed_root is not None:
        roots.append(("sealed sysroot", resolved.sealed_root))
    for label, path in roots:
        issue = _replacement_path_issue(path)
        if issue is not None:
            issues.append(
                f"{label} path is not protected from replacement "
                f"(another principal can write or replace it): {issue}"
            )
    if issues:
        return issues

    rustc = resolved.rustc.resolve()
    sysroot = resolved.sysroot.resolve()
    linked = (resolved.rustup_link if resolved.rustup_link is not None else resolved.sysroot).resolve()
    lane_sysroot = resolved.lane.sysroot.resolve()

    if any(MUTABLE_BUILD_TREE_RE.search(os.fspath(path)) for path in (linked, sysroot, lane_sysroot)):
        issues.append("Trust toolchain resolves into a mutable x.py build tree (build/<host>/stageN)")
    if linked != sysroot:
        issues.append("rustup Trust toolchain link and the pinned rustc's sysroot do not resolve identically")
    compiler_name = "trustc" if resolved.native else "rustc"
    if rustc != (sysroot / "bin" / compiler_name).resolve():
        issues.append("resolved rustc is not the compiler inside its own sysroot")
    # ONE COMPILER. targo builds with the trustc beside it; rustup's pin serves
    # the proxies (trust-analyzer, `rustup run trust ...`). A pin whose compiler
    # differs from the one the lane runs names nothing the gates measured.
    if resolved.lane.commit_hash != resolved.commit_hash:
        issues.append(
            f"the Targo lane compiles with trustc {resolved.lane.commit_hash} but the "
            f"pin resolves rustc {resolved.commit_hash}: they must be one compiler"
        )
    # The launchers the lane is entered through (on this machine: atpkg shims
    # that exec into the store) sit outside both trees; another principal able
    # to rewrite one could redirect every build without touching a sysroot.
    # A symlinked launcher is followed to the file that actually runs.
    for label, launcher in (("targo", resolved.lane.targo), ("trustc", resolved.lane.rustc)):
        assert launcher is not None
        launcher_issue = _launcher_issue(label, launcher)
        if launcher_issue is not None:
            issues.append(launcher_issue)

    if sealed_tier:
        assert resolved.sealed_root is not None
        sealed = resolved.sealed_root.resolve()
        if resolved.sealed_root.is_symlink():
            issues.append("TRUST_SEALED_SYSROOT itself must be a versioned directory, not a symlink")
        # The seal is named `trust-<prefix of the commit-hash>`, and the prefix
        # is what the producer wrote: trust's `scripts/promote-toolchain.sh`
        # sealed to `trust-${REV:0:8}` (trust-1979a7b8, trust-6500fd4d).
        # Demanding the full 40 hex meant this clause COULD NEVER PASS against
        # a promoted seal.
        #
        # Requiring a PREFIX rather than any name keeps what the clause is for:
        # the directory must still name the commit the compiler reports, so a
        # seal cannot be relabelled to impersonate another revision. And the
        # name was never the load-bearing identity check anyway — the rustup
        # link, `rustc --print sysroot`, the lane's sysroot and
        # TRUST_SEALED_SYSROOT must all resolve to this same directory (below).
        # A minimum length keeps the prefix meaningful rather than accepting
        # bare `trust-`.
        name_prefix = sealed.name.removeprefix("trust-")
        if (
            not sealed.name.startswith("trust-")
            or len(name_prefix) < 8
            or not resolved.commit_hash.startswith(name_prefix)
        ):
            issues.append(
                f"sealed sysroot directory must be named trust-<prefix of "
                f"{resolved.commit_hash}> (at least 8 hex), got {sealed.name}"
            )
        if linked != sealed or sysroot != sealed:
            issues.append("rustup link, rustc sysroot, and TRUST_SEALED_SYSROOT do not resolve identically")
        if lane_sysroot != sealed:
            issues.append("the Targo lane's trustc sysroot is not TRUST_SEALED_SYSROOT")
        issues.extend(_sealed_tree_issues(sealed))
    else:
        issues.extend(_tree_issues(sysroot, "Trust sysroot", sealed=False))
        if lane_sysroot != sysroot:
            issues.extend(_tree_issues(lane_sysroot, "Targo lane sysroot", sealed=False))

    if not resolved.host:
        issues.append("Trust rustc did not report a host triple")
    else:
        for label, root in (("pinned", sysroot), ("Targo lane", lane_sysroot)):
            if not _has_host_std(root, resolved.host):
                issues.append(f"{label} Trust sysroot has no std artifact for the reported host")
    return issues


def behavioral_issues(rustc: Path) -> list[str]:
    """Prove the installed compiler's no-flag defaults with red/green crates."""
    positive = "pub fn identity(x: u64) -> u64 { x }\n"
    refutation = "pub fn divide(x: i32, y: i32) -> i32 { x / y }\n"
    results = {}
    with tempfile.TemporaryDirectory(prefix="trust-default-authority-") as temporary:
        directory = Path(temporary)
        for name, source in (("positive", positive), ("refutation", refutation)):
            source_path = directory / f"{name}.rs"
            source_path.write_text(source, encoding="utf-8")
            command = [
                os.fspath(rustc),
                "--crate-name",
                f"trust_default_{name}",
                "--crate-type",
                "lib",
                "--edition=2021",
                "--emit",
                "metadata",
                "-o",
                os.fspath(directory / f"{name}.rmeta"),
                os.fspath(source_path),
            ]
            try:
                results[name] = subprocess.run(
                    command,
                    cwd=os.fspath(directory),
                    check=False,
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    timeout=60,
                )
            except subprocess.TimeoutExpired:
                return [f"Trust compiler behavioral {name} canary timed out"]

    positive_result = results["positive"]
    negative_result = results["refutation"]
    issues = []
    if positive_result.returncode != 0:
        issues.append("Trust compiler rejected the trivial positive default canary")
    evidence = negative_result.stdout + negative_result.stderr
    refutation_evidence = re.search(r'\b[1-9][0-9]* failed\b|\bFAILED\b|counterexample', evidence)
    if negative_result.returncode == 0:
        issues.append("Trust compiler accepted the deliberate default refutation")
    if "Trust verification:" not in evidence or refutation_evidence is None:
        issues.append("deliberate refutation lacked Trust verification failure evidence")
    return issues


def _run(command: Sequence[str], cwd: Path) -> str:
    completed = subprocess.run(
        command,
        cwd=os.fspath(cwd),
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip()
        raise RuntimeError(f"{' '.join(command)} failed: {detail}")
    return completed.stdout.strip()


def _verbose_field(verbose: str, key: str) -> Optional[str]:
    prefix = f"{key}: "
    for line in verbose.splitlines():
        if line.startswith(prefix):
            return line[len(prefix) :].strip()
    return None


def _rustup_candidates() -> list[Path]:
    """Where rustup is looked for, in order: PATH, then the Cargo home's bin
    (``$CARGO_HOME/bin``, else ``~/.cargo/bin``), which is where rustup-init
    installs it. An agent or CI shell is often spawned without that directory
    on PATH; the pin is resolvable all the same."""
    candidates = []
    found = shutil.which("rustup")
    if found:
        candidates.append(Path(found))
    cargo_home = os.environ.get("CARGO_HOME")
    if cargo_home:
        candidates.append(Path(cargo_home) / "bin" / "rustup")
    candidates.append(Path.home() / ".cargo" / "bin" / "rustup")
    return candidates


def _resolve_rustup() -> Optional[Path]:
    for candidate in _rustup_candidates():
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return candidate
    return None


RUSTUP_NOT_FOUND = (
    "rustup not found (searched PATH, $CARGO_HOME/bin and ~/.cargo/bin): the "
    "trust pin's rustc, sysroot and toolchain link cannot be resolved without it"
)


def _resolve_targo(root: Path) -> Optional[Path]:
    """Mirror scripts/run-targo.sh: TRUST_TARGO_BIN, then PATH, then rustup's
    `trust` toolchain. Never upstream Cargo."""
    explicit = os.environ.get("TRUST_TARGO_BIN")
    if explicit is not None:
        path = Path(explicit)
        if explicit and path.name == "targo" and path.is_file() and os.access(path, os.X_OK):
            return path
        return None
    found = shutil.which("targo")
    if found:
        return Path(found)
    rustup = _resolve_rustup()
    if rustup is None:
        return None
    try:
        return Path(_run([os.fspath(rustup), "which", "--toolchain", "trust", "targo"], root))
    except RuntimeError:
        return None


def resolve_lane(root: Path) -> LaneToolchain:
    """Resolve the compiler the Targo lane runs: the canonical `trustc` beside
    the resolved `targo` (targo's own discovery order puts it first)."""
    targo = _resolve_targo(root)
    if targo is None:
        return LaneToolchain(None, False, None, None, None)
    probe = subprocess.run(
        [os.fspath(targo), "--unverified", "--version"],
        cwd=os.fspath(root),
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    discriminated = probe.returncode == 0
    trustc = targo.parent / "trustc"
    if not trustc.is_file() or not os.access(trustc, os.X_OK):
        return LaneToolchain(targo, discriminated, None, None, None)
    try:
        sysroot = Path(_run([os.fspath(trustc), "--print", "sysroot"], root))
        verbose = _run([os.fspath(trustc), "-Vv"], root)
    except RuntimeError:
        return LaneToolchain(targo, discriminated, trustc, None, None)
    return LaneToolchain(targo, discriminated, trustc, sysroot, _verbose_field(verbose, "commit-hash"))


def resolve_installed(root: Path) -> ResolvedToolchain:
    lane = resolve_lane(root)
    # The compiler that native Targo actually selects is authoritative for a
    # native build. Do not require an unrelated rustup installation or proxy.
    if lane.discriminated and lane.sysroot is not None and lane.commit_hash is not None:
        compiler = lane.sysroot / "bin" / "trustc"
        try:
            frontend = _run([os.fspath(lane.targo), "-Vv"], root)
            frontend_commit = (_verbose_field(frontend, "trust-repo-commit-hash")
                               or _verbose_field(frontend, "commit-hash"))
            if frontend_commit != lane.commit_hash:
                raise RuntimeError("native Targo and its companion do not name one compiler commit")
            sysroot = Path(_run([os.fspath(compiler), "--print", "sysroot"], root))
            verbose = _run([os.fspath(compiler), "-Vv"], root)
        except RuntimeError as error:
            return ResolvedToolchain(
                None, None, None, None, None, None, lane,
                resolution_error=f"native Targo companion could not be resolved: {error}",
                native=True,
            )
        sealed = os.environ.get("TRUST_SEALED_SYSROOT")
        return ResolvedToolchain(
            rustc=compiler, sysroot=sysroot, rustup_link=None,
            sealed_root=Path(sealed) if sealed else None,
            host=_verbose_field(verbose, "host"),
            commit_hash=_verbose_field(verbose, "commit-hash"),
            lane=lane, native=True,
        )
    rustup = _resolve_rustup()
    if rustup is None:
        return ResolvedToolchain(
            None, None, None, None, None, None, lane, resolution_error=RUSTUP_NOT_FOUND
        )
    try:
        rustc = Path(_run([os.fspath(rustup), "which", "--toolchain", "trust", "rustc"], root))
        sysroot = Path(_run([os.fspath(rustc), "--print", "sysroot"], root))
        verbose = _run([os.fspath(rustc), "-Vv"], root)
    except RuntimeError as error:
        return ResolvedToolchain(
            None, None, None, None, None, None, lane,
            resolution_error=f"{rustup} could not resolve the trust toolchain's rustc: {error}",
        )

    rustup_home = Path(os.environ.get("RUSTUP_HOME", os.fspath(Path.home() / ".rustup")))
    sealed = os.environ.get("TRUST_SEALED_SYSROOT")
    return ResolvedToolchain(
        rustc=rustc,
        sysroot=sysroot,
        rustup_link=rustup_home / "toolchains" / "trust",
        sealed_root=Path(sealed) if sealed else None,
        host=_verbose_field(verbose, "host"),
        commit_hash=_verbose_field(verbose, "commit-hash"),
        lane=lane,
    )


def check(root: Path, require_verified_default: bool) -> list[str]:
    toolchain_path = root / "rust-toolchain.toml"
    config_paths = (root / ".cargo" / "config.toml", root / ".cargo" / "config")
    structural_issues = []
    if toolchain_path.is_symlink():
        structural_issues.append("rust-toolchain.toml must not be a symlink")
    existing_configs = [path for path in config_paths if path.exists() or path.is_symlink()]
    if len(existing_configs) > 1:
        structural_issues.append(
            "both .cargo/config.toml and legacy .cargo/config exist; precedence is ambiguous"
        )
    if any(path.is_symlink() for path in existing_configs):
        structural_issues.append("verified Cargo configuration must not be a symlink")
    try:
        toolchain_text = toolchain_path.read_text(encoding="utf-8") if toolchain_path.exists() else ""
        channel = toolchain_channel(toolchain_text)
    except (OSError, ValueError) as error:
        return [f"invalid rust-toolchain.toml: {error}"]
    config_text = "\n".join(
        path.read_text(encoding="utf-8") for path in existing_configs if path.is_file()
    )
    if channel != "trust":
        if require_verified_default:
            return [f"verified default required, but repository channel is {channel or 'unpinned'}"]
        return []
    issues = structural_issues + policy_issues(
        toolchain_text, config_text, dict(os.environ),
        destination=require_verified_default,
    )
    if issues:
        return issues
    resolved = resolve_installed(root)
    issues = resolved_issues(resolved, require_seal=require_verified_default)
    if issues:
        return issues
    assert resolved.rustc is not None
    return behavioral_issues(resolved.rustc)


def configured_policies(root: Path) -> list[str]:
    """The distinct -Ztrust-policy values the repository's Cargo configuration
    names (both spellings of the config file are read, as ``check`` does)."""
    texts = [
        path.read_text(encoding="utf-8")
        for path in (root / ".cargo" / "config.toml", root / ".cargo" / "config")
        if path.is_file()
    ]
    flags = configured_flags("\n".join(texts))
    return sorted({flag for flag in flags if flag.startswith("-Ztrust-policy")})


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--require-verified-default", action="store_true")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    issues = check(root, args.require_verified_default)
    toolchain = root / "rust-toolchain.toml"
    try:
        channel = toolchain_channel(toolchain.read_text(encoding="utf-8")) if toolchain.is_file() else None
    except (OSError, ValueError) as error:
        channel = None
        issue = f"invalid rust-toolchain.toml: {error}"
        if issue not in issues:
            issues.append(issue)
    # Whatever the verdict, a configured policy is reported with its scope, so
    # nobody reads it as the policy a verified (`targo trust`) run obeys.
    policies = configured_policies(root) if channel == "trust" else []
    if policies:
        print(f"NOTE: configured {', '.join(policies)}: {POLICY_SCOPE}.")
    if issues:
        for issue in issues:
            print(f"FAIL: {issue}", file=sys.stderr)
        return 1
    print("PASS: repository default makes no uncertified Trust authority claim")
    if channel == "trust" and not args.require_verified_default:
        sealed = "sealed" if os.environ.get("TRUST_SEALED_SYSROOT") else "caller-owned"
        print(
            f"NOTE: trust pin on the RAMP ({sealed} toolchain, compiler default measured "
            "refutation-fatal); it is not a verified default. Verified results come "
            "from the `targo trust` lane; --require-verified-default is the destination."
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
