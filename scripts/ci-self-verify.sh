#!/usr/bin/env bash
# Repo-owned self-build/self-verify gate for TrustIr snapshots.
#
# Policy: the core TrustIr format has no required external dependency. The
# default builder graph consumes the Clean kernel through exact, uniform
# clean.git revisions, while the
# non-default `trust-ir-ay` adapter consumes an exact AY revision. This gate
# therefore does not forbid git dependencies outright; it forbids FLOATING
# ones (branch=/tag= without rev=), which would make the verified toolchain
# non-reproducible. `dependency_pin_coherence.rs` separately keeps every Clean
# declaration and the standalone frontend lock on one authority. Rust tests
# and rustdoc examples must execute (or use an explicit bounded opt-in).
# `#[ignore]` and rustdoc `ignore`/`no_run` fences are rejected below.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
TARGO_RUNNER="$ROOT/scripts/run-targo.sh"
# Build parallelism: Targo's default (one job per CPU) unless
# TRUST_IR_TARGO_JOBS caps it (e.g. 1 on a memory-constrained host).
TARGO_JOBS_ARGS=()
if [[ -n "${TRUST_IR_TARGO_JOBS:-}" ]]; then
    if [[ ! "$TRUST_IR_TARGO_JOBS" =~ ^[1-9][0-9]*$ ]]; then
        printf 'TRUST_IR_TARGO_JOBS must be a positive integer, got %q.\n' \
            "$TRUST_IR_TARGO_JOBS" >&2
        exit 2
    fi
    TARGO_JOBS_ARGS=(-j "$TRUST_IR_TARGO_JOBS")
fi

log() {
    printf '\n==> %s\n' "$*"
}

run() {
    log "$*"
    "$@"
}

# Reject git dependencies that are not pinned to an immutable rev. A line like
#   ay = { git = "...", branch = "main" }
# is rejected; pinning with rev = "<sha>" is required for reproducibility.
check_git_deps_are_rev_pinned() {
    log "checking that any git dependencies are rev-pinned (reproducible)"

    local hits
    hits="$(
        find "$ROOT" \
            -path "$ROOT/.git" -prune -o \
            -path "$ROOT/target" -prune -o \
            -name Cargo.toml -print0 |
            xargs -0 awk '
                {
                    line = $0
                    sub(/[[:space:]]*#.*/, "", line)
                    if (line ~ /git[[:space:]]*=/ && line !~ /rev[[:space:]]*=/) {
                        printf "%s:%d:%s\n", FILENAME, FNR, $0
                    }
                }
            '
    )"

    if [[ -n "$hits" ]]; then
        printf 'Found git dependency without a rev pin (non-reproducible):\n%s\n' "$hits" >&2
        printf 'Pin it with rev = "<commit-sha>" instead of branch=/tag=.\n' >&2
        return 1
    fi

    printf 'All git dependencies (if any) are rev-pinned.\n'
}

# Publication must fail closed when a private dependency revision has no
# reviewed public mapping. A direct URL/revision rewrite would create a snapshot
# that looks publishable without proving that either dependency is available at
# the advertised public authority.
#
# Since 2026-09-30 each pin is projected FORWARD onto its dependency's newest
# attested publication, by the publication engine's own rule
# (bin/pub_projection.py project_forward, loaded from its file). The structural
# half below holds the call sites to that shape and exercises the ledger-row
# verifier; publish/test_transforms.py drives forward_mapping's refusals and,
# with the engine present, the whole T1 block against the real projection rule.
check_publish_dependency_mappings_fail_closed() {
    log "checking that publication requires verified Clean and AY mappings"

    python3 - "$ROOT/publish/transforms.sh" <<'PY'
import ast
import pathlib
import re
import sys

path = pathlib.Path(sys.argv[1])
text = path.read_text(encoding="utf-8")
match = re.search(r"<<'PY'\n(.*?)\nPY(?:\n|$)", text, flags=re.DOTALL)
if match is None:
    raise SystemExit("publication mapping gate: transform Python block not found")

tree = ast.parse(match.group(1), filename=str(path))
assignments = {}
functions = {}
for statement in tree.body:
    if isinstance(statement, ast.FunctionDef):
        functions[statement.name] = statement
    if not isinstance(statement, ast.Assign) or len(statement.targets) != 1:
        continue
    target = statement.targets[0]
    if isinstance(target, ast.Name) and target.id in {"clean", "ay", "projection"}:
        assignments[target.id] = statement.value

# Each dependency comes from forward_mapping, fed its own development pin and
# the canonical public authority, and collecting into the shared refusal list.
expected = {
    "clean": ("clean", "clean_dev_rev", "git@github.com:alabsystems/clean.git", "clean_public_url"),
    "ay": ("ay", "ay_dev_rev", "git@github.com:alabsystems/ay.git", "ay_public_url"),
}
for name, (repo, dev_rev, release_url, public_url) in expected.items():
    value = assignments.get(name)
    valid = (
        isinstance(value, ast.Call)
        and isinstance(value.func, ast.Name)
        and value.func.id == "forward_mapping"
        and len(value.args) == 7
        and isinstance(value.args[0], ast.Constant)
        and value.args[0].value == repo
        and isinstance(value.args[1], ast.Name)
        and value.args[1].id == dev_rev
        and isinstance(value.args[2], ast.Constant)
        and value.args[2].value == release_url
        and isinstance(value.args[3], ast.Name)
        and value.args[3].id == public_url
        and isinstance(value.args[6], ast.Name)
        and value.args[6].id == "refusals"
    )
    if not valid:
        raise SystemExit(
            f"publication mapping gate: {name} must come from its forward_mapping projection"
        )


def calls(function, name):
    return any(
        isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == name
        for node in ast.walk(function)
    )


# The projection is the ENGINE's (loaded from its file, never re-implemented
# or searched for on sys.path), the landed-on row is still ledger-verified, and
# any refusal stops T1 before a single file is rewritten.
projection = assignments.get("projection")
loader = functions.get("load_engine_projection")
forward = functions.get("forward_mapping")
if not (
    isinstance(projection, ast.Call)
    and isinstance(projection.func, ast.Name)
    and projection.func.id == "load_engine_projection"
    and loader is not None
    and "pub_projection.py" in ast.unparse(loader)
    and "spec_from_file_location" in ast.unparse(loader)
):
    raise SystemExit(
        "publication mapping gate: T1 must load the engine's bin/pub_projection.py from its file"
    )
if forward is None or not calls(forward, "verified_mapping"):
    raise SystemExit("publication mapping gate: forward_mapping must verify the landed-on ledger row")
positions = {}
for index, statement in enumerate(tree.body):
    source = ast.unparse(statement)
    if isinstance(statement, ast.Assign) and statement.value in (assignments["ay"], assignments["clean"]):
        positions.setdefault("projections", []).append(index)
    elif isinstance(statement, ast.If) and source.startswith("if refusals:") and "SystemExit" in source:
        positions.setdefault("stop", index)
    elif not isinstance(statement, ast.FunctionDef) and ".write_text(" in source:
        positions.setdefault("first_write", index)
if not (
    len(positions.get("projections", [])) == 2
    and "stop" in positions
    and "first_write" in positions
    and max(positions["projections"]) < positions["stop"] < positions["first_write"]
):
    raise SystemExit(
        "publication mapping gate: a forward refusal must stop T1 after both projections "
        "and before the first write"
    )

if re.search(r'["\']verified["\']\s*:\s*False\b', match.group(1)):
    raise SystemExit("publication mapping gate: unverified dependency fallback is forbidden")

# Exercise the transform's actual verifier, not only the two call sites above.
# Otherwise a future permissive fallback inside `verified_mapping` could retain
# the expected AST shape while silently accepting an unattested revision.
required_definitions = {
    "SHA40",
    "SHA256",
    "VERIFIED_AT",
    "REQUIRED_MAPPING_FIELDS",
}
verifier_nodes = []
for statement in tree.body:
    if isinstance(statement, ast.Assign) and any(
        isinstance(target, ast.Name) and target.id in required_definitions
        for target in statement.targets
    ):
        verifier_nodes.append(statement)
    elif isinstance(statement, ast.FunctionDef) and statement.name == "verified_mapping":
        verifier_nodes.append(statement)

if len(verifier_nodes) != len(required_definitions) + 1:
    raise SystemExit("publication mapping gate: verifier definition is incomplete")

namespace = {"re": re, "sys": sys}
module = ast.fix_missing_locations(ast.Module(body=verifier_nodes, type_ignores=[]))
exec(compile(module, filename=str(path), mode="exec"), namespace)
verified_mapping = namespace["verified_mapping"]

dev_rev = "a" * 40
release_url = "git@github.com:alabsystems/clean.git"
public_url = "https://github.com/alabsystems/clean.git"
valid_entry = {
    "release_url": release_url,
    "release_rev": "1" * 40,
    "release_tree": "2" * 40,
    "staging_rev": "3" * 40,
    "export_tree": "2" * 40,
    "engine_sha": "4" * 40,
    "policy_sha": "5" * 64,
    "verified_at": "2026-07-23T00:00:00Z",
}


def expect_rejected(label, ledger):
    namespace["ledger"] = ledger
    try:
        verified_mapping("clean", dev_rev, release_url, public_url)
    except SystemExit:
        return
    raise SystemExit(f"publication mapping gate: verifier accepted {label}")


expect_rejected("a missing mapping", {"schema": 1, "mappings": {}})
expect_rejected(
    "a mapping with missing attestation fields",
    {"schema": 1, "mappings": {"clean": {dev_rev: {"release_url": release_url}}}},
)
expect_rejected(
    "a mapping for the wrong release authority",
    {
        "schema": 1,
        "mappings": {
            "clean": {dev_rev: {**valid_entry, "release_url": "git@example.invalid:clean"}}
        },
    },
)
expect_rejected(
    "a mapping whose release and export trees differ",
    {
        "schema": 1,
        "mappings": {"clean": {dev_rev: {**valid_entry, "export_tree": "6" * 40}}},
    },
)
expect_rejected(
    "a mapping with a malformed attestation digest",
    {
        "schema": 1,
        "mappings": {"clean": {dev_rev: {**valid_entry, "policy_sha": "not-a-digest"}}},
    },
)
expect_rejected(
    "a valid-looking mapping whose development revision is revoked",
    {
        "schema": 1,
        "mappings": {"clean": {dev_rev: valid_entry}},
        "revoked": {
            "clean": {
                dev_rev: {"reason": "test revocation", "revoked_at": "2026-08-13T00:00:00Z"}
            }
        },
    },
)
expect_rejected(
    "a valid-looking mapping beside a malformed revoked ledger",
    {
        "schema": 1,
        "mappings": {"clean": {dev_rev: valid_entry}},
        "revoked": [dev_rev],
    },
)
expect_rejected(
    "a valid-looking mapping beside a malformed per-repository revoked ledger",
    {
        "schema": 1,
        "mappings": {"clean": {dev_rev: valid_entry}},
        "revoked": {"clean": [dev_rev]},
    },
)

namespace["ledger"] = {"schema": 1, "mappings": {"clean": {dev_rev: valid_entry}}}
accepted = verified_mapping("clean", dev_rev, release_url, public_url)
if (
    accepted.get("dev_rev") != dev_rev
    or accepted.get("ledger_release_url") != release_url
    or accepted.get("release_url") != public_url
    or accepted.get("release_rev") != valid_entry["release_rev"]
):
    raise SystemExit("publication mapping gate: verifier corrupted a valid mapping")

# A revocation is per repository and per revision: another revision, or the
# same revision of another repository, being revoked does not refuse this row.
namespace["ledger"] = {
    "schema": 1,
    "mappings": {"clean": {dev_rev: valid_entry}},
    "revoked": {
        "clean": {"b" * 40: {"reason": "test revocation"}},
        "ay": {dev_rev: {"reason": "test revocation"}},
    },
}
if verified_mapping("clean", dev_rev, release_url, public_url).get("dev_rev") != dev_rev:
    raise SystemExit("publication mapping gate: an unrelated revocation refused a live mapping")

print("Clean and AY publication mappings are fail-closed and ledger-verified.")
PY

    # The forward step's behaviour, from the T1 block itself. It needs tomllib,
    # which /usr/bin/python3 (3.9 on a stock Mac) lacks, so pick an interpreter
    # the way publish/transforms.sh does. The end-to-end legs need the
    # publication engine (PUBLICATION_DIR, else the sibling ../publication) and
    # report themselves SKIPPED without it; the forward_mapping legs always run.
    local py=""
    for candidate in python3.14 python3.13 python3.12 python3.11 python3 \
        /opt/homebrew/bin/python3 /usr/local/bin/python3; do
        if command -v "$candidate" >/dev/null 2>&1 &&
           "$candidate" -c 'import tomllib' >/dev/null 2>&1; then
            py="$candidate"
            break
        fi
    done
    if [[ -z "$py" ]]; then
        printf 'publish/test_transforms.py needs Python >= 3.11 (tomllib); none found.\n' >&2
        return 1
    fi
    run "$py" -B "$ROOT/publish/test_transforms.py"
}

check_no_ignored_rust_tests_or_docs() {
    log "checking Rust sources for ignored tests or non-executing rustdoc examples"
    python3 -B "$ROOT/scripts/check_no_ignored_rust.py" --root "$ROOT"
}

maybe_run_lean() {
    if [[ "${TRUST_IR_SKIP_LEAN:-0}" == "1" ]]; then
        log "skipping Lean semantics build because TRUST_IR_SKIP_LEAN=1"
        return 0
    fi

    if command -v lake >/dev/null 2>&1; then
        # The same check as standing gate 14 (`lean-proofs`): the build, the
        # replayed-placeholder scan, the whole-environment axiom census and
        # the kernel replay, stated once in scripts/lean_proofs.py. A bare `lake build` passed a
        # theorem with a placeholder (a warning) and any axiom a theorem off
        # AxiomAudit's curated list depended on.
        log "building and censusing the Lean semantics package"
        python3 -B "$ROOT/scripts/lean_proofs.py" --root "$ROOT" --require
        (cd lean/trust_ir-semantics && lake build TrustIrEval &&
            lake lean TrustIrEval/SignatureAbiTests.lean -- --run)
        return
    fi

    if [[ "${TRUST_IR_REQUIRE_LEAN:-0}" == "1" ]]; then
        printf 'lake was not found, and TRUST_IR_REQUIRE_LEAN=1 was set.\n' >&2
        return 1
    fi

    log "skipping Lean semantics build because lake is not on PATH"
    printf 'Set TRUST_IR_REQUIRE_LEAN=1 to make this a hard failure, or TRUST_IR_SKIP_LEAN=1 to skip explicitly.\n'
}

check_git_deps_are_rev_pinned
check_publish_dependency_mappings_fail_closed
check_no_ignored_rust_tests_or_docs
for dep in clean ay; do
    run python3 -B "$ROOT/scripts/pin_rewrite.py" census --root "$ROOT" --dep "$dep"
done
run python3 -B "$ROOT/scripts/pin_rewrite.py" static-guard --root "$ROOT"
run python3 -B "$ROOT/scripts/wire_alloc.py" --root "$ROOT" check
run python3 -B "$ROOT/scripts/check_enforcement_links.py" --root "$ROOT" check
run bash "$ROOT/scripts/run_script_tests.sh"

# Internal formatting, linting, and compilation all go through the Trust-owned
# Targo frontend. `run-targo.sh` fails closed if canonical Targo is unavailable;
# it never falls back to upstream Cargo.
run "$TARGO_RUNNER" fmt --check --all
# tippy type-checks every target under every feature, so no separate `check`.
run "$TARGO_RUNNER" tippy --locked --workspace --all-targets --all-features \
    ${TARGO_JOBS_ARGS[@]+"${TARGO_JOBS_ARGS[@]}"} -- -D warnings

# Restrict resolution to the selected package. Workspace feature unification
# can re-enable the TV anchor through other members despite --no-default-features.
# Exercise the complete builder library and the nominal/retained/TV boundaries.
# Lint the selected graph's test targets too: all-feature lint cannot see
# helpers and tests compiled only when the TV anchor is disabled.
run "$TARGO_RUNNER" tippy --locked -Zfeature-unification \
    --config 'resolver.feature-unification="selected"' \
    -p trust-ir-build --no-default-features --lib --tests \
    ${TARGO_JOBS_ARGS[@]+"${TARGO_JOBS_ARGS[@]}"} -- -D warnings
run "$TARGO_RUNNER" test --locked -Zfeature-unification \
    --config 'resolver.feature-unification="selected"' \
    -p trust-ir-build --no-default-features \
    --lib --test nominal_level_map --test retained_image \
    --test scoped_codec_without_tv_anchor \
    ${TARGO_JOBS_ARGS[@]+"${TARGO_JOBS_ARGS[@]}"}
# Match the builder's codec-only core graph. Lint its test targets too: the
# default/all-feature graphs enable replay and exclude kernel-less request tests.
run "$TARGO_RUNNER" tippy --locked -Zfeature-unification \
    --config 'resolver.feature-unification="selected"' \
    -p trust-ir --features binary,clean-expr-codec,diff,fmt,parser --lib --tests \
    ${TARGO_JOBS_ARGS[@]+"${TARGO_JOBS_ARGS[@]}"} -- -D warnings
# The nominal text controls are integration tests, so --lib alone excludes them.
run "$TARGO_RUNNER" test --locked -Zfeature-unification \
    --config 'resolver.feature-unification="selected"' \
    -p trust-ir --features binary,clean-expr-codec,diff,fmt,parser \
    --lib --test nominal_text_levels \
    ${TARGO_JOBS_ARGS[@]+"${TARGO_JOBS_ARGS[@]}"}

# Then exercise the default workspace graph. The ay
# adapter is a non-default member with an external git dependency (network or
# credentials for the pinned ay rev); `--workspace` tests it in the same
# feature resolution as everything else instead of a separate `-p` rebuild.
if [[ "${TRUST_IR_SKIP_AY:-0}" == "1" ]]; then
    log "skipping trust-ir-ay adapter tests because TRUST_IR_SKIP_AY=1"
    run "$TARGO_RUNNER" test --locked ${TARGO_JOBS_ARGS[@]+"${TARGO_JOBS_ARGS[@]}"}
else
    run "$TARGO_RUNNER" test --locked --workspace \
        ${TARGO_JOBS_ARGS[@]+"${TARGO_JOBS_ARGS[@]}"}
fi
# Then every feature of the default members (this also runs the CLI's
# `ay`-gated `cli_discharge`, so it fetches the pinned ay rev too).
run "$TARGO_RUNNER" test --locked --all-features ${TARGO_JOBS_ARGS[@]+"${TARGO_JOBS_ARGS[@]}"}

maybe_run_lean

log "self-verify completed"
