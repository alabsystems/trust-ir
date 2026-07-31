#!/usr/bin/env bash
# Repo-owned self-build/self-verify gate for TrustIr snapshots.
#
# Policy: the core TrustIr format has no required external dependency. The
# default builder graph consumes the Clean kernel through exact, uniform
# clean.git revisions (path-patched to the sibling checkout here), while the
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
TARGO_JOBS="${TRUST_IR_TARGO_JOBS:-1}"

if [[ ! "$TARGO_JOBS" =~ ^[1-9][0-9]*$ ]]; then
    printf 'TRUST_IR_TARGO_JOBS must be a positive integer, got %q.\n' \
        "$TARGO_JOBS" >&2
    exit 2
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

# Publication must fail closed when an exact private dependency revision has no
# reviewed public mapping. A direct URL/revision rewrite would create a snapshot
# that looks publishable without proving that either dependency is available at
# the advertised public authority.
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
for statement in tree.body:
    if not isinstance(statement, ast.Assign) or len(statement.targets) != 1:
        continue
    target = statement.targets[0]
    if isinstance(target, ast.Name) and target.id in {"clean", "ay"}:
        assignments[target.id] = statement.value

expected = {
    "clean": ("clean", "clean_dev_rev", "git@github.com:alabsystems/clean.git", "clean_public_url"),
    "ay": ("ay", "ay_dev_rev", "git@github.com:alabsystems/ay.git", "ay_public_url"),
}
for name, (repo, dev_rev, release_url, public_url) in expected.items():
    value = assignments.get(name)
    valid = (
        isinstance(value, ast.Call)
        and isinstance(value.func, ast.Name)
        and value.func.id == "verified_mapping"
        and len(value.args) == 4
        and isinstance(value.args[0], ast.Constant)
        and value.args[0].value == repo
        and isinstance(value.args[1], ast.Name)
        and value.args[1].id == dev_rev
        and isinstance(value.args[2], ast.Constant)
        and value.args[2].value == release_url
        and isinstance(value.args[3], ast.Name)
        and value.args[3].id == public_url
    )
    if not valid:
        raise SystemExit(
            f"publication mapping gate: {name} must come from its exact verified_mapping lookup"
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

namespace["ledger"] = {"schema": 1, "mappings": {"clean": {dev_rev: valid_entry}}}
accepted = verified_mapping("clean", dev_rev, release_url, public_url)
if (
    accepted.get("dev_rev") != dev_rev
    or accepted.get("ledger_release_url") != release_url
    or accepted.get("release_url") != public_url
    or accepted.get("release_rev") != valid_entry["release_rev"]
):
    raise SystemExit("publication mapping gate: verifier corrupted a valid mapping")

print("Clean and AY publication mappings are fail-closed and ledger-verified.")
PY
}

check_no_ignored_rust_tests_or_docs() {
    log "checking Rust sources for ignored tests or non-executing rustdoc examples"
    python3 -B "$ROOT/scripts/check_no_ignored_rust.py" --root "$ROOT"
}

check_lean_proof_placeholders() {
    log "checking Lean sources for proof placeholders or new axioms"

    local lean_root="$ROOT/lean/trust_ir-semantics/TrustIr"
    local placeholders
    placeholders="$(
        find "$lean_root" -name '*.lean' -type f -print0 |
            xargs -0 grep -nHE \
                '(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)' \
                || true
    )"
    if [[ -n "$placeholders" ]]; then
        printf 'Lean proof placeholder(s) are forbidden:\n%s\n' "$placeholders" >&2
        return 1
    fi

    # AYBridge is the one deliberate external soundness boundary. Keep its
    # declaration explicit and reject every additional axiom so an unfinished
    # proof cannot silently expand the trusted base.
    local axioms unexpected=""
    axioms="$(
        find "$lean_root" -name '*.lean' -type f -print0 |
            xargs -0 grep -nHE '^[[:space:]]*axiom[[:space:]]+' || true
    )"
    while IFS=: read -r file line declaration; do
        [[ -z "$file" ]] && continue
        # `IFS=:` consumes the declaration's trailing colon, so match the
        # exact allowlisted name in the post-split field rather than comparing
        # against an impossible colon-suffixed string.
        if [[ "$file" == "$lean_root/Proofs/AYBridge.lean" \
              && "$declaration" =~ ^[[:space:]]*axiom[[:space:]]+ay_sound_unsat[[:space:]]*$ ]]; then
            continue
        fi
        unexpected+="$file:$line:$declaration"$'\n'
    done <<< "$axioms"
    if [[ -n "$unexpected" ]]; then
        printf 'Unexpected Lean axiom declaration(s):\n%s' "$unexpected" >&2
        return 1
    fi

    printf 'Lean sources contain no proof placeholders or unlisted axioms.\n'
}

maybe_run_lean() {
    if [[ "${TRUST_IR_SKIP_LEAN:-0}" == "1" ]]; then
        log "skipping Lean semantics build because TRUST_IR_SKIP_LEAN=1"
        return 0
    fi

    if command -v lake >/dev/null 2>&1; then
        log "building Lean semantics package"
        (cd lean/trust_ir-semantics && lake build)
        return 0
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
check_lean_proof_placeholders
run python3 -B -m unittest discover -s scripts/tests -p 'test_*.py'

# Internal formatting, linting, and compilation all go through the Trust-owned
# Targo frontend. `run-targo.sh` fails closed if canonical Targo is unavailable;
# it never falls back to upstream Cargo.
run "$TARGO_RUNNER" fmt --check --all
run "$TARGO_RUNNER" check --locked --workspace --all-targets --all-features \
    -j "$TARGO_JOBS"
run "$TARGO_RUNNER" clippy --locked --workspace --all-targets --all-features \
    -j "$TARGO_JOBS" -- -D warnings

# Default graph (uses the sibling Clean patch; excludes the AY adapter).
run "$TARGO_RUNNER" test --locked -j "$TARGO_JOBS"
run "$TARGO_RUNNER" test --locked --all-features -j "$TARGO_JOBS"
run "$TARGO_RUNNER" test --locked -p trust-ir-conformance \
    --test conformance -j "$TARGO_JOBS"

# The ay adapter is a non-default member with an external git dependency; test
# it explicitly. Requires network/credentials to fetch the pinned ay rev.
if [[ "${TRUST_IR_SKIP_AY:-0}" == "1" ]]; then
    log "skipping trust-ir-ay adapter tests because TRUST_IR_SKIP_AY=1"
else
    run "$TARGO_RUNNER" test --locked -p trust-ir-ay -j "$TARGO_JOBS"
fi

maybe_run_lean

log "self-verify completed"
