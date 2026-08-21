#!/usr/bin/env bash
# Repo-side standing CI gate runner (Program CK1, trust-ir-side gates).
#
# Gates:
#   1. lean-schema-parity   — the Rust<->Lean name-parity gate
#                             (Targo test -p trust-ir --test lean_schema_parity).
#   2. workspace-build      — Targo build --locked over the workspace default
#                             members. (trust-ir-ay is deliberately NOT a
#                             default member: it carries the only external git
#                             dependency; scripts/ci-self-verify.sh covers it.)
#   3. cli-gate-tests       — Targo test -p trust-ir-cli: the red/green
#                             integration coverage for `validate --lineage`
#                             (closed passes; Trusted rung and mis-threaded
#                             chains fail), `validate --forbid-trusted`
#                             (zero-Trusted passes; Trusted status/evidence
#                             each fail with the item named), and
#                             `validate --forbid-failed` (zero-Failed passes;
#                             a Failed obligation aborts with the item named).
#   4. zero-trusted-census  — `validate --forbid-trusted` demonstrated against
#                             the conformance corpus: green on chc_batch.tmbc
#                             (no Trusted anywhere), red on
#                             proof_annotations.tmbc (10 Trusted obligation
#                             statuses + 1 Trusted evidence certificate — the
#                             census must FIRE and name them).
#   5. lineage-closure      — `validate --lineage` demonstrated red against
#                             chc_batch.tmbc with a current-schema empty sidecar
#                             (no rungs — fail-closed), then green through the
#                             focused CLI integration fixtures in both binary
#                             and JSON sidecar formats. The green fixtures carry
#                             replay-authoritative evidence; a hand-written
#                             certless rung must never be called closed.
#   6. failed-obligation-census — `validate --forbid-failed` (the CK1 WS3-M1
#                             violated-contract build abort) demonstrated
#                             against the conformance corpus: green on
#                             chc_batch.tmbc (no Failed obligation), red on
#                             proof_diagnostics.tmbc (a Failed obligation with
#                             its refutation diagnostics — the census must
#                             FIRE and name it). The Failed rows in that
#                             fixture are also why the gate is a flag, not a
#                             default rejection.
#   7. dependency-pin-coherence — the Clean/AY pin is an atomic move
#                             (both manifests, the AY_REV provenance constant,
#                             the guard's own frozen constants,
#                             frontend/Cargo.lock, and the root Cargo.lock).
#                             The root lock now records both git authorities;
#                             the excluded frontend lock and source provenance
#                             constants still need this dedicated guard. The
#                             bumper separately checks the selected immutable
#                             Clean commit's seven co-owned AY declarations.
#                             Move a pin with scripts/bump-dep-pin.sh, never by hand.
#                             Gate 0 runs the toolchain-free half of the same
#                             invariant (scripts/pin_rewrite.py census).
#   8. wire-format-goldens  — the conformance byte-goldens, i.e. the cross-repo
#                             contract tRust/TrustCg/ty/ay pin against.
#                             `coverage` fires when a new Ty/Inst/
#                             ProofAnnotation variant ships with no fixture in
#                             any of the four formats; `back_compat` holds the
#                             never-regenerated pinned blobs proving the
#                             MIN_READ_VERSION floor still reads. The
#                             native_request_bundle group is deliberately
#                             skipped — 84% of that crate's runtime for its
#                             least structural half; ci-self-verify.sh has it.
#   9. validator-fail-closed — the closed validator holes (notably "Discharged
#                             obligation requires a ground certificate", the
#                             anti-faith-stamp rule) plus the UNTRUSTED
#                             give-back elaborator, whose entire contract is
#                             that it emits Pending and never Certified. Gate 0
#                             clippy only type-checks these; nothing ran them.
#
# Non-zero exit on any gate failure. Cross-machine CI config remains a
# separate open item — this script is the honest repo-side runner.

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FIXTURES="$ROOT/crates/trust-ir-conformance/tests/fixtures"
TARGO_RUNNER="$ROOT/scripts/run-targo.sh"
TARGO_JOBS="${TRUST_IR_TARGO_JOBS:-1}"

if [[ ! "$TARGO_JOBS" =~ ^[1-9][0-9]*$ ]]; then
    printf 'TRUST_IR_TARGO_JOBS must be a positive integer, got %q.\n' \
        "$TARGO_JOBS" >&2
    exit 2
fi

if [[ -n "${CARGO_TARGET_DIR:-}" ]]; then
    case "$CARGO_TARGET_DIR" in
        /*) TARGET_DIR="$CARGO_TARGET_DIR" ;;
        *) TARGET_DIR="$ROOT/$CARGO_TARGET_DIR" ;;
    esac
else
    TARGET_DIR="$ROOT/target"
fi
TRUST_IR_BIN="$TARGET_DIR/debug/trust-ir"

TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT

FAIL_COUNT=0
FAIL_NAMES=""

log() {
    printf '\n==> %s\n' "$*"
}

# gate <name> <command...> — run the command, print PASS/FAIL, record failure.
gate() {
    local name="$1"
    shift
    log "gate $name: $*"
    if "$@"; then
        printf 'PASS: %s\n' "$name"
    else
        printf 'FAIL: %s\n' "$name" >&2
        FAIL_COUNT=$((FAIL_COUNT + 1))
        FAIL_NAMES="$FAIL_NAMES $name"
    fi
}

# Gate 4 (red half): the census must FIRE on proof_annotations.tmbc, which
# carries real Trusted obligation statuses and one Trusted evidence
# certificate. That fixture also fails plain well-formedness (it is a
# serialization-coverage fixture), so a bare non-zero exit proves nothing —
# require the census's own diagnostic to be present.
forbid_trusted_red() {
    local out code
    out="$("$TRUST_IR_BIN" validate --forbid-trusted \
        "$FIXTURES/proof_annotations.tmbc" 2>&1)"
    code=$?
    if [[ $code -ne 0 ]] && grep -q 'trusted census failed' <<<"$out"; then
        grep 'trusted census failed' <<<"$out"
        return 0
    fi
    printf 'expected exit != 0 with "trusted census failed", got exit %d:\n%s\n' \
        "$code" "$out" >&2
    return 1
}

# Gate 6 (red half): the census must FIRE on proof_diagnostics.tmbc, which
# carries a real Failed obligation status plus its refutation diagnostics
# (the module itself is well-formed, so the exit code is attributable to the
# census alone — require its diagnostic all the same, like gate 4).
forbid_failed_red() {
    local out code
    out="$("$TRUST_IR_BIN" validate --forbid-failed \
        "$FIXTURES/proof_diagnostics.tmbc" 2>&1)"
    code=$?
    if [[ $code -ne 0 ]] && grep -q 'failed-obligation census failed' <<<"$out"; then
        grep 'failed-obligation census failed' <<<"$out"
        return 0
    fi
    printf 'expected exit != 0 with "failed-obligation census failed", got exit %d:\n%s\n' \
        "$code" "$out" >&2
    return 1
}

# Gate 5 (red half): an empty manifest has no rungs to walk — the closure
# check must fail closed, not vacuously pass.
lineage_red() {
    local manifest="$TMP_DIR/lineage-empty.json"
    printf '{ "schema_version": 2, "nodes": [], "roots": [] }\n' >"$manifest"
    local out code
    out="$("$TRUST_IR_BIN" validate --lineage "$manifest" \
        "$FIXTURES/chc_batch.tmbc" 2>&1)"
    code=$?
    if [[ $code -ne 0 ]] \
        && grep -q 'lineage check failed' <<<"$out" \
        && grep -q 'manifest has no rungs to walk' <<<"$out" \
        && ! grep -q 'unsupported proof lineage schema' <<<"$out"; then
        grep 'lineage check failed' <<<"$out" | head -2
        return 0
    fi
    printf 'expected exit != 0 with "lineage check failed", got exit %d:\n%s\n' \
        "$code" "$out" >&2
    return 1
}

# Gate 5 (green half): generate a current-schema module plus a genuinely
# replay-authoritative closed lineage through the focused integration fixture,
# then drive the built CLI over both binary and JSON sidecars. Keeping the
# builder in Rust avoids a shell fixture silently becoming a certless faith
# stamp when the authority schema tightens.
lineage_green() {
    if ! "$TARGO_RUNNER" test --locked -p trust-ir-cli --test cli_lineage \
        -j "$TARGO_JOBS" closed_lineage_passes -- --exact; then
        return 1
    fi
    "$TARGO_RUNNER" test --locked -p trust-ir-cli --test cli_lineage \
        -j "$TARGO_JOBS" json_manifest_sidecar_accepted -- --exact
}

# Gate 0 (pin half): the toolchain-free census of every Clean and AY pin leg.
# Gate 7 runs the authoritative Rust guard, but that needs Targo; this needs
# only python3, so on a machine without the trust toolchain it is the ONLY
# thing standing between a hand-edited manifest and a red main. It also names
# the disagreeing file, which the lock-mismatch error from `clippy --locked`
# does not.
pin_census() {
    local dep
    local status=0
    for dep in clean ay; do
        python3 -B "$ROOT/scripts/pin_rewrite.py" census --root "$ROOT" \
            --dep "$dep" || status=1
    done
    if [[ $status -ne 0 ]]; then
        printf 'Repair with: scripts/bump-dep-pin.sh <clean|ay> <40-hex-sha>\n' >&2
    fi
    return $status
}

# --- Gate 0: repository policy and gate-tool regressions --------------------
gate zero-ignored-rust \
    python3 -B "$ROOT/scripts/check_no_ignored_rust.py" --root "$ROOT"
gate dependency-pin-census pin_census
gate internal-gate-tests \
    python3 -B -m unittest discover -s scripts/tests -p 'test_*.py'
gate workspace-format "$TARGO_RUNNER" fmt --check --all
gate workspace-clippy \
    "$TARGO_RUNNER" clippy --locked --workspace --all-targets --all-features \
    -j "$TARGO_JOBS" -- -D warnings

# --- Gate 1: the Rust<->Lean schema parity gate -----------------------------
gate lean-schema-parity \
    "$TARGO_RUNNER" test --locked -p trust-ir --test lean_schema_parity \
    -j "$TARGO_JOBS"

# --- Gate 2: the workspace build (default members) --------------------------
gate workspace-build "$TARGO_RUNNER" build --locked -j "$TARGO_JOBS"

# The remaining gates exercise the trust-ir binary produced by gate 2.
if [[ ! -x "$TRUST_IR_BIN" ]]; then
    printf 'FAIL: %s missing — workspace build did not produce the CLI\n' \
        "$TRUST_IR_BIN" >&2
    FAIL_COUNT=$((FAIL_COUNT + 1))
    FAIL_NAMES="$FAIL_NAMES trust-ir-binary"
else
    # --- Gate 3: red/green integration coverage for both flags --------------
    gate cli-gate-tests \
        "$TARGO_RUNNER" test --locked -p trust-ir-cli -j "$TARGO_JOBS"

    # --- Gate 4: zero-Trusted census on the conformance corpus --------------
    gate zero-trusted-census-green \
        "$TRUST_IR_BIN" validate --forbid-trusted "$FIXTURES/chc_batch.tmbc"
    gate zero-trusted-census-red forbid_trusted_red

    # --- Gate 5: lineage closure against a sidecar manifest -----------------
    gate lineage-closure-red lineage_red
    gate lineage-closure-green lineage_green

    # --- Gate 6: zero-Failed census (violated-contract build abort) ---------
    gate failed-obligation-census-green \
        "$TRUST_IR_BIN" validate --forbid-failed "$FIXTURES/chc_batch.tmbc"
    gate failed-obligation-census-red forbid_failed_red
fi

# The remaining gates do not depend on the CLI binary, so they run
# unconditionally. Executing them last keeps gate numbering equal to execution
# order and puts their diagnostics immediately above the RESULT line.

# --- Gate 7: the Clean/AY dependency-pin coherence guard --------------------
gate dependency-pin-coherence \
    "$TARGO_RUNNER" test --locked -p trust-ir --test dependency_pin_coherence \
    -j "$TARGO_JOBS"

# --- Gate 8: the conformance byte-goldens (cross-repo wire contract) --------
gate wire-format-goldens \
    "$TARGO_RUNNER" test --locked -p trust-ir-conformance -j "$TARGO_JOBS" \
    --test conformance --test back_compat --test build_determinism \
    --test mixed_producer --test module_roundtrip_fuzz \
    --test interpret_differential -- --skip native_request_bundle

# --- Gate 9: validator fail-closed arms + the untrusted give-back elaborator -
gate validator-fail-closed \
    "$TARGO_RUNNER" test --locked -p trust-ir-build -j "$TARGO_JOBS" \
    --test validation_holes --test proof_obligation_source_identity
gate giveback-stays-untrusted \
    "$TARGO_RUNNER" test --locked -p trust-ir-giveback -j "$TARGO_JOBS"

# --- Summary -----------------------------------------------------------------
if [[ $FAIL_COUNT -ne 0 ]]; then
    printf '\nRESULT: FAIL — %d gate(s):%s\n' "$FAIL_COUNT" "$FAIL_NAMES" >&2
    exit 1
fi
printf '\nRESULT: PASS — all gates green\n'
