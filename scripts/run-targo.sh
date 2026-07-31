#!/usr/bin/env bash
# Resolve and invoke the Trust-owned Targo frontend for internal Rust gates.
# Compilation commands use Targo's explicit compatibility lane. Formatting is
# non-compiling and therefore runs without `--unverified`. There is
# intentionally no fallback to upstream Cargo.
set -euo pipefail

fail() {
    printf 'FAIL: %s\n' "$*" >&2
    exit 2
}

resolve_targo() {
    local candidate=""

    if [[ -n "${TRUST_TARGO_BIN+x}" ]]; then
        [[ -n "$TRUST_TARGO_BIN" ]] || fail "TRUST_TARGO_BIN is empty"
        candidate="$TRUST_TARGO_BIN"
    elif command -v targo >/dev/null 2>&1; then
        candidate="$(command -v targo)"
    elif command -v rustup >/dev/null 2>&1; then
        candidate="$(rustup which --toolchain trust targo 2>/dev/null || true)"
    fi

    [[ -n "$candidate" ]] || fail \
        "Trust targo was not found; set TRUST_TARGO_BIN or install/link the trust toolchain"
    [[ -x "$candidate" ]] || fail "TRUST_TARGO_BIN is not executable: $candidate"
    [[ "${candidate##*/}" == "targo" ]] || fail \
        "TRUST_TARGO_BIN must point to a binary named targo, not ${candidate##*/}"
    printf '%s\n' "$candidate"
}

[[ $# -gt 0 ]] || fail "usage: scripts/run-targo.sh <targo-command> [args...]"

TARGO_BIN="$(resolve_targo)"
command_name="$1"
case "$command_name" in
    fmt)
        exec "$TARGO_BIN" "$@"
        ;;
    bench|build|check|clippy|doc|fix|run|rustc|rustdoc|test)
        exec "$TARGO_BIN" --unverified "$@"
        ;;
    *)
        fail "unsupported internal Targo gate command: $command_name"
        ;;
esac
