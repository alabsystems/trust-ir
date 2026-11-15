#!/usr/bin/env bash
# Resolve and invoke the Trust-owned Targo frontend for internal Rust gates.
# Compilation commands use Targo's explicit compatibility lane. Formatting and
# dependency resolution do not compile and make no verification claim; Targo
# rejects the compilation-only `--unverified` flag for those commands. Lints run
# through `targo tippy` (Trust's clippy), which takes no lane flag. There is
# intentionally no fallback to upstream Cargo: the resolved binary must answer
# `targo --unverified --version`, which upstream Cargo named `targo` rejects.
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
        # A failed resolver's stdout is not an executable selection. Preserve
        # the unavailable diagnostic below, but never execute a printed path
        # from a rustup invocation that itself failed.
        candidate="$(rustup which --toolchain trust targo 2>/dev/null)" || candidate=""
    fi

    [[ -n "$candidate" ]] || fail \
        "Trust targo was not found; set TRUST_TARGO_BIN or install/link the trust toolchain"
    [[ -x "$candidate" ]] || fail "TRUST_TARGO_BIN is not executable: $candidate"
    [[ "${candidate##*/}" == "targo" ]] || fail \
        "TRUST_TARGO_BIN must point to a binary named targo, not ${candidate##*/}"
    "$candidate" --unverified --version >/dev/null 2>&1 || fail \
        "$candidate is not Trust's targo: \`targo --unverified --version\` failed (upstream Cargo under that name rejects the flag)"
    printf '%s\n' "$candidate"
}

[[ $# -gt 0 ]] || fail "usage: scripts/run-targo.sh <targo-command> [args...]"

TARGO_BIN="$(resolve_targo)"
command_name="$1"
case "$command_name" in
    fmt|generate-lockfile|metadata|update)
        exec "$TARGO_BIN" "$@"
        ;;
    clippy|tippy)
        shift
        exec "$TARGO_BIN" tippy "$@"
        ;;
    bench|build|check|doc|fix|run|rustc|rustdoc|test)
        exec "$TARGO_BIN" --unverified "$@"
        ;;
    *)
        fail "unsupported internal Targo gate command: $command_name"
        ;;
esac
