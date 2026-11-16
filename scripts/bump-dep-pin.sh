#!/usr/bin/env bash
# Move a Clean or AY dependency pin — ATOMICALLY, or not at all.
#
# WHY THIS SCRIPT EXISTS
# ----------------------
# A pin move is not an edit, it is a SIX-leg transaction. Moving fewer than all
# of the legs leaves `main` red, and the failure is structurally invisible to
# the natural verification for a "pure pin bump":
#
#   * Historically the only enforcement was a TEST
#     (dependency_pin_coherence.rs), which `check --workspace` cannot execute.
#     The bumper now mandates an exact Python mirror before treating a missing
#     compile-capable Targo as an honest skip; the Rust test remains the
#     independent compiled check.
#   * `--locked` could not see a Clean move at all while the root [patch]
#     rewrote clean.git to ../clean PATH deps: path deps emit no `source =`
#     row, so the root Cargo.lock was byte-identical across a Clean bump.
#     (Fixed 2026-08-19 — see STALE PRECONDITIONS below.)
#   * frontend/Cargo.lock is a SEPARATE workspace (frontend/ is `exclude`d from
#     the root), so it is invisible to every `--workspace` command.
#
# TARGET-COMMIT AUTHORITY AFTER THE 2026-08-19 PATCH DELETION
# -----------------------------------------------------------
# The workspace root no longer carries
# `[patch."https://github.com/alabsystems/clean.git"]`; cargo now compiles
# clean.git AT THE PINNED REV, and the root Cargo.lock records it. Therefore
# every external Clean check below reads `Cargo.toml` from the immutable target
# commit. A sibling checkout is only an optional local object cache: its HEAD,
# index, and working-tree bytes are deliberately irrelevant.
#
# This script owns only TrustIR's side of the cross-repository transaction.
# The repositories form a hash-addressed SCC, so requiring every repository to
# name every successor commit simultaneously is impossible. Publication uses
# the ratified predecessor-epoch cut: backedges deliberately retain immutable
# predecessor identities while the successor cohort advances, and the final
# epoch receipt records the exact edge set. Do not replace that receipt with a
# raw five-workspace SHA-equality check or chase sibling HEADs; either action
# would recreate the hash cycle this patch deletion cut.
#
# That combination shipped a partial move three times. The legs are enumerated
# machine-readably in scripts/pin_rewrite.py; this script drives them as one
# transaction with an explicit rollback, so a half-applied bump is impossible
# rather than merely detectable.
#
#   scripts/bump-dep-pin.sh clean <40-hex-sha> [--clean-version X.Y.Z]
#   scripts/bump-dep-pin.sh ay    <40-hex-sha> [--ay-version X.Y.Z]
#   scripts/bump-dep-pin.sh clean-ay <clean-sha> <ay-sha> \
#       [--clean-version X.Y.Z] [--ay-version X.Y.Z]
#
# Phases: A preconditions (read-only) -> B stage -> C backup -> D install
#         -> E refresh locks -> F verify. Any failure after D rolls the working
# tree back to exactly what was found, including uncommitted work.
#
# Exit codes: 0 success (or already at the target), 1 refusal/failure
#             (working tree unchanged), 2 usage error.

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

PIN_REWRITE="$ROOT/scripts/pin_rewrite.py"
TARGO_RUNNER="$ROOT/scripts/run-targo.sh"
AUTHORITY="$ROOT/scripts/dependency_authority.py"
AY_PACKAGE_DERIVER="$ROOT/scripts/derive_ay_package_contract.py"
# Local status/object reads must not inherit namespace, replacement, graft,
# template or global config routing. GitHub reads below use native Agh only.
for key in $(compgen -v GIT_); do unset "$key"; done
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 GIT_GRAFT_FILE=/dev/null
export GIT_NO_REPLACE_OBJECTS=1 GIT_NO_LAZY_FETCH=1 GIT_TERMINAL_PROMPT=0

CLEAN_OBJECT_REPO="${TRUST_IR_CLEAN_REPO:-${TRUST_IR_CLEAN_SIBLING:-$ROOT/../clean}}"

usage() {
    cat >&2 <<'USAGE'
usage: scripts/bump-dep-pin.sh <clean|ay> <40-hex-sha> [version] [options]
       scripts/bump-dep-pin.sh clean-ay <clean-sha> <ay-sha> [options]

  clean-ay                move both pins in one atomic transaction. This is
                          required when the target Clean co-owns a new AY pin;
                          neither single-dependency order can be coherent.

  --clean-version X.Y.Z   explicitly review and move every Clean package-
                          version leg. Required when the immutable target
                          Clean commit changes workspace.package.version.
  --ay-version X.Y.Z      explicitly review and move every AY package-version
                          leg. Required when target Clean changes its seven
                          co-owned AY dependency requirements.

  --offline               skip the remote-existence probe (the frontend lock
                          refresh still needs the network for a clean bump)
  --allow-sibling-ahead   deprecated compatibility no-op; immutable target
                          commits, never sibling HEADs, are authoritative
  --no-guard-test         skip the compiled Rust guard test. The toolchain-
                          free mirror still runs and checks every assertion
                          but one: whether frontend/Cargo.lock resolves under
                          --locked, which only the Rust guard asks Cargo
  --dry-run               stage the edits and diff them; change nothing

env:
  TRUST_IR_CLEAN_REPO     optional local Clean object cache. Its HEAD and
                          working tree are never inspected. The deprecated
                          TRUST_IR_CLEAN_SIBLING spelling remains accepted.

Version values are exact canonical package versions, not Cargo ranges: use
`0.2.0`, not `^0.2` or `>=0.2`. The immutable target Clean Cargo.toml must
advertise the same values or the transaction fails before staging.
USAGE
    exit 2
}

DEP=""
REV=""
AY_REV=""
CLEAN_VERSION=""
AY_VERSION=""
OFFLINE=0
ALLOW_SIBLING_AHEAD=0
RUN_GUARD_TEST=1
DRY_RUN=0
AUTHORITY_CLEAN_VERSION=""
AUTHORITY_AY_VERSION=""

[[ $# -ge 2 ]] || usage
DEP="$1"
REV="$2"
if [[ "$DEP" == "clean-ay" ]]; then
    [[ $# -ge 3 ]] || usage
    AY_REV="$3"
    shift 3
else
    shift 2
fi
while [[ $# -gt 0 ]]; do
    case "$1" in
        --clean-version)
            [[ $# -ge 2 ]] || { printf '%s\n' 'missing value for --clean-version' >&2; usage; }
            CLEAN_VERSION="$2"
            shift
            ;;
        --ay-version)
            [[ $# -ge 2 ]] || { printf '%s\n' 'missing value for --ay-version' >&2; usage; }
            AY_VERSION="$2"
            shift
            ;;
        --offline) OFFLINE=1 ;;
        --allow-sibling-ahead) ALLOW_SIBLING_AHEAD=1 ;;
        --no-guard-test) RUN_GUARD_TEST=0 ;;
        --dry-run) DRY_RUN=1 ;;
        -h|--help) usage ;;
        *) printf 'unknown option: %q\n' "$1" >&2; usage ;;
    esac
    shift
done

if [[ "$DEP" == "clean" && -n "$AY_VERSION" ]]; then
    printf '%s\n' 'FAIL: --ay-version is only valid for ay or clean-ay.' >&2
    exit 1
fi
if [[ "$DEP" == "ay" && -n "$CLEAN_VERSION" ]]; then
    printf '%s\n' 'FAIL: --clean-version is only valid for clean or clean-ay.' >&2
    exit 1
fi

SEMVER_RE='^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(-[0-9A-Za-z-]+(\.[0-9A-Za-z-]+)*)?(\+[0-9A-Za-z-]+(\.[0-9A-Za-z-]+)*)?$'
if [[ -n "$CLEAN_VERSION" && ! "$CLEAN_VERSION" =~ $SEMVER_RE ]]; then
    printf 'FAIL: %q is not an exact canonical Clean semantic version (expected X.Y.Z).\n' "$CLEAN_VERSION" >&2
    exit 1
fi
if [[ -n "$AY_VERSION" && ! "$AY_VERSION" =~ $SEMVER_RE ]]; then
    printf 'FAIL: %q is not an exact canonical AY semantic version (expected X.Y.Z).\n' "$AY_VERSION" >&2
    exit 1
fi

case "$DEP" in
    clean) REMOTE="https://github.com/alabsystems/clean.git" ;;
    ay) REMOTE="https://github.com/alabsystems/ay.git" ;;
    clean-ay) REMOTE="https://github.com/alabsystems/clean.git" ;;
    *) printf 'dependency must be clean, ay, or clean-ay, got %q\n' "$DEP" >&2; usage ;;
esac

if [[ ! "$REV" =~ ^[0-9a-f]{40}$ ]]; then
    printf 'FAIL: %q is not a full 40-hex lowercase commit sha.\n' "$REV" >&2
    printf '      Abbreviated revisions cannot be written into a lockfile or\n' >&2
    printf '      compared against the guard constants.\n' >&2
    exit 1
fi

if [[ "$DEP" == "clean-ay" && ! "$AY_REV" =~ ^[0-9a-f]{40}$ ]]; then
    printf 'FAIL: %q is not a full 40-hex lowercase AY commit sha.\n' "$AY_REV" >&2
    exit 1
fi

say() { printf '\n==> %s\n' "$*"; }
warn() { printf 'WARN: %s\n' "$*" >&2; }
die() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }

pin() { python3 -B "$PIN_REWRITE" "$@"; }

review_version_move() {
    local label="$1"
    local current="$2"
    local target="$3"
    local provided="$4"
    local option="$5"

    if [[ -z "$provided" ]]; then
        if [[ "$current" != "$target" ]]; then
            die "target authority changes $label package version from $current to $target.
      Confirm this separate transaction leg explicitly with $option $target.
      No file has been staged or modified."
        fi
        return
    fi
    if [[ "$provided" != "$target" ]]; then
        die "$option $provided disagrees with immutable target authority $target for $label.
      The reviewed value must match the target commit exactly; no file has
      been staged or modified."
    fi
}

clean_manifest_at() {
    local clean_rev="$1"
    if [[ $OFFLINE -eq 1 ]]; then
        python3 -B "$AUTHORITY" offline-manifest "$CLEAN_OBJECT_REPO" "$clean_rev" \
            || die "offline Clean authority check cannot find commit $clean_rev or its readable Cargo.toml in $CLEAN_OBJECT_REPO"
    else
        python3 -B "$AUTHORITY" manifest clean "$clean_rev" \
            || die "native Clean authority read refused"
    fi
}

validate_clean_commit_ay_pin() {
    local clean_rev="$1"
    local target="$2"
    local manifest
    manifest="$(clean_manifest_at "$clean_rev")" \
        || die "cannot read Clean authority commit $clean_rev"

    # Match the URL and rev independently of their order on the line. Fail
    # closed on cardinality: six declarations at the right SHA still means an
    # external transaction leg disappeared.
    local declarations count revisions
    declarations="$(printf '%s\n' "$manifest" | grep 'alabsystems/ay\.git' \
        | grep -o 'rev = "[0-9a-f]\{40\}"' | grep -o '[0-9a-f]\{40\}')"
    count="$(printf '%s\n' "$declarations" \
        | awk 'NF { count += 1 } END { print count + 0 }')"
    revisions="$(printf '%s\n' "$declarations" | awk 'NF' | sort -u)"
    if [[ "$count" -ne 7 ]]; then
        die "found $count ay.git declarations in Clean $clean_rev:Cargo.toml; expected exactly 7.
      A missing or additional declaration means the external leg shape changed,
      not that the sibling agrees. Check the file and update the
      pattern in this script and in
      crates/trust-ir/tests/dependency_pin_coherence.rs together."
    fi
    if [[ "$revisions" != "$target" ]]; then
        die "Clean $clean_rev:Cargo.toml co-owns the AY pin and holds:
$(printf '        %s\n' $revisions)
      expected the exact coordinated AY revision $target. A mismatch would
      put two AY graphs in Cargo.lock, so the transaction is refused."
    fi

    # The same immutable manifest is the semver authority for BOTH halves of
    # the coordinated move. Parse TOML rather than grepping version strings:
    # comments and unrelated dependencies must never satisfy an authority leg.
    local manifest_file="$TMP/clean-authority-${clean_rev}.toml"
    local authority
    printf '%s\n' "$manifest" >"$manifest_file" \
        || die "cannot materialize Clean authority manifest for validation"
    authority="$(pin clean-authority --manifest "$manifest_file" --ay-revision "$target")" \
        || die "Clean $clean_rev package-version authority is invalid"
    AUTHORITY_CLEAN_VERSION="$(printf '%s\n' "$authority" | sed -n 's/^clean=//p')"
    AUTHORITY_AY_VERSION="$(printf '%s\n' "$authority" | sed -n 's/^ay=//p')"
    [[ -n "$AUTHORITY_CLEAN_VERSION" && -n "$AUTHORITY_AY_VERSION" ]] \
        || die "Clean $clean_rev authority did not yield one Clean and one AY package version"
}

TMP="$(mktemp -d)"
STAGE="$TMP/stage"
BACKUP="$TMP/backup"
mkdir -p "$STAGE" "$BACKUP"

INSTALLED=0
SUCCESS=0

ROLLED_BACK=0

rollback() {
    # Idempotent: a signal handler and the EXIT trap can both reach here, and a
    # second pass would run after `cleanup` has already `rm -rf`'d the backup —
    # restoring nothing while printing success.
    if [[ $ROLLED_BACK -eq 1 ]]; then
        return 0
    fi
    ROLLED_BACK=1
    if [[ ! -d "$BACKUP" ]]; then
        printf '\nROLLBACK IMPOSSIBLE — the backup at %s is gone. The working tree may be PARTIALLY MODIFIED; inspect `git status` before doing anything else.\n' \
            "$BACKUP" >&2
        return 1
    fi
    local relative failed=0
    while IFS= read -r relative; do
        [[ -n "$relative" ]] || continue
        # VERIFY the restore instead of asserting it: the success line below is
        # a factual claim about the tree, so every copy that fails must
        # downgrade it.
        if ! cp -p "$BACKUP/$relative" "$ROOT/$relative"; then
            printf 'ROLLBACK FAILED to restore %s\n' "$relative" >&2
            failed=1
        fi
    done < <(cd "$BACKUP" && find . -type f | sed 's|^\./||')
    if [[ $failed -eq 1 ]]; then
        printf '\nROLLBACK INCOMPLETE — the working tree is NOT guaranteed unchanged. Inspect `git status`/`git diff` before re-running.\n' >&2
        return 1
    fi
    printf '\nROLLED BACK — working tree unchanged.\n' >&2
    return 0
}

cleanup() {
    if [[ $INSTALLED -eq 1 && $SUCCESS -ne 1 ]]; then
        rollback || true
    fi
    rm -rf "$TMP"
}

# EXIT alone would let a signal fall through and resume the script body: the
# handler would roll back, `cleanup` would delete TMP, execution would continue
# to the next command, fail, and roll back a SECOND time against a deleted
# backup. Re-raise so the shell dies at the signal.
trap 'cleanup' EXIT
trap 'trap - EXIT; cleanup; trap - INT; kill -INT $$' INT
trap 'trap - EXIT; cleanup; trap - TERM; kill -TERM $$' TERM

# --- PHASE A: preconditions (read-only; nothing is written) ------------------
say "PHASE A — preconditions for $DEP -> $REV"
pin integrity --root "$ROOT" \
    || die "pin input integrity failed; refusing before staging"

REPAIR=0
ALREADY_COHERENT=0
CURRENT_CLEAN_VERSION=""
CURRENT_AY_VERSION=""
CURRENT_VERSION=""
if [[ "$DEP" == "clean-ay" ]]; then
    CLEAN_CENSUS_OUT="$(pin census --root "$ROOT" --dep clean 2>&1)"
    CLEAN_CENSUS_CODE=$?
    printf '%s\n' "$CLEAN_CENSUS_OUT"
    AY_CENSUS_OUT="$(pin census --root "$ROOT" --dep ay 2>&1)"
    AY_CENSUS_CODE=$?
    printf '%s\n' "$AY_CENSUS_OUT"

    if grep -q '!!' <<<"$CLEAN_CENSUS_OUT" || grep -q '!!' <<<"$AY_CENSUS_OUT"; then
        die "a Clean or AY pin leg no longer matches its declared shape (the '!!' rows above).
      Update the leg table in scripts/pin_rewrite.py and the matching
      inventory assertions in crates/trust-ir/tests/dependency_pin_coherence.rs
      together, then re-run."
    fi

    CURRENT_CLEAN_VERSION="$(pin version-current --root "$ROOT" --dep clean 2>/dev/null)" \
        || CURRENT_CLEAN_VERSION="<split>"
    CURRENT_AY_VERSION="$(pin version-current --root "$ROOT" --dep ay 2>/dev/null)" \
        || CURRENT_AY_VERSION="<split>"

    if [[ $CLEAN_CENSUS_CODE -ne 0 || $AY_CENSUS_CODE -ne 0 ]]; then
        REPAIR=1
        printf '\nREPAIR MODE: at least one coordinated pin is currently SPLIT.\n'
        printf '             Every Clean leg moves to %s and every AY leg to %s.\n' "$REV" "$AY_REV"
    else
        CURRENT_CLEAN="$(pin current --root "$ROOT" --dep clean)" \
            || die "cannot determine the current Clean revision"
        CURRENT_AY="$(pin current --root "$ROOT" --dep ay)" \
            || die "cannot determine the current AY revision"
        if [[ "$CURRENT_CLEAN" == "$REV" && "$CURRENT_AY" == "$AY_REV" ]]; then
            ALREADY_COHERENT=1
        else
            printf '\nmoving Clean: %s -> %s\n' "$CURRENT_CLEAN" "$REV"
            printf 'moving AY:    %s -> %s\n' "$CURRENT_AY" "$AY_REV"
        fi
    fi
else
    CENSUS_OUT="$(pin census --root "$ROOT" --dep "$DEP" 2>&1)"
    CENSUS_CODE=$?
    printf '%s\n' "$CENSUS_OUT"

    # A count/shape violation means a leg's DECLARATION drifted (a manifest was
    # reformatted, a constant renamed, a fourth clean-* dependency added). The
    # anchored rewrite would silently miss it, so refuse rather than half-apply.
    if grep -q '!!' <<<"$CENSUS_OUT"; then
        die "a pin leg no longer matches its declared shape (the '!!' rows above).
      Update the leg table in scripts/pin_rewrite.py and the matching
      inventory assertions in crates/trust-ir/tests/dependency_pin_coherence.rs
      together, then re-run."
    fi

    CURRENT_VERSION="$(pin version-current --root "$ROOT" --dep "$DEP" 2>/dev/null)" \
        || CURRENT_VERSION="<split>"

    if [[ $CENSUS_CODE -ne 0 ]]; then
        # The pin is SPLIT across revisions — i.e. someone already hand-edited a
        # subset of the legs. That is the recurring failure itself, so it is a
        # supported input: rewrite every leg to the target and refresh the locks.
        REPAIR=1
        printf '\nREPAIR MODE: the %s pin is currently SPLIT across revisions.\n' "$DEP"
        printf '             Every leg above will be moved to %s.\n' "$REV"
    else
        CURRENT="$(pin current --root "$ROOT" --dep "$DEP")" \
            || die "cannot determine the current $DEP revision"
        if [[ "$CURRENT" == "$REV" ]]; then
            # DEFERRED, NOT AN EARLY EXIT. Returning here would skip PHASE A.2 —
            # and A.2 owns the one leg that lives OUTSIDE this repository.
            ALREADY_COHERENT=1
        else
            printf '\nmoving %s: %s -> %s\n' "$DEP" "$CURRENT" "$REV"
        fi
    fi
fi

if [[ "$DEP" == "clean-ay" ]]; then
    CONTROLLED_LEGS="$(printf '%s\n%s\n%s\n%s\n' \
        "$(pin legs --root "$ROOT" --dep clean)" \
        "$(pin legs --root "$ROOT" --dep ay)" \
        "$(pin version-legs --root "$ROOT" --dep clean)" \
        "$(pin version-legs --root "$ROOT" --dep ay)" | sort -u)"
else
    CONTROLLED_LEGS="$(printf '%s\n%s\n' \
        "$(pin legs --root "$ROOT" --dep "$DEP")" \
        "$(pin version-legs --root "$ROOT" --dep "$DEP")" | sort -u)"
fi
# Even a Clean-only move can change the set of resolved AY packages. Preserve
# the derived contract in that transaction's rollback boundary as well.
CONTROLLED_LEGS="$(printf '%s\ndata/ay_package_versions.json\n' "$CONTROLLED_LEGS" | sort -u)"
DIRTY="$(git -C "$ROOT" status --porcelain -- $CONTROLLED_LEGS 2>/dev/null)"
if [[ -n "$DIRTY" ]]; then
    warn "pin legs have uncommitted changes:
$DIRTY
      Proceeding — the backup is taken from the WORKING TREE, so a rollback
      restores these edits rather than discarding them."
fi

# A.2 — dependency-specific authority checks. Clean co-owns the AY pin, but
# the authority is the immutable Clean commit selected by the transaction (or
# the currently frozen Clean commit for an AY-only move). Never inspect an
# ambient sibling HEAD or working tree: neither is compiled after the path
# patch was removed, and making it authoritative recreates the SCC pin cycle.
if [[ "$DEP" == "clean" || "$DEP" == "clean-ay" ]]; then
    if [[ "$DEP" == "clean-ay" ]]; then
        # The target Clean already co-owns the target AY pin. Validate that
        # external leg before installing either half of the coordinated move.
        validate_clean_commit_ay_pin "$REV" "$AY_REV"
    else
        # A Clean-only transaction is sound only when the target Clean retains
        # TrustIR's current AY authority. If the target commit co-owns a new
        # AY revision, refreshing Cargo.lock here would resolve a split graph
        # before the single-dependency census has any chance to notice it.
        FROZEN_AY_REV="$(pin current --root "$ROOT" --dep ay)" \
            || die "cannot determine the frozen AY revision before the Clean bump"
        validate_clean_commit_ay_pin "$REV" "$FROZEN_AY_REV"
    fi

else
    # An AY-only move must agree with the exact frozen Clean commit advertised
    # by TrustIR. This reads commit content, not an ambient checkout.
    FROZEN_CLEAN_REV="$(pin current --root "$ROOT" --dep clean)" \
        || die "cannot determine the frozen Clean revision before the AY bump"
    # AY leg 6: the frozen Clean commit's Cargo.toml pins AY too.
    validate_clean_commit_ay_pin "$FROZEN_CLEAN_REV" "$REV"
fi

# A.2.1 — package versions are explicit, reviewed transaction legs. The
# immutable Clean manifest supplies both expected values. An omitted option is
# accepted only when that value is unchanged; a real semver move must be named
# on the command line so a revision bump cannot silently broaden dependency
# resolution.
if [[ "$DEP" == "clean-ay" ]]; then
    review_version_move Clean "$CURRENT_CLEAN_VERSION" \
        "$AUTHORITY_CLEAN_VERSION" "$CLEAN_VERSION" --clean-version
    review_version_move AY "$CURRENT_AY_VERSION" \
        "$AUTHORITY_AY_VERSION" "$AY_VERSION" --ay-version
    if [[ "$CURRENT_CLEAN_VERSION" != "$AUTHORITY_CLEAN_VERSION" || \
          "$CURRENT_AY_VERSION" != "$AUTHORITY_AY_VERSION" ]]; then
        ALREADY_COHERENT=0
        printf 'moving Clean package version: %s -> %s\n' \
            "$CURRENT_CLEAN_VERSION" "$AUTHORITY_CLEAN_VERSION"
        printf 'moving AY package version:    %s -> %s\n' \
            "$CURRENT_AY_VERSION" "$AUTHORITY_AY_VERSION"
    fi
elif [[ "$DEP" == "clean" ]]; then
    FROZEN_AY_VERSION="$(pin version-current --root "$ROOT" --dep ay)" \
        || die "cannot determine the frozen AY package version before the Clean bump"
    if [[ "$AUTHORITY_AY_VERSION" != "$FROZEN_AY_VERSION" ]]; then
        die "target Clean changes its co-owned AY package version from $FROZEN_AY_VERSION to $AUTHORITY_AY_VERSION.
      Use clean-ay with both revisions and both reviewed version options."
    fi
    review_version_move Clean "$CURRENT_VERSION" \
        "$AUTHORITY_CLEAN_VERSION" "$CLEAN_VERSION" --clean-version
    if [[ "$CURRENT_VERSION" != "$AUTHORITY_CLEAN_VERSION" ]]; then
        ALREADY_COHERENT=0
        printf 'moving Clean package version: %s -> %s\n' \
            "$CURRENT_VERSION" "$AUTHORITY_CLEAN_VERSION"
    fi
else
    FROZEN_CLEAN_VERSION="$(pin version-current --root "$ROOT" --dep clean)" \
        || die "cannot determine the frozen Clean package version before the AY bump"
    if [[ "$AUTHORITY_CLEAN_VERSION" != "$FROZEN_CLEAN_VERSION" ]]; then
        die "frozen Clean authority advertises package version $AUTHORITY_CLEAN_VERSION but TrustIR holds $FROZEN_CLEAN_VERSION.
      Repair the Clean authority before moving AY."
    fi
    review_version_move AY "$CURRENT_VERSION" \
        "$AUTHORITY_AY_VERSION" "$AY_VERSION" --ay-version
    if [[ "$CURRENT_VERSION" != "$AUTHORITY_AY_VERSION" ]]; then
        ALREADY_COHERENT=0
        printf 'moving AY package version: %s -> %s\n' \
            "$CURRENT_VERSION" "$AUTHORITY_AY_VERSION"
    fi
fi

if [[ $ALLOW_SIBLING_AHEAD -eq 1 ]]; then
    warn "--allow-sibling-ahead is deprecated and ignored; immutable Clean commit content is authoritative"
fi

# A.3 — the revision must exist on the remote, or downstream git consumers
# (trust, ty, trust-cg) cannot resolve what we just advertised.
if [[ $OFFLINE -eq 1 ]]; then
    warn "--offline: skipping the remote-existence probe. A revision that is
      local-only will resolve here and fail for every downstream consumer."
else
    if [[ "$DEP" == "ay" ]]; then REMOTE_REPO=ay; else REMOTE_REPO=clean; fi
    python3 -B "$AUTHORITY" remote "$REMOTE_REPO" "$REV" \
        || die "native dependency authority does not serve $REV"
    printf 'remote %s serves %s\n' "$REMOTE" "$REV"
    if [[ "$DEP" == "clean-ay" ]]; then
        python3 -B "$AUTHORITY" remote ay "$AY_REV" \
            || die "native AY authority does not serve $AY_REV"
        printf 'remote AY serves %s\n' "$AY_REV"
    fi
fi

# The deferred no-op return (see PHASE A). Reached only after EVERY
# precondition above has passed, so "nothing to do" now means the in-repo legs
# AND the external ones (Clean commit AY co-ownership, remote
# reachability) were all confirmed — not merely that the in-repo legs agree
# with each other.
if [[ $ALREADY_COHERENT -eq 1 ]]; then
    pin static-guard --root "$ROOT" \
        || die "the exact static dependency-pin guard rejected the no-op tree"
    if [[ "$DEP" == "clean-ay" ]]; then
        printf '\nalready at Clean %s + AY %s; all legs coherent and every precondition verified — nothing to do.\n' "$REV" "$AY_REV"
    else
        printf '\nalready at %s; all legs coherent and every precondition verified — nothing to do.\n' "$REV"
    fi
    SUCCESS=1
    exit 0
fi

# --- PHASE B: stage the rewrites (still nothing installed) -------------------
say "PHASE B — staging rewrites under $STAGE"
if [[ "$DEP" == "clean-ay" ]]; then
    VERSION_ARGS=()
    if [[ -n "$CLEAN_VERSION" ]]; then
        VERSION_ARGS+=(--clean-version-to "$CLEAN_VERSION")
    fi
    if [[ -n "$AY_VERSION" ]]; then
        VERSION_ARGS+=(--ay-version-to "$AY_VERSION")
    fi
    STAGED="$(pin apply-clean-ay --root "$ROOT" --clean-to "$REV" \
        --ay-to "$AY_REV" ${VERSION_ARGS[@]+"${VERSION_ARGS[@]}"} \
        --stage-dir "$STAGE")" \
        || die "coordinated staging failed; the working tree was not touched"
else
    VERSION_ARGS=()
    if [[ "$DEP" == "clean" && -n "$CLEAN_VERSION" ]]; then
        VERSION_ARGS+=(--version-to "$CLEAN_VERSION")
    elif [[ "$DEP" == "ay" && -n "$AY_VERSION" ]]; then
        VERSION_ARGS+=(--version-to "$AY_VERSION")
    fi
    STAGED="$(pin apply --root "$ROOT" --dep "$DEP" --to "$REV" \
        ${VERSION_ARGS[@]+"${VERSION_ARGS[@]}"} --stage-dir "$STAGE")" \
        || die "staging failed; the working tree was not touched"
fi
printf '%s\n' "$STAGED"

if [[ $DRY_RUN -eq 1 ]]; then
    say "--dry-run — staged vs working tree"
    while IFS= read -r relative; do
        [[ -n "$relative" ]] || continue
        diff -u "$ROOT/$relative" "$STAGE/$relative" \
            --label "a/$relative" --label "b/$relative"
    done <<<"$STAGED"
    printf '\nDRY RUN — nothing installed, no locks refreshed.\n'
    SUCCESS=1
    exit 0
fi

# --- PHASE C: back up every file the transaction can touch -------------------
say "PHASE C — backing up the legs and both lockfiles"
BACKUP_LIST="$CONTROLLED_LEGS
Cargo.lock
frontend/Cargo.lock"
while IFS= read -r relative; do
    [[ -n "$relative" ]] || continue
    [[ -f "$ROOT/$relative" ]] || continue
    mkdir -p "$BACKUP/$(dirname "$relative")"
    cp -p "$ROOT/$relative" "$BACKUP/$relative" \
        || die "cannot back up $relative; refusing to proceed"
done <<<"$(printf '%s\n' "$BACKUP_LIST" | sort -u)"

# --- PHASE D: install ---------------------------------------------------------
say "PHASE D — installing the staged legs"
INSTALLED=1
while IFS= read -r relative; do
    [[ -n "$relative" ]] || continue
    cp "$STAGE/$relative" "$ROOT/$relative" \
        || die "cannot install $relative"
    printf 'installed %s\n' "$relative"
done <<<"$STAGED"

# --- PHASE E: refresh the lockfiles ------------------------------------------
# The root lock is refreshed for BOTH dependencies. Since the path patch was
# removed it records the selected Clean revision and Clean's dependency graph.
# Resolve through the same explicitly selected Trust-owned frontend as the
# compiled guard. These commands do not compile or establish verification;
# run-targo deliberately omits the compilation-only --unverified flag here.
say "PHASE E — refreshing lockfiles"
"$TARGO_RUNNER" metadata --format-version 1 --all-features \
    --manifest-path "$ROOT/Cargo.toml" >"$TMP/root-metadata.json" \
    || die "root lock refresh failed (Targo metadata)"
printf 'refreshed Cargo.lock\n'

if [[ "$DEP" == "clean" || "$DEP" == "clean-ay" ]]; then
    # THE LEG THAT KEEPS GETTING MISSED. frontend/ is a separate, workspace-
    # excluded package with no [patch], so this lock records the git revision
    # literally — and no --workspace command will ever touch it.
    # The frontend is a different workspace, so Targo must select that
    # workspace's managed target rather than inherit the root's explicit
    # build-cache owner. Keep the caller's selection for the compiled guard.
    # Normal resolution moves the exact Git revision already in the manifest
    # while preserving unrelated locked registry versions; update -p would
    # unnecessarily unlock the transitive registry graph.
    (
        unset CARGO_TARGET_DIR
        "$TARGO_RUNNER" metadata --format-version 1 \
            --manifest-path "$ROOT/frontend/Cargo.toml" >/dev/null
    ) \
        || die "frontend/Cargo.lock refresh failed (Targo metadata)"
    printf 'refreshed frontend/Cargo.lock\n'
fi

# Cargo locates packages; immutable authenticated manifests authorize their
# individual versions. Never infer vendored package versions from AY's root.
case "$DEP" in
    ay) CONTRACT_AY_REV="$REV" ;;
    clean-ay) CONTRACT_AY_REV="$AY_REV" ;;
    clean) CONTRACT_AY_REV="$FROZEN_AY_REV" ;;
esac
CONTRACT_AY_VERSION="$(pin version-current --root "$ROOT" --dep ay)" \
    || die "cannot determine the installed AY workspace version"
python3 "$AY_PACKAGE_DERIVER" --metadata "$TMP/root-metadata.json" \
    --revision "$CONTRACT_AY_REV" --workspace-version "$CONTRACT_AY_VERSION" \
    --output "$ROOT/data/ay_package_versions.json" \
    || die "immutable AY package contract derivation failed"

# --- PHASE F: verify ----------------------------------------------------------
say "PHASE F — verification"

# Tier 1 (MANDATORY, no Rust toolchain required): every leg agrees on the new
# revision, then an exact Python mirror replays every runtime assertion in the
# compiled dependency_pin_coherence guard (manifest selectors, provenance,
# versions/cardinality, root patch exclusion, and both lockfiles) except one:
# whether frontend/Cargo.lock still RESOLVES under --locked is Cargo's
# resolver's answer, so only Tier 2 (and Phase E's refresh) asks it.
if [[ "$DEP" == "clean-ay" ]]; then
    pin census --root "$ROOT" --dep clean \
        || die "post-bump Clean census is still incoherent — see the table above"
    pin census --root "$ROOT" --dep ay \
        || die "post-bump AY census is still incoherent — see the table above"
else
    pin census --root "$ROOT" --dep "$DEP" \
        || die "post-bump census is still incoherent — see the table above"
fi
pin static-guard --root "$ROOT" \
    || die "the exact static dependency-pin guard FAILED after the bump"

if [[ $REPAIR -eq 0 ]]; then
    if [[ "$DEP" == "clean-ay" ]]; then
        for OLD_NEW_REV in "$CURRENT_CLEAN $REV" "$CURRENT_AY $AY_REV"; do
            read -r OLD_REV NEW_REV <<<"$OLD_NEW_REV"
            # A coordinated transaction can move only one authority (for
            # example, a new Clean commit that retains the exact AY pin).
            # In that case the unchanged revision is still authoritative, so
            # every controlled occurrence is expected rather than stale.
            [[ "$OLD_REV" == "$NEW_REV" ]] && continue
            STALE="$(git -C "$ROOT" grep -l -F -e "$OLD_REV" -- . ':!*.lock' 2>/dev/null)"
            if [[ -n "$STALE" ]]; then
                warn "the previous revision $OLD_REV still appears in:
$(printf '        %s\n' $STALE)
      Those are not controlled pin legs (docs, ledgers, fixtures). Review
      whether any should move."
            fi
        done
    else
        STALE="$(git -C "$ROOT" grep -l -F -e "$CURRENT" -- . ':!*.lock' 2>/dev/null)"
        if [[ -n "$STALE" ]]; then
            warn "the previous revision $CURRENT still appears in:
$(printf '        %s\n' $STALE)
      Those are not pin legs (docs, ledgers, fixtures). Review whether any
      should move."
        fi
    fi
fi

# Tier 2 (BEST-EFFORT): the Rust guard itself. Routed through run-targo.sh like
# every other Rust gate — never bare upstream Cargo.
if [[ $RUN_GUARD_TEST -eq 1 ]]; then
    GUARD_OUT="$("$TARGO_RUNNER" test --locked -p trust-ir \
        --test dependency_pin_coherence 2>&1)"
    GUARD_CODE=$?
    if [[ $GUARD_CODE -eq 0 ]]; then
        printf '%s\n' "$GUARD_OUT"
        printf 'VERIFY: guard test PASSED\n'
    elif grep -q 'Trust targo was not found' <<<"$GUARD_OUT"; then
        printf 'VERIFY: compiled guard SKIPPED (targo unavailable) — the exact\n'
        printf '        static mirror passed. Run the compiled gate before pushing.\n'
    else
        printf '%s\n' "$GUARD_OUT" >&2
        die "the coherence guard test FAILED after the bump"
    fi
else
    printf 'VERIFY: guard test skipped (--no-guard-test)\n'
fi

if [[ "$DEP" == "clean-ay" ]]; then
    say "DONE — Clean pinned at $REV and AY at $AY_REV across every leg"
else
    say "DONE — $DEP pinned at $REV across every leg"
fi
printf 'Review with: git diff --stat\n'
SUCCESS=1
