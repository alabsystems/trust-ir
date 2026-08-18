#!/usr/bin/env bash
# Move a Clean or AY dependency pin — ATOMICALLY, or not at all.
#
# WHY THIS SCRIPT EXISTS
# ----------------------
# A pin move is not an edit, it is a SIX-leg transaction. Moving fewer than all
# of the legs leaves `main` red, and the failure is structurally invisible to
# the natural verification for a "pure pin bump":
#
#   * The only enforcement is a TEST (dependency_pin_coherence.rs). A bumper who
#     verifies with `check --workspace` cannot see it — no compile step reads
#     the guard's frozen constants.
#   * `--locked` cannot see a Clean move at all. The root [patch] rewrites
#     clean.git to ../clean PATH deps, and path deps emit no `source =` row, so
#     the root Cargo.lock is byte-identical across a Clean bump.
#   * frontend/Cargo.lock is a SEPARATE workspace (frontend/ is `exclude`d from
#     the root), so it is invisible to every `--workspace` command.
#
# That combination shipped a partial move three times. The legs are enumerated
# machine-readably in scripts/pin_rewrite.py; this script drives them as one
# transaction with an explicit rollback, so a half-applied bump is impossible
# rather than merely detectable.
#
#   scripts/bump-dep-pin.sh clean <40-hex-sha>
#   scripts/bump-dep-pin.sh ay    <40-hex-sha>
#   scripts/bump-dep-pin.sh clean-ay <clean-sha> <ay-sha>
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
CARGO_CLEAN_SIBLING="$ROOT/../clean"
CLEAN_SIBLING="${TRUST_IR_CLEAN_SIBLING:-$CARGO_CLEAN_SIBLING}"

usage() {
    cat >&2 <<'USAGE'
usage: scripts/bump-dep-pin.sh <clean|ay> <40-hex-sha> [options]
       scripts/bump-dep-pin.sh clean-ay <clean-sha> <ay-sha> [options]

  clean-ay                move both pins in one atomic transaction. This is
                          required when the target Clean co-owns a new AY pin;
                          neither single-dependency order can be coherent.

  --offline               skip the remote-existence probe (the frontend lock
                          refresh still needs the network for a clean bump)
  --allow-sibling-ahead   accept a ../clean HEAD that is a DESCENDANT of the
                          rev instead of requiring an exact match
  --no-guard-test         skip the Rust guard test; the toolchain-free census
                          still runs and still proves every leg coherent
  --dry-run               stage the edits and diff them; change nothing

env:
  TRUST_IR_CLEAN_SIBLING  alternate spelling/symlink for ../clean; it must
                          resolve to the checkout Cargo's [patch] compiles
USAGE
    exit 2
}

DEP=""
REV=""
AY_REV=""
OFFLINE=0
ALLOW_SIBLING_AHEAD=0
RUN_GUARD_TEST=1
DRY_RUN=0

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
        --offline) OFFLINE=1 ;;
        --allow-sibling-ahead) ALLOW_SIBLING_AHEAD=1 ;;
        --no-guard-test) RUN_GUARD_TEST=0 ;;
        --dry-run) DRY_RUN=1 ;;
        -h|--help) usage ;;
        *) printf 'unknown option: %q\n' "$1" >&2; usage ;;
    esac
    shift
done

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

validate_sibling_ay_pin() {
    local target="$1"
    [[ -f "$CLEAN_SIBLING/Cargo.toml" ]] \
        || die "no $CLEAN_SIBLING/Cargo.toml — cannot confirm that Clean's
      co-owned AY pin agrees. The root lock resolves AY through Clean too."

    # Match the URL and rev independently of their order on the line. Fail
    # closed on cardinality: six declarations at the right SHA still means an
    # external transaction leg disappeared.
    local declarations count revisions
    declarations="$(grep 'alabsystems/ay\.git' "$CLEAN_SIBLING/Cargo.toml" \
        | grep -o 'rev = "[0-9a-f]\{40\}"' | grep -o '[0-9a-f]\{40\}')"
    count="$(printf '%s\n' "$declarations" \
        | awk 'NF { count += 1 } END { print count + 0 }')"
    revisions="$(printf '%s\n' "$declarations" | awk 'NF' | sort -u)"
    if [[ "$count" -ne 7 ]]; then
        die "found $count ay.git declarations in $CLEAN_SIBLING/Cargo.toml; expected exactly 7.
      A missing or additional declaration means the external leg shape changed,
      not that the sibling agrees. Check the file and update the
      pattern in this script and in
      crates/trust-ir/tests/dependency_pin_coherence.rs together."
    fi
    if [[ "$revisions" != "$target" ]]; then
        die "$CLEAN_SIBLING/Cargo.toml co-owns the AY pin and holds:
$(printf '        %s\n' $revisions)
      expected the exact coordinated AY revision $target. A mismatch would
      put two AY graphs in Cargo.lock, so the transaction is refused."
    fi
}

# Cargo.toml hard-codes every Clean [patch] path under ../clean.  An override
# may name that checkout through a symlink, but it cannot redirect Cargo.  If
# validation inspected one checkout while metadata compiled another, a Clean
# bump could be blessed without ever building the advertised revision.
if [[ -n "${TRUST_IR_CLEAN_SIBLING+x}" ]]; then
    VALIDATED_CLEAN_SIBLING="$(cd "$CLEAN_SIBLING" 2>/dev/null && pwd -P)" \
        || die "TRUST_IR_CLEAN_SIBLING is not an accessible directory: $CLEAN_SIBLING"
    PATCHED_CLEAN_SIBLING="$(cd "$CARGO_CLEAN_SIBLING" 2>/dev/null && pwd -P)" \
        || die "Cargo's [patch] checkout is not accessible: $CARGO_CLEAN_SIBLING"
    [[ "$VALIDATED_CLEAN_SIBLING" == "$PATCHED_CLEAN_SIBLING" ]] \
        || die "TRUST_IR_CLEAN_SIBLING resolves to $VALIDATED_CLEAN_SIBLING,
      but Cargo's [patch] table compiles $PATCHED_CLEAN_SIBLING.
      Arrange TrustIR and Clean as sibling checkouts (or point the override
      through a symlink to ../clean) so validation and compilation agree."
fi

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

REPAIR=0
ALREADY_COHERENT=0
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
    CONTROLLED_LEGS="$(printf '%s\n%s\n' \
        "$(pin legs --root "$ROOT" --dep clean)" \
        "$(pin legs --root "$ROOT" --dep ay)" | sort -u)"
else
    CONTROLLED_LEGS="$(pin legs --root "$ROOT" --dep "$DEP")"
fi
DIRTY="$(git -C "$ROOT" status --porcelain -- $CONTROLLED_LEGS 2>/dev/null)"
if [[ -n "$DIRTY" ]]; then
    warn "pin legs have uncommitted changes:
$DIRTY
      Proceeding — the backup is taken from the WORKING TREE, so a rollback
      restores these edits rather than discarding them."
fi

# A.2 — the dependency-specific preconditions. These are the actual
# bug-catchers: the root [patch] and the sibling Clean checkout's co-ownership of the AY pin both
# live outside this repository's leg table.
# A linked `git worktree` has a `.git` FILE pointing at the shared object
# store, not a `.git` directory. Ask Git whether this is a work tree rather
# than rejecting the exact checkout shape used for isolated pin gates. This is
# required for every transaction kind: the root [patch] compiles this checkout
# while refreshing the lock even when the only pin being moved is AY.
[[ "$(git -C "$CLEAN_SIBLING" rev-parse --is-inside-work-tree 2>/dev/null)" == "true" ]] \
    || die "no Clean sibling checkout at $CLEAN_SIBLING
      The root [patch] resolves clean.git to that path; without it the
      workspace cannot resolve at all. Set TRUST_IR_CLEAN_SIBLING."

SIBLING_DIRTY="$(git -C "$CLEAN_SIBLING" status --porcelain --untracked-files=all)"
if [[ -n "$SIBLING_DIRTY" ]]; then
    die "$CLEAN_SIBLING has uncommitted changes:
$(printf '        %s\n' "$SIBLING_DIRTY")
      The root [patch] compiles those working-tree bytes, not an advertised
      commit. Refusing to certify a pin against a different source tree; use a
      clean isolated sibling checkout for the bump."
fi

if [[ "$DEP" == "clean" || "$DEP" == "clean-ay" ]]; then
    git -C "$CLEAN_SIBLING" rev-parse --verify --quiet "${REV}^{commit}" >/dev/null \
        || die "$CLEAN_SIBLING does not contain $REV.
      The root [patch] is a PATH dep: cargo compiles the sibling's WORKING
      TREE, not the pinned revision, so a pin the sibling lacks is a pin
      nothing builds. Fetch and check it out first (this script will never
      mutate a sibling repository):
          git -C $CLEAN_SIBLING fetch origin
          git -C $CLEAN_SIBLING checkout $REV"

    SIBLING_HEAD="$(git -C "$CLEAN_SIBLING" rev-parse HEAD)"
    if [[ "$SIBLING_HEAD" != "$REV" ]]; then
        if [[ $ALLOW_SIBLING_AHEAD -eq 1 ]] \
            && git -C "$CLEAN_SIBLING" merge-base --is-ancestor "$REV" HEAD; then
            warn "--allow-sibling-ahead: $CLEAN_SIBLING is at $SIBLING_HEAD,
      a DESCENDANT of the pin $REV. The workspace therefore compiles code
      NEWER than what downstream git consumers will resolve."
        else
            die "$CLEAN_SIBLING is at $SIBLING_HEAD, not $REV.
      Because the [patch] is a PATH dep, the workspace would compile the
      sibling's working tree while the manifests advertise a different
      revision. Align them first:
          git -C $CLEAN_SIBLING checkout $REV
      (or pass --allow-sibling-ahead if the sibling is deliberately ahead)"
        fi
    fi

    if [[ "$DEP" == "clean-ay" ]]; then
        # The target Clean already co-owns the target AY pin. Validate that
        # external leg before installing either half of the coordinated move.
        validate_sibling_ay_pin "$AY_REV"
    else
        # A Clean-only transaction is sound only when the target Clean retains
        # TrustIR's current AY authority. If the sibling already co-owns a new
        # AY revision, refreshing Cargo.lock here would resolve a split graph
        # before the single-dependency census has any chance to notice it.
        FROZEN_AY_REV="$(pin current --root "$ROOT" --dep ay)" \
            || die "cannot determine the frozen AY revision before the Clean bump"
        validate_sibling_ay_pin "$FROZEN_AY_REV"
    fi

else
    # An AY-only move must still compile the exact Clean revision advertised by
    # TrustIR. Otherwise `cargo metadata` validates an ambient sibling HEAD and
    # the resulting lock can be blessed without ever building the frozen Clean
    # authority recorded in the manifests.
    FROZEN_CLEAN_REV="$(pin current --root "$ROOT" --dep clean)" \
        || die "cannot determine the frozen Clean revision before the AY bump"
    git -C "$CLEAN_SIBLING" rev-parse --verify --quiet "${FROZEN_CLEAN_REV}^{commit}" >/dev/null \
        || die "$CLEAN_SIBLING does not contain frozen Clean revision $FROZEN_CLEAN_REV"
    SIBLING_HEAD="$(git -C "$CLEAN_SIBLING" rev-parse HEAD)"
    if [[ "$SIBLING_HEAD" != "$FROZEN_CLEAN_REV" ]]; then
        if [[ $ALLOW_SIBLING_AHEAD -eq 1 ]] \
            && git -C "$CLEAN_SIBLING" merge-base --is-ancestor "$FROZEN_CLEAN_REV" HEAD; then
            warn "--allow-sibling-ahead: $CLEAN_SIBLING is at $SIBLING_HEAD,
      a DESCENDANT of frozen Clean $FROZEN_CLEAN_REV. The workspace therefore
      compiles Clean code newer than what TrustIR advertises."
        else
            die "$CLEAN_SIBLING is at $SIBLING_HEAD, not frozen Clean $FROZEN_CLEAN_REV.
      Align the path-patched checkout before moving AY, or explicitly pass
      --allow-sibling-ahead for a non-public preparation run."
        fi
    fi

    # AY leg 6: the sibling Clean checkout's Cargo.toml pins AY too.
    validate_sibling_ay_pin "$REV"
fi

# A.3 — the revision must exist on the remote, or downstream git consumers
# (trust, ty, trust-cg) cannot resolve what we just advertised.
if [[ $OFFLINE -eq 1 ]]; then
    warn "--offline: skipping the remote-existence probe. A revision that is
      local-only will resolve here and fail for every downstream consumer."
else
    PROBE="$TMP/remote-probe"
    git init -q "$PROBE" || die "cannot create the remote probe repository"
    if ! GIT_TERMINAL_PROMPT=0 git -C "$PROBE" fetch --depth=1 -q "$REMOTE" "$REV" \
        2>"$TMP/probe.err"; then
        die "$REMOTE does not serve $REV:
$(sed 's/^/        /' "$TMP/probe.err")
      Push the revision before pinning it, or pass --offline if you are
      deliberately pinning an unpushed commit."
    fi
    printf 'remote %s serves %s\n' "$REMOTE" "$REV"
    if [[ "$DEP" == "clean-ay" ]]; then
        AY_REMOTE="https://github.com/alabsystems/ay.git"
        if ! GIT_TERMINAL_PROMPT=0 git -C "$PROBE" fetch --depth=1 -q "$AY_REMOTE" "$AY_REV" \
            2>"$TMP/ay-probe.err"; then
            die "$AY_REMOTE does not serve $AY_REV:
$(sed 's/^/        /' "$TMP/ay-probe.err")
      Push the AY revision before pinning it, or pass --offline only for a
      deliberately non-public preparation run."
        fi
        printf 'remote %s serves %s\n' "$AY_REMOTE" "$AY_REV"
    fi
fi

# The deferred no-op return (see PHASE A). Reached only after EVERY
# precondition above has passed, so "nothing to do" now means the in-repo legs
# AND the external ones (sibling checkout, sibling AY co-ownership, remote
# reachability) were all confirmed — not merely that the in-repo legs agree
# with each other.
if [[ $ALREADY_COHERENT -eq 1 ]]; then
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
    STAGED="$(pin apply-clean-ay --root "$ROOT" --clean-to "$REV" \
        --ay-to "$AY_REV" --stage-dir "$STAGE")" \
        || die "coordinated staging failed; the working tree was not touched"
else
    STAGED="$(pin apply --root "$ROOT" --dep "$DEP" --to "$REV" --stage-dir "$STAGE")" \
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
# The root lock is refreshed for BOTH dependencies. For a Clean move it is
# normally byte-identical (the [patch] absorbs the revision) — refresh anyway,
# because the sibling's own dependency graph is recorded there.
say "PHASE E — refreshing lockfiles"
cargo metadata --format-version 1 --all-features \
    --manifest-path "$ROOT/Cargo.toml" >/dev/null \
    || die "root lock refresh failed (cargo metadata)"
printf 'refreshed Cargo.lock\n'

if [[ "$DEP" == "clean" || "$DEP" == "clean-ay" ]]; then
    # THE LEG THAT KEEPS GETTING MISSED. frontend/ is a separate, workspace-
    # excluded package with no [patch], so this lock records the git revision
    # literally — and no --workspace command will ever touch it.
    cargo update --manifest-path "$ROOT/frontend/Cargo.toml" -p clean-kernel \
        || die "frontend/Cargo.lock refresh failed (cargo update -p clean-kernel)"
    printf 'refreshed frontend/Cargo.lock\n'
fi

# --- PHASE F: verify ----------------------------------------------------------
say "PHASE F — verification"

# Tier 1 (MANDATORY, no Rust toolchain required): every leg agrees on the new
# revision, and the old one survives nowhere in tracked sources.
if [[ "$DEP" == "clean-ay" ]]; then
    pin census --root "$ROOT" --dep clean \
        || die "post-bump Clean census is still incoherent — see the table above"
    pin census --root "$ROOT" --dep ay \
        || die "post-bump AY census is still incoherent — see the table above"
else
    pin census --root "$ROOT" --dep "$DEP" \
        || die "post-bump census is still incoherent — see the table above"
fi

if [[ $REPAIR -eq 0 ]]; then
    if [[ "$DEP" == "clean-ay" ]]; then
        for OLD_REV in "$CURRENT_CLEAN" "$CURRENT_AY"; do
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
        printf '%s\n' "$GUARD_OUT" | tail -5
        printf 'VERIFY: guard test PASSED\n'
    elif grep -q 'Trust targo was not found' <<<"$GUARD_OUT"; then
        printf 'VERIFY: SKIPPED (targo unavailable) — tier 1 already proved every\n'
        printf '        leg coherent. Run scripts/ci_gates.sh gate 7 before pushing.\n'
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
